import Lean
/-!
# Shared plumbing for the `leantools` commands

Environment loading, name classification for Aeneas-emitted constants,
source-span extraction and JSON helpers. Every command returns one JSON
object on stdout; see `Main.lean`.
-/
open Lean Meta

namespace LeanTools

/-- Where the emitted project lives and which root module / namespace it uses. -/
structure Project where
  root : System.FilePath
  /-- Root module and namespace of the emitted crate (e.g. `Corpus`). -/
  ns : Name
  deriving Repr

/-- Load the emitted project's environment (root module only; it imports everything). -/
def Project.loadEnv (p : Project) (extraImports : Array Name := #[]) : IO Environment := do
  initSearchPath (← findSysroot)
  let imports := (#[p.ns] ++ extraImports).map fun m => ({ module := m } : Import)
  importModules (imports := imports) (opts := {}) (trustLevel := 0) (loadExts := true)

/-- Run a `MetaM` computation against a loaded environment, returning the value and
the messages produced. Heartbeats are unlimited; commands impose their own timeouts. -/
def runMeta (env : Environment) (x : MetaM α) (fileName : String := "<leantools>") : IO (α × Environment × MessageLog) := do
  let opts : Options := maxHeartbeats.set {} 0
  let ctx : Core.Context := { fileName, fileMap := default, options := opts,
                              maxHeartbeats := 0, currNamespace := .anonymous }
  let (a, coreSt, _) ← x.toIO ctx { env }
  return (a, coreSt.env, coreSt.messages)

/-- Modules emitted for the crate: everything under the root namespace. -/
def crateModules (env : Environment) (ns : Name) : Std.HashSet Name :=
  env.header.moduleNames.foldl (init := {}) fun acc m =>
    if ns.isPrefixOf m then acc.insert m else acc

/-- All constant names declared in the crate's modules (cheap: does not scan Mathlib). -/
def crateConstNames (env : Environment) (mods : Std.HashSet Name) : Array Name := Id.run do
  let mut out := #[]
  for m in mods.toList do
    if let some idx := env.getModuleIdx? m then
      out := out ++ env.header.moduleData[idx.toNat]!.constNames
  return out

/-- Is `n` an external model: declared in a crate module named `…External` (Aeneas's
`FunsExternal` / `TypesExternal`), or an axiom / opaque constant of the crate? -/
def isExternalConst (env : Environment) (mods : Std.HashSet Name) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    mods.contains m && ((m.getString!.endsWith "External") ||
      (match env.find? n with | some (.axiomInfo _) | some (.opaqueInfo _) => true | _ => false))
  | none => false

/-- Is `n` declared in one of the crate's modules? -/
def isCrateConst (env : Environment) (mods : Std.HashSet Name) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => mods.contains env.header.moduleNames[idx.toNat]!
  | none => false

private def numericSuffix (s : String) (prefix_ : String) : Bool :=
  s.startsWith prefix_ && (s.drop prefix_.length).all Char.isDigit && s.length > prefix_.length

/-- Names Lean (or Aeneas) generates alongside a definition rather than definitions
in their own right: `_unsafe_rec`, `match_n`, `_proof_n`, `proof_n`, `eq_n`,
`eq_def`, `.mutual`, `induct`, … -/
def isAuxName (n : Name) : Bool :=
  n.isInternal || n.isInternalDetail ||
  match n with
  | .str _ s =>
    s.startsWith "_" || numericSuffix s "match_" || numericSuffix s "proof_" ||
    numericSuffix s "eq_" || s == "eq_def" || s == "eq_unfold" || s == "mutual" ||
    s == "induct" || s == "mutual_induct" || s == "fixpoint_induct" ||
    s == "partial_correctness" || s == "read_discriminant" || numericSuffix s "spec_"
  | .num .. => true
  | .anonymous => true

/-- Head constant of a type after stripping its Π-binders. -/
def resultHead (type : Expr) : MetaM (Option Name) :=
  forallTelescopeReducing type fun _ body => do
    return body.getAppFn.constName?

/-- Is `n` an Aeneas-emitted *function*: a definition in a crate module whose
return type is `Result _`, and not an auxiliary? -/
def isEmittedFunction (env : Environment) (mods : Std.HashSet Name) (n : Name) (ci : ConstantInfo) : MetaM Bool := do
  let .defnInfo _ := ci | return false
  unless isCrateConst env mods n do return false
  if isExternalConst env mods n then return false
  if isAuxName n then return false
  if isMatcherCore env n || isAuxRecursor env n || isRecCore env n || isCasesOnRecursor env n then return false
  if env.isProjectionFn n then return false
  if ← isInstance n then return false
  return (← resultHead ci.type) == some `Aeneas.Std.Result

/-- Constants used by `n`'s value, following auxiliary constants of the crate
(matchers, `_proof_n`, `_unsafe_rec`, `.mutual`, instance structures, …)
transitively but stopping at emitted functions and at anything outside the crate. -/
partial def reachableConsts (env : Environment) (mods : Std.HashSet Name)
    (isNode : Name → Bool) (start : Name) : Std.HashSet Name := Id.run do
  let mut visited : Std.HashSet Name := {}
  let mut out : Std.HashSet Name := {}
  let mut stack : List Name := [start]
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c then continue
      visited := visited.insert c
      let some ci := env.find? c | continue
      let some v := ci.value? | continue
      for u in v.getUsedConstants do
        if u == start then
          out := out.insert u
        else if isNode u then
          out := out.insert u
        else if isExternalConst env mods u then
          -- external model: a leaf, reported by the graph as `externals`
          out := out.insert u
        else if isCrateConst env mods u then
          -- auxiliary of the crate: walk through it (but not through `_proof_n`
          -- terms — decidability proofs of literals never mention emitted functions)
          match u with
          | .str _ s => if s.startsWith "_proof_" || (s.startsWith "proof_") then pure () else stack := u :: stack
          | _ => stack := u :: stack
        else
          out := out.insert u
  return out

/-- File of a module relative to the project root (`Corpus.Funs` → `Corpus/Funs.lean`). -/
def moduleFile (p : Project) (m : Name) : System.FilePath :=
  let parts := m.components.map toString
  (parts.foldl (init := p.root) fun acc c => acc / c).addExtension "lean"

/-- The lines `[l₀, l₁]` (1-based, inclusive) of a file, joined. Cached per file. -/
structure SourceCache where
  files : Std.HashMap System.FilePath (Array String) := {}

def SourceCache.lines (c : SourceCache) (f : System.FilePath) : IO (SourceCache × Array String) := do
  match c.files[f]? with
  | some ls => return (c, ls)
  | none =>
    let txt ← IO.FS.readFile f
    let ls := (txt.splitOn "\n").toArray
    return ({ files := c.files.insert f ls }, ls)

/-- Source text of a declaration (the whole command: doc comment, attributes,
signature, body, `partial_fixpoint`), via the persisted declaration ranges. -/
def declSource (p : Project) (env : Environment) (c : SourceCache) (n : Name) : IO (SourceCache × Option String) := do
  let some ranges := declRangeExt.find? env n | return (c, none)
  let some idx := env.getModuleIdxFor? n | return (c, none)
  let m := env.header.moduleNames[idx.toNat]!
  let (c, ls) ← c.lines (moduleFile p m)
  let r := ranges.range
  let l0 := r.pos.line - 1
  let l1 := r.endPos.line - 1
  if l1 < ls.size then
    return (c, some (String.intercalate "\n" (ls.extract l0 (l1 + 1)).toList))
  return (c, none)

/-- Strip one `_loop<digits>` suffix, after dropping a trailing `.body` component. -/
def stripLoopSuffix (n : Name) : Option Name :=
  let n := match n with
    | .str p "body" => p
    | _ => n
  match n with
  | .str p s =>
    match s.splitOn "_loop" with
    | [] | [_] => none
    | parts =>
      let last := parts.getLast!
      if last.all Char.isDigit then
        let base := String.intercalate "_loop" (parts.dropLast)
        if base.isEmpty then none else some (.str p base)
      else none
  | _ => none

/-- The closest name-pattern ancestor of `n` satisfying `isNode`. -/
partial def loopParentByName (isNode : Name → Bool) (n : Name) : Option Name :=
  match stripLoopSuffix n with
  | none => none
  | some p => if isNode p then some p else loopParentByName isNode p

/-- Root of the loop-name chain of `n` (`f_loop0_loop0.body` → `f`). -/
def loopRootByName (isNode : Name → Bool) (n : Name) : Name := Id.run do
  let mut cur := n
  for _ in [0:16] do
    match loopParentByName isNode cur with
    | some p => cur := p
    | none => break
  return cur

/-- `unit` together with every crate constant whose loop-name chain leads to it
(by name only; the graph command additionally checks edges). -/
def loopFamily (env : Environment) (mods : Std.HashSet Name) (unit : Name) : Array Name := Id.run do
  let names := crateConstNames env mods
  let isNode := fun n => env.contains n && !isAuxName n
  let mut out := #[unit]
  for n in names do
    if n != unit && !isAuxName n && loopRootByName isNode n == unit then out := out.push n
  return out

/-- Strip the `Aeneas.Std.` prefix for compact type heads. -/
def shortName (n : Name) : String :=
  let s := n.toString
  if s.startsWith "Aeneas.Std." then String.ofList (s.toList.drop "Aeneas.Std.".length) else s

/-- Print a JSON object and exit with status 0. -/
def emit (j : Json) : IO Unit := IO.println j.compress

/-- Print `{"error": msg}` and exit 1. -/
def emitError (msg : String) : IO Unit := do
  IO.println (Json.mkObj [("error", msg)]).compress
  IO.Process.exit 1

/-- Minimal `--key value` argument parser; flags without values are set to "true". -/
def parseArgs (args : List String) : Std.HashMap String String := Id.run do
  let mut m : Std.HashMap String String := {}
  let mut rest := args
  while true do
    match rest with
    | [] => break
    | k :: v :: tl =>
      if k.startsWith "--" then
        if v.startsWith "--" then
          m := m.insert (String.ofList (k.toList.drop 2)) "true"; rest := v :: tl
        else
          m := m.insert (String.ofList (k.toList.drop 2)) v; rest := tl
      else rest := v :: tl
    | [k] =>
      if k.startsWith "--" then m := m.insert (String.ofList (k.toList.drop 2)) "true"
      rest := []
  return m

def Project.ofArgs (a : Std.HashMap String String) : IO Project := do
  let some root := a["project"]? | throw <| IO.userError "missing --project"
  let ns := (a.getD "namespace" "Corpus").toName
  return { root := root, ns }

end LeanTools
