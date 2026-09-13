import LeanTools.Common
import LeanTools.Frontend
/-!
# `leantools mutate` — type-preserving mutants of a unit (Task 4)

Mutants are produced as *source splices* on the unit's pretty-printed
definitions: the text is parsed with the project's syntax, mutation sites are
located on the syntax tree (restricted to definition bodies), and each site
yields one candidate. Every member of the unit (`f`, `f_loop`, `f_loop.body`)
is renamed to `<name>_mut<n>` — references included — and the candidate is
re-elaborated in the project environment; candidates that fail to elaborate
are dropped, so every emitted mutant is a well-typed program with the
original's signature.

Operators (`op` tag): `arith_swap`, `rel_swap`, `bound_shift`, `branch_swap`,
`ok_to_fail`, `drop_bind`, `list_perm`, `list_dup`, `list_drop`.
-/
open Lean Elab Parser

namespace LeanTools.Mutate

structure Edit where
  startPos : String.Pos.Raw
  endPos : String.Pos.Raw
  replacement : String
  deriving Inhabited

structure Candidate where
  op : String
  edits : Array Edit
  /-- position of the first edit, for reporting -/
  pos : String.Pos.Raw
  deriving Inhabited

structure Mutant where
  id : String
  op : String
  site : String           -- "line:col" in the unit source
  before : String         -- original text at the (first) site
  after : String          -- replacement text
  source : String         -- the mutated, renamed unit source (all members)
  names : Array (String × String)   -- original member → mutated member
  deriving ToJson, FromJson, Inhabited

/-- Header used to parse/elaborate unit sources and mutants. -/
def mutantHeader (ns : Name) : String :=
  specHeader ns ++ "open ControlFlow Error\n"

/-- Apply edits (non-overlapping), last first. -/
def applyEdits (text : String) (edits : Array Edit) : String := Id.run do
  let sorted := edits.qsort fun a b => a.startPos.byteIdx > b.startPos.byteIdx
  let mut t := text
  for e in sorted do
    t := String.Pos.Raw.extract t ⟨0⟩ e.startPos ++ e.replacement ++ String.Pos.Raw.extract t e.endPos t.rawEndPos
  return t

private def isIdChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == '\'' || c == '!' || c == '?' || c.val > 127

/-- Rename maximal identifier tokens found in `table`. Doc comments and strings
are scanned too, which is harmless for the names we rename. -/
def renameIdents (text : String) (table : Std.HashMap String String) : String := Id.run do
  let chars := text.toList.toArray
  let mut out : String := ""
  let mut i := 0
  while i < chars.size do
    if isIdChar chars[i]! then
      let mut j := i
      while j < chars.size && isIdChar chars[j]! do j := j + 1
      let tok := String.ofList (chars.extract i j).toList
      out := out ++ (table.getD tok tok)
      i := j
    else
      out := out.push chars[i]!
      i := i + 1
  return out

/-- Range of a syntax node in the source text. -/
private def rangeOf (stx : Syntax) : Option (String.Pos.Raw × String.Pos.Raw) :=
  match stx.getPos?, stx.getTailPos? with
  | some s, some e => some (s, e)
  | _, _ => none

private def within (r : String.Pos.Raw × String.Pos.Raw) (lo hi : String.Pos.Raw) : Bool :=
  lo.byteIdx ≤ r.1.byteIdx && r.2.byteIdx ≤ hi.byteIdx

private def textOf (text : String) (stx : Syntax) : String :=
  match rangeOf stx with
  | some (s, e) => String.Pos.Raw.extract text s e
  | none => ""

private def swapAtom : Std.HashMap String (String × String) :=
  Std.HashMap.ofList [
    ("+", ("-", "arith_swap")), ("-", ("+", "arith_swap")),
    ("*", ("/", "arith_swap")), ("/", ("*", "arith_swap")),
    ("<", ("≤", "rel_swap")), ("≤", ("<", "rel_swap")),
    (">", ("≥", "rel_swap")), ("≥", (">", "rel_swap")),
    ("=", ("≠", "rel_swap")), ("≠", ("=", "rel_swap")),
    ("==", ("!=", "rel_swap")), ("!=", ("==", "rel_swap"))]

private def isOkHead (stx : Syntax) : Bool :=
  stx.isIdent && (let s := stx.getId.toString; s == "ok" || s == "Result.ok" || s == "Aeneas.Std.Result.ok")

/-- Shift every line after the first by `toCol - fromCol` columns, so that a
multi-line block moved to a different column keeps its layout. -/
def reindent (txt : String) (fromCol toCol : Nat) : String :=
  match txt.splitOn "\n" with
  | [] => txt
  | first :: rest =>
    let shift (l : String) : String :=
      if toCol ≥ fromCol then String.ofList (List.replicate (toCol - fromCol) ' ') ++ l
      else
        let k := fromCol - toCol
        let lead := (l.toList.takeWhile (· == ' ')).length
        String.ofList (l.toList.drop (min k lead))
    String.intercalate "\n" (first :: rest.map shift)

/-- Direct children with one level of `null` grouping nodes flattened. -/
private def flatChildren (args : Array Syntax) : Array Syntax :=
  args.flatMap fun a => if a.getKind == nullKind then a.getArgs else #[a]

/-- Collect candidates from one definition body. -/
partial def collect (fileMap : FileMap) (text : String) (lo hi : String.Pos.Raw) (stx : Syntax) (acc : Array Candidate) : Array Candidate := Id.run do
  let mut acc := acc
  let colOf (pos : String.Pos.Raw) : Nat := (fileMap.toPosition pos).column
  let moved (src : Syntax) (dst : Syntax) : String :=
    match rangeOf src, rangeOf dst with
    | some rs, some rd => reindent (textOf text src) (colOf rs.1) (colOf rd.1)
    | _, _ => textOf text src
  match stx with
  | .node _ kind args =>
    if let some r := rangeOf stx then
      if within r lo hi then
        let k := kind.toString
        -- binary operators: `«term_+_»` etc. have the operator atom at index 1
        if k.startsWith "«term_" && args.size == 3 then
          if let .atom info a := args[1]! then
            if let some (rep, op) := swapAtom[a]? then
              if let (some s, some e) := (info.getPos?, info.getTailPos?) then
                acc := acc.push { op, edits := #[{ startPos := s, endPos := e, replacement := rep }], pos := s }
        -- numeric literals
        if kind == `num then
          if let some n := stx.isNatLit? then
            acc := acc.push { op := "bound_shift", edits := #[{ startPos := r.1, endPos := r.2, replacement := toString (n + 1) }], pos := r.1 }
            if n ≥ 1 then
              acc := acc.push { op := "bound_shift", edits := #[{ startPos := r.1, endPos := r.2, replacement := toString (n - 1) }], pos := r.1 }
        -- if-then-else (plain and dependent): swap the branches
        if kind == `termIfThenElse || kind == `termDepIfThenElse || kind == ``Lean.Parser.Term.doIf then
          let fa := flatChildren args
          let mut thenT : Option Syntax := none
          let mut elseT : Option Syntax := none
          for i in [0:fa.size] do
            if let .atom _ "then" := fa[i]! then thenT := fa[i+1]?
            if let .atom _ "else" := fa[i]! then elseT := fa[i+1]?
          if let (some t, some e) := (thenT, elseT) then
            if let (some rt, some re) := (rangeOf t, rangeOf e) then
              acc := acc.push { op := "branch_swap", pos := rt.1, edits := #[
                { startPos := rt.1, endPos := rt.2, replacement := moved e t },
                { startPos := re.1, endPos := re.2, replacement := moved t e }] }
        -- match: rotate the arm bodies
        if kind == ``Lean.Parser.Term.match || kind == ``Lean.Parser.Term.doMatch then
          if let some alts := args.find? fun a => a.isOfKind ``Lean.Parser.Term.matchAlts || a.isOfKind ``Lean.Parser.Term.doMatchAlts then
            let arms := alts.getArgs.filter fun a => a.isOfKind ``Lean.Parser.Term.matchAlt || a.getKind.toString.endsWith "MatchAlt"
            if arms.size ≥ 2 then
              let rhs := arms.map fun a => a.getArgs.back!
              if rhs.all fun x => (rangeOf x).isSome then
                let mut edits := #[]
                for i in [0:rhs.size] do
                  let (s, e) := (rangeOf rhs[i]!).get!
                  edits := edits.push { startPos := s, endPos := e, replacement := moved rhs[(i + 1) % rhs.size]! rhs[i]! }
                acc := acc.push { op := "branch_swap", pos := (rangeOf rhs[0]!).get!.1, edits }
        -- `ok e`: failure and semantic-relation mutants
        if kind == ``Lean.Parser.Term.app && args.size == 2 && isOkHead args[0]! then
          let argsNode := args[1]!
          if argsNode.getNumArgs == 1 then
            let arg := argsNode[0]!
            let argText := textOf text arg
            acc := acc.push { op := "ok_to_fail", pos := r.1, edits := #[{ startPos := r.1, endPos := r.2, replacement := "(Aeneas.Std.Result.fail Aeneas.Std.Error.panic)" }] }
            for (op, fn) in [("list_perm", "perm"), ("list_dup", "dup"), ("list_drop", "drop")] do
              acc := acc.push { op, pos := r.1, edits := #[{ startPos := r.1, endPos := r.2, replacement := s!"(Aeneas.Std.Result.ok (LeanTools.Mut.{fn} ({argText})))" }] }
        -- `let x ← e` in `do`: the bound value becomes `default`
        if kind == ``Lean.Parser.Term.doLetArrow then
          let decl := (args.find? fun a => a.isOfKind ``Lean.Parser.Term.doIdDecl || a.isOfKind ``Lean.Parser.Term.doPatDecl).getD Syntax.missing
          let dargs := decl.getArgs
          for i in [0:dargs.size] do
            if let .atom _ "←" := dargs[i]! then
              if let some rhs := dargs[i+1]? then
                if let some (s, e) := rangeOf rhs then
                  acc := acc.push { op := "drop_bind", pos := s, edits := #[{ startPos := s, endPos := e, replacement := s!"(LeanTools.Mut.dropBind ({textOf text rhs}))" }] }
    for a in args do
      acc := collect fileMap text lo hi a acc
    return acc
  | _ => return acc

/-- Bodies (`declVal`) of the definitions in the parsed commands. -/
def bodyRanges (cmds : Array Syntax) : Array (String.Pos.Raw × String.Pos.Raw) := Id.run do
  let mut out := #[]
  for c in cmds do
    if c.isOfKind ``Lean.Parser.Command.declaration then
      let d := c[1]
      if d.isOfKind ``Lean.Parser.Command.definition then
        if let some r := rangeOf d[3] then out := out.push r
  return out

/-- Deterministic shuffle. -/
def shuffle (xs : Array α) (seed : Nat) : Array α := Id.run do
  let mut g := mkStdGen seed
  let mut a := xs
  for i in [0:a.size] do
    let (j, g') := randNat g i (a.size - 1)
    g := g'
    a := a.swapIfInBounds i j
  return a

/-- Interleave candidates across operators (uniform over operators, then uniform
within an operator), deterministically. -/
def interleave (cands : Array Candidate) (seed : Nat) : Array Candidate := Id.run do
  let ops := (cands.map (·.op)).toList.eraseDups.toArray.qsort (fun a b => decide (a < b))
  let mut queues : Array (Array Candidate) := ops.map fun op => shuffle (cands.filter (·.op == op)) seed
  let mut out := #[]
  let mut progress := true
  while progress do
    progress := false
    for i in [0:queues.size] do
      if h : i < queues.size then
        let q := queues[i]
        if q.size > 0 then
          out := out.push q[q.size - 1]!
          queues := queues.set i q.pop
          progress := true
  return out

structure Result where
  unit : String
  members : Array String
  header : String
  original : String
  candidates : Nat
  dropped : Array (String × String)   -- (op, first error line) for candidates that failed to elaborate
  mutants : Array Mutant
  deriving ToJson, FromJson

/-- Generate up to `max` elaborating mutants of the unit whose members are `members`. -/
def generate (p : Project) (env : Environment) (_mods : Std.HashSet Name) (unitId : Name)
    (members : Array Name) (max : Nat) (seed : Nat) : IO Result := do
  -- 1. unit source, members in declaration order (loop bodies precede loops precede parents)
  let lineOf (m : Name) : Nat := match declRangeExt.find? env m with
    | some r => r.range.pos.line
    | none => 0
  let members := members.qsort fun a b => lineOf a < lineOf b
  let mut cache : SourceCache := {}
  let mut src := ""
  for m in members do
    let (c', s?) ← declSource p env cache m
    cache := c'
    let some s := s? | throw <| IO.userError s!"no source for {m}"
    src := src ++ s ++ "\n\n"
  let header := mutantHeader p.ns
  let nsPrefix := p.ns.toString ++ "."
  let short (n : Name) : String :=
    let s := n.toString
    if s.startsWith nsPrefix then String.ofList (s.toList.drop nsPrefix.length) else s
  let renameTable (suffix : String) (from_ : String := "") : Std.HashMap String String := Id.run do
    let mut table : Std.HashMap String String := {}
    for m in members do
      let s := short m
      table := table.insert (s ++ from_) (s ++ suffix) |>.insert (nsPrefix ++ s ++ from_) (nsPrefix ++ s ++ suffix)
    return table
  -- 2. parse a `_mut0` copy (the originals already exist in the environment); this
  --    also checks that the unit's source elaborates as we reproduce it
  let src0 := renameIdents src (renameTable "_mut0")
  let full := header ++ src0
  let r ← elabCommands env full "<unit>"
  unless r.errors.isEmpty do
    throw <| IO.userError s!"unit source does not elaborate: {r.errors[0]!}"
  let cmds := r.commands
  let fileMap := FileMap.ofString full
  let mut cands : Array Candidate := #[]
  for (lo, hi) in bodyRanges cmds do
    for c in cmds do
      cands := collect fileMap full lo hi c cands
  let ordered := interleave cands seed
  let mut mutants : Array Mutant := #[]
  let mut dropped : Array (String × String) := #[]
  let mut k := 0
  for cand in ordered do
    if mutants.size ≥ max then break
    k := k + 1
    let suffix := s!"_mut{k}"
    let names : Array (String × String) := members.map fun m => (m.toString, m.toString ++ suffix)
    let mutatedFull := applyEdits full cand.edits
    let mutatedSrc := renameIdents (String.Pos.Raw.extract mutatedFull header.rawEndPos mutatedFull.rawEndPos) (renameTable suffix "_mut0")
    -- 3. re-elaborate on the base environment
    let r' ← elabCommands env (header ++ mutatedSrc) s!"<mut{k}>"
    if r'.errors.isEmpty then
      let e0 := cand.edits[0]!
      let pos := fileMap.toPosition cand.pos
      let srcPos := fileMap.toPosition header.rawEndPos
      mutants := mutants.push {
        id := s!"m{k}", op := cand.op,
        site := s!"{pos.line - srcPos.line + 1}:{pos.column}",
        before := String.Pos.Raw.extract full e0.startPos e0.endPos,
        after := e0.replacement,
        source := mutatedSrc, names }
    else
      dropped := dropped.push (cand.op, (r'.errors[0]!.splitOn "\n")[0]!)
  return { unit := unitId.toString, members := members.map toString, header,
           original := src, candidates := cands.size, dropped, mutants }

def run (p : Project) (unit : Name) (members? : Option (Array Name)) (max seed : Nat) : IO Json := do
  let env ← p.loadEnv #[`LeanTools.Instances, `LeanTools.Mut]
  let mods := crateModules env p.ns
  let members := members?.getD (loopFamily env mods unit)
  let res ← generate p env mods unit members max seed
  return toJson res

end LeanTools.Mutate
