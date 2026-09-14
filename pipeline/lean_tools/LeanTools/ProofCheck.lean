import LeanTools.Common
import LeanTools.Frontend
import LeanTools.Mutate
/-!
# `leantools proofcheck` — kernel, axioms, static modularity, opaque re-check (Task 6)

Inputs: the unit, its spec file(s) and proof file(s), and a directory of
admitted callee specs (`<callee>.lean`, one `@[step] theorem … := by sorry`
each). A spec/proof argument may be a file (single-member unit) or a
directory holding `<member>.lean` for every member of the unit; members are
checked together, loop helpers first.

Checks:
1. `kernel_ok` — the spec elaborates with `sorry` replaced by the proof; no
   errors, no `sorry`.
2. `axioms` ⊆ `{propext, Classical.choice, Quot.sound}`.
3. static — constants used by the proof terms (and by auxiliary lemmas the
   proof generated) must not include `g.eq_n`, `g.eq_def`, `g.eq_unfold`,
   `g._unfold`, `g.match_n`, `g._unsafe_rec` for an emitted `g` outside the unit.
4. opaque — a fresh environment with `Aeneas`, the crate's types module, every
   callee replaced by `opaque g : <signature>` plus `@[step] axiom g_spec`,
   the unit's own definitions verbatim, and the spec+proof again.
5. blame — best effort: when the kernel check fails and the error mentions
   exactly one callee outside the unit, that callee's unit is blamed.
-/
open Lean Meta Elab

namespace LeanTools.ProofCheck

structure Result where
  kernel_ok : Bool := false
  axioms : Array String := #[]
  axioms_ok : Bool := false
  static_ok : Bool := false
  static_violations : Array String := #[]
  opaque_ok : Option Bool := none
  opaque_error : String := ""
  error : Option String := none
  blame : Option String := none
  theorems : Array String := #[]
  missing_callee_specs : Array String := #[]
  deriving ToJson, FromJson

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Read `<dir>/<member>.lean` per member, or a single file. -/
def readPerMember (path : System.FilePath) (members : Array Name) : IO (Array (Name × String)) := do
  if ← path.isDir then
    let mut out := #[]
    for m in members do
      let f := path / s!"{m}.lean"
      if ← f.pathExists then out := out.push (m, ← IO.FS.readFile f)
    return out
  else
    return #[(members[0]!, ← IO.FS.readFile path)]

/-- Replace the final `by sorry` of a spec with the proof block. -/
def spliceProof (spec : String) (proof : String) : String :=
  -- dedent uniformly (the model may indent the first line differently from the rest)
  let lines := (proof.splitOn "\n").filter fun l => !l.trimAscii.toString.isEmpty
  let indent := lines.foldl (fun m l => min m ((l.toList.takeWhile (· == ' ')).length)) 1000
  let lines := lines.map fun l => String.ofList (l.toList.drop indent)
  let proof := String.intercalate "\n" lines
  let proofBlock := if proof.startsWith "by" then proof else "by\n  " ++ (String.intercalate "\n  " (proof.splitOn "\n"))
  match spec.splitOn "by sorry" with
  | [] => spec
  | parts =>
    let init := parts.dropLast
    let last := parts.getLast!
    String.intercalate "by sorry" init ++ proofBlock ++ last

private def suffixIsEqLemma (s : String) : Bool :=
  (s.startsWith "eq_" && (String.ofList (s.toList.drop 3)).all Char.isDigit) || s == "eq_def" || s == "eq_unfold" ||
  s == "_unfold" || s == "_sunfold" || s == "_unsafe_rec" || s == "mutual" ||
  (s.startsWith "match_" && (String.ofList (s.toList.drop 6)).all Char.isDigit)

/-- Callee-equation constants reachable from the proofs. -/
def staticViolations (env : Environment) (mods : Std.HashSet Name) (members : Std.HashSet Name)
    (isNode : Name → Bool) (roots : Array Name) : Array String := Id.run do
  let mut visited : Std.HashSet Name := {}
  let mut stack := roots.toList
  let mut viol : Array String := #[]
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
        match u with
        | .str g s =>
          if suffixIsEqLemma s && isNode g && !members.contains g && isCrateConst env mods g then
            if !viol.contains u.toString then viol := viol.push u.toString
        | _ => pure ()
        -- follow auxiliaries generated for this proof (added by the elaboration): they are not
        -- in any module
        if (env.getModuleIdxFor? u).isNone && !visited.contains u then stack := u :: stack
  return viol

/-- Maximal identifier tokens of a text. -/
def identTokens (text : String) : Array String := Id.run do
  let isId (c : Char) := c.isAlphanum || c == '_' || c == '.' || c == '\''
  let mut out := #[]
  let mut cur := ""
  for c in text.toList do
    if isId c then cur := cur.push c
    else
      if !cur.isEmpty then out := out.push cur
      cur := ""
  if !cur.isEmpty then out := out.push cur
  return out

/-- Tactic kinds whose lemma lists unfold definitions. Non-recursive callees are
delta-unfolded by these without any equation lemma appearing in the proof term,
so the static check also inspects the proof *syntax*. -/
private def unfoldingTactic (kind : Name) : Bool :=
  let s := (kind.toString.splitOn ".").getLast!
  ["simp", "simpAll", "dsimp", "simpa", "simpArith", "unfold", "delta", "rwSeq", "rewriteSeq",
   "rwa", "simp_all", "normNum", "unfoldLet", "unfold?"].contains s ||
  s.startsWith "simp"

/-- Callees named inside unfolding tactics of the proof syntax. -/
partial def syntaxUnfolds (callees : Array Name) (stx : Syntax) (acc : Array String) : Array String := Id.run do
  let mut acc := acc
  match stx with
  | .node _ kind args =>
    if unfoldingTactic kind then
      for t in identTokens ((stx.reprint.getD "")) do
        for g in callees do
          let full := g.toString
          if (t == full || full.endsWith ("." ++ t)) && !acc.contains full then acc := acc.push full
    for a in args do acc := syntaxUnfolds callees a acc
    return acc
  | _ => return acc

/-- `def f … : T := …` source → `opaque f … : T` (signature cut at the first ` :=`). -/
def opaqueDecl (src : String) : Option String := Id.run do
  -- drop doc comment and attributes: keep from the first line starting with `def `
  let lines := src.splitOn "\n"
  let some idx := lines.findIdx? (fun l => l.startsWith "def " || l.startsWith "noncomputable def ") | return none
  let body := String.intercalate "\n" (lines.drop idx)
  let body := if body.startsWith "noncomputable def " then String.ofList (body.toList.drop 14) else body
  match body.splitOn " :=" with
  | [] => return none
  | sig :: _ => return some ("opaque " ++ String.ofList (sig.toList.drop 4))

/-- `@[step] theorem n binders : type := by sorry` → `@[step] axiom n binders : type`. -/
def specToAxiom (specText : String) : String :=
  let t := specText.trimAscii.toString
  let t := match t.splitOn ":= by sorry" with
    | s :: _ => s
    | [] => t
  let t := match t.splitOn ":= by\n  sorry" with
    | s :: _ => s
    | [] => t
  (t.replace "theorem " "axiom ").trimAscii.toString

unsafe def run (p : Project) (unit : Name) (members? : Option (Array Name)) (specPath proofPath calleeDir : System.FilePath)
    (typesModule? : Option Name) : IO Json := do
  let env ← p.loadEnv #[`LeanTools.Instances]
  let mods := crateModules env p.ns
  let members := members?.getD (loopFamily env mods unit)
  let lineOf (m : Name) : Nat := match declRangeExt.find? env m with
    | some r => r.range.pos.line
    | none => 0
  let members := members.qsort fun a b => lineOf a < lineOf b
  let memberSet : Std.HashSet Name := members.foldl (·.insert ·) {}
  let header := Mutate.mutantHeader p.ns
  let (isNodeArr, _, _) ← runMeta env do
    let mut acc : Std.HashSet Name := {}
    for n in crateConstNames env mods do
      if let some ci := env.find? n then
        if ← isEmittedFunction env mods n ci then acc := acc.insert n
    return acc
  let isNode := fun n => isNodeArr.contains n
  -- constants the unit needs, in file order: nodes (callees) and every crate constant walked
  -- through on the way to them (globals, instance structures, …), which the opaque scratch
  -- must copy verbatim
  let needed := Id.run do
    let mut acc : Std.HashSet Name := {}
    let mut visited : Std.HashSet Name := {}
    let mut stack : List Name := members.toList
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
          if memberSet.contains u || !isCrateConst env mods u then continue
          acc := acc.insert u
          if !isNode u && !isExternalConst env mods u && !isAuxName u then stack := u :: stack
    return acc
  let neededArr := needed.toArray.qsort fun a b => lineOf a < lineOf b
  let calleeNodes := neededArr.filter isNode
  -- callee specs (admitted elsewhere) as `@[step]` axioms, in scope for both checks
  let mut calleeText := ""
  let mut missing : Array String := #[]
  for g in calleeNodes do
    let f := calleeDir / s!"{g}.lean"
    if ← f.pathExists then calleeText := calleeText ++ specToAxiom (← IO.FS.readFile f) ++ "\n\n"
    else missing := missing.push g.toString
  let rc ← elabCommands env (header ++ calleeText) "<callee specs>"
  unless rc.errors.isEmpty do
    return toJson ({ error := some s!"callee specs do not elaborate: {rc.errors[0]!}", missing_callee_specs := missing } : Result)
  let calleeAxioms : Std.HashSet Name := rc.added.foldl (·.insert ·) {}
  -- 1. assemble spec+proof per member
  let specs ← readPerMember specPath members
  let proofs ← readPerMember proofPath members
  let mut text := ""
  for (m, s) in specs do
    let some (_, pr) := proofs.find? (·.1 == m) | return toJson ({ error := some s!"no proof for {m}" } : Result)
    text := text ++ spliceProof s pr ++ "\n\n"
  let r ← elabCommands rc.env (header ++ text) "<proof>"
  let mut res : Result := { missing_callee_specs := missing }
  let thmNames := r.added.filter fun n => match r.env.find? n with
    | some (.thmInfo _) => !isAuxName n && !(n.toString.endsWith "mvcgen_spec")
    | _ => false
  res := { res with theorems := thmNames.map toString }
  let sorryWarn := r.warnings.any fun w => (w.splitOn "declaration uses `sorry`").length > 1
  if !r.errors.isEmpty || sorryWarn || thmNames.isEmpty then
    let errText := String.intercalate "\n" r.errors.toList
    -- blame: exactly one callee outside the unit mentioned (by any name suffix) in the error text
    let tokens := identTokens errText
    let mentioned := calleeNodes.filter fun g =>
      let full := g.toString
      tokens.any fun t => t == full || full.endsWith ("." ++ t)
    let blame := if mentioned.size == 1 then some mentioned[0]!.toString else none
    let errMsg := if errText.isEmpty then "declaration uses sorry" else errText
    return toJson { res with kernel_ok := false, blame, error := some errMsg }
  res := { res with kernel_ok := true }
  -- 2. axioms
  let (axs, _, _) ← runMeta r.env do
    let mut acc : Array Name := #[]
    for t in thmNames do
      let a ← collectAxioms t
      for x in a do if !acc.contains x then acc := acc.push x
    return acc
  let axs := axs.filter fun a => !calleeAxioms.contains a
  res := { res with axioms := axs.map toString, axioms_ok := axs.all allowedAxioms.contains }
  -- 3. static
  let mut viol := staticViolations r.env mods memberSet isNode thmNames
  for c in r.commands do
    viol := syntaxUnfolds calleeNodes c viol
  res := { res with static_violations := viol, static_ok := viol.isEmpty }
  if !res.static_ok || !res.axioms_ok then
    return toJson res
  -- 4. opaque re-check in a fresh environment: Aeneas + types + instances
  let typesModule := typesModule?.getD (p.ns ++ `Types)
  -- external models (`<ns>.FunsExternal`, `<ns>.FunsExternalSpecs`, …) are not callees: keep them
  let externalMods := env.header.moduleNames.filter fun m =>
    p.ns.isPrefixOf m && (m.getString!.endsWith "External" || m.getString!.endsWith "ExternalSpecs")
  let envO ← (do
    initSearchPath (← findSysroot)
    Lean.enableInitializersExecution
    let imports := #[{ module := `Aeneas }, { module := typesModule }, { module := `LeanTools.Instances }]
      ++ externalMods.map fun m => ({ module := m } : Import)
    importModules (imports := imports) (opts := {}) (trustLevel := 0) (loadExts := true))
  -- nodes outside the unit → opaque + spec axiom; other crate constants not in the
  -- types module → verbatim source
  let typesIdx := env.getModuleIdx? typesModule
  let mut cache : SourceCache := {}
  let mut scratch := ""
  for g in neededArr do
    if env.getModuleIdxFor? g == typesIdx || isExternalConst env mods g then continue
    let (c', s?) ← declSource p env cache g
    cache := c'
    let some src := s? | continue
    if isNode g then
      let some od := opaqueDecl src | continue
      scratch := scratch ++ od ++ "\n\n"
      let f := calleeDir / s!"{g}.lean"
      if ← f.pathExists then
        scratch := scratch ++ specToAxiom (← IO.FS.readFile f) ++ "\n\n"
    else
      if isAuxName g then continue
      scratch := scratch ++ src ++ "\n\n"
  for m in members do
    let (c', s?) ← declSource p env cache m
    cache := c'
    scratch := scratch ++ (s?.getD "") ++ "\n\n"
  scratch := scratch ++ text
  let ro ← elabCommands envO (header ++ scratch) "<opaque>"
  let sorryO := ro.warnings.any fun w => (w.splitOn "declaration uses `sorry`").length > 1 && !(w.splitOn "axiom").length > 1
  if ro.errors.isEmpty && !sorryO then
    res := { res with opaque_ok := some true }
  else
    let oerr := String.intercalate "\n" ro.errors.toList
    res := { res with opaque_ok := some false, opaque_error := oerr }
  return toJson res

end LeanTools.ProofCheck
