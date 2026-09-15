import LeanTools.Common
import LeanTools.Frontend
import LeanTools.Instances
import LeanTools.Sample
import LeanTools.Mut
import LeanTools.Eval
import LeanTools.Mutate
/-!
# `leantools gate` — mutation + PBT gate for one spec (Task 5)

Builds a scratch program on top of the project environment:

* `deriving instance Repr/DecidableEq/Arbitrary/Shrinkable` for every crate
  type reachable from the spec's binders and the target's result type
  (each derivation elaborated separately; failures are tolerated and reported);
* the mutants of the unit (Task 4);
* `LT_In` — the input telescope of the spec's *data* binders as nested `Σ`;
  `LT_gen` samples it in binder order (`Usize` binders that later binders
  depend on — array lengths — are drawn small);
* `LT_pre` (hypotheses), `LT_spec_orig` (the closed Prop's `Decidable` instance
  compiled to `Bool`), `LT_run_orig` (the program), and per mutant
  `LT_spec_m<k>`, `LT_run_m<k>`, `LT_diff_m<k>` (observational difference);
* `LT_main : IO String` calling `LeanTools.Eval.gateMain`, evaluated with
  `evalExpr` (compiled IR, never kernel `decide`).

Output is the gate result of IMPLEMENTATION.md §3.4.
-/
open Lean Meta Elab

namespace LeanTools.Gate

/-- One binder group of the theorem, as written. -/
structure Binder where
  names : Array String
  type : String
  isProp : Bool
  small : Bool          -- draw as a small Usize (array length parameter)
  deriving Repr, Inhabited

private def binderKinds : List Name :=
  [``Parser.Term.explicitBinder, ``Parser.Term.implicitBinder, ``Parser.Term.strictImplicitBinder, ``Parser.Term.instBinder]

/-- Binder groups from the theorem's `declSig`, with `isProp`/`small` decided on the
elaborated statement. -/
def binderGroups (env : Environment) (thmType : Expr) (bindersStx : Syntax) : IO (Array Binder) := do
  -- elaborated facts by user name
  let ((props, smalls), _, _) ← runMeta env do
    forallTelescope thmType fun xs _ => do
      let mut props : Std.HashSet String := {}
      let mut smalls : Std.HashSet String := {}
      for h : i in [0:xs.size] do
        let d ← xs[i].fvarId!.getDecl
        let n := d.userName.toString
        if ← isProp d.type then props := props.insert n
        else
          -- `Usize`-typed and mentioned by a later binder's type
          let isUsize := match (← instantiateMVars d.type).getAppFn.constName? with
            | some c => c == `Aeneas.Std.Usize || c == `Aeneas.Std.UScalar
            | none => false
          if isUsize then
            -- a length parameter: implicit (`{SIZE : Usize}`, a const generic) or mentioned by a
            -- later binder's type; sampled small so arrays stay small
            let mut used := d.binderInfo != .default
            for j in [i+1:xs.size] do
              let dj ← xs[j]!.fvarId!.getDecl
              if (← instantiateMVars dj.type).containsFVar xs[i].fvarId! then used := true
            if used then smalls := smalls.insert n
      return (props, smalls)
  let mut out := #[]
  for b in bindersStx.getArgs do
    if binderKinds.contains b.getKind then
      let idents := b[1].getArgs.filterMap fun i => if i.isIdent then some i.getId.toString else
        if let .atom _ "_" := i then some "_" else none
      -- type: explicit/implicit binders carry `[":" type]` at index 2; instBinder has the type at 2 as well
      let tyStx := if b.isOfKind ``Parser.Term.instBinder then b[2] else b[2][1]
      let ty := (tyStx.reprint.getD "").trimAscii.toString
      let isProp := idents.all props.contains
      let small := idents.all smalls.contains
      out := out.push { names := idents, type := ty, isProp, small }
  return out

/-- Crate inductive types reachable from `e` through constructor argument types. -/
partial def crateTypesOf (env : Environment) (mods : Std.HashSet Name) (e : Expr) (acc : Std.HashSet Name) : Std.HashSet Name := Id.run do
  let mut acc := acc
  let mut stack : List Name := e.getUsedConstants.toList
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if acc.contains c then continue
      let foreignModel := (`Aeneas.Std.core).isPrefixOf c || (`Aeneas.Std.alloc).isPrefixOf c
      if !isCrateConst env mods c && !foreignModel then continue
      match env.find? c with
      | some (.inductInfo info) =>
        acc := acc.insert c
        for ctor in info.ctors do
          if let some (.ctorInfo ci) := env.find? ctor then
            stack := ci.type.getUsedConstants.toList ++ stack
      | some ci =>
        -- type abbreviations (`@[reducible] def T := …`): follow the body
        if let some v := ci.value? then
          if ci.type.isSort || ci.type.getForallBody.isSort then
            stack := v.getUsedConstants.toList ++ stack
      | none => pure ()
  return acc

/-- Hand-built instance text for a structure when `deriving instance` fails (parameterised
structures such as `MlKemPrivateKey (SIZE : Usize)`, or Aeneas's `core.ops.range.Range`). -/
def fallbackInstance (env : Environment) (t : Name) (cls : String) : MetaM (Option String) := do
  let some (.inductInfo info) := env.find? t | return none
  let some sinfo := getStructureInfo? env t | return none
  let fields := sinfo.fieldNames
  if fields.isEmpty then return none
  forallTelescope info.type fun params _ => do
    let mut binders := ""
    let mut instBinders := ""
    let mut args := ""
    for p in params do
      let d ← p.fvarId!.getDecl
      let dty ← instantiateMVars d.type
      let ty ← if dty.isSort then pure (Std.Format.text "Type") else ppExpr dty
      binders := binders ++ s!" \{{d.userName} : {ty}}"
      args := args ++ s!" {d.userName}"
      if (← instantiateMVars d.type).isSort then
        let c := match cls with
          | "Arbitrary" => "Plausible.Arbitrary" | "Shrinkable" => "Plausible.Shrinkable"
          | "Repr" => "Repr" | _ => "DecidableEq"
        instBinders := instBinders ++ s!" [{c} {d.userName}]"
    let target := s!"({t}{args})"
    -- field names may be keywords (`end`): quote accessors, use positional names for binders
    let fs := fields.map fun f => s!"«{f}»"
    let vs := (List.range fs.size).map fun i => s!"v{i}"
    let body ← match cls with
      | "Arbitrary" =>
        let lets := String.join (vs.map fun v => s!"let {v} ← Plausible.Arbitrary.arbitrary; ")
        pure s!"⟨do {lets}pure ⟨{String.intercalate ", " vs}⟩⟩"
      | "Shrinkable" => pure "⟨fun _ => []⟩"
      | "Repr" =>
        let parts := fields.map fun f => s!"\"{f} := \" ++ reprStr x.«{f}»"
        pure s!"⟨fun x _ => Std.Format.text (\"\{ \" ++ {String.intercalate " ++ \", \" ++ " parts.toList} ++ \" }\")⟩"
      | _ =>
        let eqs := String.intercalate " ∧ " (fs.map fun f => s!"a.{f} = b.{f}").toList
        pure s!"fun a b => decidable_of_iff ({eqs}) (by cases a; cases b; simp)"
    let clsName := match cls with
      | "Arbitrary" => "Plausible.Arbitrary" | "Shrinkable" => "Plausible.Shrinkable"
      | "Repr" => "Repr" | _ => "DecidableEq"
    return some s!"instance{binders}{instBinders} : {clsName} {target} :=\n  {body}\n"

structure Elab1 where
  env : Environment
  ok : Bool
  error : String

/-- Elaborate one snippet on `env`; on error keep `env`. -/
def elab1 (env : Environment) (header : String) (snippet : String) (tag : String) : IO Elab1 := do
  let r ← elabCommands env (header ++ snippet) tag
  if r.errors.isEmpty then return { env := r.env, ok := true, error := "" }
  return { env, ok := false, error := String.intercalate "\n" r.errors.toList }

/-- `deriving instance <cls> for <t>` for every type and class (each elaborated separately,
retried a few passes for dependency order), then hand-built fallbacks for what remains.
Returns the extended environment and notes about what could not be derived. -/
def deriveInstances (env : Environment) (header : String) (types : Std.HashSet Name) (classes : Array String) :
    IO (Environment × Array String) := do
  let mut e := env
  let mut notes : Array String := #[]
  let typeList := types.toArray.qsort Name.lt
  let mut pending := typeList.toList.flatMap fun t => classes.toList.map fun cls => (t, cls)
  for _ in [0:4] do
    let mut next := []
    for (t, cls) in pending do
      let r1 ← elab1 e header s!"deriving instance {cls} for {t}\n" s!"<derive {cls} {t}>"
      if r1.ok then e := r1.env else next := (t, cls) :: next
    pending := next.reverse
    if pending.isEmpty then break
  -- fallbacks, iterated so that a structure whose fields are other structures comes after them
  let mut still := pending
  let mut lastErr : Std.HashMap String String := {}
  for _ in [0:4] do
    let mut next := []
    for (t, cls) in still do
      let (txt?, _, _) ← runMeta e (fallbackInstance e t cls)
      match txt? with
      | some txt =>
        let r1 ← elab1 e header txt s!"<fallback {cls} {t}>"
        if r1.ok then e := r1.env
        else
          next := (t, cls) :: next
          lastErr := lastErr.insert s!"{cls} {t}" (txt ++ "\n" ++ (r1.error.splitOn "\n")[0]!)
      | none =>
        next := (t, cls) :: next
        lastErr := lastErr.insert s!"{cls} {t}" "not a structure"
    still := next.reverse
    if still.isEmpty then break
  for (t, cls) in still do
    notes := notes.push s!"could not derive {cls} for {t}: {lastErr.getD s!"{cls} {t}" ""}"
  return (e, notes)

def run (p : Project) (unit : Name) (members? : Option (Array Name)) (specFile : System.FilePath)
    (runs maxMutants timeoutS seed chunk : Nat) : IO Json := do
  let env ← p.loadEnv #[`LeanTools.Instances, `LeanTools.Sample, `LeanTools.Mut, `LeanTools.Eval]
  let mods := crateModules env p.ns
  let members := members?.getD (loopFamily env mods unit)
  let header := Mutate.mutantHeader p.ns
  -- 1. the spec: elaborate, find the theorem and its syntax
  let specText ← IO.FS.readFile specFile
  let r ← elabCommands env (header ++ specText) specFile.toString
  unless r.errors.isEmpty do
    return Json.mkObj [("error", s!"spec does not elaborate: {r.errors[0]!}")]
  let thmCmds := r.commands.filter isTheoremCommand
  let some thmCmd := thmCmds[0]? | return Json.mkObj [("error", "no theorem in spec file")]
  let thmNames := r.added.filter fun n => match r.env.find? n with
    | some (.thmInfo _) => !isAuxName n && !(n.toString.endsWith "mvcgen_spec")
    | _ => false
  let some thmName := thmNames[0]? | return Json.mkObj [("error", "no theorem constant")]
  let thmType := (r.env.find? thmName).get!.type
  let thmStx := thmCmd[1]
  let bindersStx := thmStx[2][0]
  let conclStx := thmStx[2][1][1]
  let concl := (conclStx.reprint.getD "").trimAscii.toString
  -- program `e` of `e ⦃ … ⦄`: first child of the spec notation node
  let progText := (conclStx[0].reprint.getD "").trimAscii.toString
  let binders ← binderGroups r.env thmType bindersStx
  let dataBinders := binders.filter (!·.isProp)
  let hyps := binders.filter (·.isProp)
  -- 2. mutants
  let mutRes ← Mutate.generate p env mods unit members maxMutants seed
  let nsPrefix := p.ns.toString ++ "."
  let short (n : Name) : String :=
    let s := n.toString
    if s.startsWith nsPrefix then String.ofList (s.toList.drop nsPrefix.length) else s
  let renameFor (m : Mutate.Mutant) : Std.HashMap String String := Id.run do
    let mut t : Std.HashMap String String := {}
    for (o, n) in m.names do
      let (os, ns) := (short o.toName, short n.toName)
      t := t.insert os ns |>.insert (nsPrefix ++ os) (nsPrefix ++ ns)
    return t
  -- 3. scratch program, elaborated incrementally
  let mut e := env
  let mut notes : Array String := #[]
  -- derivings for crate types in binders and in the target's type
  let (types, _, _) ← runMeta env do
    let mut acc : Std.HashSet Name := {}
    acc := crateTypesOf env mods thmType acc
    for m in members do
      if let some ci := env.find? m then acc := crateTypesOf env mods ci.type acc
    return acc
  let (e', notes') ← deriveInstances e header types #["Repr", "DecidableEq", "Arbitrary", "Shrinkable"]
  e := e'
  notes := notes ++ notes'
  -- mutants
  let mut muts : Array Mutate.Mutant := #[]
  for m in mutRes.mutants do
    let r1 ← elab1 e header (m.source ++ "\n") s!"<{m.id}>"
    if r1.ok then e := r1.env; muts := muts.push m
    else notes := notes.push s!"mutant {m.id} dropped in scratch: {(r1.error.splitOn "\n")[0]!}"
  -- input telescope
  let names := dataBinders.flatMap fun b => b.names.map fun n => if n == "_" then "_x" else n
  let typedNames := dataBinders.flatMap fun b => b.names.map fun n => (if n == "_" then "_x" else n, b.type, b.small)
  let inType :=
    if typedNames.isEmpty then "Unit"
    else Id.run do
      let mut s := typedNames.back!.2.1
      for (n, t, _) in typedNames.pop.reverse do
        s := s!"({n} : {t}) × ({s})"
      return s
  let pat := if names.isEmpty then "_" else if names.size == 1 then names[0]! else "⟨" ++ String.intercalate ", " names.toList ++ "⟩"
  let genBody := Id.run do
    let mut s := ""
    for (n, t, small) in typedNames do
      s := s ++ (if small then s!"  let {n} ← LeanTools.genSmallUsize\n"
                 else s!"  let {n} ← (Plausible.Arbitrary.arbitrary : Plausible.Gen ({t}))\n")
    let ret := if names.isEmpty then "()" else if names.size == 1 then names[0]! else "⟨" ++ String.intercalate ", " names.toList ++ "⟩"
    return s ++ s!"  pure ({ret})\n"
  let hypProp := if hyps.isEmpty then "True" else String.intercalate " ∧ " (hyps.map fun h => s!"({h.type})").toList
  -- data binders of the theorem, as written (implicit ones made explicit), for the Prop abbreviations
  let dataBindersTxt := String.intercalate " " (dataBinders.map fun b =>
    "(" ++ String.intercalate " " b.names.toList ++ " : " ++ b.type ++ ")").toList
  let appArgs := String.intercalate " " names.toList
  let base :=
    s!"abbrev LT_In : Type := {inType}\n" ++
    s!"def LT_gen : Plausible.Gen LT_In := do\n{genBody}" ++
    s!"abbrev LT_hyp {dataBindersTxt} : Prop := {hypProp}\n" ++
    s!"def LT_pre : LT_In → Bool := fun {pat} => decide (LT_hyp {appArgs})\n" ++
    s!"abbrev LT_prop_orig {dataBindersTxt} : Prop := {concl}\n" ++
    s!"def LT_spec_orig : LT_In → Bool := fun {pat} => decide (LT_prop_orig {appArgs})\n" ++
    s!"def LT_probe_orig : LT_In → Bool := fun {pat} => let _ := ({progText}); true\n"
  let rb ← elab1 e header base "<gate base>"
  unless rb.ok do
    let msg := rb.error
    let err := if (msg.splitOn "Arbitrary").length > 1 then
        let tail := (msg.splitOn "Arbitrary")[1]!
        s!"no generator for{(tail.splitOn "\n")[0]!}"
      else s!"gate scratch failed: {msg}"
    return Json.mkObj [("error", err), ("scratch", base), ("notes", toJson notes)]
  e := rb.env
  -- optional printers
  let showBody := if names.isEmpty then "\"()\"" else
    String.intercalate " ++ \", \" ++ " (names.map fun n => s!"\"{n} := \" ++ reprStr {n}").toList
  let rs ← elab1 e header s!"def LT_show : LT_In → String := fun {pat} => {showBody}\n" "<show>"
  if rs.ok then e := rs.env
  else
    notes := notes.push "inputs are not printable (no Repr)"
    let r2 ← elab1 e header "def LT_show : LT_In → String := fun _ => \"<unprintable input>\"\n" "<show2>"
    e := r2.env
  let ro ← elab1 e header s!"def LT_out_orig : LT_In → String := fun {pat} => reprStr ({progText})\n" "<out>"
  if ro.ok then e := ro.env
  else
    let r2 ← elab1 e header "def LT_out_orig : LT_In → String := fun _ => \"<unprintable output>\"\n" "<out2>"
    e := r2.env
  -- per-mutant closures
  let mut mutIns : Array Eval.MutantIn := #[]
  let mut specNames : Array String := #[]
  let mut diffNames : Array String := #[]
  let mut outNames : Array String := #[]
  for m in muts do
    let tbl := renameFor m
    let conclM := Mutate.renameIdents concl tbl
    let progM := Mutate.renameIdents progText tbl
    let k := m.id
    let r1 ← elab1 e header
      (s!"abbrev LT_prop_{k} {dataBindersTxt} : Prop := {conclM}\n" ++
       s!"def LT_spec_{k} : LT_In → Bool := fun {pat} => decide (LT_prop_{k} {appArgs})\n") s!"<{k} closures>"
    unless r1.ok do
      notes := notes.push s!"mutant {k}: spec closure failed: {(r1.error.splitOn "\n")[0]!}"
      continue
    e := r1.env
    let rd ← elab1 e header s!"def LT_diff_{k} : LT_In → Plausible.Gen Bool := fun {pat} => LeanTools.obsNe ({progText}) ({progM})\n" s!"<{k} diff>"
    let comparable := rd.ok
    if rd.ok then e := rd.env
    else
      let r2 ← elab1 e header s!"def LT_diff_{k} : LT_In → Plausible.Gen Bool := fun _ => pure false\n" s!"<{k} diff2>"
      e := r2.env
    let rout ← elab1 e header s!"def LT_out_{k} : LT_In → String := fun {pat} => reprStr ({progM})\n" s!"<{k} out>"
    if rout.ok then e := rout.env
    else
      let r2 ← elab1 e header s!"def LT_out_{k} : LT_In → String := fun _ => \"<unprintable output>\"\n" s!"<{k} out2>"
      e := r2.env
    mutIns := mutIns.push { id := m.id, op := m.op, site := m.site, before := m.before, after := m.after, comparable }
    specNames := specNames.push s!"LT_spec_{k}"
    diffNames := diffNames.push s!"LT_diff_{k}"
    outNames := outNames.push s!"LT_out_{k}"
  let arr (xs : Array String) : String := "#[" ++ String.intercalate ", " xs.toList ++ "]"
  let mutJson := (toJson mutIns).compress
  let mainDef :=
    s!"def LT_muts : Array LeanTools.Eval.MutantIn := match Lean.Json.parse {repr mutJson} >>= Lean.fromJson? with | .ok v => v | .error _ => #[]\n" ++
    s!"def LT_main : IO String := LeanTools.Eval.gateMain LT_gen LT_pre LT_spec_orig LT_show LT_out_orig LT_muts {arr specNames} {arr diffNames} {arr outNames} {seed} {runs} {timeoutS * 1000} {chunk}\n"
  let rm ← elab1 e header mainDef "<main>"
  unless rm.ok do
    return Json.mkObj [("error", s!"gate main failed: {rm.error}"), ("notes", toJson notes)]
  e := rm.env
  -- 4. evaluate
  let (out, _, _) ← runMeta e (do
    let v ← unsafe evalExpr (IO String) (mkApp (mkConst ``IO) (mkConst ``String)) (mkConst (p.ns ++ `LT_main))
    liftM (m := IO) v)
  let some j := (Json.parse out).toOption | return Json.mkObj [("error", "gate produced invalid JSON")]
  return j.mergeObj (Json.mkObj [
    ("unit", toJson unit.toString), ("theorem", toJson thmName.toString),
    ("mutant_candidates", toJson mutRes.candidates),
    ("mutants_dropped_at_generation", toJson mutRes.dropped.size),
    ("binders", toJson (binders.map fun b => Json.mkObj [("names", toJson b.names), ("type", toJson b.type), ("prop", toJson b.isProp), ("small", toJson b.small)])),
    ("notes", toJson notes)])

end LeanTools.Gate
