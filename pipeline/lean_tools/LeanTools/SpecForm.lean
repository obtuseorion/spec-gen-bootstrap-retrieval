import LeanTools.Common
import LeanTools.Frontend
import LeanTools.Instances
/-!
# `leantools specform` — shape, vocabulary and decidability of a spec (Task 2)

The spec file contains exactly one declaration:

```lean
@[step] theorem <f>_spec (binders) (hyps) : <f> <args> ⦃ r => <Post r> ⦄ := by sorry
```

(the exact flavour is `⦃ r => r = <expr> ⦄`). See docs/phase0.md, deviation 3,
for why `WP.spec` rather than `∃ r, f args = ok r ∧ Post r`.

The closed Prop is the theorem's own statement: `∀ binders, hyps → WP.spec (f args) P`.
Decidability is checked for every hypothesis and for the conclusion under the
binders, with the instances of `LeanTools.Instances` available.
-/
open Lean Meta Elab

namespace LeanTools.SpecForm

structure Result where
  shape_ok : Bool := false
  shape : String := ""              -- "exact" | "post" | ""
  shape_error : String := ""
  attr_ok : Bool := false
  vocab_ok : Bool := false
  vocab_violations : Array String := #[]
  decidable_ok : Bool := false
  undecidable : Array String := #[]
  spec_prop : String := ""          -- `∀ <binders>, <conclusion>` built from the theorem syntax
  spec_prop_pp : String := ""       -- the elaborated statement, pretty-printed (informational)
  spec_prop_reelab_ok : Bool := false
  spec_prop_reelab_error : String := ""
  theorem_name : String := ""
  target : String := ""
  binders : Array String := #[]     -- explicit binder names in order, for sampling
  error : Option String := none
  warnings : Array String := #[]
  deriving ToJson, FromJson

/-- Is `post` syntactically `fun r => r = e` or `fun r => e = r` with `e` not mentioning `r`? -/
private def isExactPost (post : Expr) : Bool :=
  match post with
  | .lam _ _ body _ =>
    match body.getAppFn.constName?, body.getAppArgs with
    | some ``Eq, #[_, l, r] =>
      (l == .bvar 0 && !r.hasLooseBVars) || (r == .bvar 0 && !l.hasLooseBVars)
    | _, _ => false
  | _ => false

/-- Number of Π-binders of a constant's type. -/
private def arity (type : Expr) : Nat := type.getForallBinderNames.length

/-- Constants of the crate that a spec statement may mention: types, constructors,
projections, instances and matcher auxiliaries — never emitted functions or globals
other than the target. -/
private def allowedCrateConst (env : Environment) (n : Name) : MetaM Bool := do
  let some ci := env.find? n | return true
  match ci with
  | .inductInfo _ | .ctorInfo _ | .recInfo _ | .quotInfo _ | .axiomInfo _ => return true
  | _ => pure ()
  if env.isProjectionFn n || isMatcherCore env n || isAuxRecursor env n || isCasesOnRecursor env n then return true
  if ← isInstance n then return true
  if isAuxName n then return true
  -- `structure` derived `instDecidableEq…`, `Insts`, discriminant readers, …: instances above.
  return false

def run (p : Project) (unit : Name) (members? : Option (Array Name)) (specFile : System.FilePath) : IO Json := do
  let env ← p.loadEnv #[`LeanTools.Instances]
  let mods := crateModules env p.ns
  let members := members?.getD (loopFamily env mods unit)
  let text ← IO.FS.readFile specFile
  let full := specHeader p.ns ++ text
  let r ← elabCommands env full specFile.toString
  let mut res : Result := {}
  if !r.errors.isEmpty then
    res := { res with error := some (String.intercalate "\n" r.errors.toList), warnings := r.warnings }
    return toJson res
  res := { res with warnings := r.warnings }
  -- exactly one command, a theorem
  let headerCmds := (specHeader p.ns).splitOn "\n" |>.filter (· ≠ "") |>.length
  let cmds := r.commands.toList.drop headerCmds |>.toArray
  let decls := cmds.filter fun c => !(c.isOfKind ``Parser.Command.eoi)
  let mut violations : Array String := #[]
  let thms := decls.filter isTheoremCommand
  for c in decls do
    if !isTheoremCommand c then violations := violations.push s!"extra declaration: {commandKind c}"
  if thms.size != 1 then
    let msg := s!"expected exactly one theorem, found {thms.size}"
    res := { res with vocab_violations := violations, error := some msg }
    return toJson res
  let attrs := declAttrNames thms[0]!
  let attrOk := attrs.any fun a => a.startsWith "@[step]" || a.startsWith "@[progress]" || (a.splitOn "step").length > 1
  res := { res with attr_ok := attrOk }
  -- the theorem constant
  let thmNames := r.added.filter fun n => match r.env.find? n with
    | some (.thmInfo _) => !isAuxName n && !(n.toString.endsWith "mvcgen_spec")
    | _ => false
  let some thmName := thmNames[0]? |
    return toJson { res with error := some "no theorem constant was added" }
  res := { res with theorem_name := thmName.toString }
  let thm := r.env.find? thmName |>.get!
  let (res', _, _) ← runMeta r.env (do
    let mut res := res
    let type ← instantiateMVars thm.type
    -- shape
    let (shapeOk, shape, shapeErr, target, binders) ← forallTelescope type fun xs body => do
      let mut binders := #[]
      for x in xs do
        let d ← x.fvarId!.getDecl
        if d.binderInfo == .default then binders := binders.push d.userName.toString
      let body ← instantiateMVars body
      match body.getAppFn.constName?, body.getAppArgs with
      | some ``Aeneas.Std.WP.dspec, #[_, prog, _] =>
        let f := (prog.getAppFn.constName?.map toString).getD ""
        return (false, "", "partial-correctness statement (⦄div) is not permitted", f, binders)
      | some ``Aeneas.Std.WP.spec, #[_, prog, post] =>
        let prog ← instantiateMVars prog
        match prog.getAppFn.constName? with
        | some f =>
          if !members.contains f then
            return (false, "", s!"conclusion is about {f}, not a member of the unit {unit}", f.toString, binders)
          let args := prog.getAppArgs
          let fArity := arity (env.find? f |>.get!.type)
          if args.size != fArity then
            return (false, "", s!"{f} applied to {args.size} arguments, expected {fArity}", f.toString, binders)
          let fvars := args.filterMap fun a => a.fvarId?
          if fvars.size != args.size then
            return (false, "", "arguments of the target must be bound variables of the theorem", f.toString, binders)
          if fvars.toList.eraseDups.length != fvars.size then
            return (false, "", "the target's arguments must be distinct variables", f.toString, binders)
          for v in fvars do
            if !(xs.any fun x => x.fvarId! == v) then
              return (false, "", "argument is not a binder of the theorem", f.toString, binders)
          let shape := if isExactPost post then "exact" else "post"
          return (true, shape, "", f.toString, binders)
        | none => return (false, "", "program is not an application of a constant", "", binders)
      | _, _ =>
        return (false, "", s!"conclusion must be `<f> <args> ⦃ r => … ⦄`, got {← ppExpr body}", "", binders)
    res := { res with shape_ok := shapeOk, shape, shape_error := shapeErr, target, binders }
    -- vocabulary
    let mut viol := violations
    for c in type.getUsedConstants do
      if isCrateConst env mods c && c.toString != target then
        if !(← allowedCrateConst env c) then viol := viol.push c.toString
    res := { res with vocab_violations := viol, vocab_ok := viol.isEmpty }
    -- decidability of hypotheses and conclusion under the binders
    let undec ← forallTelescope type fun xs body => do
      let mut bad : Array String := #[]
      for x in xs do
        let d ← x.fvarId!.getDecl
        if ← isProp d.type then
          match ← synthInstance? (mkApp (mkConst ``Decidable) d.type) with
          | some _ => pure ()
          | none => bad := bad.push s!"hypothesis {d.userName}: {← ppExpr d.type}"
      match ← synthInstance? (mkApp (mkConst ``Decidable) body) with
      | some _ => pure ()
      | none => bad := bad.push s!"conclusion: {← ppExpr body}"
      return bad
    res := { res with undecidable := undec, decidable_ok := undec.isEmpty }
    -- closed Prop (the statement itself), pretty-printed
    let pp ← withOptions (fun o => ((pp.funBinderTypes.set o true) |> (pp.coercions.set · false)) |> (pp.proofs.set · true)) do ppExpr type
    res := { res with spec_prop_pp := toString pp }
    return res)
  res := res'
  -- closed Prop from the theorem's own syntax: `∀ <binders>, <conclusion>`
  let thmStx := (thms[0]!)[1]
  let bindersStx := thmStx[2][0]
  let typeStx := thmStx[2][1][1]
  let bindersTxt := (bindersStx.reprint.getD "").trimAscii.toString
  let typeTxt := (typeStx.reprint.getD "").trimAscii.toString
  let prop := if bindersTxt.isEmpty then typeTxt else s!"∀ {bindersTxt}, {typeTxt}"
  res := { res with spec_prop := prop }
  -- does it re-elaborate (in the environment that elaborated the spec)?
  let re ← elabCommands r.env (specHeader p.ns ++ s!"example : {prop} := by sorry\n") "<spec_prop>"
  res := { res with spec_prop_reelab_ok := re.errors.isEmpty,
                    spec_prop_reelab_error := String.intercalate "\n" re.errors.toList }
  return toJson res

end LeanTools.SpecForm
