import Aeneas
/-!
# Decidability of the spec statement

`Aeneas.Std.WP.spec x p ↔ ∃ y, x = ok y ∧ p y`; for a decidable postcondition
this is decidable by inspecting `x`. These instances are what make the closed
Prop derived from a spec statement executable in the gate (Task 5). They are
imported by every scratch environment `leantools` builds, never by spec files.
-/
open Aeneas Aeneas.Std

namespace LeanTools

instance decSpec {α : Type u} (x : Result α) (p : α → Prop) [DecidablePred p] :
    Decidable (WP.spec x p) :=
  match x with
  | .ok v => decidable_of_iff (p v) (WP.spec_ok v).symm
  | .fail _ => isFalse (by simp [WP.spec, WP.theta])
  | .div => isFalse (by simp [WP.spec, WP.theta])

/-- `⦃ x y => P x y ⦄` desugars to `WP.uncurry' (fun x y => P x y)`. -/
instance decUncurry' {α β} (p : α → β → Prop) [∀ a b, Decidable (p a b)] :
    DecidablePred (WP.uncurry' p) :=
  fun x => decidable_of_iff (p x.1 x.2) (by rw [WP.uncurry'_eq])

/-- `⦃ (x, y) => P x y ⦄` desugars to `uncurry (fun x y => P x y)`. -/
instance decUncurry {α β} (p : α → β → Prop) [∀ a b, Decidable (p a b)] :
    DecidablePred (uncurry p) :=
  fun x => decidable_of_iff (p x.1 x.2) (by cases x; simp)

/-! `Array`, `Slice` and `Vec` are subtypes of `List` declared with `def`, so
instance search does not see through them. -/

instance decEqArray {α : Type u} {n : Usize} [DecidableEq α] : DecidableEq (Array α n) :=
  fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm

instance decEqSlice {α : Type u} [DecidableEq α] : DecidableEq (Slice α) :=
  fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm

instance decEqVec {α : Type u} [DecidableEq α] : DecidableEq (alloc.vec.Vec α) :=
  fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm

deriving instance DecidableEq for Error

instance decEqResult {α : Type u} [DecidableEq α] : DecidableEq (Result α) :=
  fun a b =>
    match a, b with
    | .ok x, .ok y => decidable_of_iff (x = y) (by simp)
    | .fail e, .fail e' => decidable_of_iff (e = e') (by simp)
    | .div, .div => isTrue rfl
    | .ok _, .fail _ | .ok _, .div | .fail _, .ok _ | .fail _, .div | .div, .ok _ | .div, .fail _ =>
      isFalse (by simp)

/-! Case analysis on `core.result.Result` / `Option` results, written as bounded `∀`
(`match` is not decidable for testing: each `match` is its own matcher constant). -/

instance decForallOk {T E : Type} (r : core.result.Result T E) (P : T → Prop) [DecidablePred P] :
    Decidable (∀ t, r = core.result.Result.Ok t → P t) :=
  match r with
  | .Ok t => decidable_of_iff (P t) (by simp)
  | .Err _ => isTrue (by simp)

instance decForallErr {T E : Type} (r : core.result.Result T E) (Q : E → Prop) [DecidablePred Q] :
    Decidable (∀ e, r = core.result.Result.Err e → Q e) :=
  match r with
  | .Ok _ => isTrue (by simp)
  | .Err e => decidable_of_iff (Q e) (by simp)

instance decForallSome {T : Type} (o : Option T) (P : T → Prop) [DecidablePred P] :
    Decidable (∀ t, o = some t → P t) :=
  match o with
  | some t => decidable_of_iff (P t) (by simp)
  | none => isTrue (by simp)

/-! Loop bodies return `ControlFlow` (`cont` / `done`), which Aeneas derives only `BEq` for. -/

instance decEqControlFlow {α β : Type} [DecidableEq α] [DecidableEq β] : DecidableEq (ControlFlow α β) :=
  fun a b =>
    match a, b with
    | .cont x, .cont y => decidable_of_iff (x = y) (by simp)
    | .done x, .done y => decidable_of_iff (x = y) (by simp)
    | .cont _, .done _ | .done _, .cont _ => isFalse (by simp)

instance decForallCont {α β : Type} (r : ControlFlow α β) (P : α → Prop) [DecidablePred P] :
    Decidable (∀ v, r = ControlFlow.cont v → P v) :=
  match r with
  | .cont v => decidable_of_iff (P v) (by simp)
  | .done _ => isTrue (by simp)

instance decForallDone {α β : Type} (r : ControlFlow α β) (Q : β → Prop) [DecidablePred Q] :
    Decidable (∀ v, r = ControlFlow.done v → Q v) :=
  match r with
  | .cont _ => isTrue (by simp)
  | .done v => decidable_of_iff (Q v) (by simp)

/-- `⦃ r => ∀ a b, r = .cont (a, b) → … ⦄`: the pair pattern the loop bodies use. -/
instance decForallCont2 {α β γ : Type} (r : ControlFlow (α × β) γ) (P : α → β → Prop)
    [∀ a b, Decidable (P a b)] :
    Decidable (∀ a b, r = ControlFlow.cont (a, b) → P a b) :=
  match r with
  | .cont (a, b) => decidable_of_iff (P a b) (by simp)
  | .done _ => isTrue (by simp)

end LeanTools
