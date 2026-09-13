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

instance decEqVec {α : Type u} [DecidableEq α] : DecidableEq (Vec α) :=
  fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm

instance decEqResult {α : Type u} [DecidableEq α] : DecidableEq (Result α) :=
  fun a b =>
    match a, b with
    | .ok x, .ok y => decidable_of_iff (x = y) (by simp)
    | .fail e, .fail e' => decidable_of_iff (e = e') (by simp)
    | .div, .div => isTrue rfl
    | .ok _, .fail _ | .ok _, .div | .fail _, .ok _ | .fail _, .div | .div, .ok _ | .div, .fail _ =>
      isFalse (by simp)

end LeanTools
