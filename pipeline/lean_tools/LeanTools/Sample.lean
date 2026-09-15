import Plausible
import Aeneas
import LeanTools.Instances
/-!
# Property-based-testing instances for Aeneas types (Task 3)

`Plausible.Arbitrary` / `Plausible.Shrinkable` (and therefore
`Plausible.SampleableExt` through `selfContained`) for machine integers,
`Array α N`, `Slice α`, `Vec α`, plus `Repr` instances that print values as
Lean literals so that witnesses in gate reports re-elaborate.

Crate structs/enums get their instances in the scratch module through
`deriving instance Repr, Arbitrary, Shrinkable for <T>` (Plausible ships the
deriving handlers); when that fails the gate reports `no generator for <T>`.

Scalar distribution (IMPLEMENTATION.md, Task 3): boundary values
`{0, 1, 2, max−1, max}` with total weight 0.3, small values `< 64` with weight
0.5, uniform otherwise. Shrinking moves toward 0.
-/
open Plausible Aeneas Aeneas.Std

namespace LeanTools

/-! ## Literal `Repr` -/

def UScalarTy.suffix : UScalarTy → String
  | .Usize => "usize" | .U8 => "u8" | .U16 => "u16" | .U32 => "u32" | .U64 => "u64" | .U128 => "u128"

def IScalarTy.suffix : IScalarTy → String
  | .Isize => "isize" | .I8 => "i8" | .I16 => "i16" | .I32 => "i32" | .I64 => "i64" | .I128 => "i128"

instance (priority := high) instReprUScalar {ty : UScalarTy} : Repr (UScalar ty) :=
  ⟨fun x _ => Std.Format.text s!"{x.val}#{UScalarTy.suffix ty}"⟩

instance (priority := high) instReprIScalar {ty : IScalarTy} : Repr (IScalar ty) :=
  ⟨fun x _ =>
    let v := x.val
    Std.Format.text (if v < 0 then s!"({v})#{IScalarTy.suffix ty}" else s!"{v}#{IScalarTy.suffix ty}")⟩

instance (priority := high) instReprAeneasArray {α : Type u} [Repr α] {n : Usize} : Repr (Array α n) :=
  ⟨fun a _ => Std.Format.text s!"(Array.make {n.val}#usize {reprStr a.val})"⟩

instance (priority := high) instReprSlice {α : Type u} [Repr α] : Repr (Slice α) :=
  ⟨fun a _ => Std.Format.text s!"(⟨{reprStr a.val}, by scalar_tac⟩ : Slice _)"⟩

instance (priority := high) instReprVec {α : Type u} [Repr α] : Repr (alloc.vec.Vec α) :=
  ⟨fun a _ => Std.Format.text s!"(⟨{reprStr a.val}, by scalar_tac⟩ : alloc.vec.Vec _)"⟩

instance (priority := high) instReprResult {α : Type u} [Repr α] : Repr (Result α) :=
  ⟨fun r _ => match r with
    | .ok v => Std.Format.text s!"(ok {reprStr v})"
    | .fail e => Std.Format.text s!"(fail .{reprStr e})"
    | .div => Std.Format.text "div"⟩

deriving instance Repr for Error

/-! ## Generators -/

/-- `Gen.choose` returning the bare value. -/
def chooseNat (lo hi : Nat) (h : lo ≤ hi) : Gen Nat := do return (← Gen.choose Nat lo hi h).val
def chooseInt (lo hi : Int) (h : lo ≤ hi) : Gen Int := do return (← Gen.choose Int lo hi h).val

/-- Weighted natural number in `[0, max]`: boundary 0.3, small 0.5, uniform 0.2.
When the generator size is 0 ("small mode", set per array/slice by the sequence
generators) only small values and the small boundary values are drawn, so that
lane-wise preconditions on vectors are satisfiable. -/
def genNatWeighted (max : Nat) : Gen Nat := do
  let sz ← Gen.getSize
  if sz == 0 then
    let v ← chooseNat 0 63 (Nat.zero_le _)
    return min v max
  let k ← chooseNat 0 9 (Nat.zero_le _)
  if k < 3 then
    let i ← chooseNat 0 4 (Nat.zero_le _)
    let cands := #[0, 1, 2, max - 1, max]
    return min cands[i]! max
  else if k < 8 then
    let v ← chooseNat 0 63 (Nat.zero_le _)
    return min v max
  else
    chooseNat 0 max (Nat.zero_le _)

/-- Weighted integer in `[min, max]` (`min ≤ 0 ≤ max`): boundary 0.3, small 0.5, uniform 0.2. -/
def genIntWeighted (min max : Int) (h : min ≤ max) : Gen Int := do
  let clamp (v : Int) : Int := if v < min then min else if v > max then max else v
  let sz ← Gen.getSize
  if sz == 0 then
    let v ← chooseInt (-63) 63 (by decide)
    return clamp v
  let k ← chooseNat 0 9 (Nat.zero_le _)
  if k < 3 then
    let i ← chooseNat 0 7 (Nat.zero_le _)
    let cands := #[0, 1, -1, 2, max, max - 1, min, min + 1]
    return clamp cands[i]!
  else if k < 8 then
    let v ← chooseInt (-63) 63 (by decide)
    return clamp v
  else
    chooseInt min max h

def genUScalar (ty : UScalarTy) : Gen (UScalar ty) := do
  let v ← genNatWeighted (UScalar.max ty)
  return ⟨BitVec.ofNat _ v⟩

def genIScalar (ty : IScalarTy) : Gen (IScalar ty) := do
  let v ← genIntWeighted (IScalar.min ty) (IScalar.max ty) (by
    have := IScalar.min_lt_max ty; omega)
  return ⟨BitVec.ofInt _ v⟩

/-- Small `Usize` for array lengths and other size parameters: `≤ 16`. -/
def genSmallUsize (bound : Nat := 16) : Gen Usize := do
  let v ← chooseNat 0 bound (Nat.zero_le _)
  return ⟨BitVec.ofNat _ v⟩

instance instArbitraryUScalar {ty : UScalarTy} : Arbitrary (UScalar ty) := ⟨genUScalar ty⟩
instance instArbitraryIScalar {ty : IScalarTy} : Arbitrary (IScalar ty) := ⟨genIScalar ty⟩

instance instShrinkableUScalar {ty : UScalarTy} : Shrinkable (UScalar ty) :=
  ⟨fun x => (Nat.shrink x.val).map fun v => ⟨BitVec.ofNat _ v⟩⟩

instance instShrinkableIScalar {ty : IScalarTy} : Shrinkable (IScalar ty) :=
  ⟨fun x => (Nat.shrink x.val.natAbs).map fun n =>
    ⟨BitVec.ofInt _ (if x.val < 0 then -(n : Int) else n)⟩⟩

/-- A list of exactly `k` generated elements, with its length proof. -/
def genListExact {α : Type} [Arbitrary α] : (k : Nat) → Gen { l : List α // l.length = k }
  | 0 => pure ⟨[], rfl⟩
  | k + 1 => do
    let x ← (Arbitrary.arbitrary : Gen α)
    let ⟨l, h⟩ ← genListExact k
    pure ⟨x :: l, by simp [h]⟩

/-- A list of at most `bound` generated elements. -/
def genListBounded {α : Type} [Arbitrary α] (bound : Nat := 16) : Gen { l : List α // l.length ≤ bound } := do
  let k ← Gen.choose Nat 0 bound (Nat.zero_le _)
  let ⟨l, h⟩ ← genListExact (α := α) k.val
  pure ⟨l, by rw [h]; exact k.property.2⟩

/-- Largest slice / vector length the generators draw. -/
def maxSeqLen : Nat := 2048

/-- Length of a slice or vector: short (`≤ 16`, 40%), medium (`17..64`, 20%), one of the sizes
fixed-size buffers commonly have (`32, 48, 64, …, 2048`, 30%), otherwise uniform up to
`maxSeqLen` (10%). Preconditions such as `32 ≤ s.length` or `s.length = 64` then hold on a
testable fraction of the draws (two slices both `≥ 32`: about 0.29). -/
def genSeqLen : Gen { k : Nat // k ≤ maxSeqLen } := do
  let sizes : Array Nat := #[32, 48, 64, 96, 128, 192, 256, 384, 512, 768, 1024, 1536, 2048]
  let k ← chooseNat 0 9 (Nat.zero_le _)
  let v ← if k < 4 then chooseNat 0 16 (Nat.zero_le _)
    else if k < 6 then chooseNat 17 64 (by decide)
    else if k < 9 then do let i ← chooseNat 0 (sizes.size - 1) (Nat.zero_le _); pure sizes[i]!
    else chooseNat 0 maxSeqLen (Nat.zero_le _)
  pure ⟨min v maxSeqLen, Nat.min_le_right _ _⟩

/-- A list whose length follows `genSeqLen`. -/
def genListSeq {α : Type} [Arbitrary α] : Gen { l : List α // l.length ≤ maxSeqLen } := do
  let k ← genSeqLen
  let ⟨l, h⟩ ← genListExact (α := α) k.val
  pure ⟨l, by rw [h]; exact k.property⟩

/-- Run `g` in "small mode" (size 0) half of the time: all elements of one sequence are
then small, so conjunctive bounds over every element hold often enough to be tested. -/
def withSeqMode {α : Type} (g : Gen α) : Gen α := do
  let k ← chooseNat 0 1 (Nat.zero_le _)
  if k == 0 then Gen.resize (fun _ => 0) g else g

instance instArbitraryAeneasArray {α : Type} [Arbitrary α] {n : Usize} : Arbitrary (Array α n) :=
  ⟨withSeqMode (do let ⟨l, h⟩ ← genListExact (α := α) n.val; pure ⟨l, h⟩)⟩

theorem sixteen_le_usize_max : 16 ≤ Usize.max := by scalar_tac
theorem maxSeqLen_le_usize_max : maxSeqLen ≤ Usize.max := by simp [maxSeqLen]; scalar_tac

instance instArbitrarySlice {α : Type} [Arbitrary α] : Arbitrary (Slice α) :=
  ⟨withSeqMode (do
      let ⟨l, h⟩ ← genListSeq (α := α)
      pure ⟨l, by have := maxSeqLen_le_usize_max; omega⟩)⟩

instance instArbitraryVec {α : Type} [Arbitrary α] : Arbitrary (alloc.vec.Vec α) :=
  ⟨withSeqMode (do
      let ⟨l, h⟩ ← genListSeq (α := α)
      pure ⟨l, by have := maxSeqLen_le_usize_max; omega⟩)⟩

/-- Iteration ranges: a small start and a small, non-negative extent, so that
`start ≤ end ≤ <sequence length>` holds on a testable fraction of the draws. Declared with high
priority because the gate also derives a (uniform) instance for this structure. -/
instance (priority := high) instArbitraryRangeUsize : Arbitrary (core.ops.range.Range Usize) :=
  ⟨do let s ← chooseNat 0 16 (Nat.zero_le _)
      let d ← chooseNat 0 16 (Nat.zero_le _)
      pure { start := ⟨BitVec.ofNat _ s⟩, «end» := ⟨BitVec.ofNat _ (s + d)⟩ }⟩

/-- Shrink one element at a time; the length is fixed by the type. -/
def shrinkListSameLength {α : Type u} [Shrinkable α] (l : List α) : List (List α) :=
  (List.range l.length).flatMap fun i =>
    match l[i]? with
    | none => []
    | some x => (Shrinkable.shrink x).map fun x' => l.set i x'

instance instShrinkableAeneasArray {α : Type u} [Shrinkable α] {n : Usize} : Shrinkable (Array α n) :=
  ⟨fun a => (shrinkListSameLength a.val).filterMap fun l =>
    if h : l.length = n.val then some ⟨l, h⟩ else none⟩

instance instShrinkableSlice {α : Type u} [Shrinkable α] : Shrinkable (Slice α) :=
  ⟨fun a => (Shrinkable.shrink a.val).filterMap fun l =>
    if h : l.length ≤ Usize.max then some ⟨l, h⟩ else none⟩

instance instShrinkableVec {α : Type u} [Shrinkable α] : Shrinkable (alloc.vec.Vec α) :=
  ⟨fun a => (Shrinkable.shrink a.val).filterMap fun l =>
    if h : l.length ≤ Usize.max then some ⟨l, h⟩ else none⟩

/-- Dependent pair: a small length, then an array of exactly that length. -/
instance instArbitrarySigmaArray {α : Type} [Arbitrary α] : Arbitrary ((N : Usize) × Array α N) :=
  ⟨do let n ← genSmallUsize
      let a ← (Arbitrary.arbitrary : Gen (Array α n))
      pure ⟨n, a⟩⟩

instance instShrinkableSigmaArray {α : Type} [Shrinkable α] : Shrinkable ((N : Usize) × Array α N) :=
  ⟨fun ⟨n, a⟩ => (Shrinkable.shrink a).map fun a' => ⟨n, a'⟩⟩

instance instReprSigmaArray {α : Type} [Repr α] : Repr ((N : Usize) × Array α N) :=
  ⟨fun ⟨n, a⟩ _ => Std.Format.text s!"⟨{n.val}#usize, {reprStr a}⟩"⟩

/-! `SampleableExt` for all of the above follows from `Plausible.selfContained`
(`Repr` + `Shrinkable` + `Arbitrary`). -/
example : SampleableExt U32 := inferInstance
example : SampleableExt I128 := inferInstance
example : SampleableExt (Array U8 4#usize) := inferInstance
example : SampleableExt (Slice U64) := inferInstance
example : SampleableExt ((N : Usize) × Array U32 N) := inferInstance

/-! ## Running generators deterministically -/

/-- Run `g` `n` times from `seed`, threading the generator state. -/
def runGenN {α : Type} (g : Gen α) (n : Nat) (seed : Nat) (size : Nat := 100) : Except GenError (Array α) := do
  let mut st : ULift StdGen := ⟨mkStdGen seed⟩
  let mut out := #[]
  for _ in [0:n] do
    let (x, st') ← ReaderT.run (StateT.run g st) ⟨size⟩
    out := out.push x
    st := st'
  return out

end LeanTools
