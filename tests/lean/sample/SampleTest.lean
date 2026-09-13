import Corpus
import LeanTools.Sample
/-!
Task 3 check: sample 1000 values of every std type and of three crate types
without error, and confirm the boundary values show up.
Run from pipeline/lean_tools: `lake env lean ../../tests/lean/sample/SampleTest.lean`
-/
open Plausible Aeneas Aeneas.Std LeanTools

deriving instance Repr, Arbitrary, Shrinkable for Corpus.adt.Struct
deriving instance Repr, Arbitrary, Shrinkable for Corpus.hashmap.Fraction
deriving instance Repr, Arbitrary, Shrinkable for Corpus.avl.Ordering

def N := 1000

def checkU (label : String) (ty : UScalarTy) : IO Unit := do
  match runGenN (genUScalar ty) N 7 with
  | .error e => throw <| IO.userError s!"{label}: generation failed: {repr e}"
  | .ok xs =>
    let vals := xs.map (·.val)
    let max := UScalar.max ty
    for b in [0, 1, 2, max - 1, max] do
      unless vals.contains b do throw <| IO.userError s!"{label}: boundary {b} never sampled"
    let small := (vals.filter (· < 64)).size
    unless small ≥ N / 2 do throw <| IO.userError s!"{label}: only {small} small values"
    -- shrinking moves toward 0
    unless (Shrinkable.shrink (⟨BitVec.ofNat _ 40⟩ : UScalar ty)).all (·.val < 40) do
      throw <| IO.userError s!"{label}: shrink does not decrease"
    IO.println s!"{label}: ok ({xs.size} samples, {small} small, sample {reprStr xs[0]!})"

def checkI (label : String) (ty : IScalarTy) : IO Unit := do
  match runGenN (genIScalar ty) N 11 with
  | .error e => throw <| IO.userError s!"{label}: generation failed: {repr e}"
  | .ok xs =>
    let vals := xs.map (·.val)
    for b in [0, 1, -1, IScalar.max ty, IScalar.max ty - 1, IScalar.min ty, IScalar.min ty + 1] do
      unless vals.contains b do throw <| IO.userError s!"{label}: boundary {b} never sampled"
    let small := (vals.filter fun v => v.natAbs < 64).size
    unless small ≥ N / 2 do throw <| IO.userError s!"{label}: only {small} small values"
    unless (Shrinkable.shrink (⟨BitVec.ofInt _ (-40)⟩ : IScalar ty)).all (·.val.natAbs < 40) do
      throw <| IO.userError s!"{label}: shrink does not decrease"
    IO.println s!"{label}: ok ({xs.size} samples, {small} small, sample {reprStr xs[0]!})"

def checkGen {α : Type} [Repr α] (label : String) (g : Gen α) (seed : Nat) (pred : Array α → Bool := fun _ => true) : IO Unit := do
  match runGenN g N seed with
  | .error e => throw <| IO.userError s!"{label}: generation failed: {repr e}"
  | .ok xs =>
    unless xs.size == N do throw <| IO.userError s!"{label}: {xs.size} samples"
    unless pred xs do throw <| IO.userError s!"{label}: distribution check failed"
    IO.println s!"{label}: ok ({xs.size} samples, sample {reprStr (xs[0]?.map reprStr)})"

#eval do
  checkU "U8" .U8; checkU "U16" .U16; checkU "U32" .U32; checkU "U64" .U64; checkU "U128" .U128; checkU "Usize" .Usize
  checkI "I8" .I8; checkI "I16" .I16; checkI "I32" .I32; checkI "I64" .I64; checkI "I128" .I128; checkI "Isize" .Isize
  checkGen "Array U32 8" (Arbitrary.arbitrary : Gen (Array U32 8#usize)) 3 (fun xs => xs.all fun a => a.val.length == 8)
  checkGen "Slice U8" (Arbitrary.arbitrary : Gen (Slice U8)) 5
    (fun xs => xs.all (fun s => s.val.length ≤ 16) && xs.any (fun s => s.val.length == 0) && xs.any (fun s => s.val.length == 16))
  checkGen "Vec I16" (Arbitrary.arbitrary : Gen (alloc.vec.Vec I16)) 9 (fun xs => xs.all fun v => v.val.length ≤ 16)
  checkGen "Σ N, Array U8 N" (Arbitrary.arbitrary : Gen ((N : Usize) × Array U8 N)) 13
    (fun xs => xs.all (fun ⟨n, a⟩ => a.val.length == n.val && n.val ≤ 16) && xs.any (fun ⟨n, _⟩ => n.val == 16))
  checkGen "adt.Struct" (Arbitrary.arbitrary : Gen Corpus.adt.Struct) 17 (fun xs => xs.any fun s => s.len.val == 0)
  checkGen "hashmap.Fraction" (Arbitrary.arbitrary : Gen Corpus.hashmap.Fraction) 19
    (fun xs => xs.any (fun f => f.divisor.val == 0) && xs.any (fun f => f.dividend.val == UScalar.max .Usize))
  checkGen "avl.Ordering" (Arbitrary.arbitrary : Gen Corpus.avl.Ordering) 23
    (fun xs => xs.any (fun o => match o with | .Less => true | _ => false) && xs.any (fun o => match o with | .Greater => true | _ => false))
  -- SampleableExt is derivable for all of them (selfContained)
  let _ : SampleableExt Corpus.hashmap.Fraction := inferInstance
  let _ : SampleableExt (Array Corpus.adt.Struct 3#usize) := inferInstance
  IO.println "SAMPLE_TEST_OK"
