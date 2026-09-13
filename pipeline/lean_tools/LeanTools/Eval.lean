import Plausible
import Aeneas
import LeanTools.Instances
import LeanTools.Sample
/-!
# Evaluation library for the empirical gate (Task 5)

Natively compiled into `leantools`; the scratch program the `gate` command
builds calls `LeanTools.Eval.gateMain` with interpreted closures for the
sampler, the precondition, the spec on the original, and the spec / output
difference for every mutant.

* Inputs are drawn until `runs` satisfy the hypotheses or `10 × runs` draws
  were made; `precond_density = satisfying / draws`.
* Each batch (the original, or one mutant over all inputs) runs in its own
  task with a deadline; a batch that does not finish is reported as
  `timeout`, with the input being evaluated at that moment as witness.
* Output difference uses `ObsEq`: exact where `DecidableEq` exists, and
  observational (sampled arguments) for function-valued components such as
  Aeneas back functions.
-/
open Plausible Aeneas Aeneas.Std Lean

namespace LeanTools

/-- Observational inequality: `ne a b` samples where it must (functions). -/
class ObsEq (α : Type u) where
  ne : α → α → Gen Bool

instance (priority := high) ObsEq.ofDecidableEq {α : Type u} [DecidableEq α] : ObsEq α :=
  ⟨fun a b => pure (decide (a ≠ b))⟩

instance ObsEq.prod {α β : Type} [ObsEq α] [ObsEq β] : ObsEq (α × β) :=
  ⟨fun a b => do
    if ← ObsEq.ne a.1 b.1 then return true
    ObsEq.ne a.2 b.2⟩

instance ObsEq.fn {α β : Type} [Arbitrary α] [ObsEq β] : ObsEq (α → β) :=
  ⟨fun f g => do
    for _ in [0:8] do
      let x ← (Arbitrary.arbitrary : Gen α)
      if ← ObsEq.ne (f x) (g x) then return true
    return false⟩

instance ObsEq.result {α : Type} [ObsEq α] : ObsEq (Result α) :=
  ⟨fun a b => match a, b with
    | .ok x, .ok y => ObsEq.ne x y
    | .fail e, .fail e' => pure (decide (e ≠ e'))
    | .div, .div => pure false
    | _, _ => pure true⟩

instance ObsEq.option {α : Type} [ObsEq α] : ObsEq (Option α) :=
  ⟨fun a b => match a, b with
    | some x, some y => ObsEq.ne x y
    | none, none => pure false
    | _, _ => pure true⟩

partial def ObsEq.listNe {α : Type} [ObsEq α] : List α → List α → Gen Bool
  | [], [] => pure false
  | x :: xs, y :: ys => do
    if ← ObsEq.ne x y then return true
    ObsEq.listNe xs ys
  | _, _ => pure true

instance ObsEq.list {α : Type} [ObsEq α] : ObsEq (List α) := ⟨ObsEq.listNe⟩
instance ObsEq.array {α : Type} [ObsEq α] {n : Usize} : ObsEq (Array α n) := ⟨fun a b => ObsEq.listNe a.val b.val⟩
instance ObsEq.slice {α : Type} [ObsEq α] : ObsEq (Slice α) := ⟨fun a b => ObsEq.listNe a.val b.val⟩
instance ObsEq.vec {α : Type} [ObsEq α] : ObsEq (alloc.vec.Vec α) := ⟨fun a b => ObsEq.listNe a.val b.val⟩
instance ObsEq.unit : ObsEq Unit := ⟨fun _ _ => pure false⟩

/-- `obsNe a b`: do `a` and `b` observably differ? -/
def obsNe {α : Type} [ObsEq α] (a b : α) : Gen Bool := ObsEq.ne a b

namespace Eval

/-- Run a generator once with a seed. -/
def runGen1 {α : Type} (g : Gen α) (seed : Nat) (size : Nat := 100) : Option α :=
  match ReaderT.run (StateT.run g ⟨mkStdGen seed⟩) ⟨size⟩ with
  | .ok (x, _) => some x
  | .error _ => none

/-- Run `act` in a dedicated task and wait at most `ms` milliseconds. -/
def withDeadline {α : Type} (ms : Nat) (act : IO α) : IO (Option α) := do
  let t ← IO.asTask act .dedicated
  let start ← IO.monoMsNow
  let mut done := false
  while !done do
    if ← IO.hasFinished t then done := true
    else if (← IO.monoMsNow) - start > ms then
      IO.cancel t
      return none
    else IO.sleep 2
  return some (← IO.ofExcept t.get)

structure MutantIn where
  id : String
  op : String
  site : String
  before : String
  after : String
  comparable : Bool
  deriving ToJson, FromJson, Inhabited, Repr

structure MutantOut where
  id : String
  op : String
  site : String
  before : String
  after : String
  killed : Bool
  distinguishable : Bool
  timeout : Bool
  comparable : Bool
  witness : Option String
  observed : Option String
  expected : Option String
  deriving ToJson, FromJson, Inhabited

structure Report where
  spec_ok_on_original : Bool
  original_witness : Option String
  original_observed : Option String
  original_timeout : Bool
  precond_density : Float
  effective_runs : Nat
  total_draws : Nat
  output_comparable : Bool
  mutants : Array MutantOut
  deriving ToJson, FromJson

/-- Evaluate `f` on every input in a deadline-bounded task, recording results as
they come. Returns the completed results and whether the batch timed out. -/
def runBatch {In β : Type} (timeoutMs : Nat) (inputs : Array In) (f : Nat → In → IO β) :
    IO (Array β × Bool) := do
  let ref ← IO.mkRef (#[] : Array β)
  let res ← withDeadline timeoutMs do
    let mut i := 0
    for x in inputs do
      let y ← f i x
      ref.modify (·.push y)
      i := i + 1
  let done ← ref.get
  return (done, res.isNone)

/-- Sample up to `runs` inputs satisfying `pre`, drawing at most `10 × runs` times. -/
def sampleInputs {In : Type} (gen : Gen In) (pre : In → Bool) (runs seed : Nat) : IO (Array In × Nat) := do
  let mut st : ULift StdGen := ⟨mkStdGen seed⟩
  let mut out : Array In := #[]
  let mut draws := 0
  let maxDraws := 10 * runs
  while out.size < runs && draws < maxDraws do
    draws := draws + 1
    match ReaderT.run (StateT.run gen st) ⟨100⟩ with
    | .ok (x, st') =>
      st := st'
      if pre x then out := out.push x
    | .error _ => pure ()
  return (out, draws)

def gateMain {In : Type}
    (gen : Gen In) (pre : In → Bool) (specOrig : In → Bool)
    (showIn : In → String) (outOrig : In → String)
    (muts : Array MutantIn) (mutSpec : Array (In → Bool)) (mutDiff : Array (In → Gen Bool))
    (mutOut : Array (In → String))
    (seed runs timeoutMs chunk : Nat) : IO String := do
  IO.eprintln "[gate] sampling"
  let (inputs, draws) ← sampleInputs gen pre runs seed
  IO.eprintln s!"[gate] {inputs.size} inputs from {draws} draws"
  let density : Float := if draws == 0 then 0 else (Float.ofNat inputs.size) / (Float.ofNat draws)
  -- original
  let (origRes, origTimeout) ← runBatch timeoutMs inputs fun _ x => pure (specOrig x)
  IO.eprintln s!"[gate] original done: {origRes.size} results, timeout={origTimeout}"
  let firstBad := origRes.findIdx? (· == false)
  let origOk := !origTimeout && firstBad.isNone
  let witnessIdx := firstBad.getD origRes.size
  let (origWitness, origObserved) ←
    if origOk then pure (none, none)
    else match inputs[witnessIdx]? with
      | some x =>
        let obs ← withDeadline timeoutMs (pure (outOrig x))
        pure (some (showIn x), obs)
      | none => pure (none, none)
  let mut outs : Array MutantOut := #[]
  if origOk then
    -- mutants, in chunks of concurrent batches
    let mut i := 0
    while i < muts.size do
      let hi := min muts.size (i + chunk)
      let mut tasks : Array (Task (Except IO.Error (Array (Bool × Bool) × Bool))) := #[]
      for k in [i:hi] do
        let spec := mutSpec[k]!
        let diff := mutDiff[k]!
        let t ← IO.asTask (runBatch timeoutMs inputs fun j x => do
          let s := spec x
          let d := if muts[k]!.comparable then (runGen1 (diff x) (seed + j)).getD false else false
          pure (s, d)) .dedicated
        tasks := tasks.push t
      IO.eprintln s!"[gate] chunk {i}-{hi} started"
      for k in [i:hi] do
        let (res, timedOut) ← IO.ofExcept (← IO.wait tasks[k - i]!)
        let m := muts[k]!
        IO.eprintln s!"[gate] mutant {m.id} {m.op}: {res.size} results, timeout={timedOut}"
        let killedIdx := res.findIdx? (fun (s, _) => !s)
        let diffIdx := res.findIdx? (fun (_, d) => d)
        let killed := killedIdx.isSome
        let distinguishable := diffIdx.isSome || killedIdx.isSome || timedOut
        let wIdx := diffIdx.orElse (fun _ => killedIdx) |>.getD res.size   -- timeout input if neither
        let (witness, observed, expected) ←
          match inputs[wIdx]? with
          | some x =>
            let obs ← if timedOut && wIdx == res.size then pure (some "<timeout>")
                      else withDeadline timeoutMs (pure (mutOut[k]! x))
            let exp ← withDeadline timeoutMs (pure (outOrig x))
            pure (some (showIn x), obs, exp)
          | none => pure (none, none, none)
        outs := outs.push { id := m.id, op := m.op, site := m.site, before := m.before, after := m.after,
                            killed, distinguishable, timeout := timedOut, comparable := m.comparable,
                            witness, observed, expected }
      i := hi
  let report : Report := {
    spec_ok_on_original := origOk, original_witness := origWitness, original_observed := origObserved,
    original_timeout := origTimeout, precond_density := density, effective_runs := inputs.size,
    total_draws := draws, output_comparable := muts.all (·.comparable), mutants := outs }
  return (Lean.toJson report).compress

end Eval
end LeanTools
