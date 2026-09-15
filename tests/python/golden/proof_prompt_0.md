You prove Lean 4 specifications of functions that Aeneas produced from Rust.

## Proof rules (mandatory)

- Unfold the target definition (and its `_loop` / `_loop.body` helpers) only.
- Handle every call to another function of the crate with the `step` tactic, which
  uses that function's `@[step]` specification listed below (`step*` steps through a
  whole `do` block; `step` handles one call; `step with <lemma>` picks a lemma).
- Never `unfold`, `simp [g]`, `delta g`, `rw [g]` or otherwise open the definition of a
  callee `g`; do not rely on definitional unfolding of callees (`rfl`, `decide`).
- No `sorry`, no `admit`, no `native_decide`, no new `axiom`.
- Loops: `Aeneas.Std.loop` has `loop.spec_decr_nat` (invariant + measure); the loop body
  and loop helpers have their own specifications listed with the target.
- Arithmetic side conditions are usually closed by `scalar_tac`; `simp` / `omega` for the rest.
  After `step`, each result `x` comes with a hypothesis `x_post`; substitute or `simp only [x_post]`
  before `scalar_tac` so the bound on `x` is visible. Casts: `IScalar.cast`/`UScalar.hcast` have
  `simp`/`scalar_tac` support; keep the proof short and mechanical.

## Available step lemmas (callee specifications)

```lean
@[step]
theorem demo.mul2_add1_spec (x : U32) (h : 2 * x.val + 1 ≤ U32.max) :
    demo.mul2_add1 x ⦃ r => r.val = 2 * x.val + 1 ⦄ := by sorry
```

## Target

The unit (Corpus.demo.use_mul2_add1) consists of the following definitions:

```lean
def demo.use_mul2_add1 (x : Std.U32) (y : Std.U32) : Result Std.U32 := do
  let i ← demo.mul2_add1 x
  i + y
```

Prove this specification of `Corpus.demo.use_mul2_add1`:

```lean
@[step]
theorem demo.use_mul2_add1_spec (x y : U32) (h : 2 * x.val + 1 + y.val ≤ U32.max) :
    demo.use_mul2_add1 x y ⦃ r => r.val = 2 * x.val + 1 + y.val ⦄ := by sorry
```

Replace `sorry`. Reply with exactly one ```lean block containing only the tactic block
(the lines that follow `:= by`), nothing else.
