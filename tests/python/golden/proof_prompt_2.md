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

## Available step lemmas (callee specifications)

```lean
@[step]
theorem demo.mul2_add1_spec (x : U32) (h : 2 * x.val + 1 ≤ U32.max) :
    demo.mul2_add1 x ⦃ r => r.val = 2 * x.val + 1 ⦄ := by sorry
```

## Verified examples from this codebase

### Example 1

```lean
def demo.ex1 (x : Std.U32) : Result Std.U32 := do
  x + 1#u32
```

```lean
@[step]
theorem demo.ex1_spec (x : U32) (h : x.val + 1 ≤ U32.max) :
    demo.ex1 x ⦃ r => r.val = x.val + 1 ⦄ := by sorry
```

```lean
-- proof of Corpus.demo.ex1
unfold demo.ex1
step* <;> scalar_tac
```

### Example 2

```lean
def demo.ex2 (x : Std.U32) : Result Std.U32 := do
  x + 2#u32
```

```lean
@[step]
theorem demo.ex2_spec (x : U32) (h : x.val + 2 ≤ U32.max) :
    demo.ex2 x ⦃ r => r.val = x.val + 2 ⦄ := by sorry
```

```lean
-- proof of Corpus.demo.ex2
unfold demo.ex2
step* <;> scalar_tac
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
