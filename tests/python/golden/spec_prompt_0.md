You write Lean 4 specifications for functions that Aeneas produced from Rust.

## Specification form (mandatory)

Write exactly one theorem, in this shape, with `by sorry` as the body:

```lean
@[step]
theorem <name>_spec (<binders>) (<hypotheses>) :
    <f> <args> ⦃ r => <postcondition on r> ⦄ := by sorry
```

When the result is fully determined, prefer the exact form `⦃ r => r = <expr> ⦄`.
Rules:

- The conclusion is `<f> <args> ⦃ … ⦄` where `<f>` is the target definition applied to
  exactly its explicit arguments, each a bound variable of the theorem, in order.
  Use the `⦃ r => … ⦄` form (`Aeneas.Std.WP.spec`); never `⦄div`, never `∃ r, … = ok r ∧ …`.
- Preconditions are explicit hypotheses `(h : …)`. Overflow, bounds and non-emptiness
  conditions must be stated, not left implicit. `f args ⦃ … ⦄` asserts that the call
  succeeds (`ok`), so add the hypotheses that rule out `fail`.
- Postconditions use only the decidable fragment: `=`, `<`, `≤`, `∧`, `∨`, `¬`,
  bounded `∀`/`∃` over lists, arrays and slices (`∀ x ∈ l, …`, `∀ i < n, …`),
  `List.length`, list membership. No unbounded quantifiers, no functions.
- Vocabulary: binders, results and constants from `Aeneas.Std`, Lean core and Mathlib
  only. Machine integers are `U8 … U128`, `I8 … I128`, `Usize`, `Isize`; use `x.val`
  for the mathematical value and `U32.max` etc. for bounds; literals are `3#u32`.
  Do not define anything else in the file. Do not mention any other function of the
  crate (not even the target) inside the postcondition; only the crate's types,
  constructors and projections may appear.
- Tuples in the result are destructured as `⦃ a b => … ⦄` (one name per component,
  the last one is the back function for `&mut` borrows).
- Names are relative to `namespace Corpus` (write `demo.incr`, not `Corpus.demo.incr`);
  the file is elaborated with `open Aeneas Aeneas.Std Result`.

## Specifications of functions this definition calls (use as given)

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

Write the specification of `Corpus.demo.use_mul2_add1`

Emit exactly one theorem in the required form, in a single ```lean block, with `by sorry` as the body.
