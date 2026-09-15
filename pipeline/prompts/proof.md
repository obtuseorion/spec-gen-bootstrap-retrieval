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

{{callee_specs}}

{{#examples}}
## Verified examples from this codebase

{{examples}}
{{/examples}}
## Target

The unit ({{unit_id}}) consists of the following definitions:

```lean
{{source}}
```
{{#other_specs}}
Specifications of the other members of this unit (available as step lemmas):

{{other_specs}}
{{/other_specs}}
Prove this specification of `{{target}}`:

```lean
{{spec_stmt}}
```
{{#feedback}}
## Feedback on the previous attempt

{{feedback}}
{{/feedback}}
Replace `sorry`. Reply with exactly one ```lean block containing only the tactic block
(the lines that follow `:= by`), nothing else.
