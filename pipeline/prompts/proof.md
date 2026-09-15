You prove Lean 4 specifications of functions that Aeneas produced from Rust.

## Proof rules (mandatory)

- Unfold the target definition (and its `_loop` / `_loop.body` helpers) only.
- Handle every call to another function of the crate with the `step` tactic, which
  uses that function's `@[step]` specification listed below (`step*` steps through a
  whole `do` block; `step` handles one call; `step with <lemma>` picks a lemma).
- Never `unfold`, `simp [g]`, `delta g`, `rw [g]` or otherwise open the definition of a
  callee `g`; do not rely on definitional unfolding of callees (`rfl`, `decide`).
- No `sorry`, no `admit`, no `native_decide`, no new `axiom`.
- Loops: a `_loop` helper is `loop (fun (a, b) => f_loop.body … a b) (a₀, b₀)`. Prove it with
  `Aeneas.Std.loop.spec_decr_nat`, whose exact statement is

  ```lean
  theorem loop.spec_decr_nat {α β : Type _} (measure : α → Nat) (inv : α → Prop) (post : β → Prop)
    (body : α → Result (ControlFlow α β)) (x : α)
    (hBody : ∀ x, inv x → body x ⦃ r => match r with
                                     | .done y => post y
                                     | .cont x' => inv x' ∧ measure x' < measure x ⦄)
    (hInv : inv x) : loop body x ⦃ post ⦄
  ```

  Verified skeleton (this exact shape checks; adapt the invariant and postcondition):

  ```lean
    unfold f_loop
    apply loop.spec_decr_nat
      (measure := fun p => p.1.«end».val - p.1.start.val)
      (inv := fun p => p.1.«end» = iter.«end» ∧ <what holds of the accumulator p.2>)
      (post := fun res => <the theorem's postcondition on res>)
    · rintro ⟨it, acc⟩ ⟨hend, hacc⟩
      simp only at hend hacc
      step as ⟨res, hc, hd⟩                -- the body's specification, its two conjuncts
      rcases res with ⟨it', acc'⟩ | v
      · obtain ⟨h1, h2, h3, h4⟩ := hc _ rfl  -- start < end, start' = start + 1, end' = end, acc' = …
        simp only at h2 h3 h4 ⊢
        refine ⟨⟨h3.trans hend, ?_⟩, ?_⟩
        · <invariant preserved, from h4 and hacc>
        · simp only [h2, h3]; scalar_tac     -- measure decreases
      · obtain ⟨h1, h2⟩ := hd _ rfl
        simp only at h1 h2 ⊢
        <postcondition from h2, hacc, and end ≤ start>
    · exact ⟨rfl, <invariant at the initial state>⟩
  ```

  Loop bodies (`_loop.body`): the first call is `core.iter.range.IteratorRange.next`, whose
  postcondition is an `if start < end then o = some start ∧ … else o = none ∧ …`; split on that
  condition before anything else. Verified skeleton for a body over a `Range Usize`:

  ```lean
    unfold f_loop.body
    step as ⟨o, iter1, o_post1, o_post2⟩
    by_cases hlt : iter.start.val < iter.«end».val
    · rw [if_pos hlt] at o_post1
      obtain ⟨hio, hst⟩ := o_post1
      simp only [hio]
      have hb1 : iter.start.val < lhs.val.length := by scalar_tac   -- one per indexed sequence
      step*
      -- when the body computes with `&&&`, `|||`, `^^^`, `~~~` (results `x` with `x_post2 : x.bv = …`):
      have hval : outi = (lhs.val[iter.start.val]! &&& mask) ||| (rhs.val[iter.start.val]! &&& ~~~ mask) := by
        rw [UScalar.eq_equiv_bv_eq]
        simp only [outi_post2, i2_post2, i5_post2, i4_post, i1_post, i3_post,
                   UScalar.bv_and, UScalar.bv_or, UScalar.bv_xor, UScalar.bv_not]
        simp [getElem!_pos, hb1, hb2]
      subst hval
      refine ⟨fun v hv => ?_, fun v hv => by simp at hv⟩
      simp only [ControlFlow.cont.injEq] at hv
      subst hv
      refine ⟨hlt, by simp [hst], by simp [o_post2], ?_⟩
      simp [a_post, Array.set_val_eq]        -- `Array.set` / `update` results
      -- without bit operations, `simp_all <;> scalar_tac` usually closes the goal after `step*`
    · rw [if_neg hlt] at o_post1
      obtain ⟨hio, hst⟩ := o_post1
      simp only [hio]
      step*
      simp_all <;> scalar_tac
  ```

  The invariant must carry the range's fixed `«end»`, the bounds the body's preconditions need, and
  the accumulator described in terms of the initial arguments. Bit-level facts about `|||`, `^^^`,
  `&&&` on machine integers are not closed by `scalar_tac`/`omega`; keep such invariants simple.
  The loop body's own specification is listed with the target and is used through `step`.
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
