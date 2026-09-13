@[step]
theorem demo.mul2_add1_spec (x : U32) (h : 1 ≤ x.val ∧ 2 * x.val + 1 ≤ U32.max) :
    demo.mul2_add1 x ⦃ _ => True ⦄ := by sorry
