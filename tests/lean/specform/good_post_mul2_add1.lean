@[step]
theorem demo.mul2_add1_spec (x : U32) (h : 2 * x.val + 1 ≤ U32.max) :
    demo.mul2_add1 x ⦃ r => r.val = 2 * x.val + 1 ∧ r.val ≤ U32.max ⦄ := by sorry
