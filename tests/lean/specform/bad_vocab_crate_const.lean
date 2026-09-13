@[step]
theorem demo.use_mul2_add1_spec (x y : U32) (h : 2 * x.val + 1 + y.val ≤ U32.max) :
    demo.use_mul2_add1 x y ⦃ r => ∃ i, demo.mul2_add1 x = ok i ∧ r.val = i.val + y.val ⦄ := by sorry
