@[step]
theorem demo.use_mul2_add1_spec (x y : U32) (h : 2 * x.val + 1 + y.val ≤ U32.max) :
    demo.use_mul2_add1 x y ⦃ r => r.val = 2 * x.val + 1 + y.val ⦄ := by sorry
