@[step]
theorem demo.incr_spec (x : U32) (h : x.val = 0) :
    demo.incr x ⦃ r => r.val = 1 ⦄ := by sorry
