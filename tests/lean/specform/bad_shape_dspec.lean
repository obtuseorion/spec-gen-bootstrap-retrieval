@[step]
theorem demo.incr_spec (x : U32) (h : x.val + 1 ≤ U32.max) :
    demo.incr x ⦃ r => r.val = x.val + 1 ⦄div := by sorry
