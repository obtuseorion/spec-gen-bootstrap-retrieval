@[step]
theorem demo.incr_spec (x : U32) (h : x.val + 1 ≤ U32.max) :
    demo.incr x ⦃ r => ∃ n : Nat, r.val = n + x.val ⦄ := by sorry
