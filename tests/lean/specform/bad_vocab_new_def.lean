def incrPost (x r : U32) : Prop := r.val = x.val + 1

@[step]
theorem demo.incr_spec (x : U32) (h : x.val + 1 ≤ U32.max) :
    demo.incr x ⦃ r => incrPost x r ⦄ := by sorry
