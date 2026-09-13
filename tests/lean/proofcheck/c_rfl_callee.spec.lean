@[step]
theorem adt_borrows.use_array_mut_borrow1_spec {N : Usize} (x : Array U32 N) :
    adt_borrows.use_array_mut_borrow1 x ⦃ r back => r = x ∧ back = fun y => y ⦄ := by sorry
