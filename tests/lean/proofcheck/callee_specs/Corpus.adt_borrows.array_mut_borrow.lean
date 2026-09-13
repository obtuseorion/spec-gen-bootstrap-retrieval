@[step]
theorem adt_borrows.array_mut_borrow_spec {N : Usize} (x : Array U32 N) :
    adt_borrows.array_mut_borrow x ⦃ r back => r = x ∧ back = fun y => y ⦄ := by sorry
