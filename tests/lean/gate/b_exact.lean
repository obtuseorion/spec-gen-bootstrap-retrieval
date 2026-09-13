@[step]
theorem adt_borrows.array_shared_borrow_spec {N : Usize} (x : Array U32 N) :
    adt_borrows.array_shared_borrow x ⦃ r => r = x ⦄ := by sorry
