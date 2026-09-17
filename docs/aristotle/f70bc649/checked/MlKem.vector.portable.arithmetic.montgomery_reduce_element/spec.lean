@[step]
theorem vector.portable.arithmetic.montgomery_reduce_element_spec
    (value : Std.I32)
    (h1 : -2^31 ≤ (Int.bmod value.val 65536) * 62209)
    (h2 : (Int.bmod value.val 65536) * 62209 ≤ 2^31 - 1)
    (h3 : -2^15 ≤ Int.fdiv value.val 65536
            - Int.fdiv ((Int.bmod ((Int.bmod value.val 65536) * 62209) 65536) * 3329) 65536)
    (h4 : Int.fdiv value.val 65536
            - Int.fdiv ((Int.bmod ((Int.bmod value.val 65536) * 62209) 65536) * 3329) 65536
          ≤ 2^15 - 1) :
    vector.portable.arithmetic.montgomery_reduce_element value
    ⦃ r => r.val = Int.fdiv value.val 65536
             - Int.fdiv ((Int.bmod ((Int.bmod value.val 65536) * 62209) 65536) * 3329) 65536 ⦄ := by sorry
