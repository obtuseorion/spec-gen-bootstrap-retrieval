@[step]
theorem vector.portable.serialize.serialize_10_int_spec (v : Slice Std.I16)
    (h : 4 ≤ v.val.length) :
    vector.portable.serialize.serialize_10_int v
    ⦃ r0 r1 r2 r3 r4 =>
        r0.val = v.val[0]!.val % 256 ∧
        r1.val = 4 * (v.val[1]!.val % 64) + (Int.ediv v.val[0]!.val 256) % 4 ∧
        r2.val = 16 * (v.val[2]!.val % 16) + (Int.ediv v.val[1]!.val 64) % 16 ∧
        r3.val = 64 * (v.val[3]!.val % 4) + (Int.ediv v.val[2]!.val 16) % 64 ∧
        r4.val = (Int.ediv v.val[3]!.val 4) % 256 ⦄ := by sorry
