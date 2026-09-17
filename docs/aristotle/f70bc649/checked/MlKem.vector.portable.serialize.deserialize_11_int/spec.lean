@[step]
theorem vector.portable.serialize.deserialize_11_int_spec
    (bytes : Slice Std.U8) (h : 11 ≤ bytes.val.length) :
    vector.portable.serialize.deserialize_11_int bytes
    ⦃ r0 r1 r2 r3 r4 r5 r6 r7 =>
        r0.val = (bytes.val[1]!.val % 8) * 256 + bytes.val[0]!.val ∧
        r1.val = (bytes.val[2]!.val % 64) * 32 + bytes.val[1]!.val / 8 ∧
        r2.val = (bytes.val[4]!.val % 2) * 1024 + bytes.val[3]!.val * 4
                 + bytes.val[2]!.val / 64 ∧
        r3.val = (bytes.val[5]!.val % 16) * 128 + bytes.val[4]!.val / 2 ∧
        r4.val = (bytes.val[6]!.val % 128) * 16 + bytes.val[5]!.val / 16 ∧
        r5.val = (bytes.val[8]!.val % 4) * 512 + bytes.val[7]!.val * 2
                 + bytes.val[6]!.val / 128 ∧
        r6.val = (bytes.val[9]!.val % 32) * 64 + bytes.val[8]!.val / 4 ∧
        r7.val = bytes.val[10]!.val * 8 + bytes.val[9]!.val / 32 ⦄ := by sorry
