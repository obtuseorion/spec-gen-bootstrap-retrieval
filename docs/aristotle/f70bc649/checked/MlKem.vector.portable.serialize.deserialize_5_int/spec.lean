@[step]
theorem vector.portable.serialize.deserialize_5_int_spec
    (bytes : Slice Std.U8) (h : 5 ≤ bytes.val.length) :
    vector.portable.serialize.deserialize_5_int bytes
    ⦃ v0 v1 v2 v3 v4 v5 v6 v7 =>
      v0.val = ((bytes.val[0]!.val % 32 : Nat) : Int) ∧
      v1.val = (((bytes.val[1]!.val % 4) * 8 + bytes.val[0]!.val / 32 : Nat) : Int) ∧
      v2.val = (((bytes.val[1]!.val / 4) % 32 : Nat) : Int) ∧
      v3.val = (((bytes.val[2]!.val % 16) * 2 + bytes.val[1]!.val / 128 : Nat) : Int) ∧
      v4.val = (((bytes.val[3]!.val % 2) * 16 + bytes.val[2]!.val / 16 : Nat) : Int) ∧
      v5.val = (((bytes.val[3]!.val / 2) % 32 : Nat) : Int) ∧
      v6.val = (((bytes.val[4]!.val % 8) * 4 + bytes.val[3]!.val / 64 : Nat) : Int) ∧
      v7.val = ((bytes.val[4]!.val / 8 : Nat) : Int) ⦄ := by sorry
