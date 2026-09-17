have u8_hcast_i16_val : ∀ (x : Std.U8), (UScalar.hcast .I16 x).val = (x.val : Int) := by
  intro x
  have h : x.val < 256 := by scalar_tac
  simp only [UScalar.hcast_val_eq, IScalarTy.numBits]
  norm_num
  apply Int.bmod_eq_of_le <;> omega
have u8_bound : ∀ (x : Std.U8), x.val < 256 := by
  intro x
  scalar_tac
have nat_or_eq_add : ∀ {a b k : Nat} (hb : b < 2 ^ k), a * 2 ^ k ||| b = a * 2 ^ k + b := by
  intro a b k hb
  rw [Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hb]
have u8_size_eq : U8.size = 256 := by
  simp [U8.size, U8.numBits, UScalarTy.numBits]
unfold vector.portable.serialize.deserialize_5_int
step*
have c0 := u8_bound i; have c2 := u8_bound i2; have c9 := u8_bound i9
have c14 := u8_bound i14; have c21 := u8_bound i21
-- `v0`: the low 5 bits of byte 0
have k0 : i1.val = i.val % 32 := by
  rw [i1_post1]; exact Nat.and_two_pow_sub_one_eq_mod i.val 5
-- `v1`: the low 2 bits of byte 1, shifted up, or-ed with the top 3 bits of byte 0
have h3 : i3.val = i2.val % 4 := by
  rw [i3_post1]; exact Nat.and_two_pow_sub_one_eq_mod i2.val 2
have h5 : i5.val = i.val / 32 := by
  rw [i5_post1]; exact Nat.shiftRight_eq_div_pow i.val 5
have h4 : i4.val = i3.val * 8 := by
  rw [i4_post1, Nat.shiftLeft_eq, u8_size_eq]; omega
have k1 : i6.val = (i2.val % 4) * 8 + i.val / 32 := by
  rw [i6_post1, UScalar.val_or, h4, h5, h3]; exact nat_or_eq_add (k := 3) (by omega)
-- `v2`: bits 2..6 of byte 1
have h7 : i7.val = i2.val / 4 := by
  rw [i7_post1]; exact Nat.shiftRight_eq_div_pow i2.val 2
have k2 : i8.val = (i2.val / 4) % 32 := by
  rw [i8_post1, UScalar.val_and, h7]; exact Nat.and_two_pow_sub_one_eq_mod (i2.val / 4) 5
-- `v3`: the low 4 bits of byte 2, shifted up, or-ed with the top bit of byte 1
have h10 : i10.val = i9.val % 16 := by
  rw [i10_post1]; exact Nat.and_two_pow_sub_one_eq_mod i9.val 4
have h12 : i12.val = i2.val / 128 := by
  rw [i12_post1]; exact Nat.shiftRight_eq_div_pow i2.val 7
have h11 : i11.val = i10.val * 2 := by
  rw [i11_post1, Nat.shiftLeft_eq, u8_size_eq]; omega
have k3 : i13.val = (i9.val % 16) * 2 + i2.val / 128 := by
  rw [i13_post1, UScalar.val_or, h11, h12, h10]; exact nat_or_eq_add (k := 1) (by omega)
-- `v4`: the low bit of byte 3, shifted up, or-ed with the top 4 bits of byte 2
have h15 : i15.val = i14.val % 2 := by
  rw [i15_post1]; exact Nat.and_two_pow_sub_one_eq_mod i14.val 1
have h17 : i17.val = i9.val / 16 := by
  rw [i17_post1]; exact Nat.shiftRight_eq_div_pow i9.val 4
have h16 : i16.val = i15.val * 16 := by
  rw [i16_post1, Nat.shiftLeft_eq, u8_size_eq]; omega
have k4 : i18.val = (i14.val % 2) * 16 + i9.val / 16 := by
  rw [i18_post1, UScalar.val_or, h16, h17, h15]; exact nat_or_eq_add (k := 4) (by omega)
-- `v5`: bits 1..5 of byte 3
have h19 : i19.val = i14.val / 2 := by
  rw [i19_post1]; exact Nat.shiftRight_eq_div_pow i14.val 1
have k5 : i20.val = (i14.val / 2) % 32 := by
  rw [i20_post1, UScalar.val_and, h19]; exact Nat.and_two_pow_sub_one_eq_mod (i14.val / 2) 5
-- `v6`: the low 3 bits of byte 4, shifted up, or-ed with the top 2 bits of byte 3
have h22 : i22.val = i21.val % 8 := by
  rw [i22_post1]; exact Nat.and_two_pow_sub_one_eq_mod i21.val 3
have h24 : i24.val = i14.val / 64 := by
  rw [i24_post1]; exact Nat.shiftRight_eq_div_pow i14.val 6
have h23 : i23.val = i22.val * 4 := by
  rw [i23_post1, Nat.shiftLeft_eq, u8_size_eq]; omega
have k6 : i25.val = (i21.val % 8) * 4 + i14.val / 64 := by
  rw [i25_post1, UScalar.val_or, h23, h24, h22]; exact nat_or_eq_add (k := 2) (by omega)
-- `v7`: the top 5 bits of byte 4
have k7 : i26.val = i21.val / 8 := by
  rw [i26_post1]; exact Nat.shiftRight_eq_div_pow i21.val 3
have e0 : bytes.val[0]! = bytes.val[0]'(by omega) := getElem!_pos _ _ (by omega)
have e1 : bytes.val[1]! = bytes.val[1]'(by omega) := getElem!_pos _ _ (by omega)
have e2 : bytes.val[2]! = bytes.val[2]'(by omega) := getElem!_pos _ _ (by omega)
have e3 : bytes.val[3]! = bytes.val[3]'(by omega) := getElem!_pos _ _ (by omega)
have e4 : bytes.val[4]! = bytes.val[4]'(by omega) := getElem!_pos _ _ (by omega)
subst i_post i2_post i9_post i14_post i21_post v0_post v1_post v2_post v3_post v4_post v5_post
  v6_post v7_post
simp only [e0, e1, e2, e3, e4, u8_hcast_i16_val, k0, k1, k2, k3, k4, k5, k6, k7]
simp
