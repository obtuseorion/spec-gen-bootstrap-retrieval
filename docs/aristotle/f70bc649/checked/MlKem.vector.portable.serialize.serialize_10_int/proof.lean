have int_ediv_eq_div : ∀ (a b : Int), Int.ediv a b = a / b := by
  intro a b
  exact rfl
have nat_or_eq_add : ∀ {a b k : Nat} (hb : b < 2 ^ k), a * 2 ^ k ||| b = a * 2 ^ k + b := by
  intro a b k hb
  rw [Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hb]
have u8_size_eq : U8.size = 256 := by
  simp [U8.size, U8.numBits, UScalarTy.numBits]
have int_bmod_emod : ∀ (a : Int) (m : Nat), Int.bmod a m % m = a % m := by
  intro a m
  simp only [Int.bmod]; split <;> simp
have int_emod_emod_small : ∀ (a m n : Int) (hm : 0 < m) (h : m ≤ n), (a % m) % n = a % m := by
  intro a m n hm h
  exact Int.emod_eq_of_lt (Int.emod_nonneg a (ne_of_gt hm))
    (lt_of_lt_of_le (Int.emod_lt_of_pos a hm) h)
have i16_and_mask : ∀ (x y : Std.I16) (k : Nat) (m : Int) (hk : k ≤ 15)
    (hy : y.bv.toNat = 2 ^ k - 1) (hm : (2 : Int) ^ k = m), (x &&& y).val = x.val % m := by
  intro x y k m hk hy hm
  subst hm
  have hkpos : 0 < (2 : Nat) ^ k := Nat.two_pow_pos k
  have hk2 : (2 : Nat) ^ k ≤ 2 ^ 15 := Nat.pow_le_pow_right (by norm_num) hk
  have htn : (x &&& y).bv.toNat = x.bv.toNat % 2 ^ k := by
    rw [IScalar.bv_and, BitVec.toNat_and, hy, Nat.and_two_pow_sub_one_eq_mod]
  have hlt : x.bv.toNat % 2 ^ k < 2 ^ k := Nat.mod_lt _ hkpos
  have hb : ((x.bv.toNat % 2 ^ k : Nat) : Int) < 32768 := by
    exact_mod_cast lt_of_lt_of_le hlt hk2
  have hb0 : (0 : Int) ≤ ((x.bv.toNat % 2 ^ k : Nat) : Int) := Int.natCast_nonneg _
  push_cast at hb hb0
  have h1 : (x &&& y).val = ((x.bv.toNat % 2 ^ k : Nat) : Int) := by
    show ((x &&& y).bv).toInt = _
    rw [show ((x &&& y).bv).toInt = Int.bmod ((x &&& y).bv.toNat) (2 ^ 16) from
      BitVec.toInt_eq_toNat_bmod _, htn]
    apply Int.bmod_eq_of_le <;> norm_num <;> omega
  have hdvd : ((2 : Int) ^ k) ∣ ((2 : Nat) ^ 16 : Nat) := by
    have : (2 : Int) ^ k ∣ (2 : Int) ^ 16 := pow_dvd_pow 2 (by omega)
    simpa using this
  have h2 : x.val % 2 ^ k = ((x.bv.toNat % 2 ^ k : Nat) : Int) := by
    show x.bv.toInt % 2 ^ k = _
    rw [show x.bv.toInt = Int.bmod (x.bv.toNat) (2 ^ 16) from BitVec.toInt_eq_toNat_bmod _,
      ← Int.emod_emod_of_dvd _ hdvd, int_bmod_emod, Int.emod_emod_of_dvd _ hdvd]
    push_cast
    ring_nf
  rw [h1, h2]
have i16_hcast_u8_val : ∀ (x : Std.I16), ((IScalar.hcast .U8 x).val : Int) = x.val % 256 := by
  intro x
  rw [IScalar.hcast_val_eq]
  simp only [UScalarTy.numBits]
  norm_num
  exact Int.emod_nonneg _ (by norm_num)
unfold vector.portable.serialize.serialize_10_int
step*
-- byte 0: the low 8 bits of coefficient 0
have h1 : i1.val = i.val % 256 := by
  rw [i1_post1]; exact i16_and_mask i 255#i16 8 256 (by omega) rfl (by norm_num)
have k0 : (r0.val : Int) = i.val % 256 := by
  rw [r0_post, i16_hcast_u8_val, h1]; exact int_emod_emod_small _ 256 256 (by norm_num) le_rfl
-- byte 1: the low 6 bits of coefficient 1, above bits 8-9 of coefficient 0
have h3 : i3.val = i2.val % 64 := by
  rw [i3_post1]; exact i16_and_mask i2 63#i16 6 64 (by omega) rfl (by norm_num)
have h4 : (i4.val : Int) = i2.val % 64 := by
  rw [i4_post, i16_hcast_u8_val, h3]; exact int_emod_emod_small _ 64 256 (by norm_num) (by norm_num)
have h6 : i6.val = i.val / 256 := by
  rw [i6_post1, Int.shiftRight_eq_div_pow]; norm_num
have h7 : i7.val = i6.val % 4 := by
  rw [i7_post1]; exact i16_and_mask i6 3#i16 2 4 (by omega) rfl (by norm_num)
have h8 : (i8.val : Int) = i6.val % 4 := by
  rw [i8_post, i16_hcast_u8_val, h7]; exact int_emod_emod_small _ 4 256 (by norm_num) (by norm_num)
have h5 : i5.val = i4.val * 4 := by
  rw [i5_post1, Nat.shiftLeft_eq, u8_size_eq]; omega
have k1 : (r1.val : Int) = 4 * (i2.val % 64) + (i.val / 256) % 4 := by
  have hr1 : r1.val = i4.val * 4 + i8.val := by
    rw [r1_post1, UScalar.val_or, h5]; exact nat_or_eq_add (k := 2) (by omega)
  omega
-- byte 2: the low 4 bits of coefficient 2, above bits 6-9 of coefficient 1
have h10 : i10.val = i9.val % 16 := by
  rw [i10_post1]; exact i16_and_mask i9 15#i16 4 16 (by omega) rfl (by norm_num)
have h11 : (i11.val : Int) = i9.val % 16 := by
  rw [i11_post, i16_hcast_u8_val, h10]
  exact int_emod_emod_small _ 16 256 (by norm_num) (by norm_num)
have h13 : i13.val = i2.val / 64 := by
  rw [i13_post1, Int.shiftRight_eq_div_pow]; norm_num
have h14 : i14.val = i13.val % 16 := by
  rw [i14_post1]; exact i16_and_mask i13 15#i16 4 16 (by omega) rfl (by norm_num)
have h15 : (i15.val : Int) = i13.val % 16 := by
  rw [i15_post, i16_hcast_u8_val, h14]
  exact int_emod_emod_small _ 16 256 (by norm_num) (by norm_num)
have h12 : i12.val = i11.val * 16 := by
  rw [i12_post1, Nat.shiftLeft_eq, u8_size_eq]; omega
have k2 : (r2.val : Int) = 16 * (i9.val % 16) + (i2.val / 64) % 16 := by
  have hr2 : r2.val = i11.val * 16 + i15.val := by
    rw [r2_post1, UScalar.val_or, h12]; exact nat_or_eq_add (k := 4) (by omega)
  omega
-- byte 3: the low 2 bits of coefficient 3, above bits 4-9 of coefficient 2
have h17 : i17.val = i16.val % 4 := by
  rw [i17_post1]; exact i16_and_mask i16 3#i16 2 4 (by omega) rfl (by norm_num)
have h18 : (i18.val : Int) = i16.val % 4 := by
  rw [i18_post, i16_hcast_u8_val, h17]
  exact int_emod_emod_small _ 4 256 (by norm_num) (by norm_num)
have h20 : i20.val = i9.val / 16 := by
  rw [i20_post1, Int.shiftRight_eq_div_pow]; norm_num
have h21 : i21.val = i20.val % 64 := by
  rw [i21_post1]; exact i16_and_mask i20 63#i16 6 64 (by omega) rfl (by norm_num)
have h22 : (i22.val : Int) = i20.val % 64 := by
  rw [i22_post, i16_hcast_u8_val, h21]
  exact int_emod_emod_small _ 64 256 (by norm_num) (by norm_num)
have h19 : i19.val = i18.val * 64 := by
  rw [i19_post1, Nat.shiftLeft_eq, u8_size_eq]; omega
have k3 : (r3.val : Int) = 64 * (i16.val % 4) + (i9.val / 16) % 64 := by
  have hr3 : r3.val = i18.val * 64 + i22.val := by
    rw [r3_post1, UScalar.val_or, h19]; exact nat_or_eq_add (k := 6) (by omega)
  omega
-- byte 4: bits 2-9 of coefficient 3
have h23 : i23.val = i16.val / 4 := by
  rw [i23_post1, Int.shiftRight_eq_div_pow]; norm_num
have h24 : i24.val = i23.val % 256 := by
  rw [i24_post1]; exact i16_and_mask i23 255#i16 8 256 (by omega) rfl (by norm_num)
have k4 : (r4.val : Int) = (i16.val / 4) % 256 := by
  rw [r4_post, i16_hcast_u8_val, h24, h23]
  exact int_emod_emod_small _ 256 256 (by norm_num) le_rfl
have e0 : v.val[0]! = v.val[0]'(by omega) := getElem!_pos _ _ (by omega)
have e1 : v.val[1]! = v.val[1]'(by omega) := getElem!_pos _ _ (by omega)
have e2 : v.val[2]! = v.val[2]'(by omega) := getElem!_pos _ _ (by omega)
have e3 : v.val[3]! = v.val[3]'(by omega) := getElem!_pos _ _ (by omega)
subst i_post i2_post i9_post i16_post
simp only [e0, e1, e2, e3, int_ediv_eq_div]
refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega
