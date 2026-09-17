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
have int_bmod_emod : ∀ (a : Int) (m : Nat), Int.bmod a m % m = a % m := by
  intro a m
  simp only [Int.bmod]; split <;> simp
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
have i16_size_eq : I16.size = 65536 := by
  simp [I16.size, I16.numBits, IScalarTy.numBits]
have i16_bv_toNat_of_nonneg : ∀ (x : Std.I16) (h : 0 ≤ x.val), (x.bv.toNat : Int) = x.val := by
  intro x h
  have hlt : x.bv.toNat < 65536 := x.bv.isLt
  rw [show x.val = Int.bmod (x.bv.toNat) (2 ^ 16) from BitVec.toInt_eq_toNat_bmod _] at h ⊢
  simp only [Int.bmod] at h ⊢
  split at h <;> omega
have i16_bmod_shiftLeft : ∀ (a : Int) (k : Nat) (m : Int) (hm : (2 : Int) ^ k = m)
    (h0 : 0 ≤ a) (h1 : a * m < 32768), (a <<< k).bmod I16.size = a * m := by
  intro a k m hm h0 h1
  subst hm
  rw [i16_size_eq, Int.shiftLeft_eq]
  have hmpos : (0 : Int) < 2 ^ k := by positivity
  apply Int.bmod_eq_of_le <;> norm_num <;> nlinarith
have i16_or_eq_add : ∀ (x y : Std.I16) (k : Nat) (m : Int) (hm : (2 : Int) ^ k = m)
    (hx0 : 0 ≤ x.val) (hxd : x.val % m = 0) (hy0 : 0 ≤ y.val) (hyk : y.val < m)
    (hsum : x.val + y.val < 32768), (x ||| y).val = x.val + y.val := by
  intro x y k m hm hx0 hxd hy0 hyk hsum
  subst hm
  have hmpos : (0 : Int) < 2 ^ k := by positivity
  have hxn := i16_bv_toNat_of_nonneg x hx0
  have hyn := i16_bv_toNat_of_nonneg y hy0
  obtain ⟨a, ha⟩ := Int.dvd_of_emod_eq_zero hxd
  have ha0 : 0 ≤ a := by nlinarith
  have hxnat : x.bv.toNat = a.toNat * 2 ^ k := by
    have h : ((x.bv.toNat : Nat) : Int) = ((a.toNat * 2 ^ k : Nat) : Int) := by
      push_cast [Int.toNat_of_nonneg ha0]
      rw [hxn, ha]; ring
    exact_mod_cast h
  have hynat : y.bv.toNat < 2 ^ k := by
    have h : ((y.bv.toNat : Nat) : Int) < ((2 ^ k : Nat) : Int) := by push_cast; omega
    exact_mod_cast h
  have hor : (x ||| y).bv.toNat = a.toNat * 2 ^ k + y.bv.toNat := by
    rw [IScalar.bv_or, BitVec.toNat_or, hxnat]; exact nat_or_eq_add hynat
  have hcast : ((a.toNat * 2 ^ k + y.bv.toNat : Nat) : Int) = x.val + y.val := by
    push_cast [Int.toNat_of_nonneg ha0]
    rw [hyn, ha]; ring
  show ((x ||| y).bv).toInt = _
  rw [show ((x ||| y).bv).toInt = Int.bmod ((x ||| y).bv.toNat) (2 ^ 16) from
    BitVec.toInt_eq_toNat_bmod _, hor, hcast]
  apply Int.bmod_eq_of_le <;> norm_num <;> omega
unfold vector.portable.serialize.deserialize_11_int
step*
have c0 := u8_bound i; have c1 := u8_bound i4; have c2 := u8_bound i6
have c3 := u8_bound i12; have c4 := u8_bound i16; have c5 := u8_bound i22
have c6 := u8_bound i28; have c7 := u8_bound i34; have c8 := u8_bound i38
have c9 := u8_bound i44; have c10 := u8_bound i50
-- coefficient 0: byte 0 together with the low 3 bits of byte 1
have g1 : i1.val = (i.val : Int) := by rw [i1_post]; exact u8_hcast_i16_val i
have g2 : i2.val = i1.val % 8 := by
  rw [i2_post1]; exact i16_and_mask i1 7#i16 3 8 (by omega) rfl (by norm_num)
have g3 : i3.val = i2.val * 256 := by
  rw [i3_post1]; exact i16_bmod_shiftLeft i2.val 8 256 (by norm_num) (by omega) (by omega)
have g5 : i5.val = (i4.val : Int) := by rw [i5_post]; exact u8_hcast_i16_val i4
have k0 : r0.val = (i.val : Int) % 8 * 256 + (i4.val : Int) := by
  rw [r0_post1,
    i16_or_eq_add i3 i5 8 256 (by norm_num) (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega
-- coefficient 1: the top 5 bits of byte 1 and the low 6 bits of byte 2
have g7 : i7.val = (i6.val : Int) := by rw [i7_post]; exact u8_hcast_i16_val i6
have g8 : i8.val = i7.val % 64 := by
  rw [i8_post1]; exact i16_and_mask i7 63#i16 6 64 (by omega) rfl (by norm_num)
have g9 : i9.val = i8.val * 32 := by
  rw [i9_post1]; exact i16_bmod_shiftLeft i8.val 5 32 (by norm_num) (by omega) (by omega)
have g10 : i10.val = (i.val : Int) := by rw [i10_post]; exact u8_hcast_i16_val i
have g11 : i11.val = i10.val / 8 := by
  rw [i11_post1, Int.shiftRight_eq_div_pow]; norm_num
have k1 : r1.val = (i6.val : Int) % 64 * 32 + (i.val : Int) / 8 := by
  rw [r1_post1,
    i16_or_eq_add i9 i11 5 32 (by norm_num) (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega
-- coefficient 2: the top 2 bits of byte 2, byte 3, and the low bit of byte 4
have g13 : i13.val = (i12.val : Int) := by rw [i13_post]; exact u8_hcast_i16_val i12
have g14 : i14.val = i13.val % 2 := by
  rw [i14_post1]; exact i16_and_mask i13 1#i16 1 2 (by omega) rfl (by norm_num)
have g15 : i15.val = i14.val * 1024 := by
  rw [i15_post1]; exact i16_bmod_shiftLeft i14.val 10 1024 (by norm_num) (by omega) (by omega)
have g17 : i17.val = (i16.val : Int) := by rw [i17_post]; exact u8_hcast_i16_val i16
have g18 : i18.val = i17.val * 4 := by
  rw [i18_post1]; exact i16_bmod_shiftLeft i17.val 2 4 (by norm_num) (by omega) (by omega)
have g19 : i19.val = i15.val + i18.val := by
  rw [i19_post1]
  exact i16_or_eq_add i15 i18 10 1024 (by norm_num) (by omega) (by omega) (by omega) (by omega)
    (by omega)
have g20 : i20.val = (i6.val : Int) := by rw [i20_post]; exact u8_hcast_i16_val i6
have g21 : i21.val = i20.val / 64 := by
  rw [i21_post1, Int.shiftRight_eq_div_pow]; norm_num
have k2 : r2.val = (i12.val : Int) % 2 * 1024 + (i16.val : Int) * 4 + (i6.val : Int) / 64 := by
  rw [r2_post1,
    i16_or_eq_add i19 i21 2 4 (by norm_num) (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega
-- coefficient 3: the top 7 bits of byte 4 and the low 4 bits of byte 5
have g23 : i23.val = (i22.val : Int) := by rw [i23_post]; exact u8_hcast_i16_val i22
have g24 : i24.val = i23.val % 16 := by
  rw [i24_post1]; exact i16_and_mask i23 15#i16 4 16 (by omega) rfl (by norm_num)
have g25 : i25.val = i24.val * 128 := by
  rw [i25_post1]; exact i16_bmod_shiftLeft i24.val 7 128 (by norm_num) (by omega) (by omega)
have g26 : i26.val = (i12.val : Int) := by rw [i26_post]; exact u8_hcast_i16_val i12
have g27 : i27.val = i26.val / 2 := by
  rw [i27_post1, Int.shiftRight_eq_div_pow]; norm_num
have k3 : r3.val = (i22.val : Int) % 16 * 128 + (i12.val : Int) / 2 := by
  rw [r3_post1,
    i16_or_eq_add i25 i27 7 128 (by norm_num) (by omega) (by omega) (by omega) (by omega)
      (by omega)]
  omega
-- coefficient 4: the top 4 bits of byte 5 and the low 7 bits of byte 6
have g29 : i29.val = (i28.val : Int) := by rw [i29_post]; exact u8_hcast_i16_val i28
have g30 : i30.val = i29.val % 128 := by
  rw [i30_post1]; exact i16_and_mask i29 127#i16 7 128 (by omega) rfl (by norm_num)
have g31 : i31.val = i30.val * 16 := by
  rw [i31_post1]; exact i16_bmod_shiftLeft i30.val 4 16 (by norm_num) (by omega) (by omega)
have g32 : i32.val = (i22.val : Int) := by rw [i32_post]; exact u8_hcast_i16_val i22
have g33 : i33.val = i32.val / 16 := by
  rw [i33_post1, Int.shiftRight_eq_div_pow]; norm_num
have k4 : r4.val = (i28.val : Int) % 128 * 16 + (i22.val : Int) / 16 := by
  rw [r4_post1,
    i16_or_eq_add i31 i33 4 16 (by norm_num) (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega
-- coefficient 5: the top bit of byte 6, byte 7, and the low 2 bits of byte 8
have g35 : i35.val = (i34.val : Int) := by rw [i35_post]; exact u8_hcast_i16_val i34
have g36 : i36.val = i35.val % 4 := by
  rw [i36_post1]; exact i16_and_mask i35 3#i16 2 4 (by omega) rfl (by norm_num)
have g37 : i37.val = i36.val * 512 := by
  rw [i37_post1]; exact i16_bmod_shiftLeft i36.val 9 512 (by norm_num) (by omega) (by omega)
have g39 : i39.val = (i38.val : Int) := by rw [i39_post]; exact u8_hcast_i16_val i38
have g40 : i40.val = i39.val * 2 := by
  rw [i40_post1]; exact i16_bmod_shiftLeft i39.val 1 2 (by norm_num) (by omega) (by omega)
have g41 : i41.val = i37.val + i40.val := by
  rw [i41_post1]
  exact i16_or_eq_add i37 i40 9 512 (by norm_num) (by omega) (by omega) (by omega) (by omega)
    (by omega)
have g42 : i42.val = (i28.val : Int) := by rw [i42_post]; exact u8_hcast_i16_val i28
have g43 : i43.val = i42.val / 128 := by
  rw [i43_post1, Int.shiftRight_eq_div_pow]; norm_num
have k5 : r5.val = (i34.val : Int) % 4 * 512 + (i38.val : Int) * 2 + (i28.val : Int) / 128 := by
  rw [r5_post1,
    i16_or_eq_add i41 i43 1 2 (by norm_num) (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega
-- coefficient 6: the top 6 bits of byte 8 and the low 5 bits of byte 9
have g45 : i45.val = (i44.val : Int) := by rw [i45_post]; exact u8_hcast_i16_val i44
have g46 : i46.val = i45.val % 32 := by
  rw [i46_post1]; exact i16_and_mask i45 31#i16 5 32 (by omega) rfl (by norm_num)
have g47 : i47.val = i46.val * 64 := by
  rw [i47_post1]; exact i16_bmod_shiftLeft i46.val 6 64 (by norm_num) (by omega) (by omega)
have g48 : i48.val = (i34.val : Int) := by rw [i48_post]; exact u8_hcast_i16_val i34
have g49 : i49.val = i48.val / 4 := by
  rw [i49_post1, Int.shiftRight_eq_div_pow]; norm_num
have k6 : r6.val = (i44.val : Int) % 32 * 64 + (i34.val : Int) / 4 := by
  rw [r6_post1,
    i16_or_eq_add i47 i49 6 64 (by norm_num) (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega
-- coefficient 7: the top 3 bits of byte 9 and byte 10
have g51 : i51.val = (i50.val : Int) := by rw [i51_post]; exact u8_hcast_i16_val i50
have g52 : i52.val = i51.val * 8 := by
  rw [i52_post1]; exact i16_bmod_shiftLeft i51.val 3 8 (by norm_num) (by omega) (by omega)
have g53 : i53.val = (i44.val : Int) := by rw [i53_post]; exact u8_hcast_i16_val i44
have g54 : i54.val = i53.val / 32 := by
  rw [i54_post1, Int.shiftRight_eq_div_pow]; norm_num
have k7 : r7.val = (i50.val : Int) * 8 + (i44.val : Int) / 32 := by
  rw [r7_post1,
    i16_or_eq_add i52 i54 3 8 (by norm_num) (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega
have e0 : bytes.val[0]! = bytes.val[0]'(by omega) := getElem!_pos _ _ (by omega)
have e1 : bytes.val[1]! = bytes.val[1]'(by omega) := getElem!_pos _ _ (by omega)
have e2 : bytes.val[2]! = bytes.val[2]'(by omega) := getElem!_pos _ _ (by omega)
have e3 : bytes.val[3]! = bytes.val[3]'(by omega) := getElem!_pos _ _ (by omega)
have e4 : bytes.val[4]! = bytes.val[4]'(by omega) := getElem!_pos _ _ (by omega)
have e5 : bytes.val[5]! = bytes.val[5]'(by omega) := getElem!_pos _ _ (by omega)
have e6 : bytes.val[6]! = bytes.val[6]'(by omega) := getElem!_pos _ _ (by omega)
have e7 : bytes.val[7]! = bytes.val[7]'(by omega) := getElem!_pos _ _ (by omega)
have e8 : bytes.val[8]! = bytes.val[8]'(by omega) := getElem!_pos _ _ (by omega)
have e9 : bytes.val[9]! = bytes.val[9]'(by omega) := getElem!_pos _ _ (by omega)
have e10 : bytes.val[10]! = bytes.val[10]'(by omega) := getElem!_pos _ _ (by omega)
subst i_post i4_post i6_post i12_post i16_post i22_post i28_post i34_post i38_post i44_post
  i50_post
simp only [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
