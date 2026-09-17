import MlKem
open Aeneas Aeneas.Std Result
set_option Aeneas.Deprecated.progressWarning false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
namespace MlKem

/-! Callee specifications (admitted elsewhere; treat the callees as opaque and use these through `step`). -/
@[step]
axiom I16.Insts.Libcrux_secretsIntCastOps.as_i32_spec (x : Std.I16) :
    I16.Insts.Libcrux_secretsIntCastOps.as_i32 x ⦃ r => r = IScalar.cast .I32 x ⦄ 

@[step]
axiom I16.Insts.Libcrux_secretsIntCastOps.as_u8_spec (x : Std.I16) :
    I16.Insts.Libcrux_secretsIntCastOps.as_u8 x ⦃ r => r = IScalar.hcast .U8 x ⦄ 

@[step]
axiom I32.Insts.Libcrux_secretsIntCastOps.as_i16_spec (x : Std.I32) :
    I32.Insts.Libcrux_secretsIntCastOps.as_i16 x ⦃ r => r = IScalar.cast .I16 x ⦄ 

@[step]
axiom U32.Insts.Libcrux_secretsIntCastOps.as_i32_spec (x : Std.U32) :
    U32.Insts.Libcrux_secretsIntCastOps.as_i32 x ⦃ r => r = UScalar.hcast .I32 x ⦄ 

@[step]
axiom U8.Insts.Libcrux_secretsIntCastOps.as_i16_spec (x : Std.U8) :
    U8.Insts.Libcrux_secretsIntCastOps.as_i16 x ⦃ r => r = UScalar.hcast .I16 x ⦄ 

@[step]
axiom libcrux_secrets.traits.Classify.Blanket.classify_spec {T : Type} (inst : libcrux_secrets.traits.Scalar T) (x : T) :
    libcrux_secrets.traits.Classify.Blanket.classify inst x ⦃ r => r = x ⦄ 

/-! Auxiliary facts used to move between the signed (`I16`) and unsigned (`U8`) views of
    the same word, so that the bit-level reasoning (`&&&`, `|||`, `<<<`, `>>>`) can be
    replaced by plain `Int`/`Nat` arithmetic that `omega` can discharge. -/

/-- Zero-extending a `U8` into an `I16` preserves the value. -/
theorem u8_hcast_i16_val (x : Std.U8) : (UScalar.hcast .I16 x).val = (x.val : Int) := by
  have h : x.val < 256 := by scalar_tac
  simp only [UScalar.hcast_val_eq, IScalarTy.numBits]
  norm_num
  apply Int.bmod_eq_of_le <;> omega

theorem u8_bound (x : Std.U8) : x.val < 256 := by scalar_tac

theorem int_ediv_eq_div (a b : Int) : Int.ediv a b = a / b := rfl

/-! Elementary bit-manipulation facts on `Nat`, used to turn the `&&&`, `|||`, `<<<`
    and `>>>` post-conditions produced by `step` into plain arithmetic, which `omega`
    can then handle. -/

/-- A disjoint bitwise `or` is an addition. -/
theorem nat_or_eq_add {a b k : Nat} (hb : b < 2 ^ k) : a * 2 ^ k ||| b = a * 2 ^ k + b := by
  rw [Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hb]

theorem u8_size_eq : U8.size = 256 := by simp [U8.size, U8.numBits, UScalarTy.numBits]

/-- `Int.bmod` and `Int.emod` agree modulo `m`. -/
theorem int_bmod_emod (a : Int) (m : Nat) : Int.bmod a m % m = a % m := by
  simp only [Int.bmod]; split <;> simp

/-- Reducing an already-reduced remainder modulo a larger modulus does nothing. -/
theorem int_emod_emod_small (a m n : Int) (hm : 0 < m) (h : m ≤ n) : (a % m) % n = a % m :=
  Int.emod_eq_of_lt (Int.emod_nonneg a (ne_of_gt hm))
    (lt_of_lt_of_le (Int.emod_lt_of_pos a hm) h)

/-- Masking a signed 16-bit word with `2^k - 1` (`k ≤ 15`) is reduction modulo `2^k`;
    the result is the (nonnegative) Euclidean remainder. -/
theorem i16_and_mask (x y : Std.I16) (k : Nat) (m : Int) (hk : k ≤ 15)
    (hy : y.bv.toNat = 2 ^ k - 1) (hm : (2 : Int) ^ k = m) : (x &&& y).val = x.val % m := by
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

theorem i16_size_eq : I16.size = 65536 := by simp [I16.size, I16.numBits, IScalarTy.numBits]

/-- A nonnegative `I16` is its own unsigned reading. -/
theorem i16_bv_toNat_of_nonneg (x : Std.I16) (h : 0 ≤ x.val) : (x.bv.toNat : Int) = x.val := by
  have hlt : x.bv.toNat < 65536 := x.bv.isLt
  rw [show x.val = Int.bmod (x.bv.toNat) (2 ^ 16) from BitVec.toInt_eq_toNat_bmod _] at h ⊢
  simp only [Int.bmod] at h ⊢
  split at h <;> omega

/-- A left shift of a small nonnegative value does not wrap around. -/
theorem i16_bmod_shiftLeft (a : Int) (k : Nat) (m : Int) (hm : (2 : Int) ^ k = m)
    (h0 : 0 ≤ a) (h1 : a * m < 32768) : (a <<< k).bmod I16.size = a * m := by
  subst hm
  rw [i16_size_eq, Int.shiftLeft_eq]
  have hmpos : (0 : Int) < 2 ^ k := by positivity
  apply Int.bmod_eq_of_le <;> norm_num <;> nlinarith

/-- Or-ing together two nonnegative `I16`s whose set bits are disjoint (the left one is a
    multiple of `m = 2^k`, the right one is smaller than `m`) is an addition. -/
theorem i16_or_eq_add (x y : Std.I16) (k : Nat) (m : Int) (hm : (2 : Int) ^ k = m)
    (hx0 : 0 ≤ x.val) (hxd : x.val % m = 0) (hy0 : 0 ≤ y.val) (hyk : y.val < m)
    (hsum : x.val + y.val < 32768) : (x ||| y).val = x.val + y.val := by
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

/-- Truncating an `I16` to a `U8` keeps the value modulo `256`. -/
theorem i16_hcast_u8_val (x : Std.I16) : ((IScalar.hcast .U8 x).val : Int) = x.val % 256 := by
  rw [IScalar.hcast_val_eq]
  simp only [UScalarTy.numBits]
  norm_num
  exact Int.emod_nonneg _ (by norm_num)

/-! Targets: fill in the `sorry`s below. Do not unfold callees; use their `@[step]` lemmas. -/
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
             - Int.fdiv ((Int.bmod ((Int.bmod value.val 65536) * 62209) 65536) * 3329) 65536 ⦄ := by
  have hv0 : -2147483648 ≤ value.val ∧ value.val ≤ 2147483647 := by constructor <;> scalar_tac
  have hf : ∀ a : Int, Int.fdiv a 65536 = a / 65536 :=
    fun a => Int.fdiv_eq_ediv_of_nonneg a (by norm_num)
  have hbb : Int.bmod (Int.bmod value.val 65536 * 62209) 65536
      = Int.bmod (value.val * 62209) 65536 := Int.bmod_mul_bmod
  have hc1 : Int.bmod (62209 : Int) 4294967296 = 62209 := by norm_num [Int.bmod]
  have hc2 : Int.bmod (3329 : Int) 65536 = 3329 := by norm_num [Int.bmod]
  have hb0 : -32768 ≤ Int.bmod value.val 65536 := by
    have := Int.le_bmod (x := value.val) (m := 65536) (by norm_num); norm_num at this ⊢; omega
  have hb1 : Int.bmod value.val 65536 < 32768 := by
    have := Int.bmod_lt (x := value.val) (m := 65536) (by norm_num); norm_num at this ⊢; omega
  have hb2 : -32768 ≤ Int.bmod (value.val * 62209) 65536 := by
    have := Int.le_bmod (x := value.val * 62209) (m := 65536) (by norm_num)
    norm_num at this ⊢; omega
  have hb3 : Int.bmod (value.val * 62209) 65536 < 32768 := by
    have := Int.bmod_lt (x := value.val * 62209) (m := 65536) (by norm_num)
    norm_num at this ⊢; omega
  have hd0 : Int.bmod (value.val / 65536) 65536 = value.val / 65536 :=
    Int.bmod_eq_of_le (by norm_num; omega) (by norm_num; omega)
  have hd1 : Int.bmod ((Int.bmod (value.val * 62209) 65536 * 3329) / 65536) 65536
      = (Int.bmod (value.val * 62209) 65536 * 3329) / 65536 :=
    Int.bmod_eq_of_le (by norm_num; omega) (by norm_num; omega)
  rw [hbb, hf, hf] at h3 h4
  unfold vector.portable.arithmetic.montgomery_reduce_element
  step*
  all_goals
    simp only [*, IScalar.cast_val_eq, UScalar.hcast_val_eq, vector.traits.FIELD_MODULUS,
      vector.traits.INVERSE_OF_MODULUS_MOD_MONTGOMERY_R,
      vector.portable.arithmetic.MONTGOMERY_SHIFT, IScalarTy.numBits,
      Int.shiftRight_eq_div_pow, I32.max, I32.min, I16.max, I16.min, I32.numBits, I16.numBits]
  all_goals norm_num [hc1, hc2]
  all_goals try simp only [hd0, hd1]
  all_goals omega

@[step]
theorem vector.portable.serialize.serialize_10_int_spec (v : Slice Std.I16)
    (h : 4 ≤ v.val.length) :
    vector.portable.serialize.serialize_10_int v
    ⦃ r0 r1 r2 r3 r4 =>
        r0.val = v.val[0]!.val % 256 ∧
        r1.val = 4 * (v.val[1]!.val % 64) + (Int.ediv v.val[0]!.val 256) % 4 ∧
        r2.val = 16 * (v.val[2]!.val % 16) + (Int.ediv v.val[1]!.val 64) % 16 ∧
        r3.val = 64 * (v.val[3]!.val % 4) + (Int.ediv v.val[2]!.val 16) % 64 ∧
        r4.val = (Int.ediv v.val[3]!.val 4) % 256 ⦄ := by
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
        r7.val = bytes.val[10]!.val * 8 + bytes.val[9]!.val / 32 ⦄ := by
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
      v7.val = ((bytes.val[4]!.val / 8 : Nat) : Int) ⦄ := by
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

end MlKem