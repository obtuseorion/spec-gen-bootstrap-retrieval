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

/-! Auxiliary facts used to move between the signed (`I16`) and unsigned (`U8`/`U16`)
    views of the same 16-bit word, so that the bit-level reasoning can be done with
    `bv_tac` in the unsigned world and transported back with `omega`. -/

/-- Reinterpreting an `I16` as a `U16` gives its value modulo `2^16`. -/
theorem i16_to_u16_val (x : Std.I16) : ((IScalar.hcast .U16 x).val : Int) = x.val % 65536 := by
  simp only [IScalar.hcast_val_eq, UScalarTy.numBits]
  norm_num
  exact Int.emod_nonneg _ (by norm_num)

/-- Zero-extending a `U8` into an `I16` preserves the value. -/
theorem u8_hcast_i16_val (x : Std.U8) : (UScalar.hcast .I16 x).val = (x.val : Int) := by
  have h : x.val < 256 := by scalar_tac
  simp only [UScalar.hcast_val_eq, IScalarTy.numBits]
  norm_num
  apply Int.bmod_eq_of_le <;> omega

theorem i16_bounds (x : Std.I16) : -32768 ≤ x.val ∧ x.val < 32768 := by
  constructor <;> scalar_tac

theorem u8_bound (x : Std.U8) : x.val < 256 := by scalar_tac

theorem int_ediv_eq_div (a b : Int) : Int.ediv a b = a / b := rfl

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
  have k0 : r0.val = (IScalar.hcast .U16 i).val % 256 := by
    clear * - r0_post i1_post2; bv_tac 16
  have k1 : r1.val = 4 * ((IScalar.hcast .U16 i2).val % 64)
      + ((IScalar.hcast .U16 i).val / 256) % 4 := by
    clear * - r1_post2 i5_post2 i4_post i3_post2 i8_post i7_post2 i6_post2; bv_tac 16
  have k2 : r2.val = 16 * ((IScalar.hcast .U16 i9).val % 16)
      + ((IScalar.hcast .U16 i2).val / 64) % 16 := by
    clear * - r2_post2 i12_post2 i11_post i10_post2 i15_post i14_post2 i13_post2; bv_tac 16
  have k3 : r3.val = 64 * ((IScalar.hcast .U16 i16).val % 4)
      + ((IScalar.hcast .U16 i9).val / 16) % 64 := by
    clear * - r3_post2 i19_post2 i18_post i17_post2 i22_post i21_post2 i20_post2; bv_tac 16
  have k4 : r4.val = ((IScalar.hcast .U16 i16).val / 4) % 256 := by
    clear * - r4_post i24_post2 i23_post2; bv_tac 16
  have m0 := i16_to_u16_val i
  have m1 := i16_to_u16_val i2
  have m2 := i16_to_u16_val i9
  have m3 := i16_to_u16_val i16
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
  have k0 : (IScalar.hcast .U16 r0).val = (i.val % 8) * 256 + i4.val := by
    clear * - r0_post2 i3_post2 i2_post2 i1_post i5_post; bv_tac 16
  have k1 : (IScalar.hcast .U16 r1).val = (i6.val % 64) * 32 + i.val / 8 := by
    clear * - r1_post2 i9_post2 i8_post2 i7_post i11_post2 i10_post; bv_tac 16
  have k2 : (IScalar.hcast .U16 r2).val = (i12.val % 2) * 1024 + i16.val * 4 + i6.val / 64 := by
    clear * - r2_post2 i19_post2 i15_post2 i14_post2 i13_post i18_post2 i17_post i21_post2 i20_post
    bv_tac 16
  have k3 : (IScalar.hcast .U16 r3).val = (i22.val % 16) * 128 + i12.val / 2 := by
    clear * - r3_post2 i25_post2 i24_post2 i23_post i27_post2 i26_post; bv_tac 16
  have k4 : (IScalar.hcast .U16 r4).val = (i28.val % 128) * 16 + i22.val / 16 := by
    clear * - r4_post2 i31_post2 i30_post2 i29_post i33_post2 i32_post; bv_tac 16
  have k5 : (IScalar.hcast .U16 r5).val = (i34.val % 4) * 512 + i38.val * 2 + i28.val / 128 := by
    clear * - r5_post2 i41_post2 i37_post2 i36_post2 i35_post i40_post2 i39_post i43_post2 i42_post
    bv_tac 16
  have k6 : (IScalar.hcast .U16 r6).val = (i44.val % 32) * 64 + i34.val / 4 := by
    clear * - r6_post2 i47_post2 i46_post2 i45_post i49_post2 i48_post; bv_tac 16
  have k7 : (IScalar.hcast .U16 r7).val = i50.val * 8 + i44.val / 32 := by
    clear * - r7_post2 i52_post2 i51_post i54_post2 i53_post; bv_tac 16
  have m0 := i16_to_u16_val r0; have m1 := i16_to_u16_val r1
  have m2 := i16_to_u16_val r2; have m3 := i16_to_u16_val r3
  have m4 := i16_to_u16_val r4; have m5 := i16_to_u16_val r5
  have m6 := i16_to_u16_val r6; have m7 := i16_to_u16_val r7
  have b0 := i16_bounds r0; have b1 := i16_bounds r1
  have b2 := i16_bounds r2; have b3 := i16_bounds r3
  have b4 := i16_bounds r4; have b5 := i16_bounds r5
  have b6 := i16_bounds r6; have b7 := i16_bounds r7
  have c0 := u8_bound i; have c1 := u8_bound i4; have c2 := u8_bound i6
  have c3 := u8_bound i12; have c4 := u8_bound i16; have c5 := u8_bound i22
  have c6 := u8_bound i28; have c7 := u8_bound i34; have c8 := u8_bound i38
  have c9 := u8_bound i44; have c10 := u8_bound i50
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
  have k0 : i1.val = i.val % 32 := by clear * - i1_post2; bv_tac 8
  have k1 : i6.val = (i2.val % 4) * 8 + i.val / 32 := by
    clear * - i6_post2 i4_post2 i3_post2 i5_post2; bv_tac 8
  have k2 : i8.val = (i2.val / 4) % 32 := by clear * - i8_post2 i7_post2; bv_tac 8
  have k3 : i13.val = (i9.val % 16) * 2 + i2.val / 128 := by
    clear * - i13_post2 i11_post2 i10_post2 i12_post2; bv_tac 8
  have k4 : i18.val = (i14.val % 2) * 16 + i9.val / 16 := by
    clear * - i18_post2 i16_post2 i15_post2 i17_post2; bv_tac 8
  have k5 : i20.val = (i14.val / 2) % 32 := by clear * - i20_post2 i19_post2; bv_tac 8
  have k6 : i25.val = (i21.val % 8) * 4 + i14.val / 64 := by
    clear * - i25_post2 i23_post2 i22_post2 i24_post2; bv_tac 8
  have k7 : i26.val = i21.val / 8 := by clear * - i26_post2; bv_tac 8
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