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
             - Int.fdiv ((Int.bmod ((Int.bmod value.val 65536) * 62209) 65536) * 3329) 65536 ⦄ := by sorry

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

end MlKem