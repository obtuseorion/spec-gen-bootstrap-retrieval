-- Step lemmas for the external models of MlKem/FunsExternal.lean (spec pipeline).
import Aeneas
import MlKem.Types
import MlKem.FunsExternal
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
open MlKem

@[step]
theorem core.hint.black_box_spec {T : Type} (x : T) :
    core.hint.black_box x ⦃ r => r = x ⦄ := by
  simp [core.hint.black_box]

@[step]
theorem libcrux_platform.platform.simd128_support_spec  :
    libcrux_platform.platform.simd128_support ⦃ r => r = false ⦄ := by
  simp [libcrux_platform.platform.simd128_support]

@[step]
theorem libcrux_platform.platform.simd256_support_spec  :
    libcrux_platform.platform.simd256_support ⦃ r => r = false ⦄ := by
  simp [libcrux_platform.platform.simd256_support]

@[step]
theorem libcrux_secrets.traits.Classify.Blanket.classify_spec {T : Type} (inst : libcrux_secrets.traits.Scalar T) (x : T) :
    libcrux_secrets.traits.Classify.Blanket.classify inst x ⦃ r => r = x ⦄ := by
  simp [libcrux_secrets.traits.Classify.Blanket.classify]

@[step]
theorem libcrux_secrets.traits.Declassify.Blanket.declassify_spec {T : Type} (inst : libcrux_secrets.traits.Scalar T) (x : T) :
    libcrux_secrets.traits.Declassify.Blanket.declassify inst x ⦃ r => r = x ⦄ := by
  simp [libcrux_secrets.traits.Declassify.Blanket.declassify]

@[step]
theorem Array.Insts.Libcrux_secretsTraitsClassifyArray.classify_spec {T : Type} {N : Usize} (inst : libcrux_secrets.traits.Scalar T) (a : Array T N) :
    Array.Insts.Libcrux_secretsTraitsClassifyArray.classify inst a ⦃ r => r = a ⦄ := by
  simp [Array.Insts.Libcrux_secretsTraitsClassifyArray.classify]

@[step]
theorem Array.Insts.Libcrux_secretsTraitsDeclassifyArray.declassify_spec {T : Type} {N : Usize} (inst : libcrux_secrets.traits.Scalar T) (a : Array T N) :
    Array.Insts.Libcrux_secretsTraitsDeclassifyArray.declassify inst a ⦃ r => r = a ⦄ := by
  simp [Array.Insts.Libcrux_secretsTraitsDeclassifyArray.declassify]

@[step]
theorem SharedASlice.Insts.Libcrux_secretsTraitsClassifyRefSharedASlice.classify_ref_spec {T : Type} (inst : libcrux_secrets.traits.Scalar T) (s : Slice T) :
    SharedASlice.Insts.Libcrux_secretsTraitsClassifyRefSharedASlice.classify_ref inst s ⦃ r => r = s ⦄ := by
  simp [SharedASlice.Insts.Libcrux_secretsTraitsClassifyRefSharedASlice.classify_ref]

@[step]
theorem libcrux_secrets.int.classify_public.classify_mut_slice_spec {T : Type} (x : T) :
    libcrux_secrets.int.classify_public.classify_mut_slice x ⦃ r => r = x ⦄ := by
  simp [libcrux_secrets.int.classify_public.classify_mut_slice]

@[step]
theorem libcrux_secrets.int.I16_spec (x : Std.I16) :
    libcrux_secrets.int.I16 x ⦃ r => r = x ⦄ := by
  simp [libcrux_secrets.int.I16]

@[step]
theorem I16.Insts.Libcrux_secretsIntCastOps.as_u8_spec (x : Std.I16) :
    I16.Insts.Libcrux_secretsIntCastOps.as_u8 x ⦃ r => r = IScalar.hcast .U8 x ⦄ := by
  simp [I16.Insts.Libcrux_secretsIntCastOps.as_u8]

@[step]
theorem I16.Insts.Libcrux_secretsIntCastOps.as_u16_spec (x : Std.I16) :
    I16.Insts.Libcrux_secretsIntCastOps.as_u16 x ⦃ r => r = IScalar.hcast .U16 x ⦄ := by
  simp [I16.Insts.Libcrux_secretsIntCastOps.as_u16]

@[step]
theorem I32.Insts.Libcrux_secretsIntCastOps.as_i16_spec (x : Std.I32) :
    I32.Insts.Libcrux_secretsIntCastOps.as_i16 x ⦃ r => r = IScalar.cast .I16 x ⦄ := by
  simp [I32.Insts.Libcrux_secretsIntCastOps.as_i16]

@[step]
theorem U16.Insts.Libcrux_secretsIntCastOps.as_i16_spec (x : Std.U16) :
    U16.Insts.Libcrux_secretsIntCastOps.as_i16 x ⦃ r => r = UScalar.hcast .I16 x ⦄ := by
  simp [U16.Insts.Libcrux_secretsIntCastOps.as_i16]

@[step]
theorem U32.Insts.Libcrux_secretsIntCastOps.as_i16_spec (x : Std.U32) :
    U32.Insts.Libcrux_secretsIntCastOps.as_i16 x ⦃ r => r = UScalar.hcast .I16 x ⦄ := by
  simp [U32.Insts.Libcrux_secretsIntCastOps.as_i16]

@[step]
theorem U8.Insts.Libcrux_secretsIntCastOps.as_i16_spec (x : Std.U8) :
    U8.Insts.Libcrux_secretsIntCastOps.as_i16 x ⦃ r => r = UScalar.hcast .I16 x ⦄ := by
  simp [U8.Insts.Libcrux_secretsIntCastOps.as_i16]

@[step]
theorem I16.Insts.Libcrux_secretsIntCastOps.as_i16_spec (x : Std.I16) :
    I16.Insts.Libcrux_secretsIntCastOps.as_i16 x ⦃ r => r = x ⦄ := by
  simp [I16.Insts.Libcrux_secretsIntCastOps.as_i16]

@[step]
theorem U64.Insts.Libcrux_secretsIntCastOps.as_u32_spec (x : Std.U64) :
    U64.Insts.Libcrux_secretsIntCastOps.as_u32 x ⦃ r => r = UScalar.cast .U32 x ⦄ := by
  simp [U64.Insts.Libcrux_secretsIntCastOps.as_u32]

@[step]
theorem I16.Insts.Libcrux_secretsIntCastOps.as_i32_spec (x : Std.I16) :
    I16.Insts.Libcrux_secretsIntCastOps.as_i32 x ⦃ r => r = IScalar.cast .I32 x ⦄ := by
  simp [I16.Insts.Libcrux_secretsIntCastOps.as_i32]

@[step]
theorem U32.Insts.Libcrux_secretsIntCastOps.as_i32_spec (x : Std.U32) :
    U32.Insts.Libcrux_secretsIntCastOps.as_i32 x ⦃ r => r = UScalar.hcast .I32 x ⦄ := by
  simp [U32.Insts.Libcrux_secretsIntCastOps.as_i32]

@[step]
theorem U16.Insts.Libcrux_secretsIntCastOps.as_u64_spec (x : Std.U16) :
    U16.Insts.Libcrux_secretsIntCastOps.as_u64 x ⦃ r => r = UScalar.cast .U64 x ⦄ := by
  simp [U16.Insts.Libcrux_secretsIntCastOps.as_u64]

