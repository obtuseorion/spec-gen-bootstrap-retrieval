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
