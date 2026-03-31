import MidenLean.AIR.Proofs.StackArith
import MidenLean.Proofs.Helpers
/-!
# U32 Semantic Soundness

Deep soundness theorems connecting AIR constraints + range checks to
natural number arithmetic. The key lemmas `v_lo_val_lt` and `v_hi_val_lt`
prove that the limb decomposition values are genuine u32 naturals.
-/

namespace MidenLean.AIR.Proofs.U32Semantic

open MidenLean MidenLean.AIR MidenLean.AIR.Constraints

private theorem pow16_felt_val : ((65536 : Nat) : Felt).val = 65536 :=
  ZMod.val_natCast_of_lt (by unfold GOLDILOCKS_PRIME; omega)

private theorem add_mul_pow16_val (a b : Felt) (ha : a.val < 2^16) (hb : b.val < 2^16) :
    (a * (65536 : Felt) + b).val = a.val * 65536 + b.val := by
  rw [show (65536 : Felt) = ((65536 : Nat) : Felt) from rfl]
  rw [ZMod.val_add_of_lt]
  · congr 1; rw [ZMod.val_mul, pow16_felt_val]
    exact Nat.mod_eq_of_lt (by unfold GOLDILOCKS_PRIME; omega)
  · rw [ZMod.val_mul, pow16_felt_val, Nat.mod_eq_of_lt (by unfold GOLDILOCKS_PRIME; omega)]
    unfold GOLDILOCKS_PRIME; omega

theorem v_lo_val_lt (f : Frame) (hrc : f.RangeChecked) :
    f.v_lo.val < 2^32 := by
  show (f.h 1 * two_pow_16 + f.h 0).val < 2^32
  show (f.h 1 * (65536 : Felt) + f.h 0).val < 2^32
  have h0_lt := hrc.h0_lt; have h1_lt := hrc.h1_lt
  rw [add_mul_pow16_val _ _ h1_lt h0_lt]; omega

theorem v_hi_val_lt (f : Frame) (hrc : f.RangeChecked) :
    f.v_hi.val < 2^32 := by
  show (f.h 3 * two_pow_16 + f.h 2).val < 2^32
  show (f.h 3 * (65536 : Felt) + f.h 2).val < 2^32
  have h2_lt := hrc.h2_lt; have h3_lt := hrc.h3_lt
  rw [add_mul_pow16_val _ _ h3_lt h2_lt]; omega

theorem air_u32add_semantic (f : Frame)
    (hsat : f.satisfies Constraints.u32add)
    (hrc : f.RangeChecked) :
    f.s' 0 = f.v_lo ∧ f.s' 1 = f.v_hi ∧ f.s 0 + f.s 1 = f.v48
    ∧ f.v_lo.val < 2^32 ∧ f.v_hi.val < 2^32 := by
  have ⟨h1, h2, h3⟩ := air_u32add_sound f hsat
  exact ⟨h1, h2, h3, v_lo_val_lt f hrc, v_hi_val_lt f hrc⟩

theorem air_u32mul_semantic (f : Frame)
    (hsat : f.satisfies Constraints.u32mul)
    (hrc : f.RangeChecked) :
    (1 - f.h 4 * (two_pow_32_minus_one - f.v_hi)) * f.v_lo = 0
    ∧ f.s' 0 = f.v_lo ∧ f.s' 1 = f.v_hi ∧ f.s 0 * f.s 1 = f.v64
    ∧ f.v_lo.val < 2^32 ∧ f.v_hi.val < 2^32 := by
  have ⟨h1, h2, h3, h4⟩ := air_u32mul_sound f hsat
  exact ⟨h1, h2, h3, h4, v_lo_val_lt f hrc, v_hi_val_lt f hrc⟩

end MidenLean.AIR.Proofs.U32Semantic
