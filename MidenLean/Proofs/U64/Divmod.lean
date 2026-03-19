import MidenLean.Proofs.U64
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 32000000 in
/-- u64.divmod verifies that advice-provided quotient and remainder
    satisfy the division identity a = b * q + r with r < b.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Advice stack: [q_lo, q_hi, r_lo, r_hi] ++ adv_rest
    Output stack: [r_hi, r_lo, q_hi, q_lo] ++ rest -/
theorem u64_divmod_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt)
    (q_lo q_hi r_lo r_hi : Felt) (adv_rest : List Felt)
    (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (hadv : s.advice = q_lo :: q_hi :: r_lo :: r_hi :: adv_rest)
    (hq_hi_u32 : q_hi.isU32 = true)
    (hq_lo_u32 : q_lo.isU32 = true)
    (hr_hi_u32 : r_hi.isU32 = true)
    (hr_lo_u32 : r_lo.isU32 = true)
    (hb_lo_u32 : b_lo.isU32 = true)
    (hb_hi_u32 : b_hi.isU32 = true)
    -- Cross-product verification hypotheses (instructions 4-13)
    (cross0_hi_val : (Felt.ofNat ((b_lo.val * q_hi.val) / 2^32)).val =
        (b_lo.val * q_hi.val) / 2^32)
    (h_madd1_hi_zero : (Felt.ofNat ((b_hi.val * q_hi.val +
        (b_lo.val * q_hi.val) / 2^32) / 2^32) == (0 : Felt)) = true)
    (madd1_lo_val : (Felt.ofNat ((b_hi.val * q_hi.val +
        (b_lo.val * q_hi.val) / 2^32) % 2^32)).val =
        (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32)
    -- Second cross-product (instructions 14-19)
    (h_madd2_hi_zero : (Felt.ofNat ((b_lo.val * q_lo.val +
        (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) / 2^32) ==
        (0 : Felt)) = true)
    -- b_hi * q_lo == 0 check (instructions 20-24)
    (h_bhi_qlo_zero : ((b_hi * q_lo : Felt) == (0 : Felt)) = true)
    (cross0_lo_val : (Felt.ofNat ((b_lo.val * q_hi.val) % 2^32)).val =
        (b_lo.val * q_hi.val) % 2^32)
    (madd2_lo_val : (Felt.ofNat ((b_lo.val * q_lo.val +
        (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32)).val =
        (b_lo.val * q_lo.val +
        (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32)
    -- r < b check (instructions 25-35)
    (h_lt_result :
        let borrow_lo := decide (r_hi.val < b_lo.val)
        let borrow_hi := decide (r_lo.val < b_hi.val)
        let hi_eq := Felt.ofNat (u32OverflowingSub r_lo.val b_hi.val).2 == (0 : Felt)
        (borrow_hi || (hi_eq && borrow_lo)) = true)
    -- a == b*q + r verification (instructions 36-50)
    (h_add2_hi_zero : (Felt.ofNat ((r_lo.val +
        (b_lo.val * q_lo.val +
          (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32 +
        (r_hi.val + (b_lo.val * q_hi.val) % 2^32) / 2^32) / 2^32) ==
        (0 : Felt)) = true)
    (h_a_hi_eq : a_hi = Felt.ofNat ((r_lo.val +
        (b_lo.val * q_lo.val +
          (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32 +
        (r_hi.val + (b_lo.val * q_hi.val) % 2^32) / 2^32) % 2^32))
    (h_a_lo_eq : a_lo = Felt.ofNat ((r_hi.val +
        (b_lo.val * q_hi.val) % 2^32) % 2^32)) :
    execWithEnv u64ProcEnv 50 s Miden.Core.U64.divmod =
    some { stack := r_hi :: r_lo :: q_hi :: q_lo :: rest,
           memory := s.memory,
           locals := s.locals,
           advice := adv_rest } := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  simp only [] at hadv
  subst hs; subst hadv
  unfold Miden.Core.U64.divmod execWithEnv
  simp only [List.foldlM, u64ProcEnv]
  simp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  -- 1: emitImm (no-op)
  rw [stepEmitImm]; miden_bind
  -- 2: advPush 2 (read q_lo, q_hi from advice)
  rw [stepAdvPush2]; miden_bind
  -- 3: u32Assert2 (assert q_hi, q_lo are u32)
  rw [stepU32Assert2 (ha := hq_lo_u32) (hb := hq_hi_u32)]; miden_bind
  -- 4: dup 2 (duplicate b_lo)
  miden_dup
  -- 5: dup 1 (duplicate q_hi)
  miden_dup
  -- 6: u32WidenMul (b_lo * q_hi)
  rw [stepU32WidenMul (ha := hq_hi_u32) (hb := hb_lo_u32)]; miden_bind
  -- 7: swap 1
  miden_swap
  -- 8: dup 5 (duplicate b_hi)
  miden_dup
  -- 9: dup 3 (duplicate q_hi)
  miden_dup
  -- 10: u32WidenMadd (b_hi * q_hi + cross0_hi)
  have h_cross0_hi_u32 : (Felt.ofNat ((b_lo.val * q_hi.val) / 2^32)).isU32 = true := by
    simp only [Felt.isU32, decide_eq_true_eq]; rw [cross0_hi_val]
    simp only [Felt.isU32, decide_eq_true_eq] at hb_lo_u32 hq_hi_u32
    calc (b_lo.val * q_hi.val) / 2^32
        ≤ (2^32 - 1) * (2^32 - 1) / 2^32 :=
          Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))
      _ < 2^32 := by native_decide
  rw [stepU32WidenMadd (ha := hq_hi_u32) (hb := hb_hi_u32) (hc := h_cross0_hi_u32)]; miden_bind
  rw [cross0_hi_val]
  -- 11: swap 1
  miden_swap
  -- 12: eqImm 0
  rw [stepEqImm]; miden_bind
  -- 13: assertWithError (assert madd1_hi == 0)
  rw [stepAssertWithError (ha := by
    simp only [beq_iff_eq] at h_madd1_hi_zero
    rw [h_madd1_hi_zero]; simp [Felt.val_zero'])]; miden_bind
  -- 14: dup 4 (duplicate b_lo)
  miden_dup
  -- 15: dup 4 (duplicate q_lo)
  miden_dup
  -- 16: u32WidenMadd (b_lo * q_lo + madd1_lo)
  have h_madd1_lo_u32 : (Felt.ofNat ((b_hi.val * q_hi.val +
      (b_lo.val * q_hi.val) / 2^32) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  rw [stepU32WidenMadd (ha := hq_lo_u32) (hb := hb_lo_u32) (hc := h_madd1_lo_u32)]; miden_bind
  rw [madd1_lo_val]
  -- 17: swap 1
  miden_swap
  -- 18: eqImm 0
  rw [stepEqImm]; miden_bind
  -- 19: assertWithError (assert madd2_hi == 0)
  rw [stepAssertWithError (ha := by
    simp only [beq_iff_eq] at h_madd2_hi_zero
    rw [h_madd2_hi_zero]; simp [Felt.val_zero'])]; miden_bind
  -- 20: dup 5 (duplicate b_hi)
  miden_dup
  -- 21: dup 4 (duplicate q_lo)
  miden_dup
  -- 22: mul (b_hi * q_lo)
  rw [stepMul]; miden_bind
  -- 23: eqImm 0
  rw [stepEqImm]; miden_bind
  -- 24: assertWithError (assert b_hi * q_lo == 0)
  rw [stepAssertWithError (ha := by
    simp only [beq_iff_eq] at h_bhi_qlo_zero
    rw [h_bhi_qlo_zero]; simp [Felt.val_zero'])]; miden_bind
  -- 25: advPush 2 (read r_lo, r_hi from advice)
  rw [stepAdvPush2]; miden_bind
  -- 26: u32Assert2 (assert r_hi, r_lo are u32)
  rw [stepU32Assert2 (ha := hr_lo_u32) (hb := hr_hi_u32)]; miden_bind
  -- 27: movup 6 (bring a_hi up)
  miden_movup
  -- 28: movup 7 (bring a_lo up)
  miden_movup
  -- 29: swap 1
  miden_swap
  -- 30: dup 3 (duplicate r_hi)
  miden_dup
  -- 31: dup 3 (duplicate r_lo)
  miden_dup
  -- 32: movup 3 (bring b_hi up)
  miden_movup
  -- 33: movup 3 (bring b_lo up)
  miden_movup
  -- 34: exec "lt" (compare r < b)
  simp only [u64ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  unfold Miden.Core.U64.lt execWithEnv
  simp only [List.foldlM, bind, Bind.bind, Option.bind, pure, Pure.pure]
  -- lt body: 20 instructions for u64 comparison
  miden_movup; miden_movup; miden_movup; miden_swap
  rw [stepU32OverflowSub (ha := hr_lo_u32) (hb := hb_hi_u32)]; miden_bind
  miden_movdn; rw [stepDrop]; miden_bind
  rw [stepU32OverflowSub (ha := hr_hi_u32) (hb := hb_lo_u32)]; miden_bind
  miden_swap
  rw [stepEqImm]; miden_bind
  miden_movup
  rw [u32OverflowingSub_borrow_ite r_hi.val b_lo.val]
  rw [stepAndIte]; miden_bind
  rw [u32OverflowingSub_borrow_ite r_lo.val b_hi.val]
  rw [stepOrIte]; miden_bind
  -- 35: assertWithError (assert r < b)
  rw [stepAssertWithError (ha := by
    simp only [Felt.ite_val_eq_one]; exact h_lt_result)]; miden_bind
  -- 36: dup 0 (duplicate r_lo)
  miden_dup
  -- 37: movup 4
  miden_movup
  -- 38: u32WidenAdd (r_lo + cross0_lo)
  have h_cross0_lo_u32 : (Felt.ofNat ((b_lo.val * q_hi.val) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  rw [stepU32WidenAdd (ha := h_cross0_lo_u32) (hb := hr_hi_u32)]; miden_bind
  rw [cross0_lo_val]
  -- 39: swap 1
  miden_swap
  -- 40: dup 3
  miden_dup
  -- 41: movup 5
  miden_movup
  -- 42: movup 2
  miden_movup
  -- 43: u32WidenAdd3
  have h_madd2_lo_u32 : (Felt.ofNat ((b_lo.val * q_lo.val +
      (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  have h_add1_carry_u32 : (Felt.ofNat ((r_hi.val + (b_lo.val * q_hi.val) % 2^32) / 2^32)).isU32 = true := by
    apply felt_ofNat_isU32_of_lt
    have hrhi := Felt.isU32 ▸ hr_hi_u32 |>.mp rfl
    calc (r_hi.val + (b_lo.val * q_hi.val) % 2^32) / 2^32
        ≤ ((2^32 - 1) + (2^32 - 1)) / 2^32 :=
          Nat.div_le_div_right (Nat.add_le_add
            (by simp only [Felt.isU32, decide_eq_true_eq] at hr_hi_u32; omega)
            (by omega))
      _ < 2^32 := by native_decide
  rw [stepU32WidenAdd3 (ha := h_add1_carry_u32) (hb := hr_lo_u32) (hc := h_madd2_lo_u32)]; miden_bind
  rw [madd2_lo_val]
  -- 44: swap 1
  miden_swap
  -- 45: eqImm 0
  rw [stepEqImm]; miden_bind
  -- 46: assertWithError (assert add2_hi == 0)
  rw [stepAssertWithError (ha := by
    simp only [beq_iff_eq] at h_add2_hi_zero
    rw [h_add2_hi_zero]; simp [Felt.val_zero'])]; miden_bind
  -- 47: movup 7 (bring a_hi)
  miden_movup
  -- 48: assertEqWithError (a_hi == sum_hi)
  rw [stepAssertEqWithError (hab := by rw [h_a_hi_eq])]; miden_bind
  -- 49: movup 5 (bring a_lo)
  miden_movup
  -- 50: assertEqWithError (a_lo == sum_lo)
  rw [stepAssertEqWithError (hab := by rw [h_a_lo_eq])]
  dsimp only [pure, Pure.pure]

end MidenLean.Proofs
