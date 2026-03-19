import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Proofs.Interp
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- u64.divmod verifies that advice-provided quotient and remainder
    satisfy the division identity a = b * q + r with r < b.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Advice stack: [q_hi, q_lo, r_hi, r_lo] ++ adv_rest
    (advPush reverses pairs, so stack gets [q_lo, q_hi] and
    [r_lo, r_hi] in standard u64 LE layout)
    Output stack: [r_lo, r_hi, q_lo, q_hi] ++ rest -/
theorem u64_divmod_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt)
    (q_lo q_hi r_lo r_hi : Felt) (adv_rest : List Felt)
    (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (hadv : s.advice = q_hi :: q_lo :: r_hi :: r_lo :: adv_rest)
    (hq_hi_u32 : q_hi.isU32 = true)
    (hq_lo_u32 : q_lo.isU32 = true)
    (hr_hi_u32 : r_hi.isU32 = true)
    (hr_lo_u32 : r_lo.isU32 = true)
    (hb_lo_u32 : b_lo.isU32 = true)
    (hb_hi_u32 : b_hi.isU32 = true)
    -- Cross-product hypotheses matching actual MASM computation:
    -- p1 = b_lo * q_lo (step 6)
    (p1_hi_val : (Felt.ofNat ((b_lo.val * q_lo.val) / 2^32)).val =
        (b_lo.val * q_lo.val) / 2^32)
    -- p2 = b_hi * q_lo + p1_hi (step 10), assert p2_hi == 0
    (h_p2_hi_zero : (Felt.ofNat ((b_hi.val * q_lo.val +
        (b_lo.val * q_lo.val) / 2^32) / 2^32) == (0 : Felt)) = true)
    (p2_lo_val : (Felt.ofNat ((b_hi.val * q_lo.val +
        (b_lo.val * q_lo.val) / 2^32) % 2^32)).val =
        (b_hi.val * q_lo.val + (b_lo.val * q_lo.val) / 2^32) % 2^32)
    -- p3 = b_lo * q_hi + p2_lo (step 16), assert p3_hi == 0
    (h_p3_hi_zero : (Felt.ofNat ((b_lo.val * q_hi.val +
        (b_hi.val * q_lo.val + (b_lo.val * q_lo.val) / 2^32) % 2^32) / 2^32) ==
        (0 : Felt)) = true)
    -- q_hi * b_hi == 0 check (step 22)
    (h_qhi_bhi_zero : ((b_hi * q_hi : Felt) == (0 : Felt)) = true)
    (p1_lo_val : (Felt.ofNat ((b_lo.val * q_lo.val) % 2^32)).val =
        (b_lo.val * q_lo.val) % 2^32)
    (p3_lo_val : (Felt.ofNat ((b_lo.val * q_hi.val +
        (b_hi.val * q_lo.val + (b_lo.val * q_lo.val) / 2^32) % 2^32) % 2^32)).val =
        (b_lo.val * q_hi.val +
        (b_hi.val * q_lo.val + (b_lo.val * q_lo.val) / 2^32) % 2^32) % 2^32)
    -- r < b check (exec "lt")
    (h_lt_result :
        let borrow_lo := decide (r_lo.val < b_lo.val)
        let borrow_hi := decide (r_hi.val < b_hi.val)
        let hi_eq := Felt.ofNat (u32OverflowingSub r_hi.val b_hi.val).2 == (0 : Felt)
        (borrow_hi || (hi_eq && borrow_lo)) = true)
    -- a == b*q + r verification
    (h_carry_hi_zero : (Felt.ofNat ((r_hi.val +
        (b_lo.val * q_hi.val +
          (b_hi.val * q_lo.val + (b_lo.val * q_lo.val) / 2^32) % 2^32) % 2^32 +
        (r_lo.val + (b_lo.val * q_lo.val) % 2^32) / 2^32) / 2^32) ==
        (0 : Felt)) = true)
    (h_a_hi_eq : a_hi = Felt.ofNat ((r_hi.val +
        (b_lo.val * q_hi.val +
          (b_hi.val * q_lo.val + (b_lo.val * q_lo.val) / 2^32) % 2^32) % 2^32 +
        (r_lo.val + (b_lo.val * q_lo.val) % 2^32) / 2^32) % 2^32))
    (h_a_lo_eq : a_lo = Felt.ofNat ((r_lo.val +
        (b_lo.val * q_lo.val) % 2^32) % 2^32)) :
    execWithEnv u64ProcEnv 50 s Miden.Core.U64.divmod =
    some { stack := r_lo :: r_hi :: q_lo :: q_hi :: rest,
           memory := s.memory,
           locals := s.locals,
           advice := adv_rest,
           events := 14153021663962350784 :: s.events } := by
  obtain ⟨stk, mem, locs, adv, evts⟩ := s
  simp only [] at hs ⊢
  simp only [] at hadv
  subst hs; subst hadv
  unfold Miden.Core.U64.divmod execWithEnv
  simp only [List.foldlM, u64ProcEnv]
  simp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  -- 1: emitImm (no-op)
  rw [stepEmitImm]; miden_bind
  -- 2: advPush 2 (pops q_hi, q_lo from advice → stack [q_lo, q_hi, ...])
  rw [stepAdvPush2]; miden_bind
  -- 3: u32Assert2 (assert q_lo, q_hi are u32)
  rw [stepU32Assert2 (ha := hq_lo_u32) (hb := hq_hi_u32)]; miden_bind
  -- 4: dup 2 (duplicate b_lo)
  miden_dup
  -- 5: dup 1 (duplicate q_lo)
  miden_dup
  -- 6: u32WidenMul (b_lo * q_lo)
  rw [stepU32WidenMul (ha := hb_lo_u32) (hb := hq_lo_u32)]; miden_bind
  -- 7: swap 1
  miden_swap
  -- 8: dup 5 (duplicate b_hi)
  miden_dup
  -- 9: dup 3 (duplicate q_lo)
  miden_dup
  -- 10: u32WidenMadd (b_hi * q_lo + p1_hi)
  have h_p1_hi_u32 : (Felt.ofNat ((b_lo.val * q_lo.val) / 2^32)).isU32 = true := by
    simp only [Felt.isU32, decide_eq_true_eq]; rw [p1_hi_val]
    simp only [Felt.isU32, decide_eq_true_eq] at hb_lo_u32 hq_lo_u32
    calc (b_lo.val * q_lo.val) / 2^32
        ≤ (2^32 - 1) * (2^32 - 1) / 2^32 :=
          Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))
      _ < 2^32 := by native_decide
  rw [stepU32WidenMadd (ha := hb_hi_u32) (hb := hq_lo_u32) (hc := h_p1_hi_u32)]; miden_bind
  rw [p1_hi_val]
  -- 11: swap 1
  miden_swap
  -- 12: eqImm 0
  rw [stepEqImm]; miden_bind
  -- 13: assertWithError (assert p2_hi == 0)
  rw [stepAssertWithError (ha := by
    simp only [beq_iff_eq] at h_p2_hi_zero
    rw [h_p2_hi_zero]; simp)]; miden_bind
  -- 14: dup 4 (duplicate b_lo)
  miden_dup
  -- 15: dup 4 (duplicate q_hi)
  miden_dup
  -- 16: u32WidenMadd (b_lo * q_hi + p2_lo)
  have h_p2_lo_u32 : (Felt.ofNat ((b_hi.val * q_lo.val +
      (b_lo.val * q_lo.val) / 2^32) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  rw [stepU32WidenMadd (ha := hb_lo_u32) (hb := hq_hi_u32) (hc := h_p2_lo_u32)]; miden_bind
  rw [p2_lo_val]
  -- 17: swap 1
  miden_swap
  -- 18: eqImm 0
  rw [stepEqImm]; miden_bind
  -- 19: assertWithError (assert p3_hi == 0)
  rw [stepAssertWithError (ha := by
    simp only [beq_iff_eq] at h_p3_hi_zero
    rw [h_p3_hi_zero]; simp)]; miden_bind
  -- 20: dup 5 (duplicate b_hi)
  miden_dup
  -- 21: dup 4 (duplicate q_hi)
  miden_dup
  -- 22: mul (q_hi * b_hi)
  rw [stepMul]; miden_bind
  -- 23: eqImm 0
  rw [stepEqImm]; miden_bind
  -- 24: assertWithError (assert q_hi * b_hi == 0)
  rw [stepAssertWithError (ha := by
    simp only [beq_iff_eq] at h_qhi_bhi_zero
    rw [h_qhi_bhi_zero]; simp)]; miden_bind
  -- 25: advPush 2 (pops r_hi, r_lo from advice → stack [r_lo, r_hi, ...])
  rw [stepAdvPush2]; miden_bind
  -- 26: u32Assert2 (assert r_lo, r_hi are u32)
  rw [stepU32Assert2 (ha := hr_lo_u32) (hb := hr_hi_u32)]; miden_bind
  -- 27: movup 6 (bring b_lo up)
  miden_movup
  -- 28: movup 7 (bring b_hi up)
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
  unfold Miden.Core.U64.lt execWithEnv
  simp only [List.foldlM, bind, Bind.bind, Option.bind, pure, Pure.pure]
  -- lt body: u64 comparison (movup 3, movup 3, movup 2, u32OverflowSub, ...)
  -- After movups, stack is [b_lo, r_lo, r_hi, b_hi, ...]
  miden_movup; miden_movup; miden_movup
  -- First sub: r_lo - b_lo (lo limbs)
  rw [stepU32OverflowSub (ha := hr_lo_u32) (hb := hb_lo_u32)]; miden_bind
  miden_movdn; rw [stepDrop]; miden_bind
  -- After movdn+drop+swap: stack has [b_hi, r_hi, ...]
  miden_swap
  -- Second sub: r_hi - b_hi (hi limbs)
  rw [stepU32OverflowSub (ha := hr_hi_u32) (hb := hb_hi_u32)]; miden_bind
  miden_swap
  rw [stepEqImm]; miden_bind
  miden_movup
  rw [u32OverflowingSub_borrow_ite r_lo.val b_lo.val]
  rw [stepAndIte]; miden_bind
  rw [u32OverflowingSub_borrow_ite r_hi.val b_hi.val]
  rw [stepOrIte]; miden_bind
  -- 35: assertWithError (assert r < b)
  rw [stepAssertWithError (ha := by
    simp only [Felt.ite_val_eq_one]; exact h_lt_result)]; miden_bind
  -- 36: dup 0 (duplicate r_lo)
  miden_dup
  -- 37: movup 4
  miden_movup
  -- 38: u32WidenAdd (p1_lo + r_lo)
  have h_p1_lo_u32 : (Felt.ofNat ((b_lo.val * q_lo.val) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  rw [stepU32WidenAdd (ha := hr_lo_u32) (hb := h_p1_lo_u32)]; miden_bind
  rw [p1_lo_val]
  -- 39: swap 1
  miden_swap
  -- 40: dup 3
  miden_dup
  -- 41: movup 5
  miden_movup
  -- 42: movup 2
  miden_movup
  -- 43: u32WidenAdd3
  have h_p3_lo_u32 : (Felt.ofNat ((b_lo.val * q_hi.val +
      (b_hi.val * q_lo.val + (b_lo.val * q_lo.val) / 2^32) % 2^32) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  have h_add1_carry_u32 : (Felt.ofNat ((r_lo.val + (b_lo.val * q_lo.val) % 2^32) / 2^32)).isU32 = true := by
    apply felt_ofNat_isU32_of_lt
    calc (r_lo.val + (b_lo.val * q_lo.val) % 2^32) / 2^32
        ≤ ((2^32 - 1) + (2^32 - 1)) / 2^32 :=
          Nat.div_le_div_right (Nat.add_le_add
            (by simp only [Felt.isU32, decide_eq_true_eq] at hr_lo_u32; omega)
            (by omega))
      _ < 2^32 := by native_decide
  rw [stepU32WidenAdd3 (ha := hr_hi_u32) (hb := h_p3_lo_u32) (hc := h_add1_carry_u32)]; miden_bind
  rw [p3_lo_val]
  -- Reduce carry_lo Felt.val to raw Nat
  have h_add1_carry_val : (Felt.ofNat ((r_lo.val + (b_lo.val * q_lo.val) % 2^32) / 2^32)).val =
      (r_lo.val + (b_lo.val * q_lo.val) % 2^32) / 2^32 := by
    apply felt_ofNat_val_lt
    calc (r_lo.val + (b_lo.val * q_lo.val) % 2^32) / 2^32
        ≤ ((2^32 - 1) + (2^32 - 1)) / 2^32 :=
          Nat.div_le_div_right (Nat.add_le_add
            (by simp only [Felt.isU32, decide_eq_true_eq] at hr_lo_u32; omega)
            (by omega))
      _ < GOLDILOCKS_PRIME := by native_decide
  rw [h_add1_carry_val]
  -- 44: swap 1
  miden_swap
  -- 45: eqImm 0
  rw [stepEqImm]; miden_bind
  -- 46: assertWithError (assert carry_hi == 0)
  rw [stepAssertWithError (ha := by
    simp only [beq_iff_eq] at h_carry_hi_zero
    rw [h_carry_hi_zero]; simp)]; miden_bind
  -- 47: movup 7 (bring a_hi)
  miden_movup
  -- 48: assertEqWithError (a_hi == sum_hi)
  rw [stepAssertEqWithError (hab := by rw [h_a_hi_eq]; simp)]; miden_bind
  -- 49: movup 5 (bring a_lo)
  miden_movup
  -- 50: assertEqWithError (a_lo == sum_lo)
  rw [stepAssertEqWithError (hab := by rw [h_a_lo_eq]; simp)]

/-- Extract Nat value 0 from Felt.ofNat n == 0. -/
private theorem felt_beq_zero_val {n : Nat}
    (hlt : n < GOLDILOCKS_PRIME)
    (h : (Felt.ofNat n == (0 : Felt)) = true) :
    n = 0 := by
  rw [beq_iff_eq] at h
  have hval : (Felt.ofNat n).val = 0 := by
    rw [h]; simp
  simp only [Felt.ofNat] at hval
  rwa [ZMod.val_natCast_of_lt hlt] at hval

/-- Extract Nat product = 0 from Felt product == 0. -/
private theorem felt_mul_beq_zero_val
    (a b : Felt)
    (hlt : a.val * b.val < GOLDILOCKS_PRIME)
    (h : ((a * b : Felt) == (0 : Felt)) = true) :
    a.val * b.val = 0 := by
  rw [beq_iff_eq] at h
  have hval := congrArg ZMod.val h
  simp only [ZMod.val_zero] at hval
  rwa [ZMod.val_mul_of_lt hlt] at hval

/-- Sub-lemma: h_lt_result implies toU64 r < toU64 b. -/
theorem divmod_lt_bridge
    (r_lo r_hi b_lo b_hi : Felt)
    (hr_lo : r_lo.isU32 = true)
    (hr_hi : r_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true)
    (hb_hi : b_hi.isU32 = true)
    (h : (decide (r_hi.val < b_hi.val) ||
      ((Felt.ofNat (u32OverflowingSub r_hi.val
        b_hi.val).2 == (0 : Felt)) &&
        decide (r_lo.val < b_lo.val))) = true) :
    toU64 r_lo r_hi < toU64 b_lo b_hi := by
  rw [u64_lt_condition_eq r_lo r_hi b_lo b_hi
    hr_lo hr_hi hb_lo hb_hi] at h
  exact decide_eq_true_eq.mp h

/-- Sub-lemma: carry chain hypotheses imply the u64
    division identity a = b*q + r. -/
theorem divmod_eq_bridge
    (a_lo a_hi b_lo b_hi q_lo q_hi r_lo r_hi : Felt)
    (hq_lo : q_lo.isU32 = true)
    (hq_hi : q_hi.isU32 = true)
    (hr_lo : r_lo.isU32 = true)
    (hr_hi : r_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true)
    (hb_hi : b_hi.isU32 = true)
    (hp2 : (Felt.ofNat ((b_hi.val * q_lo.val +
      (b_lo.val * q_lo.val) / 2^32) / 2^32) ==
      (0 : Felt)) = true)
    (hp3 : (Felt.ofNat ((b_lo.val * q_hi.val +
      (b_hi.val * q_lo.val +
        (b_lo.val * q_lo.val) / 2^32) % 2^32) /
      2^32) == (0 : Felt)) = true)
    (hqb : ((b_hi * q_hi : Felt) ==
      (0 : Felt)) = true)
    (hcarry : (Felt.ofNat ((r_hi.val +
      (b_lo.val * q_hi.val + (b_hi.val * q_lo.val +
        (b_lo.val * q_lo.val) / 2^32) % 2^32) %
        2^32 +
      (r_lo.val + (b_lo.val * q_lo.val) % 2^32) /
        2^32) / 2^32) == (0 : Felt)) = true)
    (hahi : a_hi = Felt.ofNat ((r_hi.val +
      (b_lo.val * q_hi.val + (b_hi.val * q_lo.val +
        (b_lo.val * q_lo.val) / 2^32) % 2^32) %
        2^32 +
      (r_lo.val + (b_lo.val * q_lo.val) % 2^32) /
        2^32) % 2^32))
    (halo : a_lo = Felt.ofNat ((r_lo.val +
      (b_lo.val * q_lo.val) % 2^32) % 2^32)) :
    toU64 a_lo a_hi =
    toU64 b_lo b_hi * toU64 q_lo q_hi +
    toU64 r_lo r_hi := by
  simp only [toU64]
  simp only [Felt.isU32, decide_eq_true_eq] at *
  -- Explicit nonlinear bounds for omega
  have hbq : b_lo.val * q_lo.val ≤
      (2^32-1)*(2^32-1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hbhq : b_hi.val * q_lo.val ≤
      (2^32-1)*(2^32-1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hblqh : b_lo.val * q_hi.val ≤
      (2^32-1)*(2^32-1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hbhqh : b_hi.val * q_hi.val ≤
      (2^32-1)*(2^32-1) :=
    Nat.mul_le_mul (by omega) (by omega)
  -- Extract Nat equalities from Felt assertions
  have hp2_nat := felt_beq_zero_val
    (by unfold GOLDILOCKS_PRIME; omega) hp2
  have hp3_nat := felt_beq_zero_val
    (by unfold GOLDILOCKS_PRIME; omega) hp3
  have hqb_nat := felt_mul_beq_zero_val b_hi q_hi
    (by unfold GOLDILOCKS_PRIME; omega) hqb
  have hcarry_nat := felt_beq_zero_val
    (by unfold GOLDILOCKS_PRIME; omega) hcarry
  -- Extract a_lo.val and a_hi.val
  have halo_val : a_lo.val =
      (r_lo.val + (b_lo.val * q_lo.val) % 2^32) %
      2^32 := by
    rw [halo, felt_ofNat_val_lt _ (by
      unfold GOLDILOCKS_PRIME; omega)]
  have hahi_val : a_hi.val =
      (r_hi.val + (b_lo.val * q_hi.val +
        (b_hi.val * q_lo.val +
          (b_lo.val * q_lo.val) / 2^32) % 2^32) %
        2^32 +
      (r_lo.val + (b_lo.val * q_lo.val) % 2^32) /
        2^32) % 2^32 := by
    rw [hahi, felt_ofNat_val_lt _ (by
      unfold GOLDILOCKS_PRIME; omega)]
  exact divmod_carry_chain a_lo.val a_hi.val
    b_lo.val b_hi.val q_lo.val q_hi.val
    r_lo.val r_hi.val
    hp2_nat hp3_nat hqb_nat hcarry_nat
    hahi_val halo_val

/-- divmod: the operational hypotheses collectively
    establish the standard division relationship. -/
theorem u64_divmod_semantic
    (a_lo a_hi b_lo b_hi q_lo q_hi r_lo r_hi : Felt)
    (hq_lo : q_lo.isU32 = true)
    (hq_hi : q_hi.isU32 = true)
    (hr_lo : r_lo.isU32 = true)
    (hr_hi : r_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true)
    (hb_hi : b_hi.isU32 = true)
    (hp2 : (Felt.ofNat ((b_hi.val * q_lo.val +
      (b_lo.val * q_lo.val) / 2^32) / 2^32) ==
      (0 : Felt)) = true)
    (hp3 : (Felt.ofNat ((b_lo.val * q_hi.val +
      (b_hi.val * q_lo.val +
        (b_lo.val * q_lo.val) / 2^32) % 2^32) /
      2^32) == (0 : Felt)) = true)
    (hqb : ((b_hi * q_hi : Felt) ==
      (0 : Felt)) = true)
    (hcarry : (Felt.ofNat ((r_hi.val +
      (b_lo.val * q_hi.val + (b_hi.val * q_lo.val +
        (b_lo.val * q_lo.val) / 2^32) % 2^32) %
        2^32 +
      (r_lo.val + (b_lo.val * q_lo.val) % 2^32) /
        2^32) / 2^32) == (0 : Felt)) = true)
    (hahi : a_hi = Felt.ofNat ((r_hi.val +
      (b_lo.val * q_hi.val + (b_hi.val * q_lo.val +
        (b_lo.val * q_lo.val) / 2^32) % 2^32) %
        2^32 +
      (r_lo.val + (b_lo.val * q_lo.val) % 2^32) /
        2^32) % 2^32))
    (halo : a_lo = Felt.ofNat ((r_lo.val +
      (b_lo.val * q_lo.val) % 2^32) % 2^32))
    (hlt : (decide (r_hi.val < b_hi.val) ||
      ((Felt.ofNat (u32OverflowingSub r_hi.val
        b_hi.val).2 == (0 : Felt)) &&
        decide (r_lo.val < b_lo.val))) = true) :
    toU64 r_lo r_hi < toU64 b_lo b_hi ∧
    toU64 a_lo a_hi =
      toU64 b_lo b_hi * toU64 q_lo q_hi +
      toU64 r_lo r_hi :=
  ⟨divmod_lt_bridge r_lo r_hi b_lo b_hi
    hr_lo hr_hi hb_lo hb_hi hlt,
   divmod_eq_bridge a_lo a_hi b_lo b_hi q_lo q_hi
    r_lo r_hi hq_lo hq_hi hr_lo hr_hi hb_lo hb_hi
    hp2 hp3 hqb hcarry hahi halo⟩

end MidenLean.Proofs
