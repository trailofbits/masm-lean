import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Helper lemmas for u64.shr
-- ============================================================================

private theorem pow2_val_eq (shift : Felt) (hshift : shift.val ≤ 63) :
    (Felt.ofNat (2 ^ shift.val)).val = 2 ^ shift.val := by
  apply felt_ofNat_val_lt
  calc 2 ^ shift.val ≤ 2 ^ 63 := Nat.pow_le_pow_right (by omega) hshift
    _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide

private theorem pow2_div_lt_prime (shift : Felt) (hshift : shift.val ≤ 63) :
    (Felt.ofNat (2 ^ shift.val)).val / 2 ^ 32 < GOLDILOCKS_PRIME := by
  rw [pow2_val_eq shift hshift]
  calc 2 ^ shift.val / 2 ^ 32 ≤ 2 ^ 63 / 2 ^ 32 :=
    Nat.div_le_div_right (Nat.pow_le_pow_right (by omega) hshift)
    _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide

private theorem pow2_div_lt_u32 (shift : Felt) (hshift : shift.val ≤ 63) :
    2 ^ shift.val / 2 ^ 32 < 2 ^ 32 := by
  calc 2 ^ shift.val / 2 ^ 32 ≤ (2 ^ 63) / 2 ^ 32 :=
    Nat.div_le_div_right (Nat.pow_le_pow_right (by omega) hshift)
    _ < 2 ^ 32 := by native_decide

/-- pow2 value for shift <= 63: hi32.val + lo32.val < GOLDILOCKS_PRIME. -/
private theorem pow2_hi32_add_lo32_val (shift : Felt) (hshift : shift.val ≤ 63) :
    ((Felt.ofNat (2 ^ shift.val)).hi32.val + (Felt.ofNat (2 ^ shift.val)).lo32.val) <
      GOLDILOCKS_PRIME := by
  simp only [Felt.lo32, Felt.hi32]
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  rw [felt_ofNat_val_lt _ (pow2_div_lt_prime shift hshift), pow2_val_eq shift hshift]
  have hmod : 2 ^ shift.val % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hdiv : 2 ^ shift.val / 2 ^ 32 < 2 ^ 32 := pow2_div_lt_u32 shift hshift
  unfold GOLDILOCKS_PRIME; omega

/-- The field addition hi32 + lo32 of pow2 has the expected val. -/
private theorem pow2_denom_val (shift : Felt) (hshift : shift.val ≤ 63) :
    ((Felt.ofNat (2 ^ shift.val)).hi32 + (Felt.ofNat (2 ^ shift.val)).lo32).val =
    (Felt.ofNat (2 ^ shift.val)).hi32.val + (Felt.ofNat (2 ^ shift.val)).lo32.val := by
  simp only [ZMod.val_add]
  exact Nat.mod_eq_of_lt (pow2_hi32_add_lo32_val shift hshift)

/-- denom is u32 for pow2 shift with shift <= 63. -/
private theorem pow2_denom_isU32 (shift : Felt) (hshift : shift.val ≤ 63) :
    ((Felt.ofNat (2 ^ shift.val)).hi32 + (Felt.ofNat (2 ^ shift.val)).lo32).isU32 = true := by
  simp only [Felt.isU32, decide_eq_true_eq]
  rw [pow2_denom_val shift hshift]
  simp only [Felt.lo32, Felt.hi32]
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  rw [felt_ofNat_val_lt _ (pow2_div_lt_prime shift hshift), pow2_val_eq shift hshift]
  have hmod : 2 ^ shift.val % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hdiv : 2 ^ shift.val / 2 ^ 32 < 2 ^ 32 := pow2_div_lt_u32 shift hshift
  by_cases hlt : shift.val < 32
  · have hdiv_zero : 2 ^ shift.val / 2 ^ 32 = 0 := by
      apply Nat.div_eq_of_lt
      calc 2 ^ shift.val ≤ 2 ^ 31 := Nat.pow_le_pow_right (by omega) (by omega)
        _ < 2 ^ 32 := by native_decide
    omega
  · have hle : 32 ≤ shift.val := by omega
    have hmod_zero : 2 ^ shift.val % 2 ^ 32 = 0 := by
      exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 hle)
    omega

/-- denom.val != 0 for pow2 shift with shift <= 63. -/
private theorem pow2_denom_val_ne_zero (shift : Felt) (hshift : shift.val ≤ 63) :
    (((Felt.ofNat (2 ^ shift.val)).hi32 + (Felt.ofNat (2 ^ shift.val)).lo32).val == 0) = false := by
  rw [pow2_denom_val shift hshift]
  simp only [Felt.hi32, Felt.lo32]
  rw [felt_ofNat_val_lt _ (pow2_div_lt_prime shift hshift), pow2_val_eq shift hshift]
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  have hpow_pos : 2 ^ shift.val ≥ 1 := Nat.one_le_pow _ _ (by omega)
  have : 2 ^ shift.val / 2 ^ 32 + 2 ^ shift.val % 2 ^ 32 ≥ 1 := by
    by_contra h
    push_neg at h
    have h1 : 2 ^ shift.val / 2 ^ 32 = 0 := by omega
    have h2 : 2 ^ shift.val % 2 ^ 32 = 0 := by omega
    have : 2 ^ shift.val = 2 ^ 32 * (2 ^ shift.val / 2 ^ 32) + 2 ^ shift.val % 2 ^ 32 :=
      (Nat.div_add_mod _ _).symm
    omega
  exact Bool.eq_false_iff.mpr (mt beq_iff_eq.mp (by omega))

/-- pow_lo is u32. -/
private theorem pow_lo_isU32 (shift : Felt) :
    (Felt.ofNat (2 ^ shift.val)).lo32.isU32 = true := by
  simp only [Felt.lo32, Felt.isU32, decide_eq_true_eq]
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  exact Nat.mod_lt _ (by decide)

/-- (if pow_lo == 0 then 1 else 0) is u32 -/
private theorem eq0_isU32 (pow_lo : Felt) :
    (if pow_lo == (0 : Felt) then (1 : Felt) else (0 : Felt)).isU32 = true := by
  by_cases h : pow_lo == (0 : Felt)
  · simp [h, Felt.isU32, Felt.val_one']
  · simp [h, Felt.isU32]

/-- The diff from u32OverflowingSub in the shr procedure has nonzero val. -/
private theorem shr_diff_val_ne_zero (pow_lo : Felt) :
    let eq0 : Felt := if pow_lo == (0 : Felt) then 1 else 0
    (Felt.ofNat (u32OverflowingSub pow_lo.val eq0.val).2).val ≠ 0 := by
  simp only []
  by_cases h : pow_lo == (0 : Felt)
  · simp only [h, ↓reduceIte]
    simp only [beq_iff_eq] at h
    have hval : pow_lo.val = 0 := by rw [h]; rfl
    unfold u32OverflowingSub
    simp only [hval, Felt.val_one']
    simp only [show ¬(0 ≥ 1) from by omega, ↓reduceIte]
    have hlt : u32Max - 1 + 0 < GOLDILOCKS_PRIME := by simp [u32Max, GOLDILOCKS_PRIME]
    rw [felt_ofNat_val_lt _ hlt]
    simp [u32Max]
  · have heq : (if pow_lo == (0 : Felt) then (1 : Felt) else 0) = (0 : Felt) := by simp [h]
    simp only [heq, Felt.val_zero']
    unfold u32OverflowingSub
    simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero]
    rw [felt_ofNat_val_lt _ (felt_val_lt_prime pow_lo)]
    have : pow_lo.val ≠ 0 := by
      intro heq2
      simp only [beq_iff_eq] at h
      exact h ((ZMod.val_eq_zero pow_lo).mp heq2)
    omega

/-- The diff Felt from shr is nonzero (as Felt equality). -/
private theorem shr_diff_ne_zero_felt (pow_lo : Felt) :
    let eq0 : Felt := if pow_lo == (0 : Felt) then 1 else 0
    (Felt.ofNat (u32OverflowingSub pow_lo.val eq0.val).2 == (0 : Felt)) = false := by
  simp only []
  have h := shr_diff_val_ne_zero pow_lo; simp only [] at h
  exact Bool.eq_false_iff.mpr fun hbeq =>
    h ((ZMod.val_eq_zero _).mpr (beq_iff_eq.mp hbeq))

/-- The diff is u32. -/
private theorem shr_diff_isU32 (pow_lo : Felt) (hpow_lo : pow_lo.isU32 = true) :
    let eq0 : Felt := if pow_lo == (0 : Felt) then 1 else 0
    (Felt.ofNat (u32OverflowingSub pow_lo.val eq0.val).2).isU32 = true := by
  simp only []
  apply u32OverflowingSub_snd_isU32
  · simp only [Felt.isU32, decide_eq_true_eq] at hpow_lo; exact hpow_lo
  · by_cases h : pow_lo == (0 : Felt)
    · simp [h, Felt.val_one']
    · simp [h]

/-- The diff.val is nonzero (for u32DivMod hypothesis). -/
private theorem shr_diff_val_ne_zero_beq (pow_lo : Felt) :
    let eq0 : Felt := if pow_lo == (0 : Felt) then 1 else 0
    ((Felt.ofNat (u32OverflowingSub pow_lo.val eq0.val).2).val == 0) = false := by
  simp only []
  have h := shr_diff_val_ne_zero pow_lo; simp only [] at h
  exact Bool.eq_false_iff.mpr (mt beq_iff_eq.mp h)

-- ============================================================================
-- Main theorem
-- ============================================================================

private def shr_chunk1 : List Op := [
  .inst (.movup 2),
  .inst (.swap 1),
  .inst (.pow2),
  .inst (.u32Split),
  .inst (.swap 1),
  .inst (.dup 1),
  .inst (.add),
  .inst (.movup 2),
  .inst (.swap 1),
  .inst (.u32DivMod)
]

private def shr_chunk2 : List Op := [
  .inst (.swap 1),
  .inst (.movup 3),
  .inst (.movup 3),
  .inst (.dup 0),
  .inst (.eqImm 0),
  .inst (.u32OverflowSub),
  .inst (.not),
  .inst (.movdn 4),
  .inst (.dup 0),
  .inst (.movdn 4),
  .inst (.u32DivMod)
]

private def shr_chunk3 : List Op := [
  .inst (.swap 1),
  .inst (.swap 1),
  .inst (.drop),
  .inst (.push 4294967296),
  .inst (.dup 5),
  .inst (.mul),
  .inst (.movup 4),
  .inst (.div),
  .inst (.movup 3),
  .inst (.mul),
  .inst (.add),
  .inst (.dup 2),
  .inst (.cswap)
]

private def shr_chunk4 : List Op := [
  .inst (.movup 2),
  .inst (.mul),
  .inst (.swap 1)
]

private theorem shr_decomp :
    Miden.Core.U64.shr = shr_chunk1 ++ (shr_chunk2 ++ (shr_chunk3 ++ shr_chunk4)) := by
  simp [Miden.Core.U64.shr, shr_chunk1, shr_chunk2, shr_chunk3, shr_chunk4]

private theorem shr_chunk1_correct
    (lo hi shift : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (hshift : shift.val ≤ 63) (hhi : hi.isU32 = true) :
    let pow := Felt.ofNat (2 ^ shift.val)
    let pow_lo := pow.lo32
    let pow_hi := pow.hi32
    let denom := pow_hi + pow_lo
    exec 42 ⟨shift :: lo :: hi :: rest, mem, locs, adv⟩ shr_chunk1 =
      some ⟨Felt.ofNat (hi.val % denom.val) ::
        Felt.ofNat (hi.val / denom.val) :: pow_lo :: lo :: rest, mem, locs, adv⟩ := by
  unfold exec shr_chunk1 execWithEnv
  simp only [List.foldlM]
  miden_movup
  miden_swap
  rw [stepPow2 (ha := hshift)]
  miden_bind
  rw [stepU32Split]
  miden_bind
  miden_swap
  miden_dup
  rw [stepAdd]
  miden_bind
  miden_movup
  miden_swap
  have h_denom_isU32 := pow2_denom_isU32 shift hshift
  have h_denom_ne_zero := pow2_denom_val_ne_zero shift hshift
  rw [stepU32DivMod (ha := hhi) (hb := h_denom_isU32) (hbnz := h_denom_ne_zero)]
  miden_bind
  rfl

private theorem shr_chunk2_correct
    (lo hi shift : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (hlo : lo.isU32 = true) :
    let pow := Felt.ofNat (2 ^ shift.val)
    let pow_lo := pow.lo32
    let pow_hi := pow.hi32
    let denom := pow_hi + pow_lo
    let hi_rem := Felt.ofNat (hi.val % denom.val)
    let hi_quot := Felt.ofNat (hi.val / denom.val)
    let pow_lo_eq0 : Felt := if pow_lo == (0 : Felt) then 1 else 0
    let cond := !decide (pow_lo.val < pow_lo_eq0.val)
    let diff := Felt.ofNat (u32OverflowingSub pow_lo.val pow_lo_eq0.val).2
    exec 42 ⟨hi_rem :: hi_quot :: pow_lo :: lo :: rest, mem, locs, adv⟩ shr_chunk2 =
      some ⟨Felt.ofNat (lo.val % diff.val) :: Felt.ofNat (lo.val / diff.val) ::
        hi_quot :: hi_rem :: diff :: (if cond then (1 : Felt) else 0) :: rest,
        mem, locs, adv⟩ := by
  unfold exec shr_chunk2 execWithEnv
  simp only [List.foldlM]
  miden_swap
  miden_movup
  miden_movup
  miden_dup
  rw [stepEqImm]
  miden_bind
  have h_pow_lo_isU32 := pow_lo_isU32 shift
  have h_eq0_isU32 := eq0_isU32 (Felt.ofNat (2 ^ shift.val)).lo32
  rw [stepU32OverflowSub (ha := h_pow_lo_isU32) (hb := h_eq0_isU32)]
  miden_bind
  rw [u32OverflowingSub_borrow_ite (Felt.ofNat (2 ^ shift.val)).lo32.val
    ((if (Felt.ofNat (2 ^ shift.val)).lo32 == 0 then (1 : Felt) else 0).val)]
  rw [stepNotIte]
  miden_bind
  miden_movdn
  miden_dup
  miden_movdn
  have h_diff_isU32 := shr_diff_isU32 (Felt.ofNat (2 ^ shift.val)).lo32 h_pow_lo_isU32
  simp only [] at h_diff_isU32
  have h_diff_ne_zero := shr_diff_val_ne_zero_beq (Felt.ofNat (2 ^ shift.val)).lo32
  simp only [] at h_diff_ne_zero
  rw [stepU32DivMod (ha := hlo) (hb := h_diff_isU32) (hbnz := h_diff_ne_zero)]
  miden_bind
  rfl

private theorem shr_chunk3_correct
    (lo_rem lo_quot hi_quot hi_rem diff : Felt) (cond : Bool)
    (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (hdiff_ne_zero : (diff == (0 : Felt)) = false) :
    let cond_felt : Felt := if cond then 1 else 0
    let mix := lo_quot + (((4294967296 : Felt) * cond_felt) * diff⁻¹) * hi_rem
    exec 42 ⟨lo_rem :: lo_quot :: hi_quot :: hi_rem :: diff :: cond_felt :: rest, mem, locs, adv⟩
        shr_chunk3 =
      some ⟨(if cond then hi_quot else mix) :: (if cond then mix else hi_quot) ::
        cond_felt :: rest, mem, locs, adv⟩ := by
  unfold exec shr_chunk3 execWithEnv
  simp only [List.foldlM]
  miden_swap
  miden_swap
  rw [stepDrop]
  miden_bind
  rw [stepPush]
  miden_bind
  miden_dup
  rw [stepMul]
  miden_bind
  miden_movup
  rw [stepDiv (hb := hdiff_ne_zero)]
  miden_bind
  miden_movup
  rw [stepMul]
  miden_bind
  rw [stepAdd]
  miden_bind
  miden_dup
  rw [stepCswapIte]
  miden_bind
  rfl

set_option maxHeartbeats 16000000 in
/-- `u64::shr` raw: result in terms of field arithmetic on limbs. -/
theorem u64_shr_raw
    (lo hi shift : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = shift :: lo :: hi :: rest)
    (hshift : shift.val ≤ 63)
    (hlo : lo.isU32 = true) (hhi : hi.isU32 = true) :
    let pow := Felt.ofNat (2 ^ shift.val)
    let pow_lo := pow.lo32
    let pow_hi := pow.hi32
    let denom := pow_hi + pow_lo
    let hi_rem := Felt.ofNat (hi.val % denom.val)
    let hi_quot := Felt.ofNat (hi.val / denom.val)
    let pow_lo_eq0 : Felt := if pow_lo == (0 : Felt) then 1 else 0
    let borrow := decide (pow_lo.val < pow_lo_eq0.val)
    let cond := !borrow
    let diff := Felt.ofNat (u32OverflowingSub pow_lo.val pow_lo_eq0.val).2
    let lo_quot := Felt.ofNat (lo.val / diff.val)
    exec 42 s Miden.Core.U64.shr =
    some (s.withStack (
      if cond then
        (lo_quot + (4294967296 : Felt) * diff⁻¹ * hi_rem) :: hi_quot :: rest
      else hi_quot :: (0 : Felt) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  rw [shr_decomp, MidenLean.exec_append]
  rw [shr_chunk1_correct (mem := mem) (locs := locs) (adv := adv) (hshift := hshift) (hhi := hhi)]
  simp only [bind, Bind.bind, Option.bind]
  rw [MidenLean.exec_append]
  rw [shr_chunk2_correct (mem := mem) (locs := locs) (adv := adv) (hlo := hlo)]
  simp only [bind, Bind.bind, Option.bind]
  rw [MidenLean.exec_append]
  have h_diff_ne_zero_felt := shr_diff_ne_zero_felt (Felt.ofNat (2 ^ shift.val)).lo32
  simp only [] at h_diff_ne_zero_felt
  rw [shr_chunk3_correct
    (lo_rem := Felt.ofNat
      (lo.val %
        (Felt.ofNat
          (u32OverflowingSub (Felt.ofNat (2 ^ shift.val)).lo32.val
            (if (Felt.ofNat (2 ^ shift.val)).lo32 == 0 then (1 : Felt) else 0).val).2).val))
    (lo_quot := Felt.ofNat
      (lo.val /
        (Felt.ofNat
          (u32OverflowingSub (Felt.ofNat (2 ^ shift.val)).lo32.val
            (if (Felt.ofNat (2 ^ shift.val)).lo32 == 0 then (1 : Felt) else 0).val).2).val))
    (hi_quot := Felt.ofNat
      (hi.val / ((Felt.ofNat (2 ^ shift.val)).hi32 + (Felt.ofNat (2 ^ shift.val)).lo32).val))
    (hi_rem := Felt.ofNat
      (hi.val % ((Felt.ofNat (2 ^ shift.val)).hi32 + (Felt.ofNat (2 ^ shift.val)).lo32).val))
    (diff := Felt.ofNat
      (u32OverflowingSub (Felt.ofNat (2 ^ shift.val)).lo32.val
        (if (Felt.ofNat (2 ^ shift.val)).lo32 == 0 then (1 : Felt) else 0).val).2)
    (cond := !decide
      ((Felt.ofNat (2 ^ shift.val)).lo32.val <
        (if (Felt.ofNat (2 ^ shift.val)).lo32 == 0 then (1 : Felt) else 0).val))
    (mem := mem) (locs := locs) (adv := adv) (rest := rest)
    (hdiff_ne_zero := h_diff_ne_zero_felt)]
  simp only [bind, Bind.bind, Option.bind]
  unfold exec shr_chunk4 execWithEnv
  simp only [List.foldlM]
  cases hcond : !decide
    ((Felt.ofNat (2 ^ shift.val)).lo32.val <
      (if (Felt.ofNat (2 ^ shift.val)).lo32 == 0 then (1 : Felt) else 0).val)
  · simp
    miden_movup
    rw [stepMul]
    miden_bind
    miden_swap
    simp
  · simp
    miden_movup
    rw [stepMul]
    miden_bind
    miden_swap
    simp

-- ============================================================================
-- Bridging helpers for u64_shr_correct
-- ============================================================================

/-- In GF(p), 2^32 * (2^n)⁻¹ = 2^(32-n) when n < 32. -/
private theorem felt_pow2_inv (n : Nat) (hn : n < 32) :
    (4294967296 : Felt) * (Felt.ofNat (2^n))⁻¹ = Felt.ofNat (2^(32 - n)) := by
  have h_ne : (Felt.ofNat (2^n) : Felt) ≠ 0 := by
    intro h
    have hval : (Felt.ofNat (2^n)).val = 2^n :=
      felt_ofNat_val_lt _ (calc 2^n < 2^32 := Nat.pow_lt_pow_right (by omega) hn
        _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; norm_num)
    rw [h, Felt.val_zero'] at hval; exact absurd hval (show 0 < 2^n from by positivity).ne
  have h_eq : (4294967296 : Felt) = Felt.ofNat (2^(32 - n)) * Felt.ofNat (2^n) := by
    unfold Felt.ofNat; push_cast; rw [← pow_add, show 32 - n + n = 32 from by omega]; norm_num
  rw [h_eq]; exact mul_inv_cancel_right₀ h_ne _

/-- When shift >= 32, (hi * 2^32 + lo) / 2^shift = hi / 2^(shift-32). -/
private theorem shr_toNat_ge32 (hi lo n : Nat) (hlo : lo < 2^32) (h32 : 32 ≤ n) :
    (hi * 2^32 + lo) / 2^n = hi / 2^(n - 32) := by
  rw [show 2^n = 2^32 * 2^(n - 32) from by rw [← Nat.pow_add]; congr 1; omega,
      show hi * 2^32 + lo = lo + hi * 2^32 from by omega,
      ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_right _ _ (show (0:Nat) < 2^32 from by positivity),
      Nat.div_eq_of_lt hlo, Nat.zero_add]

/-- Core quotient identity: (hi * 2^32 + lo) / 2^n for n < 32. -/
private theorem shr_toNat_div_lt32 (hi lo n : Nat) (hn : n < 32) :
    (hi * 2^32 + lo) / 2^n = hi / 2^n * 2^32 + (hi % 2^n) * 2^(32 - n) + lo / 2^n := by
  have hp : 2^32 = 2^n * 2^(32 - n) := by rw [← Nat.pow_add]; congr 1; omega
  have h1 := (Nat.div_add_mod hi (2^n)).symm  -- hi = 2^n * (hi/2^n) + hi%2^n
  have h2 := (Nat.div_add_mod lo (2^n)).symm  -- lo = 2^n * (lo/2^n) + lo%2^n
  -- Rewrite numerator into q * 2^n + r form using Euclidean decompositions
  have lhs_eq : hi * 2^32 + lo =
    (2^n * (hi / 2^n) + hi % 2^n) * (2^n * 2^(32 - n)) +
    (2^n * (lo / 2^n) + lo % 2^n) := by rw [← h1, ← h2, ← hp]
  have h_eq : hi * 2^32 + lo =
      lo % 2^n + (hi / 2^n * 2^32 + (hi % 2^n) * 2^(32 - n) + lo / 2^n) * 2^n := by
    rw [lhs_eq, hp]; ring
  rw [h_eq, Nat.add_mul_div_right _ _ (by positivity : (0:Nat) < 2^n),
      Nat.div_eq_of_lt (Nat.mod_lt lo (by positivity)), Nat.zero_add]

/-- The lo-part sum from shr_toNat_div is < 2^32. -/
private theorem shr_lo_sum_lt (hi lo n : Nat) (hlo : lo < 2^32) (hn : n < 32) :
    (hi % 2^n) * 2^(32 - n) + lo / 2^n < 2^32 := by
  have hp : 2^n * 2^(32 - n) = 2^32 := by rw [← Nat.pow_add]; congr 1; omega
  have h1 : (hi % 2^n) * 2^(32 - n) ≤ (2^n - 1) * 2^(32 - n) :=
    Nat.mul_le_mul_right _ (by omega : hi % 2^n ≤ 2^n - 1)
  have h2 : lo / 2^n < 2^(32 - n) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity : 0 < 2^n)]
    calc lo < 2^32 := hlo
      _ = 2^(32 - n) * 2^n := by rw [← Nat.pow_add]; congr 1; omega
  have h3 : (2^n - 1) * 2^(32 - n) + 2^(32 - n) = 2^32 := by
    calc (2^n - 1) * 2^(32 - n) + 2^(32 - n)
        = (2^n - 1) * 2^(32 - n) + 1 * 2^(32 - n) := by simp
      _ = (2^n - 1 + 1) * 2^(32 - n) := (add_mul _ _ _).symm
      _ = 2^n * 2^(32 - n) := by rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))]
      _ = 2^32 := hp
  linarith

set_option maxHeartbeats 8000000 in
/-- `u64::shr` right-shifts a u64 value by `shift` bits.
    Input stack:  [shift, a.lo, a.hi] ++ rest
    Output stack: [(a.shr shift).lo, (a.shr shift).hi] ++ rest -/
theorem u64_shr_correct (a : U64) (shift : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = shift :: a.lo.val :: a.hi.val :: rest)
    (hshift : shift.val ≤ 63) :
    exec 42 s Miden.Core.U64.shr =
    some (s.withStack ((a.shr shift.val).lo.val :: (a.shr shift.val).hi.val :: rest)) := by
  rw [u64_shr_raw a.lo.val a.hi.val shift rest s hs hshift a.lo.isU32 a.hi.isU32]
  -- Recover key bounds
  have hlo_u32 := a.lo.isU32
  have hlo_lt : a.lo.val.val < 2^32 := by
    simp [Felt.isU32, decide_eq_true_eq] at hlo_u32; exact hlo_u32
  have hhi_u32 := a.hi.isU32
  have hhi_lt : a.hi.val.val < 2^32 := by
    simp [Felt.isU32, decide_eq_true_eq] at hhi_u32; exact hhi_u32
  have hpow_val := pow2_val_eq shift hshift
  -- Target: show result = (a.shr shift.val).lo :: (a.shr shift.val).hi :: rest
  show _ = some (s.withStack (
    Felt.ofNat ((a.toNat / 2^shift.val) % 2^32) ::
    Felt.ofNat (((a.toNat / 2^shift.val) / 2^32) % 2^32) :: rest))
  simp only [U64.toNat]
  -- Case split on shift < 32 vs >= 32
  by_cases h32 : shift.val < 32
  · -- Case shift < 32: cond = true
    have h_pow_lt : 2^shift.val < 2^32 := Nat.pow_lt_pow_right (by omega) h32
    have h_pow_lt_prime : 2^shift.val < GOLDILOCKS_PRIME :=
      calc 2^shift.val < 2^32 := h_pow_lt
        _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; norm_num
    -- lo32.val = 2^shift, hi32.val = 0
    have h_lo32_val : (Felt.ofNat (2 ^ shift.val)).lo32.val = 2^shift.val := by
      simp only [Felt.lo32]; rw [hpow_val, Nat.mod_eq_of_lt h_pow_lt]
      exact felt_ofNat_val_lt _ h_pow_lt_prime
    have h_hi32_val : (Felt.ofNat (2 ^ shift.val)).hi32.val = 0 := by
      simp only [Felt.hi32]; rw [hpow_val, Nat.div_eq_of_lt h_pow_lt]
      exact felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; norm_num)
    -- lo32 ≠ 0
    have h_lo32_ne : (Felt.ofNat (2 ^ shift.val)).lo32 ≠ 0 := by
      intro h; rw [h, Felt.val_zero'] at h_lo32_val
      exact absurd h_lo32_val (show 0 < 2^shift.val from by positivity).ne
    -- beq false, eq0 = 0
    have h_beq : ((Felt.ofNat (2 ^ shift.val)).lo32 == 0) = false := by simp [h_lo32_ne]
    have h_eq0 : (if ((Felt.ofNat (2 ^ shift.val)).lo32 == 0) = true then (1 : Felt) else 0) = 0 := by
      simp [h_beq]
    -- Condition is true
    have h_cond : (!decide ((Felt.ofNat (2 ^ shift.val)).lo32.val <
        (if ((Felt.ofNat (2 ^ shift.val)).lo32 == 0) = true then (1 : Felt) else 0).val)) = true := by
      rw [h_eq0, Felt.val_zero', h_lo32_val]; simp
    simp only [h_cond, ite_true]
    -- Simplify u32OverflowingSub and denom
    rw [h_eq0, Felt.val_zero', h_lo32_val]
    simp only [show u32OverflowingSub (2 ^ shift.val) 0 = (0, 2 ^ shift.val) from by
      unfold u32OverflowingSub; simp]
    simp only [show (Felt.ofNat (2 ^ shift.val)).val = 2 ^ shift.val from hpow_val]
    rw [show ((Felt.ofNat (2 ^ shift.val)).hi32 + (Felt.ofNat (2 ^ shift.val)).lo32).val =
        2 ^ shift.val from by rw [pow2_denom_val shift hshift, h_hi32_val, h_lo32_val]; omega]
    -- Use nat identities
    have h_div := shr_toNat_div_lt32 a.hi.val.val a.lo.val.val shift.val h32
    have h_lo_sum_lt := shr_lo_sum_lt a.hi.val.val a.lo.val.val shift.val hlo_lt h32
    have h_hi_eq : (a.hi.val.val * 2 ^ 32 + a.lo.val.val) / 2 ^ shift.val / 2 ^ 32 = a.hi.val.val / 2^shift.val := by
      rw [h_div, show a.hi.val.val / 2^shift.val * 2^32 +
        a.hi.val.val % 2^shift.val * 2^(32 - shift.val) + a.lo.val.val / 2^shift.val =
        (a.hi.val.val % 2^shift.val * 2^(32 - shift.val) + a.lo.val.val / 2^shift.val) +
        a.hi.val.val / 2^shift.val * 2^32 from by omega,
        Nat.add_mul_div_right _ _ (show (0:Nat) < 2^32 from by positivity),
        Nat.div_eq_of_lt h_lo_sum_lt, Nat.zero_add]
    have h_lo_eq : (a.hi.val.val * 2 ^ 32 + a.lo.val.val) / 2 ^ shift.val % 2 ^ 32 =
        (a.hi.val.val % 2^shift.val) * 2^(32 - shift.val) + a.lo.val.val / 2^shift.val := by
      rw [h_div, show a.hi.val.val / 2^shift.val * 2^32 +
        a.hi.val.val % 2^shift.val * 2^(32 - shift.val) + a.lo.val.val / 2^shift.val =
        a.hi.val.val / 2^shift.val * 2^32 +
        (a.hi.val.val % 2^shift.val * 2^(32 - shift.val) + a.lo.val.val / 2^shift.val) from by omega,
        Nat.mul_add_mod_of_lt h_lo_sum_lt]
    rw [h_lo_eq, h_hi_eq]
    -- Hi limb
    have h_hi_lt : a.hi.val.val / 2^shift.val < 2^32 :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hhi_lt
    -- Field inverse: 4294967296 * (Felt.ofNat (2^n))⁻¹ = Felt.ofNat (2^(32-n))
    rw [felt_pow2_inv shift.val h32]
    congr 1; congr 1; congr 1
    · -- Lo limb: Felt.ofNat lo_q + Felt.ofNat (2^(32-n)) * Felt.ofNat hi_r = Felt.ofNat (hi_r * 2^(32-n) + lo_q)
      unfold Felt.ofNat; push_cast; ring
    · congr 1; congr 1; exact (Nat.mod_eq_of_lt h_hi_lt).symm
  · -- Case shift >= 32: cond = false
    push_neg at h32
    -- Establish pow_lo = 0, pow_hi = 2^(shift-32)
    have h_pow_mod : 2 ^ shift.val % 2 ^ 32 = 0 :=
      Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 h32)
    have h_pow_div : 2 ^ shift.val / 2 ^ 32 = 2 ^ (shift.val - 32) := by
      rw [show 2^shift.val = 2^32 * 2^(shift.val - 32) from by
        rw [← Nat.pow_add]; congr 1; omega]
      exact Nat.mul_div_cancel_left _ (by positivity)
    have h_lo32_val : (Felt.ofNat (2 ^ shift.val)).lo32.val = 0 := by
      simp only [Felt.lo32]; rw [hpow_val, h_pow_mod]
      exact felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; norm_num)
    have h_hi32_val : (Felt.ofNat (2 ^ shift.val)).hi32.val = 2 ^ (shift.val - 32) := by
      simp only [Felt.hi32]; rw [hpow_val, h_pow_div]
      exact felt_ofNat_val_lt _ (by
        calc 2^(shift.val - 32) ≤ 2^31 := Nat.pow_le_pow_right (by omega) (by omega)
          _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide)
    -- Show the condition is false (pow_lo == 0, eq0 = 1, borrow = true, cond = false)
    have h_lo32_eq_zero : (Felt.ofNat (2 ^ shift.val)).lo32 = 0 := by
      exact (ZMod.val_eq_zero _).mp h_lo32_val
    have h_beq_true : ((Felt.ofNat (2 ^ shift.val)).lo32 == 0) = true := by
      simp [h_lo32_eq_zero]
    have h_cond_false : (!decide ((Felt.ofNat (2 ^ shift.val)).lo32.val <
        (if ((Felt.ofNat (2 ^ shift.val)).lo32 == 0) = true then (1 : Felt) else 0).val)) = false := by
      simp [h_beq_true, Felt.val_one', h_lo32_val]
    simp only [h_cond_false, show (false = true) = False from by decide, ite_false]
    -- denom.val = 2^(shift-32)
    have h_denom_val : ((Felt.ofNat (2 ^ shift.val)).hi32 + (Felt.ofNat (2 ^ shift.val)).lo32).val =
        2 ^ (shift.val - 32) := by
      rw [pow2_denom_val shift hshift, h_hi32_val, h_lo32_val]; omega
    rw [h_denom_val]
    -- Use the >= 32 nat identity
    have h_nat := shr_toNat_ge32 a.hi.val.val a.lo.val.val shift.val hlo_lt h32
    rw [h_nat]
    -- result < 2^32
    have h_result_lt : a.hi.val.val / 2^(shift.val - 32) < 2^32 :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hhi_lt
    congr 1; congr 1; congr 1
    · congr 1; exact (Nat.mod_eq_of_lt h_result_lt).symm
    · congr 1; rw [Nat.div_eq_of_lt h_result_lt, Nat.mod_eq_of_lt (by norm_num : 0 < 2^32)]
      exact (Nat.cast_zero (R := Felt)).symm

end MidenLean.Proofs
