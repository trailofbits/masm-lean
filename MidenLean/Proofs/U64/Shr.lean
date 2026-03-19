import MidenLean.Proofs.Tactics
import MidenLean.Proofs.Interp
import MidenLean.Generated.U64

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
    (lo hi shift : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt) (evts : List Felt)
    (hshift : shift.val ≤ 63) (hhi : hi.isU32 = true) :
    let pow := Felt.ofNat (2 ^ shift.val)
    let pow_lo := pow.lo32
    let pow_hi := pow.hi32
    let denom := pow_hi + pow_lo
    exec 42 ⟨shift :: lo :: hi :: rest, mem, locs, adv, evts⟩ shr_chunk1 =
      some ⟨Felt.ofNat (hi.val % denom.val) ::
        Felt.ofNat (hi.val / denom.val) :: pow_lo :: lo :: rest, mem, locs, adv, evts⟩ := by
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
  rw [stepU32DivMod (ha := hhi) (hb := h_denom_isU32)
    (hbz := by intro h; rw [h] at h_denom_ne_zero; simp at h_denom_ne_zero)]
  miden_bind
  rfl

private theorem shr_chunk2_correct
    (lo hi shift : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt) (evts : List Felt)
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
    exec 42 ⟨hi_rem :: hi_quot :: pow_lo :: lo :: rest, mem, locs, adv, evts⟩ shr_chunk2 =
      some ⟨Felt.ofNat (lo.val % diff.val) :: Felt.ofNat (lo.val / diff.val) ::
        hi_quot :: hi_rem :: diff :: (if cond then (1 : Felt) else 0) :: rest,
        mem, locs, adv, evts⟩ := by
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
  rw [stepU32DivMod (ha := hlo) (hb := h_diff_isU32)
    (hbz := by intro h; rw [h] at h_diff_ne_zero; simp at h_diff_ne_zero)]
  miden_bind
  rfl

private theorem shr_chunk3_correct
    (lo_rem lo_quot hi_quot hi_rem diff : Felt) (cond : Bool)
    (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt) (evts : List Felt)
    (hdiff_ne_zero : (diff == (0 : Felt)) = false) :
    let cond_felt : Felt := if cond then 1 else 0
    let mix := lo_quot + (((4294967296 : Felt) * cond_felt) * diff⁻¹) * hi_rem
    exec 42 ⟨lo_rem :: lo_quot :: hi_quot :: hi_rem :: diff :: cond_felt :: rest, mem, locs, adv, evts⟩
        shr_chunk3 =
      some ⟨(if cond then hi_quot else mix) :: (if cond then mix else hi_quot) ::
        cond_felt :: rest, mem, locs, adv, evts⟩ := by
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

/-- `u64::shr` correctly right-shifts a u64 value.
    Input stack:  [shift, lo, hi] ++ rest
    Output stack: [result_lo, result_hi] ++ rest -/
theorem u64_shr_correct
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
  obtain ⟨stk, mem, locs, adv, evts⟩ := s
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

/-- Semantic: shr computes toU64 lo hi / 2^shift.val.
    For shift >= 32: the result is hi / 2^(shift-32).
    For 0 < shift < 32: the result decomposes into
    hi_quot * 2^32 + lo_quot + spillover.
    For shift = 0: identity. -/
theorem u64_shr_semantic
    (lo hi shift : Felt)
    (hlo : lo.isU32 = true) (hhi : hi.isU32 = true)
    (hshift : shift.val ≤ 63) :
    if shift.val ≥ 32 then
      hi.val / 2 ^ (shift.val - 32) =
        toU64 lo hi / 2 ^ shift.val
    else
      (hi.val / 2 ^ shift.val) * 2 ^ 32 +
        (lo.val / 2 ^ shift.val +
         (hi.val % 2 ^ shift.val) *
          2 ^ (32 - shift.val)) =
        toU64 lo hi / 2 ^ shift.val := by
  simp only [Felt.isU32, decide_eq_true_eq] at hlo hhi
  split
  · -- shift >= 32
    rw [show toU64 lo hi = hi.val * 2 ^ 32 +
        lo.val from rfl]
    exact (shr_hi_only lo.val hi.val
      shift.val hlo ‹_›).symm
  · -- shift < 32
    rename_i hlt
    push_neg at hlt
    by_cases h0 : shift.val = 0
    · simp only [h0, Nat.pow_zero, Nat.div_one,
        Nat.mod_one, Nat.zero_mul, Nat.add_zero,
        Nat.sub_zero, toU64]
    · rw [show toU64 lo hi = hi.val * 2 ^ 32 +
          lo.val from rfl]
      exact shr_lo_decomp lo.val hi.val
        shift.val hlo hhi hlt (by omega)

end MidenLean.Proofs
