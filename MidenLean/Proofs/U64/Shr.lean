import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean

-- ============================================================================
-- Helper lemmas for u64.shr
-- ============================================================================

/-- pow2 value for shift ≤ 63: hi32.val + lo32.val < GOLDILOCKS_PRIME. -/
private theorem pow2_hi32_add_lo32_val (shift : Felt) (hshift : shift.val ≤ 63) :
    ((Felt.ofNat (2 ^ shift.val)).hi32.val + (Felt.ofNat (2 ^ shift.val)).lo32.val) <
      GOLDILOCKS_PRIME := by
  have hlo := lo32_val (Felt.ofNat (2 ^ shift.val))
  have hhi := hi32_val (Felt.ofNat (2 ^ shift.val))
  have hpow_val : (Felt.ofNat (2 ^ shift.val)).val = 2 ^ shift.val := by
    apply felt_ofNat_val_lt
    calc 2 ^ shift.val ≤ 2 ^ 63 := Nat.pow_le_pow_right (by omega) hshift
      _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide
  rw [hlo, hhi, hpow_val]
  have hmod : 2 ^ shift.val % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hdiv : 2 ^ shift.val / 2 ^ 32 < 2 ^ 32 := by
    calc 2 ^ shift.val / 2 ^ 32 ≤ (2 ^ 63) / 2 ^ 32 :=
        Nat.div_le_div_right (Nat.pow_le_pow_right (by omega) hshift)
      _ < 2 ^ 32 := by native_decide
  unfold GOLDILOCKS_PRIME; omega

/-- The field addition hi32 + lo32 of pow2 has the expected val. -/
private theorem pow2_denom_val (shift : Felt) (hshift : shift.val ≤ 63) :
    ((Felt.ofNat (2 ^ shift.val)).hi32 + (Felt.ofNat (2 ^ shift.val)).lo32).val =
    (Felt.ofNat (2 ^ shift.val)).hi32.val + (Felt.ofNat (2 ^ shift.val)).lo32.val := by
  simp only [ZMod.val_add]
  exact Nat.mod_eq_of_lt (pow2_hi32_add_lo32_val shift hshift)

/-- denom.val ≠ 0 for pow2 shift with shift ≤ 63. -/
private theorem pow2_denom_ne_zero (shift : Felt) (hshift : shift.val ≤ 63) :
    (((Felt.ofNat (2 ^ shift.val)).hi32 + (Felt.ofNat (2 ^ shift.val)).lo32).val == 0) = false := by
  rw [pow2_denom_val shift hshift]
  have hpow_val : (Felt.ofNat (2 ^ shift.val)).val = 2 ^ shift.val := by
    apply felt_ofNat_val_lt
    calc 2 ^ shift.val ≤ 2 ^ 63 := Nat.pow_le_pow_right (by omega) hshift
      _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide
  have hhi := hi32_val (Felt.ofNat (2 ^ shift.val))
  have hlo := lo32_val (Felt.ofNat (2 ^ shift.val))
  rw [hhi, hlo, hpow_val]
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
    -- 0 ≥ 1 is false, so we take the else branch
    simp only [show ¬(0 ≥ 1) from by omega, ↓reduceIte]
    -- diff = u32Max - 1 + 0 = u32Max - 1
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

/-- The diff Felt from shr is nonzero. -/
private theorem shr_diff_ne_zero_felt (pow_lo : Felt) :
    let eq0 : Felt := if pow_lo == (0 : Felt) then 1 else 0
    (Felt.ofNat (u32OverflowingSub pow_lo.val eq0.val).2 == (0 : Felt)) = false := by
  simp only []
  have h := shr_diff_val_ne_zero pow_lo
  simp only [] at h
  exact Bool.eq_false_iff.mpr fun hbeq =>
    h ((ZMod.val_eq_zero _).mpr (beq_iff_eq.mp hbeq))

-- ============================================================================
-- Instruction sublists for phase splitting
-- ============================================================================

private def shr_phase1_instrs : List Instruction :=
  [.movup 2, .swap 1, .pow2, .u32Split, .swap 1, .dup 1, .add, .movup 2, .swap 1, .u32DivMod]

private def shr_phase2_instrs : List Instruction :=
  [.swap 1, .movup 3, .movup 3, .dup 0, .eqImm 0, .u32OverflowSub, .not, .movdn 4,
   .dup 0, .movdn 4, .u32DivMod, .swap 1, .swap 1, .drop]

private def shr_phase3_instrs : List Instruction :=
  [.push 4294967296, .dup 5, .mul, .movup 4, .div, .movup 3, .mul, .add,
   .dup 2, .cswap, .movup 2, .mul, .swap 1]

-- ============================================================================
-- Phase 1: Setup + hi divmod (10 steps)
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem shr_phase1
    (lo hi shift : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hshift : shift.val ≤ 63) :
    let pow := Felt.ofNat (2 ^ shift.val)
    let pow_lo := pow.lo32
    let pow_hi := pow.hi32
    let denom := pow_hi + pow_lo
    execInstructions ⟨shift :: lo :: hi :: rest, mem, locs, adv⟩ shr_phase1_instrs =
    some ⟨Felt.ofNat (hi.val % denom.val) ::
          Felt.ofNat (hi.val / denom.val) ::
          pow_lo :: lo :: rest, mem, locs, adv⟩ := by
  unfold shr_phase1_instrs
  simp only [execInstructions]
  miden_movup; miden_swap
  rw [execInstruction_pow2]; unfold execPow2
  simp only [show ¬(shift.val > 63) from by omega, MidenState.withStack, ↓reduceIte]
  miden_bind
  rw [execInstruction_u32Split]; unfold execU32Split; miden_bind
  miden_swap; miden_dup
  rw [execInstruction_add]; unfold execAdd; miden_bind
  miden_movup; miden_swap
  rw [execInstruction_u32DivMod, execU32DivMod_concrete _ _ _ _ _ _ (pow2_denom_ne_zero shift hshift)]

-- ============================================================================
-- Phase 2: Condition flag + lo divmod + cleanup (14 steps)
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem shr_phase2
    (lo hi_rem hi_quot pow_lo : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) :
    let pow_lo_eq0 : Felt := if pow_lo == (0 : Felt) then 1 else 0
    let borrow := decide (pow_lo.val < pow_lo_eq0.val)
    let cond := !borrow
    let diff := Felt.ofNat (u32OverflowingSub pow_lo.val pow_lo_eq0.val).2
    execInstructions ⟨hi_rem :: hi_quot :: pow_lo :: lo :: rest, mem, locs, adv⟩ shr_phase2_instrs =
    some ⟨Felt.ofNat (lo.val / diff.val) :: hi_quot :: hi_rem ::
          diff :: (if cond then (1 : Felt) else 0) :: rest,
          mem, locs, adv⟩ := by
  unfold shr_phase2_instrs
  simp only [execInstructions]
  miden_swap; miden_movup; miden_movup; miden_dup
  rw [execInstruction_eqImm]; unfold execEqImm; miden_bind
  rw [execInstruction_u32OverflowSub]; unfold execU32OverflowSub; miden_bind
  rw [u32OverflowingSub_borrow_ite]
  rw [execInstruction_not, execNot_ite]; miden_bind
  miden_movdn; miden_dup; miden_movdn
  have hb : ((Felt.ofNat (u32OverflowingSub pow_lo.val
    (if pow_lo == 0 then (1 : Felt) else 0).val).2).val == 0) = false := by
    have h := shr_diff_val_ne_zero pow_lo; simp only [] at h
    exact Bool.eq_false_iff.mpr (mt beq_iff_eq.mp h)
  rw [execInstruction_u32DivMod, execU32DivMod_concrete _ _ _ _ _ _ hb]; miden_bind
  miden_swap; miden_swap
  rw [execInstruction_drop]; unfold execDrop; miden_bind

-- ============================================================================
-- Phase 3: Cross term, combine, cswap (13 steps)
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem shr_phase3
    (lo_quot hi_quot hi_rem diff : Felt) (cond : Bool) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hb : (diff == (0 : Felt)) = false) :
    let cf : Felt := if cond then 1 else 0
    execInstructions ⟨lo_quot :: hi_quot :: hi_rem :: diff :: cf :: rest,
                      mem, locs, adv⟩ shr_phase3_instrs =
    some ⟨(if cond then
             (lo_quot + (4294967296 : Felt) * diff⁻¹ * hi_rem) :: hi_quot :: rest
           else hi_quot :: (0 : Felt) :: rest),
          mem, locs, adv⟩ := by
  unfold shr_phase3_instrs
  simp only [execInstructions]
  rw [execInstruction_push]; unfold execPush; miden_bind
  miden_dup
  rw [execInstruction_mul]; unfold execMul; miden_bind
  miden_movup
  rw [execInstruction_div, execDiv_concrete _ _ _ _ _ _ hb]; miden_bind
  miden_movup
  rw [execInstruction_mul]; unfold execMul; miden_bind
  rw [execInstruction_add]; unfold execAdd; miden_bind
  miden_dup
  rw [execInstruction_cswap, execCswap_ite]
  cases cond
  · -- cond = false
    simp only [Bool.false_eq_true, ↓reduceIte]
    miden_movup
    rw [execInstruction_mul]; unfold execMul; miden_bind
    miden_swap
    simp only [mul_zero]
  · -- cond = true
    simp only [↓reduceIte]
    miden_movup
    rw [execInstruction_mul]; unfold execMul; miden_bind
    miden_swap
    simp only [mul_one]

-- ============================================================================
-- Chaining: compose phases using execInstructions_append
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem u64_shr_steps
    (lo hi shift : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hshift : shift.val ≤ 63) :
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
    execInstructions ⟨shift :: lo :: hi :: rest, mem, locs, adv⟩
      (shr_phase1_instrs ++ shr_phase2_instrs ++ shr_phase3_instrs) =
    some ⟨(if cond then
             (lo_quot + (4294967296 : Felt) * diff⁻¹ * hi_rem) :: hi_quot :: rest
           else
             hi_quot :: (0 : Felt) :: rest),
          mem, locs, adv⟩ := by
  -- Split (phase1 ++ phase2) ++ phase3 using two applications of append
  rw [execInstructions_append]     -- split at outer ++
  rw [execInstructions_append]     -- split phase1 ++ phase2 inside bind
  rw [shr_phase1 lo hi shift rest mem locs adv hshift]
  dsimp only [Option.bind]
  rw [shr_phase2 lo
    (Felt.ofNat (hi.val % ((Felt.ofNat (2 ^ shift.val)).hi32 +
      (Felt.ofNat (2 ^ shift.val)).lo32).val))
    (Felt.ofNat (hi.val / ((Felt.ofNat (2 ^ shift.val)).hi32 +
      (Felt.ofNat (2 ^ shift.val)).lo32).val))
    (Felt.ofNat (2 ^ shift.val)).lo32 rest mem locs adv]
  dsimp only [Option.bind]
  have hb := shr_diff_ne_zero_felt (Felt.ofNat (2 ^ shift.val)).lo32
  simp only [] at hb
  exact shr_phase3 _ _ _ _ _ rest mem locs adv hb

-- ============================================================================
-- Bridge: exec on shr ↔ execInstructions on phase lists
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem shr_exec_eq_execInstructions (s : MidenState) :
    exec 40 s Miden.Core.U64.shr =
    execInstructions s (shr_phase1_instrs ++ shr_phase2_instrs ++ shr_phase3_instrs) := by
  unfold exec Miden.Core.U64.shr shr_phase1_instrs shr_phase2_instrs shr_phase3_instrs
    execWithEnv
  rfl

-- ============================================================================
-- Main theorem: just unfold and delegate
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- u64.shr correctly right-shifts a u64 value.
    Input stack:  [shift, lo, hi] ++ rest
    Output stack: [result_lo, result_hi] ++ rest -/
theorem u64_shr_correct
    (lo hi shift : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = shift :: lo :: hi :: rest)
    (hshift : shift.val ≤ 63) :
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
    exec 40 s Miden.Core.U64.shr =
    some (s.withStack (
      if cond then
        (lo_quot + (4294967296 : Felt) * diff⁻¹ * hi_rem) :: hi_quot :: rest
      else hi_quot :: (0 : Felt) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  rw [shr_exec_eq_execInstructions]
  exact u64_shr_steps lo hi shift rest mem locs adv hshift

end MidenLean.Proofs
