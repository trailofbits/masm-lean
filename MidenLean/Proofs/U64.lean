import MidenLean.Proofs.Helpers
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean

-- Helper: stepInstruction for eqImm 0 on concrete MidenState
set_option maxHeartbeats 400000 in
private theorem step_eqImm_zero (mem locs : Nat → Felt) (adv : List Felt) (a : Felt) (rest : List Felt) :
    stepInstruction ⟨a :: rest, mem, locs, adv⟩ (.eqImm 0) =
    some ⟨(if a == (0 : Felt) then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction; rfl

-- Helper: stepInstruction for swap 1 on concrete MidenState
set_option maxHeartbeats 400000 in
private theorem step_swap1 (mem locs : Nat → Felt) (adv : List Felt) (a b : Felt) (rest : List Felt) :
    stepInstruction ⟨a :: b :: rest, mem, locs, adv⟩ (.swap 1) =
    some ⟨b :: a :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction
  simp [List.set_cons_zero, List.set_cons_succ, MidenState.withStack]

-- Helper: stepInstruction for `and` with boolean ite values on concrete MidenState
set_option maxHeartbeats 800000 in
private theorem step_and_ite (mem locs : Nat → Felt) (adv : List Felt) (rest : List Felt) (p q : Bool) :
    stepInstruction
      ⟨(if p then (1 : Felt) else 0) :: (if q then (1 : Felt) else 0) :: rest, mem, locs, adv⟩
      Instruction.and =
    some ⟨(if q && p then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction
  simp only [Felt.isBool_ite_bool, MidenState.withStack]
  cases p <;> cases q <;> simp

set_option maxHeartbeats 4000000 in
/-- u64.eqz correctly tests whether a u64 value is zero.
    Input stack:  [lo, hi] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff lo = hi = 0, else 0. -/
theorem u64_eqz_correct (lo hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = lo :: hi :: rest) :
    exec 10 s Miden.Core.Math.U64.eqz =
    some (s.withStack (
      (if (lo == (0:Felt)) && (hi == (0:Felt))
       then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.Math.U64.eqz execOps
  simp only [List.foldlM]
  change (do
    let s' ← stepInstruction ⟨lo :: hi :: rest, mem, locs, adv⟩ (.eqImm 0)
    let s' ← stepInstruction s' (.swap 1)
    let s' ← stepInstruction s' (.eqImm 0)
    let s' ← stepInstruction s' Instruction.and
    pure s') = _
  rw [step_eqImm_zero]; dsimp only [bind, Bind.bind, Option.bind]
  rw [step_swap1]; dsimp only [bind, Bind.bind, Option.bind]
  rw [step_eqImm_zero]; dsimp only [bind, Bind.bind, Option.bind]
  rw [step_and_ite]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

/-- Procedure environment for u64 procedures. -/
def u64ProcEnv : ProcEnv := fun name =>
  match name with
  | "overflowing_add" => some Miden.Core.Math.U64.overflowing_add
  | _ => none

-- ============================================================================
-- Helpers for overflowing_add proof
-- ============================================================================

-- movup 2: the unfold stepInstruction gives a match on removeNth which is private,
-- but `rfl` can check definitional equality through private defs
set_option maxHeartbeats 4000000 in
private theorem step_movup2 (mem locs : Nat → Felt) (adv : List Felt)
    (a b c : Felt) (rest : List Felt) :
    stepInstruction ⟨a :: b :: c :: rest, mem, locs, adv⟩ (.movup 2) =
    some ⟨c :: a :: b :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction; rfl

set_option maxHeartbeats 4000000 in
private theorem step_movdn3 (mem locs : Nat → Felt) (adv : List Felt)
    (a b c d : Felt) (rest : List Felt) :
    stepInstruction ⟨a :: b :: c :: d :: rest, mem, locs, adv⟩ (.movdn 3) =
    some ⟨b :: c :: d :: a :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction; rfl

set_option maxHeartbeats 4000000 in
private theorem step_movdn2 (mem locs : Nat → Felt) (adv : List Felt)
    (a b c : Felt) (rest : List Felt) :
    stepInstruction ⟨a :: b :: c :: rest, mem, locs, adv⟩ (.movdn 2) =
    some ⟨b :: c :: a :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction; rfl

set_option maxHeartbeats 4000000 in
private theorem step_u32WidenAdd (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    stepInstruction ⟨b :: a :: rest, mem, locs, adv⟩ (.u32WidenAdd) =
    some ⟨Felt.ofNat ((a.val + b.val) % 2^32) :: Felt.ofNat ((a.val + b.val) / 2^32) :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction; rfl

set_option maxHeartbeats 4000000 in
private theorem step_u32WidenAdd3 (mem locs : Nat → Felt) (adv : List Felt)
    (a b c : Felt) (rest : List Felt) :
    stepInstruction ⟨c :: b :: a :: rest, mem, locs, adv⟩ (.u32WidenAdd3) =
    some ⟨Felt.ofNat ((a.val + b.val + c.val) % 2^32) :: Felt.ofNat ((a.val + b.val + c.val) / 2^32) :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction; rfl

set_option maxHeartbeats 400000 in
private theorem step_drop (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    stepInstruction ⟨a :: rest, mem, locs, adv⟩ (.drop) =
    some ⟨rest, mem, locs, adv⟩ := by
  unfold stepInstruction; rfl

-- ============================================================================
-- Key lemma: Felt.ofNat n has val = n when n < GOLDILOCKS_PRIME
-- ============================================================================

theorem felt_ofNat_val_lt (n : Nat) (h : n < GOLDILOCKS_PRIME) :
    (Felt.ofNat n).val = n := by
  unfold Felt.ofNat
  simp only [Felt, GOLDILOCKS_PRIME] at *
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt h

theorem felt_val_lt_prime (a : Felt) : a.val < GOLDILOCKS_PRIME := by
  exact ZMod.val_lt a

theorem sum_div_2_32_lt_prime (a b : Felt) : (a.val + b.val) / 2^32 < GOLDILOCKS_PRIME := by
  have ha := felt_val_lt_prime a
  have hb := felt_val_lt_prime b
  unfold GOLDILOCKS_PRIME at *
  omega

-- ============================================================================
-- Main proof: u64_overflowing_add_correct
-- ============================================================================

set_option maxHeartbeats 4000000 in
theorem u64_overflowing_add_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest) :
    exec 10 s Miden.Core.Math.U64.overflowing_add =
    some (s.withStack (
      let lo_sum := b_lo.val + a_lo.val
      let carry := lo_sum / 2^32
      let c_lo := Felt.ofNat (lo_sum % 2^32)
      let hi_sum := a_hi.val + b_hi.val + carry
      let c_hi := Felt.ofNat (hi_sum % 2^32)
      let overflow := Felt.ofNat (hi_sum / 2^32)
      overflow :: c_lo :: c_hi :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.Math.U64.overflowing_add execOps
  simp only [List.foldlM]
  change (do
    let s' ← stepInstruction ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv⟩ (.movup 2)
    let s' ← stepInstruction s' (.u32WidenAdd)
    let s' ← stepInstruction s' (.movdn 3)
    let s' ← stepInstruction s' (.u32WidenAdd3)
    let s' ← stepInstruction s' (.movdn 2)
    pure s') = _
  rw [step_movup2]; dsimp only [bind, Bind.bind, Option.bind]
  rw [step_u32WidenAdd]; dsimp only [bind, Bind.bind, Option.bind]
  rw [step_movdn3]; dsimp only [bind, Bind.bind, Option.bind]
  rw [step_u32WidenAdd3]; dsimp only [bind, Bind.bind, Option.bind]
  rw [step_movdn2]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  have hcarry : (Felt.ofNat ((b_lo.val + a_lo.val) / 2 ^ 32)).val = (b_lo.val + a_lo.val) / 2 ^ 32 :=
    felt_ofNat_val_lt _ (sum_div_2_32_lt_prime b_lo a_lo)
  rw [hcarry]

-- ============================================================================
-- Main proof: u64_wrapping_add_correct
-- ============================================================================

set_option maxHeartbeats 4000000 in
theorem u64_wrapping_add_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest) :
    execOps u64ProcEnv 10 s Miden.Core.Math.U64.wrapping_add =
    some (s.withStack (
      let lo_sum := b_lo.val + a_lo.val
      let carry := lo_sum / 2^32
      let c_lo := Felt.ofNat (lo_sum % 2^32)
      let hi_sum := a_hi.val + b_hi.val + carry
      let c_hi := Felt.ofNat (hi_sum % 2^32)
      c_lo :: c_hi :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold Miden.Core.Math.U64.wrapping_add execOps
  simp only [List.foldlM]
  change (do
    let s' ← (match u64ProcEnv "overflowing_add" with
      | some body => execOps u64ProcEnv 9 ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv⟩ body
      | none => none)
    let s' ← stepInstruction s' (.drop)
    pure s') = _
  simp only [u64ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  unfold Miden.Core.Math.U64.overflowing_add execOps
  simp only [List.foldlM]
  change (do
    let s' ← stepInstruction ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv⟩ (.movup 2)
    let s' ← stepInstruction s' (.u32WidenAdd)
    let s' ← stepInstruction s' (.movdn 3)
    let s' ← stepInstruction s' (.u32WidenAdd3)
    let s' ← stepInstruction s' (.movdn 2)
    let s' ← stepInstruction s' (.drop)
    pure s') = _
  rw [step_movup2]; dsimp only [bind, Bind.bind, Option.bind]
  rw [step_u32WidenAdd]; dsimp only [bind, Bind.bind, Option.bind]
  rw [step_movdn3]; dsimp only [bind, Bind.bind, Option.bind]
  rw [step_u32WidenAdd3]; dsimp only [bind, Bind.bind, Option.bind]
  rw [step_movdn2]; dsimp only [bind, Bind.bind, Option.bind]
  rw [step_drop]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  have hcarry : (Felt.ofNat ((b_lo.val + a_lo.val) / 2 ^ 32)).val = (b_lo.val + a_lo.val) / 2 ^ 32 :=
    felt_ofNat_val_lt _ (sum_div_2_32_lt_prime b_lo a_lo)
  rw [hcarry]

end MidenLean.Proofs
