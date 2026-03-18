import MidenLean.Proofs.Tactics
import MidenLean.Proofs.Interp
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `u64::eq` correctly tests equality of two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff b_lo == a_lo && b_hi == a_hi, else 0. -/
theorem u64_eq_correct (b_lo b_hi a_lo a_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest) :
    exec 10 s Miden.Core.U64.eq =
    some (s.withStack (
      (if (b_lo == a_lo) && (b_hi == a_hi)
       then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U64.eq execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv⟩ (.movup 2)
    let s' ← execInstruction s' (.eq)
    let s' ← execInstruction s' (.swap 2)
    let s' ← execInstruction s' (.eq)
    let s' ← execInstruction s' Instruction.and
    pure s') = _
  miden_movup
  rw [stepEq]; miden_bind
  miden_swap
  rw [stepEq]; miden_bind
  rw [stepAndIte]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

/-- Semantic version: u64.eq computes (toU64 a == toU64 b). -/
theorem u64_eq_semantic (b_lo b_hi a_lo a_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    exec 10 s Miden.Core.Math.U64.eq =
    some (s.withStack (
      (if decide (toU64 a_lo a_hi = toU64 b_lo b_hi)
       then (1 : Felt) else 0) :: rest)) := by
  rw [u64_eq_correct b_lo b_hi a_lo a_hi rest s hs]
  suffices h : ((b_lo == a_lo) && (b_hi == a_hi)) =
    decide (toU64 a_lo a_hi = toU64 b_lo b_hi) by
    simp_rw [h]
  rw [show ((b_lo == a_lo) && (b_hi == a_hi)) =
    decide (toU64 a_lo a_hi = toU64 b_lo b_hi) from by
    simp only [Bool.beq_eq_decide_eq]
    rw [show (decide (b_lo = a_lo) && decide (b_hi = a_hi)) =
      decide (b_lo = a_lo ∧ b_hi = a_hi) from
      (Bool.decide_and ..).symm]
    rw [decide_eq_decide]
    constructor
    · rintro ⟨hlo, hhi⟩
      exact (toU64_eq_iff a_lo a_hi b_lo b_hi ha_lo ha_hi hb_lo hb_hi).mpr
        (And.intro hlo.symm hhi.symm)
    · intro h
      obtain ⟨hlo, hhi⟩ := (toU64_eq_iff a_lo a_hi b_lo b_hi ha_lo ha_hi hb_lo hb_hi).mp h
      exact And.intro hlo.symm hhi.symm]

end MidenLean.Proofs
