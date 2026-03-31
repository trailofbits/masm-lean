import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `u64::or` computes bitwise OR of two u64 values, limb by limb.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [b_lo ||| a_lo, b_hi ||| a_hi] ++ rest -/
theorem u64_or_raw
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    exec 10 s Miden.Core.U64.or =
    some (s.withStack (
      Felt.ofNat (b_lo.val ||| a_lo.val) ::
      Felt.ofNat (b_hi.val ||| a_hi.val) :: rest)) := by
  obtain ⟨stk, mem, frames, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U64.or execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, frames, adv⟩ (.movup 2)
    let s' ← execInstruction s' (.u32Or)
    let s' ← execInstruction s' (.swap 2)
    let s' ← execInstruction s' (.u32Or)
    let s' ← execInstruction s' (.swap 1)
    pure s') = _
  miden_movup
  rw [stepU32Or (ha := hb_lo) (hb := ha_lo)]; miden_bind
  miden_swap
  rw [stepU32Or (ha := hb_hi) (hb := ha_hi)]; miden_bind
  miden_swap
  dsimp only [pure, Pure.pure]

/-- `u64::or` computes bitwise OR of two u64 values.
    Input stack:  [b.lo, b.hi, a.lo, a.hi] ++ rest
    Output stack: [(a ||| b).lo, (a ||| b).hi] ++ rest -/
theorem u64_or_correct (a b : U64) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest) :
    exec 10 s Miden.Core.U64.or =
    some (s.withStack ((a ||| b).lo.val :: (a ||| b).hi.val :: rest)) := by
  simp only [U64.or_lo, U64.or_hi, Nat.or_comm a.lo.val.val, Nat.or_comm a.hi.val.val]
  exact u64_or_raw a.lo.val a.hi.val b.lo.val b.hi.val rest s hs a.lo.isU32 a.hi.isU32 b.lo.isU32 b.hi.isU32

-- Soundness dual (same structure as u64_xor_sound)
set_option maxHeartbeats 16000000 in
/-- Soundness of `u64::or`: if execution succeeds, then the input stack had four
    u32 values and the output is their pairwise bitwise OR. -/
theorem u64_or_sound
    (s s' : MidenState)
    (h : exec 10 s Miden.Core.U64.or = some s') :
    ∃ b_lo b_hi a_lo a_hi rest,
      s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest
      ∧ a_lo.isU32 = true
      ∧ a_hi.isU32 = true
      ∧ b_lo.isU32 = true
      ∧ b_hi.isU32 = true
      ∧ s' = s.withStack (
          Felt.ofNat (b_lo.val ||| a_lo.val) ::
          Felt.ofNat (b_hi.val ||| a_hi.val) :: rest) := by
  obtain ⟨stk, mem, frames, adv⟩ := s
  simp only [MidenState.withStack] at h ⊢
  unfold exec Miden.Core.U64.or execWithEnv at h
  simp only [List.foldlM] at h
  match stk with
  | [] | [_] | [_, _] => simp [execInstruction, execMovup, removeNth] at h
  | b_lo :: b_hi :: a_lo :: rest3 =>
    match rest3 with
    | [] =>
      simp only [execInstruction, execMovup, removeNth, bind, Bind.bind, Option.bind,
        MidenState.withStack] at h
      by_cases hc : b_lo.isU32 = true <;> by_cases hd : a_lo.isU32 = true <;>
        simp [execU32Or, hc, hd, execSwap, MidenState.withStack] at h
    | a_hi :: rest =>
      simp only [execInstruction, execMovup, removeNth,
        List.getElem?_cons_zero, List.getElem?_cons_succ,
        List.eraseIdx_cons_succ, List.eraseIdx_cons_zero,
        bind, Bind.bind, Option.bind, MidenState.withStack] at h
      by_cases hb_lo : b_lo.isU32 = true <;> by_cases ha_lo : a_lo.isU32 = true
      · simp only [execU32Or, MidenState.withStack] at h
        simp only [execSwap, MidenState.withStack] at h
        by_cases hb_hi : b_hi.isU32 = true <;> by_cases ha_hi : a_hi.isU32 = true
        · refine ⟨b_lo, b_hi, a_lo, a_hi, rest, rfl, ha_lo, ha_hi, hb_lo, hb_hi, ?_⟩
          simp_all [pure, Pure.pure]
        all_goals (exfalso; simp_all)
      all_goals (exfalso; simp_all [execU32Or])

end MidenLean.Proofs
