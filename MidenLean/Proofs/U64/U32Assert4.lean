import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

private theorem u32Assert2_isU32 {a b : Felt} {rest : List Felt} {mem locs : Nat → Felt}
    {adv : List Felt} {s' : MidenState}
    (h : execInstruction ⟨a :: b :: rest, mem, locs, adv⟩ .u32Assert2 = some s') :
    a.isU32 = true ∧ b.isU32 = true ∧ s' = ⟨a :: b :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32Assert2 at h
  simp only [Felt.isU32] at h ⊢
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    simp only [Option.some.injEq] at h
    exact ⟨decide_eq_true_eq.mpr hcond.2, decide_eq_true_eq.mpr hcond.1, h.symm⟩
  · simp at h

private theorem bind_some_eq {x : Option MidenState} {f : MidenState → Option MidenState}
    {b : MidenState} (h : (x >>= f) = some b) : ∃ a, x = some a ∧ f a = some b := by
  simp only [bind, Bind.bind, Option.bind] at h
  split at h
  · simp at h
  · exact ⟨_, rfl, h⟩

private theorem movup3_concrete (a b c d : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt) :
    execInstruction ⟨a :: b :: c :: d :: rest, mem, locs, adv⟩ (.movup 3) =
    some ⟨d :: a :: b :: c :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execMovup removeNth
  simp [MidenState.withStack]

set_option maxHeartbeats 16000000 in
/-- `u64::u32assert4` succeeds and leaves the stack unchanged iff all four
    top elements are u32 values. -/
theorem u64_u32assert4_correct
    (a b c d : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: b :: c :: d :: rest) :
    exec 10 s Miden.Core.U64.u32assert4 =
    some (s.withStack (a :: b :: c :: d :: rest)) ↔
    (a.isU32 = true ∧ b.isU32 = true ∧ c.isU32 = true ∧ d.isU32 = true) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U64.u32assert4 execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨a :: b :: c :: d :: rest, mem, locs, adv⟩ .u32Assert2
    let s' ← execInstruction s' (.movup 3)
    let s' ← execInstruction s' (.movup 3)
    let s' ← execInstruction s' .u32Assert2
    let s' ← execInstruction s' (.movup 3)
    let s' ← execInstruction s' (.movup 3)
    pure s') = _ ↔ _
  constructor
  · -- Forward: execution succeeds → all four are u32
    intro h
    obtain ⟨s1, hs1, h⟩ := bind_some_eq h
    have ⟨ha, hb, heq1⟩ := u32Assert2_isU32 hs1; subst heq1
    obtain ⟨s2, hs2, h⟩ := bind_some_eq h
    rw [movup3_concrete] at hs2; cases hs2
    obtain ⟨s3, hs3, h⟩ := bind_some_eq h
    rw [movup3_concrete] at hs3; cases hs3
    obtain ⟨s4, hs4, h⟩ := bind_some_eq h
    have ⟨hc, hd, heq4⟩ := u32Assert2_isU32 hs4; subst heq4
    exact ⟨ha, hb, hc, hd⟩
  · -- Reverse: all four are u32 → execution succeeds
    intro ⟨ha, hb, hc, hd⟩
    rw [stepU32Assert2 (ha := ha) (hb := hb)]; miden_bind
    miden_movup; miden_movup
    rw [stepU32Assert2 (ha := hc) (hb := hd)]; miden_bind
    miden_movup; miden_movup
    dsimp only [pure, Pure.pure]

end MidenLean.Proofs
