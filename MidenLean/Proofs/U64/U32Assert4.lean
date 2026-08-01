import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

private theorem u32Assert2_isU32 {a b : Felt} {rest : List Felt} {mem : Nat → Felt}
    {frames : List LocalFrame} {adv : List Felt} {s' : Concrete.State}
    (h : execInstruction ⟨a :: b :: rest, mem, frames, adv⟩ .u32Assert2 = some s') :
    a.isU32 = true ∧ b.isU32 = true ∧ s' = ⟨a :: b :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Assert2 at h
  simp only [Felt.isU32] at h ⊢
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    simp only [Option.some.injEq] at h
    exact ⟨decide_eq_true_eq.mpr hcond.2, decide_eq_true_eq.mpr hcond.1, h.symm⟩
  · simp at h

private theorem bind_some_eq {x : Option Concrete.State} {f : Concrete.State → Option Concrete.State}
    {b : Concrete.State} (h : (x >>= f) = some b) : ∃ a, x = some a ∧ f a = some b := by
  simp only [bind, Bind.bind, Option.bind] at h
  split at h
  · simp at h
  · exact ⟨_, rfl, h⟩

private theorem movup3_concrete (a b c d : Felt) (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execInstruction ⟨a :: b :: c :: d :: rest, mem, frames, adv⟩ (.movup 3) =
    some ⟨d :: a :: b :: c :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execMovup removeNth
  simp [Concrete.State.withStack]

set_option maxHeartbeats 4000000 in
/-- `u64::u32assert4` succeeds and leaves the stack unchanged when all four
    top elements are u32 values.
    Input stack:  [a, b, c, d] ++ rest
    Output stack: [a, b, c, d] ++ rest
    Parametric in `env` and `fuel` so this lemma serves both as a callee
    summary for reflective callers and as the basis for `u64_u32assert4_correct`. -/
@[miden_exec_summary]
theorem u64_u32assert4_exec
    (env : ProcEnv) (fuel : Nat)
    (a b c d : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a :: b :: c :: d :: rest)
    (ha : a.isU32 = true) (hb : b.isU32 = true)
    (hc : c.isU32 = true) (hd : d.isU32 = true) :
    execProcedure env (fuel + 1) s Miden.Core.U64.u32assert4 =
    some (s.withStack (a :: b :: c :: d :: rest)) := by
  miden_vcg

set_option maxHeartbeats 16000000 in
/-- `u64::u32assert4` succeeds and leaves the stack unchanged iff all four
    top elements are u32 values. -/
theorem u64_u32assert4_correct
    (a b c d : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a :: b :: c :: d :: rest) :
    execProcedure emptyEnv 10 s Miden.Core.U64.u32assert4 =
    some (s.withStack (a :: b :: c :: d :: rest)) ↔
    (a.isU32 = true ∧ b.isU32 = true ∧ c.isU32 = true ∧ d.isU32 = true) := by
  constructor
  · -- Forward: execution succeeds → all four are u32
    intro h
    obtain ⟨stk, mem, frames, adv⟩ := s
    simp only [Concrete.State.withStack] at hs h
    subst hs
    unfold Miden.Core.U64.u32assert4 execProcedure at h
    simp only [List.foldlM] at h
    change (do
      let s' ← execInstruction ⟨a :: b :: c :: d :: rest, mem, frames, adv⟩ .u32Assert2
      let s' ← execInstruction s' (.movup 3)
      let s' ← execInstruction s' (.movup 3)
      let s' ← execInstruction s' .u32Assert2
      let s' ← execInstruction s' (.movup 3)
      let s' ← execInstruction s' (.movup 3)
      pure s') = _ at h
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
    exact u64_u32assert4_exec emptyEnv 9 a b c d rest s hs ha hb hc hd

end MidenLean.Proofs
