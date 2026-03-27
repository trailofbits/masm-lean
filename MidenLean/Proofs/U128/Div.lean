import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.U128.Divmod
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private theorem divmod_execWithEnv_eq_exec (fuel : Nat) (s : MidenState)
    (hf : 0 < fuel) :
    execWithEnv u128ProcEnv fuel s Miden.Core.U128.divmod =
      exec 163 s Miden.Core.U128.divmod := by
  cases fuel with
  | zero => cases hf
  | succ fuel' =>
      simp (maxSteps := 5000000) [exec, execWithEnv, u128ProcEnv, Miden.Core.U128.divmod]

set_option maxHeartbeats 12000000 in
/-- `u128::div` verifies an advice-supplied quotient and remainder for u128 division,
    then drops the remainder word and returns the quotient limbs.
    Execution succeeds iff the advice-supplied q and r satisfy q * b + r = a and r < b.
    Input stack:  [b.a0, b.a1, b.a2, b.a3, a.a0, a.a1, a.a2, a.a3] ++ rest
    Advice stack: [r.a0, r.a1, r.a2, r.a3, q.a0, q.a1, q.a2, q.a3] ++ adv_rest
    Output stack: [q.a0, q.a1, q.a2, q.a3] ++ rest -/
theorem u128_div_correct
    (a b q r : U128) (rest adv_rest : List Felt) (s : MidenState)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                    a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest)
    (hadv : s.advice = r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
                      q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val :: adv_rest) :
    execWithEnv u128ProcEnv 31 s Miden.Core.U128.div =
    some { stack := q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val :: rest,
           memory := s.memory,
           locals := s.locals,
           advice := adv_rest }
    ↔ (q.toNat * b.toNat + r.toNat = a.toNat ∧ r.toNat < b.toNat) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [] at hs hadv
  subst hs
  subst hadv
  constructor
  · intro hexec
    unfold Miden.Core.U128.div execWithEnv at hexec
    simp only [List.foldlM, u128ProcEnv] at hexec
    revert hexec
    cases h_dm : execWithEnv u128ProcEnv 30
      { stack := b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                   a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest,
        memory := mem,
        locals := locs,
        advice := r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
                  q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val :: adv_rest }
      Miden.Core.U128.divmod with
    | none =>
        simp [bind, Bind.bind, Option.bind]
    | some val =>
        intro _
        have h_dm_exec :
            exec 163
              { stack := b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                         a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest,
                memory := mem,
                locals := locs,
                advice := r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
                          q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val :: adv_rest }
              Miden.Core.U128.divmod = some val := by
          rw [← divmod_execWithEnv_eq_exec 30 _ (by decide)]
          exact h_dm
        exact u128_divmod_conditions_of_exec a b q r rest adv_rest _ rfl rfl h_dm_exec
  · intro ⟨hdiv, hlt⟩
    have h_divmod :
        exec 163
          { stack := b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                     a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest,
            memory := mem,
            locals := locs,
            advice := r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
                      q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val :: adv_rest }
          Miden.Core.U128.divmod =
        some { stack := r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
                         q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val :: rest,
               memory := mem,
               locals := locs,
               advice := adv_rest } :=
      (u128_divmod_correct a b q r rest adv_rest
        { stack := b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                   a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest,
          memory := mem,
          locals := locs,
          advice := r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
                    q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val :: adv_rest }
        rfl rfl).mpr ⟨hdiv, hlt⟩
    unfold Miden.Core.U128.div execWithEnv
    simp only [List.foldlM, u128ProcEnv]
    dsimp only [bind, Bind.bind, Option.bind]
    rw [divmod_execWithEnv_eq_exec 30 _ (by decide)]
    rw [h_divmod]
    miden_bind
    rw [stepDropw]
    rfl

end MidenLean.Proofs
