import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.U128.Divmod
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 12000000 in
/-- Success summary for `u128::mod`: given a valid advice-supplied quotient and
    remainder, the procedure returns the remainder limbs and consumes the advice.
    Input stack:  [b.a0, b.a1, b.a2, b.a3, a.a0, a.a1, a.a2, a.a3] ++ rest
    Advice stack: [r.a0, r.a1, r.a2, r.a3, q.a0, q.a1, q.a2, q.a3] ++ adv_rest
    Output stack: [r.a0, r.a1, r.a2, r.a3] ++ rest
    Parametric in `fuel` so this lemma serves both as a callee summary for
    reflective callers and as the success direction of `u128_mod_correct`. -/
@[miden_exec_summary]
theorem u128_mod_exec (fuel : Nat)
    (a b q r : U128) (rest adv_rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                    a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest)
    (hadv : s.advice = r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
                      q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val :: adv_rest)
    (hdiv : q.toNat * b.toNat + r.toNat = a.toNat) (hlt : r.toNat < b.toNat) :
    execProcedure u128ProcEnv (fuel + 2) s Miden.Core.U128.mod =
    some { stack := r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val :: rest,
           memory := s.memory,
           frames := s.frames,
           advice := adv_rest } := by
  miden_vcg

set_option maxHeartbeats 12000000 in
/-- `u128::mod` verifies an advice-supplied quotient and remainder for u128 division,
    then keeps only the remainder limbs.
    Execution succeeds iff the advice-supplied q and r satisfy q * b + r = a and r < b.
    Input stack:  [b.a0, b.a1, b.a2, b.a3, a.a0, a.a1, a.a2, a.a3] ++ rest
    Advice stack: [r.a0, r.a1, r.a2, r.a3, q.a0, q.a1, q.a2, q.a3] ++ adv_rest
    Output stack: [r.a0, r.a1, r.a2, r.a3] ++ rest -/
theorem u128_mod_correct
    (a b q r : U128) (rest adv_rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                    a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest)
    (hadv : s.advice = r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
                      q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val :: adv_rest) :
    execProcedure u128ProcEnv 34 s Miden.Core.U128.mod =
    some { stack := r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val :: rest,
           memory := s.memory,
           frames := s.frames,
           advice := adv_rest }
    ↔ (q.toNat * b.toNat + r.toNat = a.toNat ∧ r.toNat < b.toNat) := by
  obtain ⟨stk, mem, frames, adv⟩ := s
  simp only [] at hs hadv
  subst hs
  subst hadv
  constructor
  · intro hexec
    unfold Miden.Core.U128.mod execProcedure at hexec
    simp only [List.foldlM, u128ProcEnv] at hexec
    revert hexec
    cases h_dm : execProcedure u128ProcEnv 33
      { stack := b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                   a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest,
        memory := mem,
        frames := frames,
        advice := r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
                  q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val :: adv_rest }
      Miden.Core.U128.divmod with
    | none =>
        simp [bind, Bind.bind, Option.bind]
    | some val =>
        intro _
        have h_dm_exec :
            execProcedure emptyEnv 163
              { stack := b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                         a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest,
                memory := mem,
                frames := frames,
                advice := r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
                          q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val :: adv_rest }
              Miden.Core.U128.divmod = some val := by
          rw [← u128_divmod_execProcedure_eq 33 _ (by decide)]
          exact h_dm
        exact u128_divmod_conditions_of_exec a b q r rest adv_rest _ rfl rfl h_dm_exec
  · intro ⟨hdiv, hlt⟩
    exact u128_mod_exec 32 a b q r rest adv_rest _ rfl rfl hdiv hlt

end MidenLean.Proofs
