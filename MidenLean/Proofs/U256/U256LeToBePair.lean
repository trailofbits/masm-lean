import MidenLean.Proofs.U256.Common
import MidenLean.Proofs.U256.U256LeToBe
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- u256_le_to_be helper for execProcedure context
-- ============================================================================

theorem le_to_be_env (fuel : Nat)
    (x0 x1 x2 x3 x4 x5 x6 x7 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execProcedure u256ProcEnv (fuel + 1)
      ⟨x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest, mem, frames, adv⟩
      Miden.Core.U256.u256_le_to_be =
    some ⟨x7 :: x6 :: x5 :: x4 :: x3 :: x2 :: x1 :: x0 :: rest, mem, frames, adv⟩ := by
  unfold Miden.Core.U256.u256_le_to_be execProcedure Procedure.ofOps
  simp only [List.foldlM]
  rw [stepReversew]; miden_bind
  rw [stepSwapw1]; miden_bind
  rw [stepReversew]
  simp only [pure, Pure.pure]

-- ============================================================================
-- Main theorems
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- `u256::u256_le_to_be_pair` reverses each of the two 8-element groups on the
    stack (raw limb version).
    Input stack:  [x0, ..., x7, y0, ..., y7] ++ rest
    Output stack: [x7, ..., x0, y7, ..., y0] ++ rest
    Parametric in `fuel` so this lemma serves both as a callee summary for
    reflective callers and as the basis for `u256_u256_le_to_be_pair_correct`. -/
@[miden_exec_summary]
theorem u256_u256_le_to_be_pair_exec (fuel : Nat)
    (x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 : Felt)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt) :
    execProcedure u256ProcEnv (fuel + 2)
      ⟨x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 ::
       y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: y7 :: rest, mem, frames, adv⟩
      Miden.Core.U256.u256_le_to_be_pair =
    some ⟨x7 :: x6 :: x5 :: x4 :: x3 :: x2 :: x1 :: x0 ::
          y7 :: y6 :: y5 :: y4 :: y3 :: y2 :: y1 :: y0 :: rest, mem, frames, adv⟩ := by
  miden_vcg

/-- `u256::u256_le_to_be_pair` reverses each of the two 8-element groups on the stack.
    Input stack:  [x0, ..., x7, y0, ..., y7] ++ rest
    Output stack: [x7, ..., x0, y7, ..., y0] ++ rest -/
theorem u256_u256_le_to_be_pair_correct (fuel : Nat) (a b : U256)
    (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                    b.a4.val :: b.a5.val :: b.a6.val :: b.a7.val ::
                    a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
                    a.a4.val :: a.a5.val :: a.a6.val :: a.a7.val :: rest) :
    execProcedure u256ProcEnv (fuel + 2) s Miden.Core.U256.u256_le_to_be_pair =
    some { stack := b.a7.val :: b.a6.val :: b.a5.val :: b.a4.val ::
                    b.a3.val :: b.a2.val :: b.a1.val :: b.a0.val ::
                    a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
                    a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: rest,
           memory := s.memory, frames := s.frames, advice := s.advice } := by
  obtain ⟨stk, mem, frames, adv⟩ := s
  subst hs
  exact u256_u256_le_to_be_pair_exec fuel
    b.a0.val b.a1.val b.a2.val b.a3.val b.a4.val b.a5.val b.a6.val b.a7.val
    a.a0.val a.a1.val a.a2.val a.a3.val a.a4.val a.a5.val a.a6.val a.a7.val
    rest mem frames adv

end MidenLean.Proofs
