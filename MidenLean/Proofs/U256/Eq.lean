import MidenLean.Proofs.U256.U256LeToBePair
import MidenLean.Proofs.Tactics

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Helper step lemmas
-- ============================================================================

-- ============================================================================
-- Main theorems
-- ============================================================================

set_option maxHeartbeats 8000000 in
theorem u256_eq_raw (fuel : Nat)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Felt)
    (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
                    a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest) :
    execProcedure u256ProcEnv (fuel + 3) s Miden.Core.U256.eq =
    some (s.withStack (
      (if ((b3 == a3) && (b2 == a2) && (b1 == a1) && (b0 == a0)) &&
          ((b7 == a7) && (b6 == a6) && (b5 == a5) && (b4 == a4))
       then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, frames, adv⟩ := s
  simp only [Concrete.State.withStack] at hs ⊢
  subst hs
  -- Unfold procedure and resolve env
  unfold Miden.Core.U256.eq execProcedure
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- execProcedure emptyEnv "u256_le_to_be_pair"
  rw [u256_u256_le_to_be_pair_raw]
  dsimp only [bind, Bind.bind, Option.bind]
  -- swapw 3
  rw [stepSwapw3]; miden_bind
  -- eqw (lower limbs)
  rw [stepEqw]; miden_bind
  -- movdn 8
  rw [stepMovdn8]; miden_bind
  -- dropw, dropw
  rw [stepDropw]; miden_bind
  rw [stepDropw]; miden_bind
  -- movdn 8
  rw [stepMovdn8]; miden_bind
  -- eqw (upper limbs)
  rw [stepEqw]; miden_bind
  -- movdn 8
  rw [stepMovdn8]; miden_bind
  -- dropw, dropw
  rw [stepDropw]; miden_bind
  rw [stepDropw]; miden_bind
  -- and
  rw [stepAndIte]
  simp only [pure, Pure.pure]

/-- `u256::eq` tests equality of two 256-bit values.
    Input stack:  [b.a0, b.a1, ..., b.a7, a.a0, a.a1, ..., a.a7] ++ rest
    Output stack: [result] ++ rest
    where result = 1 if a = b, otherwise 0. -/
theorem u256_eq_correct (fuel : Nat) (a b : U256) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                    b.a4.val :: b.a5.val :: b.a6.val :: b.a7.val ::
                    a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
                    a.a4.val :: a.a5.val :: a.a6.val :: a.a7.val :: rest) :
    execProcedure u256ProcEnv (fuel + 3) s Miden.Core.U256.eq =
    some (s.withStack (
      (if a == b then (1 : Felt) else 0) :: rest)) := by
  rw [u256_eq_raw fuel a.a0.val a.a1.val a.a2.val a.a3.val
    a.a4.val a.a5.val a.a6.val a.a7.val
    b.a0.val b.a1.val b.a2.val b.a3.val
    b.a4.val b.a5.val b.a6.val b.a7.val rest s hs]
  congr 1; congr 1; congr 1
  simp only [U256.beq_iff, Bool.beq_comm (a := a.a0.val), Bool.beq_comm (a := a.a1.val),
    Bool.beq_comm (a := a.a2.val), Bool.beq_comm (a := a.a3.val),
    Bool.beq_comm (a := a.a4.val), Bool.beq_comm (a := a.a5.val),
    Bool.beq_comm (a := a.a6.val), Bool.beq_comm (a := a.a7.val)]
  simp only [Bool.and_assoc]
  ac_rfl

end MidenLean.Proofs
