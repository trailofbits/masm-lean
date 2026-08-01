import MidenLean.Proofs.U256.Common
import MidenLean.Proofs.U256.U256LeToBePair
import MidenLean.Proofs.U256.SubWithBorrowBe
import MidenLean.Proofs.StepLemmas

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas

set_option maxHeartbeats 4000000 in
/-- `u256::wrapping_sub` computes `(a - b) mod 2^256` for two 256-bit values.
    Input stack:  [b.a0, ..., b.a7, a.a0, ..., a.a7] ++ rest  (little-endian limbs)
    Output stack: [(a-b).a0, ..., (a-b).a7] ++ rest -/
theorem u256_wrapping_sub_correct
    (a b : U256) (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) :
    execProcedure u256ProcEnv (fuel + 3)
      ⟨b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
       b.a4.val :: b.a5.val :: b.a6.val :: b.a7.val ::
       a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
       a.a4.val :: a.a5.val :: a.a6.val :: a.a7.val :: rest, mem, frames, adv⟩
      Miden.Core.U256.wrapping_sub =
    some ⟨(a - b).a0.val :: (a - b).a1.val :: (a - b).a2.val :: (a - b).a3.val ::
          (a - b).a4.val :: (a - b).a5.val :: (a - b).a6.val :: (a - b).a7.val :: rest,
          mem, frames, adv⟩ := by
  -- Unfold procedure body
  unfold Miden.Core.U256.wrapping_sub execProcedure
  simp only [List.foldlM, u256ProcEnv]
  -- Step 1: execProcedure emptyEnv "u256_le_to_be_pair" (convert LE → BE)
  dsimp only [bind, Bind.bind, Option.bind]
  rw [u256_u256_le_to_be_pair_raw]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 2: execProcedure emptyEnv "sub_with_borrow_be"
  rw [u256_sub_with_borrow_be_correct]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 3: drop (discard borrow)
  rw [stepDrop]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 4: execProcedure emptyEnv "u256_le_to_be" (convert BE → LE)
  rw [le_to_be_env]
  simp only [pure, Pure.pure]

end MidenLean.Proofs
