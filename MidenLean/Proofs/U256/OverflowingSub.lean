import MidenLean.Proofs.U256.Common
import MidenLean.Proofs.U256.U256LeToBePair
import MidenLean.Proofs.U256.SubWithBorrowBe
import MidenLean.Proofs.Tactics

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Helper step lemmas (reused from OverflowingAdd)
-- ============================================================================

private theorem stepMovdn8 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Felt) (rest : List Felt) :
    execInstruction ⟨a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: rest, mem, frames, adv⟩
      (.movdn 8) =
    some ⟨a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a0 :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execMovdn; simp [MidenState.withStack]; rfl

private theorem stepMovup8 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Felt) (rest : List Felt) :
    execInstruction ⟨a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: rest, mem, frames, adv⟩
      (.movup 8) =
    some ⟨a8 :: a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execMovup removeNth; simp [MidenState.withStack]

-- ============================================================================
-- Main theorem
-- ============================================================================

set_option maxHeartbeats 4000000 in
/-- `u256::overflowing_sub` computes `a - b` with underflow flag for two 256-bit values.
    Input stack:  [b.a0, ..., b.a7, a.a0, ..., a.a7] ++ rest  (little-endian limbs)
    Output stack: [underflow, (a-b).a0, ..., (a-b).a7] ++ rest
    where underflow = 1 - (a.toNat + 2^256 - b.toNat) / 2^256  (0 if a >= b, 1 if a < b). -/
theorem u256_overflowing_sub_correct
    (a b : U256) (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) :
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
       b.a4.val :: b.a5.val :: b.a6.val :: b.a7.val ::
       a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
       a.a4.val :: a.a5.val :: a.a6.val :: a.a7.val :: rest, mem, frames, adv⟩
      Miden.Core.U256.overflowing_sub =
    some ⟨Felt.ofNat (1 - (a.toNat + 2^256 - b.toNat) / 2^256) ::
          (a - b).a0.val :: (a - b).a1.val :: (a - b).a2.val :: (a - b).a3.val ::
          (a - b).a4.val :: (a - b).a5.val :: (a - b).a6.val :: (a - b).a7.val :: rest,
          mem, frames, adv⟩ := by
  -- Unfold procedure body
  unfold Miden.Core.U256.overflowing_sub execWithEnv
  simp only [List.foldlM, u256ProcEnv]
  -- Step 1: exec "u256_le_to_be_pair" (convert LE → BE)
  dsimp only [bind, Bind.bind, Option.bind]
  rw [u256_u256_le_to_be_pair_raw]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 2: exec "sub_with_borrow_be"
  rw [u256_sub_with_borrow_be_correct]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 3: movdn 8 (move borrow below result limbs)
  rw [stepMovdn8]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 4: exec "u256_le_to_be" (convert BE → LE)
  rw [le_to_be_env]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 5: movup 8 (bring borrow to top)
  rw [stepMovup8]
  simp only [pure, Pure.pure]

end MidenLean.Proofs
