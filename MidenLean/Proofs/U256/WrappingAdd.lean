import MidenLean.Proofs.U256.Common
import MidenLean.Proofs.U256.U256LeToBe
import MidenLean.Proofs.U256.U256LeToBePair
import MidenLean.Proofs.U256.AddWithCarryBe
import MidenLean.Symbolic.Tactic

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `u256::wrapping_add` computes `(a + b) mod 2^256` for two 256-bit values.
    Input stack:  [b.a0, ..., b.a7, a.a0, ..., a.a7] ++ rest  (little-endian limbs)
    Output stack: [(a+b).a0, ..., (a+b).a7] ++ rest -/
theorem u256_wrapping_add_correct
    (a b : U256) (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) :
    execProcedure u256ProcEnv (fuel + 3)
      ⟨b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
       b.a4.val :: b.a5.val :: b.a6.val :: b.a7.val ::
       a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
       a.a4.val :: a.a5.val :: a.a6.val :: a.a7.val :: rest, mem, frames, adv⟩
      Miden.Core.U256.wrapping_add =
    some ⟨(a + b).a0.val :: (a + b).a1.val :: (a + b).a2.val :: (a + b).a3.val ::
          (a + b).a4.val :: (a + b).a5.val :: (a + b).a6.val :: (a + b).a7.val :: rest,
          mem, frames, adv⟩ := by
  miden_vcg
  all_goals simp only [HAdd.hAdd, Add.add, U256.ofNat_a0, U256.ofNat_a1, U256.ofNat_a2,
    U256.ofNat_a3, U256.ofNat_a4, U256.ofNat_a5, U256.ofNat_a6, U256.ofNat_a7]
  all_goals norm_num

end MidenLean.Proofs
