import MidenLean.Proofs.U256.Common
import MidenLean.Proofs.Tactics

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
theorem u256_u256_le_to_be_raw
    (x0 x1 x2 x3 x4 x5 x6 x7 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest)
    :
    exec 8 s Miden.Core.U256.u256_le_to_be =
    some (s.withStack (x7 :: x6 :: x5 :: x4 :: x3 :: x2 :: x1 :: x0 :: rest))
    := by
  miden_setup Miden.Core.U256.u256_le_to_be
  -- Instruction 1: reversew
  rw [stepReversew]; miden_bind
  -- Instruction 2: swapw 1
  rw [stepSwapw1]; miden_bind
  -- Instruction 3: reversew
  rw [stepReversew]; simp only [pure, Pure.pure]

/-- `u256::u256_le_to_be` reverses the order of eight stack elements.
    Input stack:  [a.a0, a.a1, a.a2, a.a3, a.a4, a.a5, a.a6, a.a7] ++ rest
    Output stack: [a.a7, a.a6, a.a5, a.a4, a.a3, a.a2, a.a1, a.a0] ++ rest -/
theorem u256_u256_le_to_be_correct (a : U256) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
                    a.a4.val :: a.a5.val :: a.a6.val :: a.a7.val :: rest) :
    exec 8 s Miden.Core.U256.u256_le_to_be =
    some (s.withStack (a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
                       a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: rest)) :=
  u256_u256_le_to_be_raw a.a0.val a.a1.val a.a2.val a.a3.val
    a.a4.val a.a5.val a.a6.val a.a7.val rest s hs

end MidenLean.Proofs
