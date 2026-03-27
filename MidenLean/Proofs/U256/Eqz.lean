import MidenLean.Proofs.U256.Common
import MidenLean.Proofs.Tactics

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
theorem u256_eqz_raw
    (x0 x1 x2 x3 x4 x5 x6 x7 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest)
    :
    exec 37 s Miden.Core.U256.eqz =
    some (s.withStack (
      (if (x0 == (0 : Felt)) && (x1 == (0 : Felt)) && (x2 == (0 : Felt)) &&
          (x3 == (0 : Felt)) && (x4 == (0 : Felt)) && (x5 == (0 : Felt)) &&
          (x6 == (0 : Felt)) && (x7 == (0 : Felt))
       then (1 : Felt) else 0) :: rest))
    := by
  miden_setup Miden.Core.U256.eqz
  -- Instruction 1: eqImm 0
  rw [stepEqImm]; miden_bind
  -- repeat iteration 1/7
  miden_loop
  -- Instruction 2: swap 1
  miden_step
  -- Instruction 3: eqImm 0
  rw [stepEqImm]; miden_bind
  -- Instruction 4: and
  rw [stepAndIte]; miden_bind
  miden_loop
  -- Instruction 5: swap 1
  miden_step
  -- Instruction 6: eqImm 0
  rw [stepEqImm]; miden_bind
  -- Instruction 7: and
  rw [stepAndIte]; miden_bind
  miden_loop
  -- Instruction 8: swap 1
  miden_step
  -- Instruction 9: eqImm 0
  rw [stepEqImm]; miden_bind
  -- Instruction 10: and
  rw [stepAndIte]; miden_bind
  miden_loop
  -- Instruction 11: swap 1
  miden_step
  -- Instruction 12: eqImm 0
  rw [stepEqImm]; miden_bind
  -- Instruction 13: and
  rw [stepAndIte]; miden_bind
  miden_loop
  -- Instruction 14: swap 1
  miden_step
  -- Instruction 15: eqImm 0
  rw [stepEqImm]; miden_bind
  -- Instruction 16: and
  rw [stepAndIte]; miden_bind
  miden_loop
  -- Instruction 17: swap 1
  miden_step
  -- Instruction 18: eqImm 0
  rw [stepEqImm]; miden_bind
  -- Instruction 19: and
  rw [stepAndIte]; miden_bind
  miden_loop
  -- Instruction 20: swap 1
  miden_step
  -- Instruction 21: eqImm 0
  rw [stepEqImm]; miden_bind
  -- Instruction 22: and
  rw [stepAndIte]
  -- Base case of repeat
  miden_loop
  simp only [pure, Pure.pure]

/-- `u256::eqz` tests whether a u256 value equals zero.
    Input stack:  [a.a0, a.a1, a.a2, a.a3, a.a4, a.a5, a.a6, a.a7] ++ rest
    Output stack: [result] ++ rest
    where result = 1 if all limbs equal 0, otherwise 0. -/
theorem u256_eqz_correct (a : U256) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
                    a.a4.val :: a.a5.val :: a.a6.val :: a.a7.val :: rest) :
    exec 37 s Miden.Core.U256.eqz =
    some (s.withStack (
      (if a == U256.ofNat 0 then (1 : Felt) else 0) :: rest)) := by
  simp only [U256.beq_iff, U256.ofNat]
  exact u256_eqz_raw a.a0.val a.a1.val a.a2.val a.a3.val
    a.a4.val a.a5.val a.a6.val a.a7.val rest s hs

end MidenLean.Proofs
