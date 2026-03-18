import MidenLean.Proofs.U64
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- Classification: MANUAL | Instructions: 50 | Inputs: 4 | Calls: true | Branches: false | Loops: false | Advice: true
set_option maxHeartbeats 8000000 in
/-- u64.divmod: (auto-generated skeleton)
    Input stack:  [a, b, c, d] ++ rest
    Output stack: [sorry] ++ rest -/
theorem u64_divmod_correct
    (a b c d : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: b :: c :: d :: rest)
    (v0 v1 v2 v3 : Felt) (adv_rest : List Felt)
    (hadv : s.advice = v0 :: v1 :: v2 :: v3 :: adv_rest)
    (hc_u32 : c.isU32 = true)  -- from u32WidenMadd at instruction 9
    (hd_u32 : d.isU32 = true)  -- from u32WidenMul at instruction 5
    :
    execWithEnv u64ProcEnv 175 s Miden.Core.U64.divmod =
    some (s.withStack (sorry :: rest))  -- TODO: specify output
    := by
  miden_setup_env Miden.Core.U64.divmod
  subst hadv
  -- Instruction 1: emitImm
  miden_step
  -- Instruction 2: advPush (requires hypothesis)
  miden_step
  -- Instruction 3: u32Assert2 (requires hypothesis)
  miden_step
  -- Instruction 4: dup 2
  miden_step
  -- Instruction 5: dup 1
  miden_step
  -- Instruction 6: u32WidenMul (requires hypothesis)
  miden_step
  -- Instruction 7: swap 1
  miden_step
  -- Instruction 8: dup 5
  miden_step
  -- Instruction 9: dup 3
  miden_step
  -- Instruction 10: u32WidenMadd (requires hypothesis)
  miden_step
  -- Instruction 11: swap 1
  miden_step
  -- Instruction 12: eqImm
  miden_step
  -- Instruction 13: assertWithError (requires hypothesis)
  miden_step
  -- Instruction 14: dup 4
  miden_step
  -- Instruction 15: dup 4
  miden_step
  -- Instruction 16: u32WidenMadd (requires hypothesis)
  miden_step
  -- Instruction 17: swap 1
  miden_step
  -- Instruction 18: eqImm
  miden_step
  -- Instruction 19: assertWithError (requires hypothesis)
  miden_step
  -- Instruction 20: dup 5
  miden_step
  -- Instruction 21: dup 4
  miden_step
  -- Instruction 22: mul
  miden_step
  -- Instruction 23: eqImm
  miden_step
  -- Instruction 24: assertWithError (requires hypothesis)
  miden_step
  -- Instruction 25: advPush (requires hypothesis)
  miden_step
  -- Instruction 26: u32Assert2 (requires hypothesis)
  miden_step
  -- Instruction 27: movup 6
  miden_step
  -- Instruction 28: movup 7
  miden_step
  -- Instruction 29: swap 1
  miden_step
  -- Instruction 30: dup 3
  miden_step
  -- Instruction 31: dup 3
  miden_step
  -- Instruction 32: movup 3
  miden_step
  -- Instruction 33: movup 3
  miden_step
  -- Instruction 34: exec "lt"
  simp only [u64ProcEnv]
  miden_call Miden.Core.U64.lt
  -- Instruction 35: assertWithError (requires hypothesis)
  miden_step
  -- Instruction 36: dup 0
  miden_step
  -- Instruction 37: movup 4
  miden_step
  -- Instruction 38: u32WidenAdd (requires hypothesis)
  miden_step
  -- Instruction 39: swap 1
  miden_step
  -- Instruction 40: dup 3
  miden_step
  -- Instruction 41: movup 5
  miden_step
  -- Instruction 42: movup 2
  miden_step
  -- Instruction 43: u32WidenAdd3 (requires hypothesis)
  miden_step
  -- Instruction 44: swap 1
  miden_step
  -- Instruction 45: eqImm
  miden_step
  -- Instruction 46: assertWithError (requires hypothesis)
  miden_step
  -- Instruction 47: movup 7
  miden_step
  -- Instruction 48: assertEqWithError
  miden_step
  -- Instruction 49: movup 5
  miden_step
  -- Instruction 50: assertEqWithError
  miden_step
  -- TODO: value recovery / remaining goals
  sorry

end MidenLean.Proofs
