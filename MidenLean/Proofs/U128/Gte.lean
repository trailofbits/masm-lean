import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.U128.Lt
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- `u128::gte` compares two u128 values (raw limb version).
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff `a ≥ b`, else 0. -/
@[miden_exec_summary]
theorem u128_gte_exec
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execProcedure u128ProcEnv 31 s Miden.Core.U128.gte =
    some (s.withStack ((if !(u128LtBool a0 a1 a2 a3 b0 b1 b2 b3) then (1 : Felt) else 0) :: rest)) := by
  miden_vcg

/-- `u128::gte` pushes 1 iff `b ≤ a` (i.e. `a ≥ b`).
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [(if b ≤ a then 1 else 0)] ++ rest -/
theorem u128_gte_correct (a b : U128) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest) :
    execProcedure u128ProcEnv 31 s Miden.Core.U128.gte =
    some (s.withStack (
      (if decide (b ≤ a) then (1 : Felt) else 0) :: rest)) := by
  rw [u128_gte_exec a.a0.val a.a1.val a.a2.val a.a3.val b.a0.val b.a1.val b.a2.val b.a3.val rest s hs
    a.a0.isU32 a.a1.isU32 a.a2.isU32 a.a3.isU32 b.a0.isU32 b.a1.isU32 b.a2.isU32 b.a3.isU32]
  simp only [u128LtBool_iff_lt a b]
  congr 1; congr 1; congr 1; congr 1
  cases h : decide (a < b) <;> simp_all

end MidenLean.Proofs
