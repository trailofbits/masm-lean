import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean

set_option maxHeartbeats 4000000 in
/-- `u64::eq` tests equality of two u64 values, limb by limb.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff b_lo == a_lo && b_hi == a_hi, else 0. -/
theorem u64_eq_exec (b_lo b_hi a_lo a_hi : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest) :
    execProcedure emptyEnv 10 s Miden.Core.U64.eq =
    some (s.withStack (
      (if (b_lo == a_lo) && (b_hi == a_hi)
       then (1 : Felt) else 0) :: rest)) := by
  miden_vcg
  all_goals miden_finish_reflection

/-- `u64::eq` tests equality of two u64 values.
    Input stack:  [b.lo, b.hi, a.lo, a.hi] ++ rest
    Output stack: [if a == b then 1 else 0] ++ rest -/
theorem u64_eq_correct (a b : U64) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest) :
    execProcedure emptyEnv 10 s Miden.Core.U64.eq =
    some (s.withStack (
      (if a == b then (1 : Felt) else 0) :: rest)) := by
  have h := u64_eq_exec b.lo.val b.hi.val a.lo.val a.hi.val rest s hs
  rw [U64.beq_comm a b]; exact h

end MidenLean.Proofs
