import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- `u64::gt` compares two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff a > b (as u64), else 0.
    The comparison is: b_hi < a_hi, or (b_hi == a_hi and b_lo < a_lo).
    Parametric in `env` and `fuel` so this lemma serves both as a callee
    summary for reflective callers and as the basis for `u64_gt_correct`. -/
@[miden_exec_summary]
theorem u64_gt_exec
    (env : ProcEnv) (fuel : Nat)
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    execProcedure env (fuel + 1) s Miden.Core.U64.gt =
    some (s.withStack (
      let borrow_lo := decide (b_lo.val < a_lo.val)
      let borrow_hi := decide (b_hi.val < a_hi.val)
      let hi_eq := Felt.ofNat (u32OverflowingSub b_hi.val a_hi.val).2 == (0 : Felt)
      (if borrow_hi || (hi_eq && borrow_lo) then (1 : Felt) else 0) :: rest)) := by
  miden_vcg
  all_goals miden_finish_reflection

/-- `u64::gt` pushes 1 iff `a > b` (as u64).
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [(if b < a then 1 else 0)] ++ rest -/
theorem u64_gt_correct (a b : U64) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest) :
    execProcedure emptyEnv 20 s Miden.Core.U64.gt =
    some (s.withStack (
      (if decide (b < a) then (1 : Felt) else 0) :: rest)) := by
  rw [u64_gt_exec emptyEnv 19 a.lo.val a.hi.val b.lo.val b.hi.val rest s hs a.lo.isU32 a.hi.isU32 b.lo.isU32 b.hi.isU32]
  simp only [u64_borrow_iff_lt b a]; rfl

end MidenLean.Proofs
