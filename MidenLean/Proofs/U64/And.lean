import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `u64::and` computes bitwise AND of two u64 values, limb by limb.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [b_lo &&& a_lo, b_hi &&& a_hi] ++ rest -/
theorem u64_and_exec
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    execProcedure emptyEnv 10 s Miden.Core.U64.and =
    some (s.withStack (
      Felt.ofNat (b_lo.val &&& a_lo.val) ::
      Felt.ofNat (b_hi.val &&& a_hi.val) :: rest)) := by
  miden_vcg
  all_goals miden_finish_reflection

/-- `u64::and` computes bitwise AND of two u64 values.
    Input stack:  [b.lo, b.hi, a.lo, a.hi] ++ rest
    Output stack: [(a &&& b).lo, (a &&& b).hi] ++ rest -/
theorem u64_and_correct (a b : U64) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest) :
    execProcedure emptyEnv 10 s Miden.Core.U64.and =
    some (s.withStack ((a &&& b).lo.val :: (a &&& b).hi.val :: rest)) := by
  simp only [U64.and_lo, U64.and_hi, Nat.and_comm a.lo.val.val, Nat.and_comm a.hi.val.val]
  exact u64_and_exec a.lo.val a.hi.val b.lo.val b.hi.val rest s hs a.lo.isU32 a.hi.isU32 b.lo.isU32 b.hi.isU32

end MidenLean.Proofs
