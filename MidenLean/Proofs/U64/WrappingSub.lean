import MidenLean.Proofs.U64.Common
import MidenLean.Symbolic.Tactic

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- `u64::wrapping_sub` computes wrapping subtraction of two u64 values.
    Parametric in `env` and `fuel` so this lemma serves both as a callee
    summary for reflective callers and as the basis for `u64_wrapping_sub_correct`. -/
@[miden_exec_summary]
theorem u64_wrapping_sub_exec
    (env : ProcEnv) (fuel : Nat)
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    execProcedure env (fuel + 1) s Miden.Core.U64.wrapping_sub =
    some (s.withStack (
      let sub_lo := u32OverflowingSub a_lo.val b_lo.val
      let sub_hi := u32OverflowingSub a_hi.val b_hi.val
      let sub_final := u32OverflowingSub sub_hi.2 sub_lo.1
      Felt.ofNat sub_lo.2 :: Felt.ofNat sub_final.2 :: rest)) := by
  miden_vcg

/-- `u64::wrapping_sub` computes `a - b` as a u64 value.
    Input stack:  [b.lo, b.hi, a.lo, a.hi] ++ rest
    Output stack: [(a - b).lo, (a - b).hi] ++ rest -/
theorem u64_wrapping_sub_correct (a b : U64) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest) :
    execProcedure emptyEnv 20 s Miden.Core.U64.wrapping_sub =
    some (s.withStack ((a - b).lo.val :: (a - b).hi.val :: rest)) := by
  have h := u64_wrapping_sub_exec emptyEnv 19 a.lo.val a.hi.val b.lo.val b.hi.val rest s hs a.lo.isU32 a.hi.isU32 b.lo.isU32 b.hi.isU32
  have ⟨hlo, hhi⟩ := u64_sub_limbs_felt a b
  rw [h]; simp only [hlo, hhi]

end MidenLean.Proofs
