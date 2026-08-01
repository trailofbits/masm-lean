import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `u64::xor` computes bitwise XOR of two u64 values, limb by limb.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [b_lo ^^^ a_lo, b_hi ^^^ a_hi] ++ rest
    Parametric in `env` and `fuel` so this lemma serves both as a callee
    summary for reflective callers and as the basis for `u64_xor_correct`. -/
@[miden_exec_summary]
theorem u64_xor_exec
    (env : ProcEnv) (fuel : Nat)
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    execProcedure env (fuel + 1) s Miden.Core.U64.xor =
    some (s.withStack (
      Felt.ofNat (b_lo.val ^^^ a_lo.val) ::
      Felt.ofNat (b_hi.val ^^^ a_hi.val) :: rest)) := by
  miden_vcg

/-- `u64::xor` computes bitwise XOR of two u64 values.
    Input stack:  [b.lo, b.hi, a.lo, a.hi] ++ rest
    Output stack: [(a ^^^ b).lo, (a ^^^ b).hi] ++ rest -/
theorem u64_xor_correct (a b : U64) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest) :
    execProcedure emptyEnv 10 s Miden.Core.U64.xor =
    some (s.withStack ((a ^^^ b).lo.val :: (a ^^^ b).hi.val :: rest)) := by
  simp only [U64.xor_lo, U64.xor_hi, Nat.xor_comm a.lo.val.val, Nat.xor_comm a.hi.val.val]
  exact u64_xor_exec emptyEnv 9 a.lo.val a.hi.val b.lo.val b.hi.val rest s hs a.lo.isU32 a.hi.isU32 b.lo.isU32 b.hi.isU32

end MidenLean.Proofs
