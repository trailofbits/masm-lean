import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- `u64::clo` raw: result in terms of u32CountLeadingZeros on complemented limbs. -/
theorem u64_clo_exec (lo hi : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = lo :: hi :: rest)
    (hlo : lo.isU32 = true) (hhi : hi.isU32 = true) :
    execProcedure emptyEnv 20 s Miden.Core.U64.clo =
    some (s.withStack (
      (if hi == (4294967295 : Felt)
       then Felt.ofNat (u32CountLeadingZeros (u32Max - 1 - lo.val)) + 32
       else Felt.ofNat (u32CountLeadingZeros (u32Max - 1 - hi.val))) :: rest)) := by
  miden_vcg
  all_goals miden_finish_reflection

/-- `u64::clo` counts leading ones of a u64 value.
    Input stack:  [a.lo, a.hi] ++ rest
    Output stack: [Felt.ofNat a.countLeadingOnes] ++ rest -/
theorem u64_clo_correct (a : U64) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a.lo.val :: a.hi.val :: rest) :
    execProcedure emptyEnv 20 s Miden.Core.U64.clo =
    some (s.withStack (Felt.ofNat a.countLeadingOnes :: rest)) := by
  have h := u64_clo_exec a.lo.val a.hi.val rest s hs a.lo.isU32 a.hi.isU32
  unfold U64.countLeadingOnes u32CountLeadingOnes
  by_cases hhi : a.hi.val.val = 2^32 - 1
  · rw [if_pos hhi, felt_ofNat_add]
    have : a.hi.val = (4294967295 : Felt) := Fin.ext (by simpa using hhi)
    simp only [this, beq_self_eq_true, ite_true] at h; exact h
  · rw [if_neg hhi]
    have : a.hi.val ≠ (4294967295 : Felt) := fun heq => hhi (by
      have := congrArg ZMod.val heq; simpa using this)
    simp only [show (a.hi.val == (4294967295 : Felt)) = false from decide_eq_false this] at h
    exact h

end MidenLean.Proofs
