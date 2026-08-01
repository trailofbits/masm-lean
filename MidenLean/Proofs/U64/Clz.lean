import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
private theorem u64_clz_exec_concrete (env : ProcEnv)
    (lo hi : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = lo :: hi :: rest)
    (hlo : lo.isU32 = true) (hhi : hi.isU32 = true) :
    execProcedure env 2 s Miden.Core.U64.clz =
    some (s.withStack (
      (if hi == (0 : Felt)
       then Felt.ofNat (u32CountLeadingZeros lo.val) + 32
       else Felt.ofNat (u32CountLeadingZeros hi.val)) :: rest)) := by
  miden_vcg
  all_goals miden_finish_reflection

/-- `u64::clz` raw: result in terms of u32CountLeadingZeros on individual limbs.
    Parametric in `env` and `fuel` (derived from the concrete-fuel proof by
    fuel monotonicity) so this lemma serves both as a callee summary for
    reflective callers and as the basis for `u64_clz_correct`. -/
@[miden_exec_summary]
theorem u64_clz_exec (env : ProcEnv) (fuel : Nat)
    (lo hi : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = lo :: hi :: rest)
    (hlo : lo.isU32 = true) (hhi : hi.isU32 = true) :
    execProcedure env (fuel + 2) s Miden.Core.U64.clz =
    some (s.withStack (
      (if hi == (0 : Felt)
       then Felt.ofNat (u32CountLeadingZeros lo.val) + 32
       else Felt.ofNat (u32CountLeadingZeros hi.val)) :: rest)) :=
  execProcedure_fuel_mono (by omega)
    (u64_clz_exec_concrete env lo hi rest s hs hlo hhi)

/-- `u64::clz` counts leading zeros of a u64 value.
    Input stack:  [a.lo, a.hi] ++ rest
    Output stack: [Felt.ofNat a.countLeadingZeros] ++ rest -/
theorem u64_clz_correct (a : U64) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a.lo.val :: a.hi.val :: rest) :
    execProcedure emptyEnv 20 s Miden.Core.U64.clz =
    some (s.withStack (Felt.ofNat a.countLeadingZeros :: rest)) := by
  have h := u64_clz_exec emptyEnv 18 a.lo.val a.hi.val rest s hs a.lo.isU32 a.hi.isU32
  unfold U64.countLeadingZeros
  by_cases hhi : a.hi.val.val = 0
  · rw [if_pos hhi, felt_ofNat_add]
    have : a.hi.val = (0 : Felt) := Fin.ext hhi
    simp only [this, beq_self_eq_true, ite_true] at h; exact h
  · rw [if_neg hhi]
    have : a.hi.val ≠ (0 : Felt) := fun heq => hhi (by rw [heq]; rfl)
    simp only [show (a.hi.val == (0 : Felt)) = false from decide_eq_false this] at h
    exact h

end MidenLean.Proofs
