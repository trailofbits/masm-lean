import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- `u64::ctz` raw: result in terms of u32CountTrailingZeros on individual limbs. -/
theorem u64_ctz_exec (lo hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = lo :: hi :: rest)
    (hlo : lo.isU32 = true) (hhi : hi.isU32 = true) :
    exec 20 s Miden.Core.U64.ctz =
    some (s.withStack (
      (if lo == (0 : Felt)
       then Felt.ofNat (u32CountTrailingZeros hi.val) + 32
       else Felt.ofNat (u32CountTrailingZeros lo.val)) :: rest)) := by
  miden_vcg
  all_goals miden_finish_reflection

/-- `u64::ctz` counts trailing zeros of a u64 value.
    Input stack:  [a.lo, a.hi] ++ rest
    Output stack: [Felt.ofNat a.countTrailingZeros] ++ rest -/
theorem u64_ctz_correct (a : U64) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a.lo.val :: a.hi.val :: rest) :
    exec 20 s Miden.Core.U64.ctz =
    some (s.withStack (Felt.ofNat a.countTrailingZeros :: rest)) := by
  have h := u64_ctz_exec a.lo.val a.hi.val rest s hs a.lo.isU32 a.hi.isU32
  unfold U64.countTrailingZeros
  by_cases hlo : a.lo.val.val = 0
  · rw [if_pos hlo, felt_ofNat_add]
    have : a.lo.val = (0 : Felt) := Fin.ext hlo
    simp only [this, beq_self_eq_true, ite_true] at h; exact h
  · rw [if_neg hlo]
    have : a.lo.val ≠ (0 : Felt) := fun heq => hlo (by rw [heq]; rfl)
    simp only [show (a.lo.val == (0 : Felt)) = false from decide_eq_false this] at h
    exact h

end MidenLean.Proofs
