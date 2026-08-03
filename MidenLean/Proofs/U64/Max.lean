import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.U64.Lt
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

-- Based on generated skeleton: SEMI | Instructions: 10 | Calls: true (lt)
set_option maxHeartbeats 16000000 in
/-- `u64::max` computes the maximum of two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [max_lo, max_hi] ++ rest
    lt is called on [a_lo, a_hi, b_lo, b_hi], computing b < a.
    If b < a, returns a; otherwise returns b.
    Parametric in `fuel` so this lemma serves both as a callee summary for
    reflective callers and as the basis for `u64_max_correct`. -/
@[miden_exec_summary]
theorem u64_max_exec
    (fuel : Nat)
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    execProcedure u64ProcEnv (fuel + 2) s Miden.Core.U64.max =
    some (s.withStack (
      let borrow_lo := decide (b_lo.val < a_lo.val)
      let borrow_hi := decide (b_hi.val < a_hi.val)
      let hi_eq := Felt.ofNat (u32OverflowingSub b_hi.val a_hi.val).2 == (0 : Felt)
      let is_lt := borrow_hi || (hi_eq && borrow_lo)
      (if is_lt then a_lo else b_lo) ::
      (if is_lt then a_hi else b_hi) :: rest)) := by
  miden_vcg
  all_goals simp only [Symbolic.Expr.eval] at *
  -- Both branches are vacuous: the `cdrop` selector agrees with the `lt` result.
  · rename_i h
    refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩ <;> exfalso <;>
      rcases h with h | ⟨heq, hlt⟩
    · omega
    · exact (h2 hlt) heq
    · omega
    · exact (h2 hlt) heq
  · rename_i h
    obtain ⟨hhi, hlo⟩ := h
    refine ⟨fun hc => ?_, fun hc => ?_⟩ <;> exfalso <;>
      rcases hc with hc | ⟨hlt, heq⟩
    · omega
    · have := hlo heq; omega
    · omega
    · have := hlo heq; omega

/-- `u64::max` intermediate: uses `decide (b < a)` on individual limbs. -/
theorem u64_max_ite (a b : U64) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest) :
    execProcedure u64ProcEnv 20 s Miden.Core.U64.max =
    some (s.withStack (
      (if decide (b < a) then a.lo.val else b.lo.val) ::
      (if decide (b < a) then a.hi.val else b.hi.val) :: rest)) := by
  rw [u64_max_exec 18 a.lo.val a.hi.val b.lo.val b.hi.val rest s hs a.lo.isU32 a.hi.isU32 b.lo.isU32 b.hi.isU32]
  simp only [u64_borrow_iff_lt b a]; rfl

/-- `u64::max` computes the maximum of two u64 values.
    Input stack:  [b.lo, b.hi, a.lo, a.hi] ++ rest
    Output stack: [(max a b).lo, (max a b).hi] ++ rest -/
theorem u64_max_correct (a b : U64) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest) :
    execProcedure u64ProcEnv 20 s Miden.Core.U64.max =
    some (s.withStack ((max a b).lo.val :: (max a b).hi.val :: rest)) := by
  have h := u64_max_ite a b rest s hs
  simp only [U64.max_def, U64.le_iff_toNat_le]
  by_cases hab : b.toNat < a.toNat
  · simp [hab, Nat.le_of_lt hab] at h ⊢; exact h
  · simp [hab] at h ⊢
    by_cases hle : b.toNat ≤ a.toNat
    · have := U64.eq_of_toNat_eq (Nat.le_antisymm (Nat.le_of_not_lt hab) hle)
      subst this; simp only [Nat.le_refl, ite_true]; exact h
    · simp [hle]; exact h

end MidenLean.Proofs
