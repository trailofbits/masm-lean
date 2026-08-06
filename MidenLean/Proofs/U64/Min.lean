import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.U64.Gt
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

-- Based on generated skeleton: SEMI | Instructions: 10 | Calls: true (gt)
set_option maxHeartbeats 16000000 in
/-- `u64::min` computes the minimum of two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [min_lo, min_hi] ++ rest
    If b > a (as u64), returns a; otherwise returns b.
    Parametric in `fuel` so this lemma serves both as a callee summary for
    reflective callers and as the basis for `u64_min_correct`. -/
@[miden_exec_summary]
theorem u64_min_exec
    (fuel : Nat)
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    execProcedure u64ProcEnv (fuel + 2) s Miden.Core.U64.min =
    some (s.withStack (
      let borrow_lo := decide (a_lo.val < b_lo.val)
      let borrow_hi := decide (a_hi.val < b_hi.val)
      let hi_eq := Felt.ofNat (u32OverflowingSub a_hi.val b_hi.val).2 == (0 : Felt)
      let is_gt := borrow_hi || (hi_eq && borrow_lo)
      (if is_gt then a_lo else b_lo) ::
      (if is_gt then a_hi else b_hi) :: rest)) := by
  miden_vcg
  all_goals simp only [Symbolic.Expr.eval] at *
  -- Both branches are vacuous: the `cdrop` selector agrees with the `gt` result.
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

/-- `u64::min` intermediate: uses `decide (a < b)` on individual limbs. -/
theorem u64_min_ite (a b : U64) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest) :
    execProcedure u64ProcEnv 20 s Miden.Core.U64.min =
    some (s.withStack (
      (if decide (a < b) then a.lo.val else b.lo.val) ::
      (if decide (a < b) then a.hi.val else b.hi.val) :: rest)) := by
  rw [u64_min_exec 18 a.lo.val a.hi.val b.lo.val b.hi.val rest s hs a.lo.isU32 a.hi.isU32 b.lo.isU32 b.hi.isU32]
  simp only [u64_borrow_iff_lt a b]; rfl

/-- `u64::min` computes the minimum of two u64 values.
    Input stack:  [b.lo, b.hi, a.lo, a.hi] ++ rest
    Output stack: [(min a b).lo, (min a b).hi] ++ rest -/
theorem u64_min_correct (a b : U64) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest) :
    execProcedure u64ProcEnv 20 s Miden.Core.U64.min =
    some (s.withStack ((min a b).lo.val :: (min a b).hi.val :: rest)) := by
  have h := u64_min_ite a b rest s hs
  simp only [U64.min_def, U64.le_iff_toNat_le]
  by_cases hab : a.toNat < b.toNat
  · simp only [U64.lt_iff_toNat_lt, hab, decide_true, ↓reduceIte, Nat.le_of_lt hab] at h ⊢; exact h
  · simp only [U64.lt_iff_toNat_lt, hab, decide_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hle : a.toNat ≤ b.toNat
    · -- a.toNat = b.toNat, so a = b
      have := U64.eq_of_toNat_eq (Nat.le_antisymm hle (Nat.le_of_not_lt hab))
      subst this; simp only [Nat.le_refl, ite_true]; exact h
    · simp only [hle, ↓reduceIte]; exact h

end MidenLean.Proofs
