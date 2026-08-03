import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.U64.Gt
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- `u64::lte` compares two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff a ≤ b (as u64), else 0.
    Computed as !(a > b).
    Parametric in `fuel` so this lemma serves both as a callee summary for
    reflective callers and as the basis for `u64_lte_correct`. The env is
    fixed to `u64ProcEnv` because the proof resolves the `exec gt` call by
    unfolding that environment. -/
@[miden_exec_summary]
theorem u64_lte_exec
    (fuel : Nat)
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    execProcedure u64ProcEnv (fuel + 2) s Miden.Core.U64.lte =
    some (s.withStack (
      let borrow_lo := decide (b_lo.val < a_lo.val)
      let borrow_hi := decide (b_hi.val < a_hi.val)
      let hi_eq := Felt.ofNat (u32OverflowingSub b_hi.val a_hi.val).2 == (0 : Felt)
      (if !(borrow_hi || (hi_eq && borrow_lo)) then (1 : Felt) else 0) :: rest)) := by
  miden_vcg
  · rename_i h
    intro hle
    rcases h with h | ⟨heq, hlt⟩
    · omega
    · exact ⟨hlt, heq⟩
  · rename_i h
    intro hlt heq
    have := h.2 heq
    omega

/-- `u64::lte` pushes 1 iff `a ≤ b` (as u64).
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [(if a ≤ b then 1 else 0)] ++ rest -/
theorem u64_lte_correct (a b : U64) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest) :
    execProcedure u64ProcEnv 20 s Miden.Core.U64.lte =
    some (s.withStack (
      (if a ≤ b then (1 : Felt) else 0) :: rest)) := by
  rw [u64_lte_exec 18 a.lo.val a.hi.val b.lo.val b.hi.val rest s hs a.lo.isU32 a.hi.isU32 b.lo.isU32 b.hi.isU32]
  simp only [u64_borrow_iff_lt b a]
  congr 1; congr 1; congr 1; congr 1
  cases h : decide (b.toNat < a.toNat) <;> simp_all

end MidenLean.Proofs
