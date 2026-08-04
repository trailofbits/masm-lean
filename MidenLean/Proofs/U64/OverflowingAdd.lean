import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

/-- `u64::overflowing_add` computes addition of two u64 values with carry.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [overflow, c_lo, c_hi] ++ rest
    where `(c_hi, c_lo)` is the 64-bit sum and `overflow` is the carry bit.
    Parametric in `env` and `fuel` so this lemma serves both as a callee
    summary for reflective callers and as the basis for `u64_overflowing_add_correct`. -/
@[miden_exec_summary]
theorem u64_overflowing_add_exec
    (env : ProcEnv) (fuel : Nat)
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    execProcedure env (fuel + 1) s Miden.Core.U64.overflowing_add =
    some (s.withStack (
      Felt.ofNat ((a_hi.val + b_hi.val + (b_lo.val + a_lo.val) / 2 ^ 32) / 2 ^ 32) ::
      Felt.ofNat ((b_lo.val + a_lo.val) % 2 ^ 32) ::
      Felt.ofNat ((a_hi.val + b_hi.val + (b_lo.val + a_lo.val) / 2 ^ 32) % 2 ^ 32) ::
      rest)) := by
  miden_vcg

/-- `u64::overflowing_add` computes `a + b` with overflow detection.
    Input stack:  [b.lo, b.hi, a.lo, a.hi] ++ rest
    Output stack: [overflow, (a + b).lo, (a + b).hi] ++ rest
    where overflow = 1 iff the addition overflowed 64 bits. -/
theorem u64_overflowing_add_correct (a b : U64) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest) :
    execProcedure emptyEnv 10 s Miden.Core.U64.overflowing_add =
    some (s.withStack (
      (if a.toNat + b.toNat ≥ 2^64 then (1 : Felt) else 0) ::
      (a + b).lo.val :: (a + b).hi.val :: rest)) := by
  rw [u64_overflowing_add_exec emptyEnv 9 a.lo.val a.hi.val b.lo.val b.hi.val rest s hs
    a.lo.isU32 a.hi.isU32 b.lo.isU32 b.hi.isU32]
  show _ = some (s.withStack (
    (if a.toNat + b.toNat ≥ 2^64 then (1 : Felt) else 0) ::
    Felt.ofNat ((a.toNat + b.toNat) % 2^32) ::
    Felt.ofNat (((a.toNat + b.toNat) / 2^32) % 2^32) :: rest))
  simp only [U64.toNat]
  have halo := a.lo.isU32; have hahi := a.hi.isU32
  have hblo := b.lo.isU32; have hbhi := b.hi.isU32
  simp only [Felt.isU32, decide_eq_true_eq] at halo hahi hblo hbhi
  congr 1; congr 1; congr 1
  · split_ifs with hge
    · have h : (a.hi.val.val + b.hi.val.val + (b.lo.val.val + a.lo.val.val) / 2 ^ 32) / 2 ^ 32 = 1 := by omega
      rw [h]; rfl
    · have h : (a.hi.val.val + b.hi.val.val + (b.lo.val.val + a.lo.val.val) / 2 ^ 32) / 2 ^ 32 = 0 := by omega
      rw [h]; rfl
  · congr 1
    · congr 1; omega
    · congr 1; congr 1; congr 1; omega

end MidenLean.Proofs
