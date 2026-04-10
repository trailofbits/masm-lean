import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- Raw version of `u64::wrapping_mul` with explicit Felt arguments.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [c_lo, c_hi] ++ rest
    where c_lo is the low 32 bits and c_hi the high 32 bits of (a * b) mod 2^64. -/
theorem u64_wrapping_mul_exec
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    execProcedure emptyEnv 20 s Miden.Core.U64.wrapping_mul =
    some (s.withStack (
      let prod_lo := a_lo.val * b_lo.val
      let cross1 := b_hi.val * a_lo.val + prod_lo / 2^32
      let cross2 := b_lo.val * a_hi.val + cross1 % 2^32
      Felt.ofNat (prod_lo % 2^32) :: Felt.ofNat (cross2 % 2^32) :: rest)) := by
  miden_vcg
  all_goals miden_finish_reflection

/-- `u64::wrapping_mul` computes the low 64 bits of the product `a * b`.
    Input stack:  [b.lo, b.hi, a.lo, a.hi] ++ rest
    Output stack: [(a * b).lo, (a * b).hi] ++ rest -/
theorem u64_wrapping_mul_correct (a b : U64) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest) :
    execProcedure emptyEnv 20 s Miden.Core.U64.wrapping_mul =
    some (s.withStack ((a * b).lo.val :: (a * b).hi.val :: rest)) := by
  rw [u64_wrapping_mul_exec a.lo.val a.hi.val b.lo.val b.hi.val rest s hs a.lo.isU32 a.hi.isU32 b.lo.isU32 b.hi.isU32]
  show _ = some (s.withStack (
    Felt.ofNat ((a.toNat * b.toNat) % 2^32) ::
    Felt.ofNat (((a.toNat * b.toNat) / 2^32) % 2^32) :: rest))
  simp only [U64.toNat]
  congr 1; congr 1; congr 1
  · congr 1; ring_nf; omega
  · congr 1; congr 1; ring_nf; omega

end MidenLean.Proofs
