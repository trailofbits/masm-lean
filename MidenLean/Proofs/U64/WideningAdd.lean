import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.U64.OverflowingAdd
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `u64::widening_add` computes widening addition of two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [c_lo, c_hi, overflow] ++ rest
    where (c_hi, c_lo) is the 64-bit sum and overflow is the carry bit. -/
theorem u64_widening_add_raw
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    execWithEnv u64ProcEnv 10 s Miden.Core.U64.widening_add =
    some (s.withStack (
      let lo_sum := b_lo.val + a_lo.val
      let carry := lo_sum / 2^32
      let c_lo := Felt.ofNat (lo_sum % 2^32)
      let hi_sum := a_hi.val + b_hi.val + carry
      let c_hi := Felt.ofNat (hi_sum % 2^32)
      let overflow := Felt.ofNat (hi_sum / 2^32)
      c_lo :: c_hi :: overflow :: rest)) := by
  miden_reflect
  constructor
  · exact ha_lo
  · constructor
    · exact ha_hi
    · constructor
      · exact hb_lo
      · constructor
        · exact hb_hi
        · exact u32_div_2_32_isU32 b_lo a_lo hb_lo ha_lo
  have hcarry :
      (Felt.ofNat ((b_lo.val + a_lo.val) / 2 ^ 32)).val =
        (b_lo.val + a_lo.val) / 2 ^ 32 := by
    exact felt_ofNat_val_lt _ (sum_div_2_32_lt_prime b_lo a_lo)
  have hcarry' :
      (Felt.ofNat ((b_lo.val + a_lo.val) / 4294967296)).val =
        (b_lo.val + a_lo.val) / 4294967296 := by
    simpa [u32Max] using hcarry
  constructor
  · simp [u32Max]
  · constructor
    · simpa [u32Max] using congrArg
        (fun n => Felt.ofNat ((a_hi.val + b_hi.val + n) / 4294967296)) hcarry'
    · simpa [u32Max] using congrArg
        (fun n => Felt.ofNat ((a_hi.val + b_hi.val + n) % 4294967296)) hcarry'

/-- `u64::widening_add` computes the full 65-bit sum of two u64 values.
    Input stack:  [b.lo, b.hi, a.lo, a.hi] ++ rest
    Output stack: [(a + b).lo, (a + b).hi, overflow] ++ rest -/
theorem u64_widening_add_correct (a b : U64) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest) :
    execWithEnv u64ProcEnv 10 s Miden.Core.U64.widening_add =
    some (s.withStack (
      (a + b).lo.val :: (a + b).hi.val ::
      (if a.toNat + b.toNat ≥ 2^64 then (1 : Felt) else 0) :: rest)) := by
  rw [u64_widening_add_raw a.lo.val a.hi.val b.lo.val b.hi.val rest s hs a.lo.isU32 a.hi.isU32 b.lo.isU32 b.hi.isU32]
  show _ = some (s.withStack (
    Felt.ofNat ((a.toNat + b.toNat) % 2^32) ::
    Felt.ofNat (((a.toNat + b.toNat) / 2^32) % 2^32) ::
    (if a.toNat + b.toNat ≥ 2^64 then (1 : Felt) else 0) :: rest))
  simp only [U64.toNat]
  have halo := a.lo.isU32; have hahi := a.hi.isU32
  have hblo := b.lo.isU32; have hbhi := b.hi.isU32
  simp only [Felt.isU32, decide_eq_true_eq] at halo hahi hblo hbhi
  congr 1; congr 1; congr 1
  · congr 1; omega
  · congr 1
    · congr 1; congr 1; omega
    · congr 1
      split_ifs with hge
      · have h : (a.hi.val.val + b.hi.val.val + (b.lo.val.val + a.lo.val.val) / 2 ^ 32) / 2 ^ 32 = 1 := by omega
        rw [h]; rfl
      · have h : (a.hi.val.val + b.hi.val.val + (b.lo.val.val + a.lo.val.val) / 2 ^ 32) / 2 ^ 32 = 0 := by omega
        rw [h]; rfl

end MidenLean.Proofs
