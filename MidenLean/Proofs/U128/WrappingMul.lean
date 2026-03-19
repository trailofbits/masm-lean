import MidenLean.Proofs.U128.OverflowingMul
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

private theorem wrapping_mul_decomp :
    Miden.Core.U128.wrapping_mul = u128_mul_low_chunk ++ u128_wrapping_mul_tail := by
  simp [Miden.Core.U128.wrapping_mul, u128_mul_low_chunk, u128_wrapping_mul_tail]

private def u128_wrapping_mul_tail_arith : List Op := [
  .inst (.swap 1),
  .inst (.drop),
  .inst (.dup 5),
  .inst (.dup 5),
  .inst (.u32WrappingMadd),
  .inst (.dup 6),
  .inst (.dup 4),
  .inst (.u32WrappingMadd),
  .inst (.dup 7),
  .inst (.dup 3),
  .inst (.u32WrappingMadd),
  .inst (.dup 8),
  .inst (.dup 2),
  .inst (.u32WrappingMadd)
]

private def u128_wrapping_mul_tail_cleanup : List Op := [
  .inst (.movup 9),
  .inst (.movup 10),
  .inst (.movup 11),
  .inst (.movup 3),
  .inst (.swapw 1),
  .inst (.dropw),
  .inst (.swapw 1),
  .inst (.dropw),
  .inst (.movdn 3),
  .inst (.movdn 2),
  .inst (.swap 1)
]

private theorem u128_wrapping_mul_tail_decomp :
    u128_wrapping_mul_tail = u128_wrapping_mul_tail_arith ++ u128_wrapping_mul_tail_cleanup := by
  simp [u128_wrapping_mul_tail, u128_wrapping_mul_tail_arith, u128_wrapping_mul_tail_cleanup]

private theorem u128_wrapping_mul_tail_arith_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨u128MulO2Sum a0 a1 a2 b0 b1 b2 ::
        u128MulO2Carry a0 a1 a2 b0 b1 b2 ::
        a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        u128MulC0 a0 b0 ::
        u128MulC1 a0 a1 b0 b1 ::
        u128MulC2 a0 a1 a2 b0 b1 b2 ::
        rest,
        mem, locs, adv⟩
      u128_wrapping_mul_tail_arith =
    some ⟨
      u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      rest,
      mem, locs, adv⟩ := by
  unfold execWithEnv u128_wrapping_mul_tail_arith
  simp only [List.foldlM]
  have hO2Sum_u32 : (u128MulO2Sum a0 a1 a2 b0 b1 b2).isU32 = true := by
    unfold u128MulO2Sum
    exact u32_mod_isU32 _
  miden_swap
  rw [stepDrop]
  miden_bind
  miden_dup
  miden_dup
  rw [stepU32WrappingMadd (ha := hb0) (hb := ha3) (hc := hO2Sum_u32)]
  miden_bind
  miden_dup
  miden_dup
  rw [stepU32WrappingMadd
    (a := b1) (b := a2)
    (c := Felt.ofNat ((b0.val * a3.val + (u128MulO2Sum a0 a1 a2 b0 b1 b2).val) % 2 ^ 32))
    (ha := hb1) (hb := ha2) (hc := u32_mod_isU32 _)]
  miden_bind
  miden_dup
  miden_dup
  rw [stepU32WrappingMadd
    (a := b2) (b := a1)
    (c := Felt.ofNat
      ((b1.val * a2.val + (Felt.ofNat ((b0.val * a3.val + (u128MulO2Sum a0 a1 a2 b0 b1 b2).val) % 2 ^ 32)).val) %
        2 ^ 32))
    (ha := hb2) (hb := ha1) (hc := u32_mod_isU32 _)]
  miden_bind
  miden_dup
  miden_dup
  rw [stepU32WrappingMadd
    (a := b3) (b := a0)
    (c := Felt.ofNat
      ((b2.val * a1.val +
          (Felt.ofNat
            ((b1.val * a2.val + (Felt.ofNat ((b0.val * a3.val + (u128MulO2Sum a0 a1 a2 b0 b1 b2).val) % 2 ^ 32)).val) %
              2 ^ 32)).val) %
        2 ^ 32))
    (ha := hb3) (hb := ha0) (hc := u32_mod_isU32 _)]
  miden_bind
  simp [pure, Pure.pure, u128MulP3a, u128MulP3b, u128MulP3c, u128MulC3]

private theorem u128_wrapping_mul_tail_cleanup_run
    (env : ProcEnv) (fuel : Nat)
    (c3 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv env (fuel + 1)
      ⟨c3 :: a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: c0 :: c1 :: c2 :: rest, mem, locs, adv, evts⟩
      u128_wrapping_mul_tail_cleanup =
    some ⟨c0 :: c1 :: c2 :: c3 :: rest, mem, locs, adv, evts⟩ := by
  unfold execWithEnv u128_wrapping_mul_tail_cleanup
  simp only [List.foldlM]
  miden_movup
  miden_movup
  miden_movup
  miden_movup
  rw [stepSwapw1]
  miden_bind
  rw [stepDropw]
  miden_bind
  rw [stepSwapw1]
  miden_bind
  rw [stepDropw]
  miden_bind
  miden_movdn
  miden_movdn
  miden_swap
  simp [pure, Pure.pure]

private theorem u128_wrapping_mul_tail_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨u128MulO2Sum a0 a1 a2 b0 b1 b2 ::
        u128MulO2Carry a0 a1 a2 b0 b1 b2 ::
        a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        u128MulC0 a0 b0 ::
        u128MulC1 a0 a1 b0 b1 ::
        u128MulC2 a0 a1 a2 b0 b1 b2 ::
        rest,
        mem, locs, adv⟩
      u128_wrapping_mul_tail =
    some ⟨
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
      rest,
      mem, locs, adv⟩ := by
  rw [u128_wrapping_mul_tail_decomp, execWithEnv_append]
  rw [u128_wrapping_mul_tail_arith_run env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3]
  miden_bind
  rw [u128_wrapping_mul_tail_cleanup_run env fuel
    (u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3) a0 a1 a2 a3 b0 b1 b2 b3
    (u128MulC0 a0 b0) (u128MulC1 a0 a1 b0 b1) (u128MulC2 a0 a1 a2 b0 b1 b2) rest mem locs adv]

theorem u128_wrapping_mul_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv, evts⟩
      Miden.Core.U128.wrapping_mul =
    some ⟨
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
      rest,
      mem, locs, adv⟩ := by
  rw [wrapping_mul_decomp, execWithEnv_append]
  rw [u128_mul_low_chunk_run env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3]
  miden_bind
  rw [u128_wrapping_mul_tail_run env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3]

/-- `u128::wrapping_mul` correctly computes the low 128 bits of the product of two 128-bit values.
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [c0, c1, c2, c3] ++ rest
    where `c0..c3` are the low-to-high limbs of `(a * b) mod 2^128`. -/
theorem u128_wrapping_mul_correct
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    exec 65 s Miden.Core.U128.wrapping_mul =
    some (s.withStack (
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
      rest)) := by
  obtain ⟨stk, mem, locs, adv, evts⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  simpa [exec] using
    u128_wrapping_mul_run (fun _ => none) 64 a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3

end MidenLean.Proofs
