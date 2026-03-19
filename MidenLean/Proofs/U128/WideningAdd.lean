import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.U128.OverflowingAdd
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- `u128::widening_add` correctly computes widening addition of two 128-bit values.
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [c0, c1, c2, c3, overflow] ++ rest
    where `c0..c3` are the low-to-high limbs of `a + b` and `overflow` is the carry-out. -/
theorem u128_widening_add_correct
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execWithEnv u128ProcEnv 31 s Miden.Core.U128.widening_add =
    some (s.withStack (
      let sum0 := b0.val + a0.val
      let carry0 := sum0 / 2 ^ 32
      let sum1 := carry0 + a1.val + b1.val
      let carry1 := sum1 / 2 ^ 32
      let sum2 := carry1 + a2.val + b2.val
      let carry2 := sum2 / 2 ^ 32
      let sum3 := carry2 + a3.val + b3.val
      Felt.ofNat (sum0 % 2 ^ 32) ::
      Felt.ofNat (sum1 % 2 ^ 32) ::
      Felt.ofNat (sum2 % 2 ^ 32) ::
      Felt.ofNat (sum3 % 2 ^ 32) ::
      Felt.ofNat (sum3 / 2 ^ 32) :: rest)) := by
  obtain ⟨stk, mem, locs, adv, evts⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold Miden.Core.U128.widening_add execWithEnv
  simp only [List.foldlM, u128ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  rw [show execWithEnv u128ProcEnv 30
      ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv, evts⟩
      Miden.Core.U128.overflowing_add =
      some ⟨
        let sum0 := b0.val + a0.val
        let carry0 := sum0 / 2 ^ 32
        let sum1 := carry0 + a1.val + b1.val
        let carry1 := sum1 / 2 ^ 32
        let sum2 := carry1 + a2.val + b2.val
        let carry2 := sum2 / 2 ^ 32
        let sum3 := carry2 + a3.val + b3.val
        Felt.ofNat (sum3 / 2 ^ 32) ::
        Felt.ofNat (sum0 % 2 ^ 32) ::
        Felt.ofNat (sum1 % 2 ^ 32) ::
        Felt.ofNat (sum2 % 2 ^ 32) ::
        Felt.ofNat (sum3 % 2 ^ 32) :: rest,
        mem, locs, adv⟩
      from u128_overflowing_add_run u128ProcEnv 29 a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
        ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3]
  miden_bind
  miden_movdn
  dsimp only [pure, Pure.pure]

end MidenLean.Proofs
