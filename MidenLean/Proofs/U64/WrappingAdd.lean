import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.U64.OverflowingAdd
import MidenLean.Proofs.Tactics
import MidenLean.Proofs.Interp
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- `u64::wrapping_add` correctly computes wrapping addition of two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [c_lo, c_hi] ++ rest
    where `(c_hi, c_lo)` is the low 64 bits of `a + b`. -/
theorem u64_wrapping_add_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    execWithEnv u64ProcEnv 10 s Miden.Core.U64.wrapping_add =
    some (s.withStack (
      let lo_sum := b_lo.val + a_lo.val
      let carry := lo_sum / 2 ^ 32
      let hi_sum := a_hi.val + b_hi.val + carry
      Felt.ofNat (lo_sum % 2 ^ 32) ::
      Felt.ofNat (hi_sum % 2 ^ 32) :: rest)) := by
  obtain ⟨stk, mem, locs, adv, evts⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold Miden.Core.U64.wrapping_add execWithEnv
  simp only [List.foldlM, u64ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  rw [show execWithEnv u64ProcEnv 9
      ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv, evts⟩
      Miden.Core.U64.overflowing_add =
      some ⟨
        Felt.ofNat ((a_hi.val + b_hi.val + (b_lo.val + a_lo.val) / 2 ^ 32) / 2 ^ 32) ::
        Felt.ofNat ((b_lo.val + a_lo.val) % 2 ^ 32) ::
        Felt.ofNat ((a_hi.val + b_hi.val + (b_lo.val + a_lo.val) / 2 ^ 32) % 2 ^ 32) ::
        rest,
        mem, locs, adv⟩
      from u64_overflowing_add_run u64ProcEnv 8 a_lo a_hi b_lo b_hi rest mem locs adv
        ha_lo ha_hi hb_lo hb_hi]
  miden_bind
  rw [stepDrop]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

/-- wrapping_add computes (toU64 a + toU64 b) % 2^64. -/
theorem u64_wrapping_add_semantic
    (a_lo a_hi b_lo b_hi : Felt)
    (ha_lo : a_lo.isU32 = true)
    (_ha_hi : a_hi.isU32 = true)
    (_hb_lo : b_lo.isU32 = true)
    (_hb_hi : b_hi.isU32 = true) :
    let lo_sum := b_lo.val + a_lo.val
    let carry := lo_sum / 2 ^ 32
    let hi_sum := a_hi.val + b_hi.val + carry
    (hi_sum % 2 ^ 32) * 2 ^ 32 + lo_sum % 2 ^ 32 =
    (toU64 a_lo a_hi + toU64 b_lo b_hi) % 2 ^ 64 := by
  simp only [toU64, Felt.isU32, decide_eq_true_eq] at *
  omega

end MidenLean.Proofs
