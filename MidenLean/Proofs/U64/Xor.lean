import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `u64::xor` correctly computes bitwise XOR of two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [b_lo ^^^ a_lo, b_hi ^^^ a_hi] ++ rest -/
theorem u64_xor_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    exec 10 s Miden.Core.U64.xor =
    some (s.withStack (
      Felt.ofNat (b_lo.val ^^^ a_lo.val) ::
      Felt.ofNat (b_hi.val ^^^ a_hi.val) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U64.xor execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv⟩ (.movup 2)
    let s' ← execInstruction s' (.u32Xor)
    let s' ← execInstruction s' (.swap 2)
    let s' ← execInstruction s' (.u32Xor)
    let s' ← execInstruction s' (.swap 1)
    pure s') = _
  miden_movup
  rw [stepU32Xor (ha := hb_lo) (hb := ha_lo)]; miden_bind
  miden_swap
  rw [stepU32Xor (ha := hb_hi) (hb := ha_hi)]; miden_bind
  miden_swap
  dsimp only [pure, Pure.pure]

end MidenLean.Proofs
