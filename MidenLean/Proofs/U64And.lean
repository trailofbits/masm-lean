import MidenLean.Proofs.StepLemmas
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas

set_option maxHeartbeats 4000000 in
/-- u64.and correctly computes bitwise AND of two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [b_lo &&& a_lo, b_hi &&& a_hi] ++ rest -/
theorem u64_and_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    exec 10 s Miden.Core.Math.U64.and =
    some (s.withStack (
      Felt.ofNat (b_lo.val &&& a_lo.val) ::
      Felt.ofNat (b_hi.val &&& a_hi.val) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.Math.U64.and execOps
  simp only [List.foldlM]
  -- The procedure is:
  --   movup 2   : [b_lo, b_hi, a_lo, a_hi, ...] -> [a_lo, b_lo, b_hi, a_hi, ...]
  --   u32And     : [a_lo, b_lo, b_hi, a_hi, ...] -> [b_lo &&& a_lo, b_hi, a_hi, ...]
  --   swap 2     : [b_lo &&& a_lo, b_hi, a_hi, ...] -> [a_hi, b_hi, b_lo &&& a_lo, ...]
  --   u32And     : [a_hi, b_hi, b_lo &&& a_lo, ...] -> [b_hi &&& a_hi, b_lo &&& a_lo, ...]
  --   swap 1     : [b_hi &&& a_hi, b_lo &&& a_lo, ...] -> [b_lo &&& a_lo, b_hi &&& a_hi, ...]
  change (do
    let s' ← stepInstruction ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv⟩ (.movup 2)
    let s' ← stepInstruction s' (.u32And)
    let s' ← stepInstruction s' (.swap 2)
    let s' ← stepInstruction s' (.u32And)
    let s' ← stepInstruction s' (.swap 1)
    pure s') = _
  rw [stepMovup2]; dsimp only [bind, Bind.bind, Option.bind]
  -- Stack: [a_lo, b_lo, b_hi, a_hi, ...]
  rw [stepU32And (ha := hb_lo) (hb := ha_lo)]; dsimp only [bind, Bind.bind, Option.bind]
  -- Stack: [Felt.ofNat (b_lo.val &&& a_lo.val), b_hi, a_hi, ...]
  rw [stepSwap (hn := by decide) (htop := rfl) (hnth := rfl)]
  dsimp only [bind, Bind.bind, Option.bind, List.set]
  -- Stack: [a_hi, b_hi, Felt.ofNat (b_lo.val &&& a_lo.val), ...]
  rw [stepU32And (ha := hb_hi) (hb := ha_hi)]; dsimp only [bind, Bind.bind, Option.bind]
  -- Stack: [Felt.ofNat (b_hi.val &&& a_hi.val), Felt.ofNat (b_lo.val &&& a_lo.val), ...]
  rw [stepSwap (hn := by decide) (htop := rfl) (hnth := rfl)]
  dsimp only [bind, Bind.bind, Option.bind, List.set, pure, Pure.pure]
  -- Stack: [Felt.ofNat (b_lo.val &&& a_lo.val), Felt.ofNat (b_hi.val &&& a_hi.val), ...]

end MidenLean.Proofs
