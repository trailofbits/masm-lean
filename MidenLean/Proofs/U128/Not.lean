import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

private theorem stepU32NotLocal (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .u32Not =
    some ⟨Felt.ofNat (u32Max - 1 - a.val) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32Not u32Max
  simp [ha, MidenState.withStack]

/-- `u128::not` correctly computes the bitwise complement of a 128-bit value.
    Input stack:  [a0, a1, a2, a3] ++ rest
    Output stack: [~~~a0, ~~~a1, ~~~a2, ~~~a3] ++ rest, limbwise over u32 values. -/
theorem u128_not_correct
    (a0 a1 a2 a3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a0 :: a1 :: a2 :: a3 :: rest)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true) :
    exec 13 s Miden.Core.U128.not =
    some (s.withStack (
      Felt.ofNat (u32Max - 1 - a0.val) ::
      Felt.ofNat (u32Max - 1 - a1.val) ::
      Felt.ofNat (u32Max - 1 - a2.val) ::
      Felt.ofNat (u32Max - 1 - a3.val) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U128.not execWithEnv
  simp only [List.foldlM]
  miden_movup
  rw [stepU32NotLocal (ha := ha3)]
  miden_bind
  miden_movup
  rw [stepU32NotLocal (ha := ha2)]
  miden_bind
  miden_movup
  rw [stepU32NotLocal (ha := ha1)]
  miden_bind
  miden_movup
  rw [stepU32NotLocal (ha := ha0)]
  miden_bind
  simp only [pure, Pure.pure]

end MidenLean.Proofs
