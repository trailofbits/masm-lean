import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `u128::shr_k3` shifts the highest u32 limb right by the given bit count and
    leaves any lower-word padding in `rest`.
    Input stack:  [shift, a0, a1, a2, a3] ++ rest
    Output stack: [a3 >> shift] ++ rest
    Requires `shift` and `a3` to be u32 values, with `shift ≤ 31`. -/
theorem u128_shr_k3_raw
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = shift :: a0 :: a1 :: a2 :: a3 :: rest)
    (hshift_u32 : shift.isU32 = true)
    (ha3_u32 : a3.isU32 = true)
    (hshift : shift.val ≤ 31) :
    exec 12 s Miden.Core.U128.shr_k3 =
    some (s.withStack (Felt.ofNat (a3.val / 2 ^ shift.val) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U128.shr_k3 execWithEnv
  simp only [List.foldlM]
  miden_movup
  miden_swap
  rw [stepU32ShrLocal (ha := ha3_u32) (hb := hshift_u32) (hshift := hshift)]
  miden_bind
  miden_movdn
  rw [stepDrop]
  miden_bind
  rw [stepDrop]
  miden_bind
  rw [stepDrop]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

end MidenLean.Proofs
