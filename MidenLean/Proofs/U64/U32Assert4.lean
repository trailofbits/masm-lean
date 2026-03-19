import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- `u64::u32assert4` validates that four stack elements are u32 values.
    Input stack:  [a, b, c, d] ++ rest
    Output stack: [a, b, c, d] ++ rest (unchanged)
    Fails if any of a, b, c, d is not a u32 value. -/
theorem u64_u32assert4_correct
    (a b c d : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: b :: c :: d :: rest)
    (ha : a.isU32 = true) (hb : b.isU32 = true)
    (hc : c.isU32 = true) (hd : d.isU32 = true) :
    exec 10 s Miden.Core.U64.u32assert4 =
    some (s.withStack (a :: b :: c :: d :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U64.u32assert4 execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨a :: b :: c :: d :: rest, mem, locs, adv⟩ .u32Assert2
    let s' ← execInstruction s' (.movup 3)
    let s' ← execInstruction s' (.movup 3)
    let s' ← execInstruction s' .u32Assert2
    let s' ← execInstruction s' (.movup 3)
    let s' ← execInstruction s' (.movup 3)
    pure s') = _
  rw [stepU32Assert2 (ha := ha) (hb := hb)]; miden_bind
  miden_movup; miden_movup
  rw [stepU32Assert2 (ha := hc) (hb := hd)]; miden_bind
  miden_movup; miden_movup
  dsimp only [pure, Pure.pure]

end MidenLean.Proofs
