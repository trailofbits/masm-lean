import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- u64.clo correctly counts leading ones of a u64 value.
    Input stack:  [lo, hi] ++ rest
    Output stack: [result] ++ rest
    where result = if hi == 0xFFFFFFFF then clo(lo) + 32 else clo(hi).
    clo(x) is expressed as u32CountLeadingZeros(u32Max - 1 - x) since
    u32CountLeadingOnes is private to Semantics. -/
theorem u64_clo_correct (lo hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = lo :: hi :: rest) :
    exec 20 s Miden.Core.Math.U64.clo =
    some (s.withStack (
      (if hi == (4294967295 : Felt)
       then Felt.ofNat (u32CountLeadingZeros (u32Max - 1 - lo.val)) + 32
       else Felt.ofNat (u32CountLeadingZeros (u32Max - 1 - hi.val))) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.Math.U64.clo execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨lo :: hi :: rest, mem, locs, adv⟩ (.swap 1)
    let s' ← execInstruction s' (.dup 0)
    let s' ← execInstruction s' (.eqImm 4294967295)
    let s' ← (match s'.stack with
      | cond :: rest' =>
        if cond.val == 1 then
          execWithEnv (fun _ => none) 19 (s'.withStack rest') [
            .inst (.drop), .inst (.u32Clo), .inst (.addImm 32)]
        else if cond.val == 0 then
          execWithEnv (fun _ => none) 19 (s'.withStack rest') [
            .inst (.swap 1), .inst (.drop), .inst (.u32Clo)]
        else none
      | _ => none)
    pure s') = _
  miden_swap
  miden_dup
  rw [stepEqImm]; miden_bind
  by_cases h : hi == (4294967295 : Felt)
  · simp only [h]
    unfold execWithEnv; simp only [List.foldlM]
    change (do
      let s' ← execInstruction ⟨hi :: lo :: rest, mem, locs, adv⟩ (.drop)
      let s' ← execInstruction s' (.u32Clo)
      let s' ← execInstruction s' (.addImm 32)
      pure s') = _
    rw [stepDrop]; miden_bind
    rw [stepU32Clo]; miden_bind
    rw [stepAddImm]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
    simp
  · simp only [h]
    unfold execWithEnv; simp only [List.foldlM]
    change (do
      let s' ← execInstruction ⟨hi :: lo :: rest, mem, locs, adv⟩ (.swap 1)
      let s' ← execInstruction s' (.drop)
      let s' ← execInstruction s' (.u32Clo)
      pure s') = _
    miden_swap
    rw [stepDrop]; miden_bind
    rw [stepU32Clo]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
    simp

end MidenLean.Proofs
