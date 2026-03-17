import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- u64.ctz correctly counts trailing zeros of a u64 value.
    Input stack:  [lo, hi] ++ rest
    Output stack: [result] ++ rest
    where result = if lo == 0 then ctz(hi) + 32 else ctz(lo). -/
theorem u64_ctz_correct (lo hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = lo :: hi :: rest) :
    exec 20 s Miden.Core.Math.U64.ctz =
    some (s.withStack (
      (if lo == (0 : Felt)
       then Felt.ofNat (u32CountTrailingZeros hi.val) + 32
       else Felt.ofNat (u32CountTrailingZeros lo.val)) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.Math.U64.ctz execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨lo :: hi :: rest, mem, locs, adv⟩ (.dup 0)
    let s' ← execInstruction s' (.eqImm 0)
    let s' ← (match s'.stack with
      | cond :: rest' =>
        if cond.val == 1 then
          execWithEnv (fun _ => none) 19 (s'.withStack rest') [
            .inst (.drop), .inst (.u32Ctz), .inst (.addImm 32)]
        else if cond.val == 0 then
          execWithEnv (fun _ => none) 19 (s'.withStack rest') [
            .inst (.swap 1), .inst (.drop), .inst (.u32Ctz)]
        else none
      | _ => none)
    pure s') = _
  miden_dup
  rw [stepEqImm]; miden_bind
  by_cases h : lo == (0 : Felt)
  · simp only [h]
    unfold execWithEnv; simp only [List.foldlM]
    change (do
      let s' ← execInstruction ⟨lo :: hi :: rest, mem, locs, adv⟩ (.drop)
      let s' ← execInstruction s' (.u32Ctz)
      let s' ← execInstruction s' (.addImm 32)
      pure s') = _
    rw [stepDrop]; miden_bind
    rw [stepU32Ctz]; miden_bind
    rw [stepAddImm]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
    simp
  · simp only [h]
    unfold execWithEnv; simp only [List.foldlM]
    change (do
      let s' ← execInstruction ⟨lo :: hi :: rest, mem, locs, adv⟩ (.swap 1)
      let s' ← execInstruction s' (.drop)
      let s' ← execInstruction s' (.u32Ctz)
      pure s') = _
    miden_swap
    rw [stepDrop]; miden_bind
    rw [stepU32Ctz]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
    simp

end MidenLean.Proofs
