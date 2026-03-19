import MidenLean.Proofs.Tactics
import MidenLean.Proofs.Interp
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- u64.ctz correctly counts trailing zeros of a u64 value.
    Input stack:  [lo, hi] ++ rest
    Output stack: [result] ++ rest
    where result = if lo == 0 then ctz(hi) + 32 else ctz(lo). -/
theorem u64_ctz_correct (lo hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = lo :: hi :: rest)
    (hlo : lo.isU32 = true) (hhi : hi.isU32 = true)
    (hlen : rest.length + 30 ≤ MAX_STACK_DEPTH) :
    exec 20 s Miden.Core.U64.ctz =
    some (s.withStack (
      (if lo == (0 : Felt)
       then Felt.ofNat (u32CountTrailingZeros hi.val) + 32
       else Felt.ofNat (u32CountTrailingZeros lo.val)) :: rest)) := by
  obtain ⟨stk, mem, locs, adv, evts⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U64.ctz execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨lo :: hi :: rest, mem, locs, adv, evts⟩ (.dup 0)
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
  · simp only [h, ite_true, MidenState.withStack]
    unfold execWithEnv; simp only [List.foldlM]
    rw [stepDrop]; miden_bind
    rw [stepU32Ctz (ha := hhi)]; miden_bind
    rw [stepAddImm]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
    simp
  · simp only [h, MidenState.withStack]
    unfold execWithEnv; simp only [List.foldlM]
    simp (config := { decide := true }) only [ite_false, ite_true,
      bind, Bind.bind, Option.bind, pure, Pure.pure]
    rw [stepSwap (hn := by decide) (htop := rfl) (hnth := rfl)]; miden_bind
    rw [stepDrop]; miden_bind
    rw [stepU32Ctz (ha := hlo)]

/-- The _correct output equals u64CountTrailingZeros. -/
theorem u64_ctz_semantic (lo hi : Felt) :
    (if lo == (0 : Felt)
     then Felt.ofNat (u32CountTrailingZeros hi.val) + 32
     else Felt.ofNat (u32CountTrailingZeros lo.val)) =
    Felt.ofNat (u64CountTrailingZeros lo.val hi.val) := by
  simp only [u64CountTrailingZeros]
  by_cases h : lo.val = 0
  · have : lo = (0 : Felt) := ZMod.val_injective _ h
    simp only [this, beq_self_eq_true, ite_true,
      ZMod.val_zero, Felt.ofNat]
    push_cast; ring
  · have : lo ≠ (0 : Felt) := fun heq =>
      h (by rw [heq]; simp)
    simp [this, h]

end MidenLean.Proofs
