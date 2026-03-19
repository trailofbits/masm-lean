import MidenLean.Proofs.Tactics
import MidenLean.Proofs.Interp
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- u64.clz correctly counts leading zeros of a u64 value.
    Input stack:  [lo, hi] ++ rest
    Output stack: [result] ++ rest
    where result = if hi == 0 then clz(lo) + 32 else clz(hi). -/
theorem u64_clz_correct (lo hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = lo :: hi :: rest)
    (hlo : lo.isU32 = true) (hhi : hi.isU32 = true) :
    exec 20 s Miden.Core.U64.clz =
    some (s.withStack (
      (if hi == (0 : Felt)
       then Felt.ofNat (u32CountLeadingZeros lo.val) + 32
       else Felt.ofNat (u32CountLeadingZeros hi.val)) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U64.clz execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨lo :: hi :: rest, mem, locs, adv⟩ (.swap 1)
    let s' ← execInstruction s' (.dup 0)
    let s' ← execInstruction s' (.eqImm 0)
    let s' ← (match s'.stack with
      | cond :: rest' =>
        if cond.val == 1 then
          execWithEnv (fun _ => none) 19 (s'.withStack rest') [
            .inst (.drop), .inst (.u32Clz), .inst (.addImm 32)]
        else if cond.val == 0 then
          execWithEnv (fun _ => none) 19 (s'.withStack rest') [
            .inst (.swap 1), .inst (.drop), .inst (.u32Clz)]
        else none
      | _ => none)
    pure s') = _
  miden_swap
  miden_dup
  rw [stepEqImm]; miden_bind
  -- Case split on whether hi == 0
  by_cases h : hi == (0 : Felt)
  · -- Case: hi == 0 (then branch)
    simp only [h, ite_true, MidenState.withStack]
    unfold execWithEnv; simp only [List.foldlM]
    rw [stepDrop]; miden_bind
    rw [stepU32Clz (ha := hlo)]; miden_bind
    rw [stepAddImm]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
    simp
  · -- Case: hi != 0 (else branch)
    simp only [h, MidenState.withStack]
    unfold execWithEnv; simp only [List.foldlM]
    simp (config := { decide := true }) only [ite_false, ite_true,
      bind, Bind.bind, Option.bind, pure, Pure.pure]
    rw [stepSwap (hn := by decide) (htop := rfl) (hnth := rfl)]; miden_bind
    rw [stepDrop]; miden_bind
    rw [stepU32Clz (ha := hhi)]

/-- The _correct output equals u64CountLeadingZeros
    applied to the limb values. -/
theorem u64_clz_semantic (lo hi : Felt) :
    (if hi == (0 : Felt)
     then Felt.ofNat (u32CountLeadingZeros lo.val) + 32
     else Felt.ofNat (u32CountLeadingZeros hi.val)) =
    Felt.ofNat (u64CountLeadingZeros lo.val hi.val) := by
  simp only [u64CountLeadingZeros]
  by_cases h : hi.val = 0
  · have : hi = (0 : Felt) := ZMod.val_injective _ h
    simp only [this, beq_self_eq_true, ite_true,
      ZMod.val_zero]
    simp only [Felt.ofNat]
    push_cast; ring
  · have : hi ≠ (0 : Felt) := fun heq =>
      h (by rw [heq]; simp)
    simp [this, h]

end MidenLean.Proofs
