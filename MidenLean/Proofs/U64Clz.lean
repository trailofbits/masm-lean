import MidenLean.Proofs.StepLemmas
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas

-- ============================================================================
-- Main proof: u64_clz_correct
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- u64.clz correctly counts leading zeros of a u64 value.
    Input stack:  [lo, hi] ++ rest
    Output stack: [result] ++ rest
    where result = if hi == 0 then clz(lo) + 32 else clz(hi). -/
theorem u64_clz_correct (lo hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = lo :: hi :: rest) :
    exec 20 s Miden.Core.Math.U64.clz =
    some (s.withStack (
      (if hi == (0 : Felt)
       then Felt.ofNat (u32CountLeadingZeros lo.val) + 32
       else Felt.ofNat (u32CountLeadingZeros hi.val)) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  -- Unfold exec and the procedure definition
  unfold exec Miden.Core.Math.U64.clz execOps
  simp only [List.foldlM]
  -- The foldlM processes: swap 1, dup 0, eqImm 0, then the ifElse.
  -- We rewrite the prefix as a chain of monadic binds:
  change (do
    let s' ← stepInstruction ⟨lo :: hi :: rest, mem, locs, adv⟩ (.swap 1)
    let s' ← stepInstruction s' (.dup 0)
    let s' ← stepInstruction s' (.eqImm 0)
    let s' ← (match s'.stack with
      | cond :: rest' =>
        if cond.val == 1 then
          execOps (fun _ => none) 19 (s'.withStack rest') [
            .inst (.drop), .inst (.u32Clz), .inst (.addImm 32)]
        else if cond.val == 0 then
          execOps (fun _ => none) 19 (s'.withStack rest') [
            .inst (.swap 1), .inst (.drop), .inst (.u32Clz)]
        else none
      | _ => none)
    pure s') = _
  -- Step through the prefix
  rw [stepSwap (hn := by decide) (htop := rfl) (hnth := rfl)]
  dsimp only [bind, Bind.bind, Option.bind, List.set]
  rw [stepDup (h := rfl)]; dsimp only [bind, Bind.bind, Option.bind]
  rw [stepEqImm]; dsimp only [bind, Bind.bind, Option.bind]
  -- Now we have the condition (if hi == 0 then 1 else 0) on top of stack.
  -- Case split on whether hi == 0.
  by_cases h : hi == (0 : Felt)
  · -- Case: hi == 0 (then branch)
    simp only [h]
    -- After simp, condition is (1 : Felt) and cond.val == 1 should reduce
    -- Now we're in the then branch: [drop, u32Clz, addImm 32]
    -- Stack: [hi, lo, ...rest]
    unfold execOps
    simp only [List.foldlM]
    change (do
      let s' ← stepInstruction ⟨hi :: lo :: rest, mem, locs, adv⟩ (.drop)
      let s' ← stepInstruction s' (.u32Clz)
      let s' ← stepInstruction s' (.addImm 32)
      pure s') = _
    rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepU32Clz]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepAddImm]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
    simp
  · -- Case: hi != 0 (else branch)
    simp only [h]
    -- After simp, condition is (0 : Felt) and cond.val == 1 is false, cond.val == 0 is true
    -- Now we're in the else branch: [swap 1, drop, u32Clz]
    -- Stack: [hi, lo, ...rest]
    unfold execOps
    simp only [List.foldlM]
    change (do
      let s' ← stepInstruction ⟨hi :: lo :: rest, mem, locs, adv⟩ (.swap 1)
      let s' ← stepInstruction s' (.drop)
      let s' ← stepInstruction s' (.u32Clz)
      pure s') = _
    rw [stepSwap (hn := by decide) (htop := rfl) (hnth := rfl)]
    dsimp only [bind, Bind.bind, Option.bind, List.set]
    rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepU32Clz]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
    simp

end MidenLean.Proofs
