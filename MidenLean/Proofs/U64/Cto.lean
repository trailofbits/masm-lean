import MidenLean.Proofs.Tactics
import MidenLean.Proofs.Interp
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- u64.cto correctly counts trailing ones of a u64 value.
    Input stack:  [lo, hi] ++ rest
    Output stack: [result] ++ rest
    where result = if lo == 0xFFFFFFFF then cto(hi) + 32 else cto(lo).
    cto(x) is expressed as u32CountTrailingZeros(x ^^^ (u32Max - 1)) since
    u32CountTrailingOnes is private to Semantics. -/
theorem u64_cto_correct (lo hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = lo :: hi :: rest)
    (hlo : lo.isU32 = true) (hhi : hi.isU32 = true)
    (hlen : rest.length + 30 ≤ MAX_STACK_DEPTH) :
    exec 20 s Miden.Core.U64.cto =
    some (s.withStack (
      (if lo == (4294967295 : Felt)
       then Felt.ofNat (u32CountTrailingZeros (hi.val ^^^ (u32Max - 1))) + 32
       else Felt.ofNat (u32CountTrailingZeros (lo.val ^^^ (u32Max - 1)))) :: rest)) := by
  obtain ⟨stk, mem, locs, adv, evts⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U64.cto execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨lo :: hi :: rest, mem, locs, adv, evts⟩ (.dup 0)
    let s' ← execInstruction s' (.eqImm 4294967295)
    let s' ← (match s'.stack with
      | cond :: rest' =>
        if cond.val == 1 then
          execWithEnv (fun _ => none) 19 (s'.withStack rest') [
            .inst (.drop), .inst (.u32Cto), .inst (.addImm 32)]
        else if cond.val == 0 then
          execWithEnv (fun _ => none) 19 (s'.withStack rest') [
            .inst (.swap 1), .inst (.drop), .inst (.u32Cto)]
        else none
      | _ => none)
    pure s') = _
  miden_dup
  rw [stepEqImm]; miden_bind
  by_cases h : lo == (4294967295 : Felt)
  · simp only [h, ite_true, MidenState.withStack]
    unfold execWithEnv; simp only [List.foldlM]
    rw [stepDrop]; miden_bind
    rw [stepU32Cto (ha := hhi)]; miden_bind
    rw [stepAddImm]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
    simp
  · simp only [h, MidenState.withStack]
    unfold execWithEnv; simp only [List.foldlM]
    simp (config := { decide := true }) only [ite_false, ite_true,
      bind, Bind.bind, Option.bind, pure, Pure.pure]
    rw [stepSwap (hn := by decide) (htop := rfl) (hnth := rfl)]; miden_bind
    rw [stepDrop]; miden_bind
    rw [stepU32Cto (ha := hlo)]

/-- cto computes u64CountTrailingOnes. -/
theorem u64_cto_semantic (lo hi : Felt)
    (_hlo : lo.isU32 = true) (_hhi : hi.isU32 = true) :
    (if lo == (4294967295 : Felt)
     then Felt.ofNat (u32CountTrailingZeros
       (hi.val ^^^ (u32Max - 1))) + 32
     else Felt.ofNat (u32CountTrailingZeros
       (lo.val ^^^ (u32Max - 1)))) =
    Felt.ofNat (u64CountTrailingOnes lo.val hi.val) := by
  simp only [u64CountTrailingOnes, u64CountTrailingZeros]
  have hval4 : (4294967295 : Felt).val = u32Max - 1 := by
    simp [GOLDILOCKS_PRIME, u32Max]; native_decide
  by_cases h : lo == (4294967295 : Felt)
  · simp only [h, ite_true]
    have heq : lo.val = u32Max - 1 := by
      rw [beq_iff_eq] at h; rw [h]; exact hval4
    rw [show lo.val ^^^ (u32Max - 1) = 0 from by
      rw [heq]; exact Nat.xor_self _]
    simp only [ite_true, Felt.ofNat]; push_cast; ring
  · simp only [Bool.not_eq_true] at h; simp only [h]
    have hne : lo.val ≠ u32Max - 1 := by
      intro heq; apply Bool.eq_false_iff.mp h
      rw [beq_iff_eq]
      exact ZMod.val_injective _ (by rw [heq, hval4])
    have hxor_ne : lo.val ^^^ (u32Max - 1) ≠ 0 := by
      intro habs; apply hne
      exact Nat.eq_of_testBit_eq fun j => by
        have := congrArg (·.testBit j) habs
        simp [Nat.testBit_xor] at this
        exact this
    simp [hxor_ne]

end MidenLean.Proofs
