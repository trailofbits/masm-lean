import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- `u64::clo` raw: result in terms of u32CountLeadingZeros on complemented limbs. -/
theorem u64_clo_raw (lo hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = lo :: hi :: rest)
    (hlo : lo.isU32 = true) (hhi : hi.isU32 = true) :
    exec 20 s Miden.Core.U64.clo =
    some (s.withStack (
      (if hi == (4294967295 : Felt)
       then Felt.ofNat (u32CountLeadingZeros (u32Max - 1 - lo.val)) + 32
       else Felt.ofNat (u32CountLeadingZeros (u32Max - 1 - hi.val))) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U64.clo execWithEnv
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
  · simp [h, MidenState.withStack]
    unfold execWithEnv; simp only [List.foldlM]
    rw [stepDrop]; miden_bind
    rw [stepU32Clo (ha := hlo)]; miden_bind
    rw [stepAddImm]
  · simp [h, MidenState.withStack]
    unfold execWithEnv; simp only [List.foldlM]
    simp (config := { decide := true }) only [bind, Bind.bind, Option.bind, pure, Pure.pure]
    rw [stepSwap (hn := by decide) (htop := rfl) (hnth := rfl)]; miden_bind
    rw [stepDrop]; miden_bind
    rw [stepU32Clo (ha := hhi)]

/-- `u64::clo` correctly counts leading ones of a u64 value.
    Input stack:  [a.lo, a.hi] ++ rest
    Output stack: [Felt.ofNat a.countLeadingOnes] ++ rest -/
theorem u64_clo_correct (a : U64) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a.lo.val :: a.hi.val :: rest) :
    exec 20 s Miden.Core.U64.clo =
    some (s.withStack (Felt.ofNat a.countLeadingOnes :: rest)) := by
  have h := u64_clo_raw a.lo.val a.hi.val rest s hs a.lo.isU32 a.hi.isU32
  unfold U64.countLeadingOnes u32CountLeadingOnes
  by_cases hhi : a.hi.val.val = 2^32 - 1
  · rw [if_pos hhi, felt_ofNat_add]
    have : a.hi.val = (4294967295 : Felt) := Fin.ext (by simpa using hhi)
    simp only [this, beq_self_eq_true, ite_true] at h; exact h
  · rw [if_neg hhi]
    have : a.hi.val ≠ (4294967295 : Felt) := fun heq => hhi (by
      have := congrArg ZMod.val heq; simpa using this)
    simp only [show (a.hi.val == (4294967295 : Felt)) = false from decide_eq_false this] at h
    exact h

end MidenLean.Proofs
