import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- `u64::clz` raw: result in terms of u32CountLeadingZeros on individual limbs. -/
theorem u64_clz_raw (lo hi : Felt) (rest : List Felt) (s : MidenState)
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
    simp [h, MidenState.withStack]
    unfold execWithEnv; simp only [List.foldlM]
    rw [stepDrop]; miden_bind
    rw [stepU32Clz (ha := hlo)]; miden_bind
    rw [stepAddImm]
  · -- Case: hi != 0 (else branch)
    simp [h, MidenState.withStack]
    unfold execWithEnv; simp only [List.foldlM]
    simp (config := { decide := true }) only [bind, Bind.bind, Option.bind, pure, Pure.pure]
    rw [stepSwap (hn := by decide) (htop := rfl) (hnth := rfl)]; miden_bind
    rw [stepDrop]; miden_bind
    rw [stepU32Clz (ha := hhi)]

/-- `u64::clz` correctly counts leading zeros of a u64 value.
    Input stack:  [a.lo, a.hi] ++ rest
    Output stack: [Felt.ofNat a.countLeadingZeros] ++ rest -/
theorem u64_clz_correct (a : U64) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a.lo :: a.hi :: rest) :
    exec 20 s Miden.Core.U64.clz =
    some (s.withStack (Felt.ofNat a.countLeadingZeros :: rest)) := by
  have h := u64_clz_raw a.lo a.hi rest s hs a.lo_u32 a.hi_u32
  unfold U64.countLeadingZeros
  by_cases hhi : a.hi.val = 0
  · rw [if_pos hhi, felt_ofNat_add]
    have : a.hi = (0 : Felt) := Fin.ext hhi
    simp only [this, beq_self_eq_true, ite_true] at h; exact h
  · rw [if_neg hhi]
    have : a.hi ≠ (0 : Felt) := fun heq => hhi (by rw [heq]; rfl)
    simp only [show (a.hi == (0 : Felt)) = false from decide_eq_false this, ite_false] at h
    exact h

end MidenLean.Proofs
