import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- `u64::ctz` raw: result in terms of u32CountTrailingZeros on individual limbs. -/
theorem u64_ctz_raw (lo hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = lo :: hi :: rest)
    (hlo : lo.isU32 = true) (hhi : hi.isU32 = true) :
    exec 20 s Miden.Core.U64.ctz =
    some (s.withStack (
      (if lo == (0 : Felt)
       then Felt.ofNat (u32CountTrailingZeros hi.val) + 32
       else Felt.ofNat (u32CountTrailingZeros lo.val)) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U64.ctz execWithEnv
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
  · simp [h, MidenState.withStack]
    unfold execWithEnv; simp only [List.foldlM]
    rw [stepDrop]; miden_bind
    rw [stepU32Ctz (ha := hhi)]; miden_bind
    rw [stepAddImm]
  · simp [h, MidenState.withStack]
    unfold execWithEnv; simp only [List.foldlM]
    simp (config := { decide := true }) only [bind, Bind.bind, Option.bind, pure, Pure.pure]
    rw [stepSwap (hn := by decide) (htop := rfl) (hnth := rfl)]; miden_bind
    rw [stepDrop]; miden_bind
    rw [stepU32Ctz (ha := hlo)]

/-- `u64::ctz` correctly counts trailing zeros of a u64 value.
    Input stack:  [a.lo, a.hi] ++ rest
    Output stack: [Felt.ofNat a.countTrailingZeros] ++ rest -/
theorem u64_ctz_correct (a : U64) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a.lo :: a.hi :: rest) :
    exec 20 s Miden.Core.U64.ctz =
    some (s.withStack (Felt.ofNat a.countTrailingZeros :: rest)) := by
  have h := u64_ctz_raw a.lo a.hi rest s hs a.lo_u32 a.hi_u32
  unfold U64.countTrailingZeros
  by_cases hlo : a.lo.val = 0
  · rw [if_pos hlo, felt_ofNat_add]
    have : a.lo = (0 : Felt) := Fin.ext hlo
    simp only [this, beq_self_eq_true, ite_true] at h; exact h
  · rw [if_neg hlo]
    have : a.lo ≠ (0 : Felt) := fun heq => hlo (by rw [heq]; rfl)
    simp only [show (a.lo == (0 : Felt)) = false from decide_eq_false this, ite_false] at h
    exact h

end MidenLean.Proofs
