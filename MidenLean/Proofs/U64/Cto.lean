import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- `u64::cto` raw: result in terms of u32CountTrailingZeros on XOR-complemented limbs. -/
theorem u64_cto_raw (lo hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = lo :: hi :: rest)
    (hlo : lo.isU32 = true) (hhi : hi.isU32 = true) :
    exec 20 s Miden.Core.U64.cto =
    some (s.withStack (
      (if lo == (4294967295 : Felt)
       then Felt.ofNat (u32CountTrailingZeros (hi.val ^^^ (u32Max - 1))) + 32
       else Felt.ofNat (u32CountTrailingZeros (lo.val ^^^ (u32Max - 1)))) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U64.cto execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨lo :: hi :: rest, mem, locs, adv⟩ (.dup 0)
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
  · simp [h, MidenState.withStack]
    unfold execWithEnv; simp only [List.foldlM]
    rw [stepDrop]; miden_bind
    rw [stepU32Cto (ha := hhi)]; miden_bind
    rw [stepAddImm]
  · simp [h, MidenState.withStack]
    unfold execWithEnv; simp only [List.foldlM]
    simp (config := { decide := true }) only [bind, Bind.bind, Option.bind, pure, Pure.pure]
    rw [stepSwap (hn := by decide) (htop := rfl) (hnth := rfl)]; miden_bind
    rw [stepDrop]; miden_bind
    rw [stepU32Cto (ha := hlo)]

/-- `u64::cto` correctly counts trailing ones of a u64 value.
    Input stack:  [a.lo, a.hi] ++ rest
    Output stack: [Felt.ofNat a.countTrailingOnes] ++ rest -/
theorem u64_cto_correct (a : U64) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a.lo :: a.hi :: rest) :
    exec 20 s Miden.Core.U64.cto =
    some (s.withStack (Felt.ofNat a.countTrailingOnes :: rest)) := by
  have h := u64_cto_raw a.lo a.hi rest s hs a.lo_u32 a.hi_u32
  unfold U64.countTrailingOnes u32CountTrailingOnes
  by_cases hlo : a.lo.val = 2^32 - 1
  · rw [if_pos hlo, felt_ofNat_add]
    have : a.lo = (4294967295 : Felt) := Fin.ext (by simpa using hlo)
    simp only [this, beq_self_eq_true, ite_true] at h; exact h
  · rw [if_neg hlo]
    have : a.lo ≠ (4294967295 : Felt) := fun heq => hlo (by
      have := congrArg ZMod.val heq; simpa using this)
    simp only [show (a.lo == (4294967295 : Felt)) = false from decide_eq_false this,
      ite_false] at h
    exact h

end MidenLean.Proofs
