import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- u64.eqz correctly tests whether a u64 value is zero.
    Input stack:  [lo, hi] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff lo = hi = 0, else 0. -/
theorem u64_eqz_correct (lo hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = lo :: hi :: rest) :
    exec 10 s Miden.Core.Math.U64.eqz =
    some (s.withStack (
      (if (lo == (0:Felt)) && (hi == (0:Felt))
       then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.Math.U64.eqz execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨lo :: hi :: rest, mem, locs, adv⟩ (.eqImm 0)
    let s' ← execInstruction s' (.swap 1)
    let s' ← execInstruction s' (.eqImm 0)
    let s' ← execInstruction s' Instruction.and
    pure s') = _
  rw [stepEqImm]; miden_bind
  miden_swap
  rw [stepEqImm]; miden_bind
  rw [stepAndIte]; dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

/-- Procedure environment for u64 procedures. -/
def u64ProcEnv : ProcEnv := fun name =>
  match name with
  | "overflowing_add" => some Miden.Core.Math.U64.overflowing_add
  | "gt" => some Miden.Core.Math.U64.gt
  | "lt" => some Miden.Core.Math.U64.lt
  | _ => none

-- ============================================================================
-- Main proof: u64_overflowing_add_correct
-- ============================================================================

set_option maxHeartbeats 4000000 in
theorem u64_overflowing_add_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    exec 10 s Miden.Core.Math.U64.overflowing_add =
    some (s.withStack (
      let lo_sum := b_lo.val + a_lo.val
      let carry := lo_sum / 2^32
      let c_lo := Felt.ofNat (lo_sum % 2^32)
      let hi_sum := a_hi.val + b_hi.val + carry
      let c_hi := Felt.ofNat (hi_sum % 2^32)
      let overflow := Felt.ofNat (hi_sum / 2^32)
      overflow :: c_lo :: c_hi :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.Math.U64.overflowing_add execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv⟩ (.movup 2)
    let s' ← execInstruction s' (.u32WidenAdd)
    let s' ← execInstruction s' (.movdn 3)
    let s' ← execInstruction s' (.u32WidenAdd3)
    let s' ← execInstruction s' (.movdn 2)
    pure s') = _
  miden_movup
  rw [stepU32WidenAdd (ha := by assumption) (hb := by assumption)]; miden_bind
  miden_movdn
  have h_mod_isU32 : (Felt.ofNat ((b_lo.val + a_lo.val) % 2 ^ 32)).isU32 = true :=
    u32_mod_isU32 _
  have h_carry_isU32 : (Felt.ofNat ((b_lo.val + a_lo.val) / 2 ^ 32)).isU32 = true :=
    u32_div_2_32_isU32 b_lo a_lo hb_lo ha_lo
  rw [stepU32WidenAdd3 (ha := by assumption) (hb := by assumption) (hc := by assumption)]; miden_bind
  miden_movdn
  dsimp only [pure, Pure.pure]
  have hcarry : (Felt.ofNat ((b_lo.val + a_lo.val) / 2 ^ 32)).val = (b_lo.val + a_lo.val) / 2 ^ 32 :=
    felt_ofNat_val_lt _ (sum_div_2_32_lt_prime b_lo a_lo)
  rw [hcarry]

-- ============================================================================
-- Main proof: u64_wrapping_add_correct
-- ============================================================================

set_option maxHeartbeats 4000000 in
theorem u64_wrapping_add_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    execWithEnv u64ProcEnv 10 s Miden.Core.Math.U64.wrapping_add =
    some (s.withStack (
      let lo_sum := b_lo.val + a_lo.val
      let carry := lo_sum / 2^32
      let c_lo := Felt.ofNat (lo_sum % 2^32)
      let hi_sum := a_hi.val + b_hi.val + carry
      let c_hi := Felt.ofNat (hi_sum % 2^32)
      c_lo :: c_hi :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold Miden.Core.Math.U64.wrapping_add execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← (match u64ProcEnv "overflowing_add" with
      | some body => execWithEnv u64ProcEnv 9 ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv⟩ body
      | none => none)
    let s' ← execInstruction s' (.drop)
    pure s') = _
  simp only [u64ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  unfold Miden.Core.Math.U64.overflowing_add execWithEnv
  simp only [List.foldlM]
  -- Normalize and reduce the entire chain via simp/decide
  simp only [List.foldlM, bind, Bind.bind, Option.bind, MidenState.withStack]
  simp (config := { decide := true }) only [
    execInstruction, execMovup, removeNth, execU32WidenAdd, u32WideAdd, u32Max,
    execMovdn, insertAt, execU32WidenAdd3, u32WideAdd3, execDrop,
    ha_lo, hb_lo, ha_hi, hb_hi,
    Bool.not_true, Bool.false_or, ite_false, ite_true,
    MidenState.withStack, List.eraseIdx, List.set,
    List.take, List.drop, List.cons_append, List.nil_append,
    pure, Pure.pure, bind, Bind.bind, Option.bind,
    List.getElem?_cons_zero, List.getElem?_cons_succ]
  have h_mod_isU32 : (Felt.ofNat ((b_lo.val + a_lo.val) % 2 ^ 32)).isU32 = true :=
    u32_mod_isU32 _
  have h_carry_isU32 : (Felt.ofNat ((b_lo.val + a_lo.val) / 2 ^ 32)).isU32 = true :=
    u32_div_2_32_isU32 b_lo a_lo hb_lo ha_lo
  -- Reduce all remaining matches and if-then-else
  simp (config := { decide := true }) only [h_mod_isU32, h_carry_isU32, ha_hi, hb_hi,
    Bool.not_true, Bool.false_or, ite_false, ite_true,
    MidenState.withStack, pure, Pure.pure, bind, Bind.bind, Option.bind,
    execU32WidenAdd3, u32WideAdd3, u32Max,
    execMovdn, insertAt, execDrop,
    List.take, List.drop, List.cons_append, List.nil_append]
  have hcarry : (Felt.ofNat ((b_lo.val + a_lo.val) / 2 ^ 32)).val = (b_lo.val + a_lo.val) / 2 ^ 32 :=
    felt_ofNat_val_lt _ (sum_div_2_32_lt_prime b_lo a_lo)
  rw [hcarry]

end MidenLean.Proofs
