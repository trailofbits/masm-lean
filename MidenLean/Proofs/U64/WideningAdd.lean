import MidenLean.Proofs.U64
import MidenLean.Proofs.Tactics
import MidenLean.Proofs.Interp
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- u64.widening_add correctly computes widening addition of two u64 values.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [c_lo, c_hi, overflow] ++ rest
    where (c_hi, c_lo) is the 64-bit sum and overflow is the carry bit. -/
theorem u64_widening_add_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    execWithEnv u64ProcEnv 10 s Miden.Core.U64.widening_add =
    some (s.withStack (
      let lo_sum := b_lo.val + a_lo.val
      let carry := lo_sum / 2^32
      let c_lo := Felt.ofNat (lo_sum % 2^32)
      let hi_sum := a_hi.val + b_hi.val + carry
      let c_hi := Felt.ofNat (hi_sum % 2^32)
      let overflow := Felt.ofNat (hi_sum / 2^32)
      c_lo :: c_hi :: overflow :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold Miden.Core.U64.widening_add execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← (match u64ProcEnv "overflowing_add" with
      | some body => execWithEnv u64ProcEnv 9 ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv⟩ body
      | none => none)
    let s' ← execInstruction s' (.movdn 2)
    pure s') = _
  simp only [u64ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  unfold Miden.Core.U64.overflowing_add execWithEnv
  simp only [List.foldlM, bind, Bind.bind, Option.bind]
  simp (config := { decide := true }) only [
    execInstruction, execMovup, removeNth, execU32WidenAdd, u32WideAdd, u32Max,
    execMovdn, insertAt,
    ha_lo, hb_lo,
    Bool.not_true, Bool.false_or, ite_false,
    MidenState.withStack, List.eraseIdx,
    List.take, List.drop, List.cons_append, List.nil_append,
    pure, Pure.pure,
    List.getElem?_cons_zero, List.getElem?_cons_succ]
  have h_mod_isU32 : (Felt.ofNat ((b_lo.val + a_lo.val) % 2 ^ 32)).isU32 = true :=
    u32_mod_isU32 _
  have h_carry_isU32 : (Felt.ofNat ((b_lo.val + a_lo.val) / 2 ^ 32)).isU32 = true :=
    u32_div_2_32_isU32 b_lo a_lo hb_lo ha_lo
  simp (config := { decide := true }) only [h_carry_isU32, ha_hi, hb_hi,
    Bool.not_true, Bool.false_or, ite_false,
    MidenState.withStack,
    execU32WidenAdd3, u32WideAdd3, u32Max,
    List.take, List.drop, List.cons_append, List.nil_append]
  have hcarry : (Felt.ofNat ((b_lo.val + a_lo.val) / 2 ^ 32)).val = (b_lo.val + a_lo.val) / 2 ^ 32 :=
    felt_ofNat_val_lt _ (sum_div_2_32_lt_prime b_lo a_lo)
  rw [hcarry]

/-- Semantic: widening_add computes
    toU64 a + toU64 b exactly (no truncation).
    Result is overflow * 2^64 + c_hi * 2^32 + c_lo. -/
theorem u64_widening_add_semantic
    (a_lo a_hi b_lo b_hi : Felt) :
    let lo_sum := b_lo.val + a_lo.val
    let carry := lo_sum / 2 ^ 32
    let hi_sum := a_hi.val + b_hi.val + carry
    (hi_sum / 2 ^ 32) * 2 ^ 64 +
      (hi_sum % 2 ^ 32) * 2 ^ 32 +
      (lo_sum % 2 ^ 32) =
    toU64 a_lo a_hi + toU64 b_lo b_hi := by
  simp only [toU64]
  omega

end MidenLean.Proofs
