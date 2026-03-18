import MidenLean.Proofs.U64
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Helper lemma
-- ============================================================================

/-- Normalize 4294967296 back to 2^32 after dsimp normalization. -/
private theorem nat_4294967296_eq : (4294967296 : Nat) = 2^32 := by norm_num

/-- The or operation on ite-form booleans produces an ite-form boolean
    (raw form before ite_mul_ite fires on the product). -/
private theorem Felt.ite_or_ite (p q : Bool) :
    (if p then (1 : Felt) else 0) + (if q then (1 : Felt) else 0) -
    (if p then (1 : Felt) else 0) * (if q then (1 : Felt) else 0) =
    if (p || q) then (1 : Felt) else 0 := by
  cases p <;> cases q <;> simp

/-- The or operation after ite_mul_ite has already fired on the product. -/
private theorem Felt.ite_or_ite' (p q : Bool) :
    (if p then (1 : Felt) else 0) + (if q then (1 : Felt) else 0) -
    (if (p && q) then (1 : Felt) else 0) =
    if (p || q) then (1 : Felt) else 0 := by
  cases p <;> cases q <;> simp

set_option maxHeartbeats 80000000 in
/-- u64.divmod verifies that the quotient and remainder provided on the advice
    stack satisfy a = q * b + r with r < b.

    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Advice stack: [q_lo, q_hi, r_lo, r_hi] ++ adv_rest
    Output stack: [r_hi, r_lo, q_hi, q_lo] ++ rest
    Advice after: adv_rest -/
theorem u64_divmod_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt)
    (q_lo q_hi r_lo r_hi : Felt) (adv_rest : List Felt)
    (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (hadv : s.advice = q_lo :: q_hi :: r_lo :: r_hi :: adv_rest)
    (hq_hi_u32 : q_hi.isU32 = true)
    (hq_lo_u32 : q_lo.isU32 = true)
    (hr_hi_u32 : r_hi.isU32 = true)
    (hr_lo_u32 : r_lo.isU32 = true)
    (hb_lo_u32 : b_lo.isU32 = true)
    (hb_hi_u32 : b_hi.isU32 = true)
    (cross0_hi_val : (Felt.ofNat ((b_lo.val * q_hi.val) / 2^32)).val =
        (b_lo.val * q_hi.val) / 2^32)
    (h_madd1_hi_zero : (Felt.ofNat ((b_hi.val * q_hi.val +
        (b_lo.val * q_hi.val) / 2^32) / 2^32) == (0 : Felt)) = true)
    (madd1_lo_val : (Felt.ofNat ((b_hi.val * q_hi.val +
        (b_lo.val * q_hi.val) / 2^32) % 2^32)).val =
        (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32)
    (h_madd2_hi_zero : (Felt.ofNat ((b_lo.val * q_lo.val +
        (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) / 2^32) ==
        (0 : Felt)) = true)
    (h_bhi_qlo_zero : ((b_hi * q_lo : Felt) == (0 : Felt)) = true)
    (cross0_lo_val : (Felt.ofNat ((b_lo.val * q_hi.val) % 2^32)).val =
        (b_lo.val * q_hi.val) % 2^32)
    (madd2_lo_val : (Felt.ofNat ((b_lo.val * q_lo.val +
        (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32)).val =
        (b_lo.val * q_lo.val +
        (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32)
    (h_lt_result :
        let borrow_lo := decide (r_hi.val < b_lo.val)
        let borrow_hi := decide (r_lo.val < b_hi.val)
        let hi_eq := Felt.ofNat (u32OverflowingSub r_lo.val b_hi.val).2 == (0 : Felt)
        (borrow_hi || (hi_eq && borrow_lo)) = true)
    (h_add2_hi_zero : (Felt.ofNat ((r_lo.val +
        (b_lo.val * q_lo.val +
          (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32 +
        (r_hi.val + (b_lo.val * q_hi.val) % 2^32) / 2^32) / 2^32) ==
        (0 : Felt)) = true)
    (h_a_hi_eq : a_hi = Felt.ofNat ((r_lo.val +
        (b_lo.val * q_lo.val +
          (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32 +
        (r_hi.val + (b_lo.val * q_hi.val) % 2^32) / 2^32) % 2^32))
    (h_a_lo_eq : a_lo = Felt.ofNat ((r_hi.val +
        (b_lo.val * q_hi.val) % 2^32) % 2^32)) :
    execWithEnv u64ProcEnv 50 s Miden.Core.U64.divmod =
    some { stack := r_hi :: r_lo :: q_hi :: q_lo :: rest,
           memory := s.memory,
           locals := s.locals,
           advice := adv_rest } := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [] at hs hadv ⊢
  subst hs; subst hadv
  -- Establish all isU32 hypotheses for intermediate values upfront
  have h_cross0_lo_isU32 : (Felt.ofNat ((b_lo.val * q_hi.val) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  have h_cross0_hi_isU32 : (Felt.ofNat ((b_lo.val * q_hi.val) / 2^32)).isU32 = true :=
    u32_prod_div_isU32 b_lo q_hi hb_lo_u32 hq_hi_u32
  have h_madd1_lo_isU32 : (Felt.ofNat ((b_hi.val * q_hi.val +
      (b_lo.val * q_hi.val) / 2^32) % 2^32)).isU32 = true := u32_mod_isU32 _
  have h_madd2_lo_isU32 : (Felt.ofNat ((b_lo.val * q_lo.val +
      (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  have h_add1_lo_isU32 : (Felt.ofNat ((r_hi.val + (b_lo.val * q_hi.val) % 2^32) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  have h_add1_hi_isU32 : (Felt.ofNat ((r_hi.val + (b_lo.val * q_hi.val) % 2^32) / 2^32)).isU32 = true := by
    apply felt_ofNat_isU32_of_lt
    simp only [Felt.isU32, decide_eq_true_eq] at hr_hi_u32
    have h2 : (b_lo.val * q_hi.val) % 2^32 < 2^32 := Nat.mod_lt _ (by norm_num)
    omega
  -- Substitute the equality hypotheses for assertEqWithError
  subst h_a_hi_eq; subst h_a_lo_eq
  -- Unfold divmod, resolve ProcEnv for the exec "lt" call
  unfold Miden.Core.U64.divmod execWithEnv
  simp only [List.foldlM, u64ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Unfold the lt procedure body for the exec call
  unfold Miden.Core.U64.lt execWithEnv
  simp only [List.foldlM, bind, Bind.bind, Option.bind, pure, Pure.pure]
  -- Use a single big simp pass with all exec handlers, isU32 hypotheses,
  -- value recovery hypotheses, and boolean simplification.
  -- Key: include List.reverseAux to fully reduce advPush results,
  -- and Fin.val to reduce Fin 16 coercions for dup/swap/movup/movdn indices.
  simp (config := { decide := true }) only [
    execInstruction, execAdvPush, execU32Assert2, execDup, execU32WidenMul,
    u32WideMul, u32Max, execSwap, execU32WidenMadd, u32WideMadd, execEqImm,
    execAssert, execU32WidenAdd, u32WideAdd, execU32WidenAdd3, u32WideAdd3,
    execMul, execDrop, execMovup, removeNth, execMovdn, insertAt,
    execU32OverflowSub, execEq, execAnd, execOr, execAssertEq,
    hq_hi_u32, hq_lo_u32, hr_hi_u32, hr_lo_u32, hb_lo_u32, hb_hi_u32,
    h_cross0_lo_isU32, h_cross0_hi_isU32, h_madd1_lo_isU32, h_madd2_lo_isU32,
    h_add1_lo_isU32, h_add1_hi_isU32,
    cross0_hi_val, cross0_lo_val, madd1_lo_val, madd2_lo_val,
    h_madd1_hi_zero, h_madd2_hi_zero, h_bhi_qlo_zero,
    h_lt_result, h_add2_hi_zero,
    u32OverflowingSub_borrow_ite,
    Felt.isBool_ite_bool, Felt.ite_mul_ite, Felt.ite_or_ite, Felt.ite_or_ite',
    Bool.not_true, Bool.false_or, Bool.true_or, ite_false, ite_true,
    Bool.not_false, Bool.false_and, Bool.true_and,
    MidenState.withStack, MidenState.withAdvice,
    List.eraseIdx, List.set, List.take, List.drop,
    List.reverse, List.reverseAux,
    List.cons_append, List.nil_append, List.append_nil,
    Fin.coe_ofNat_eq_mod, getElem?_pos,
    List.getElem_cons_succ, List.getElem_cons_zero,
    List.length_cons, lt_add_iff_pos_left, Order.lt_add_one_iff, Nat.zero_le,
    List.length, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.succ_lt_succ_iff, not_lt_zero',
    pure, Pure.pure, bind, Bind.bind, Option.bind]
  trace_state
  sorry

end MidenLean.Proofs
