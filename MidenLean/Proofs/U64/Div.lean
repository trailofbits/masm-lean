import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.U64.Divmod
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- u64.div computes the quotient of two u64 values by calling divmod and dropping
    the remainder.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Advice stack: [q_hi, q_lo, r_hi, r_lo] ++ adv_rest
    Output stack: [q_lo, q_hi] ++ rest
    Same preconditions as divmod. -/
theorem u64_div_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt)
    (q_lo q_hi r_lo r_hi : Felt) (adv_rest : List Felt)
    (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (hadv : s.advice = q_hi :: q_lo :: r_hi :: r_lo :: adv_rest)
    (hq_hi_u32 : q_hi.isU32 = true)
    (hq_lo_u32 : q_lo.isU32 = true)
    (hr_hi_u32 : r_hi.isU32 = true)
    (hr_lo_u32 : r_lo.isU32 = true)
    (hb_lo_u32 : b_lo.isU32 = true)
    (hb_hi_u32 : b_hi.isU32 = true)
    (p1_hi_val : (Felt.ofNat ((b_lo.val * q_lo.val) / 2^32)).val =
        (b_lo.val * q_lo.val) / 2^32)
    (h_p2_hi_zero : (Felt.ofNat ((b_hi.val * q_lo.val +
        (b_lo.val * q_lo.val) / 2^32) / 2^32) == (0 : Felt)) = true)
    (p2_lo_val : (Felt.ofNat ((b_hi.val * q_lo.val +
        (b_lo.val * q_lo.val) / 2^32) % 2^32)).val =
        (b_hi.val * q_lo.val + (b_lo.val * q_lo.val) / 2^32) % 2^32)
    (h_p3_hi_zero : (Felt.ofNat ((b_lo.val * q_hi.val +
        (b_hi.val * q_lo.val + (b_lo.val * q_lo.val) / 2^32) % 2^32) / 2^32) ==
        (0 : Felt)) = true)
    (h_qhi_bhi_zero : ((b_hi * q_hi : Felt) == (0 : Felt)) = true)
    (p1_lo_val : (Felt.ofNat ((b_lo.val * q_lo.val) % 2^32)).val =
        (b_lo.val * q_lo.val) % 2^32)
    (p3_lo_val : (Felt.ofNat ((b_lo.val * q_hi.val +
        (b_hi.val * q_lo.val + (b_lo.val * q_lo.val) / 2^32) % 2^32) % 2^32)).val =
        (b_lo.val * q_hi.val +
        (b_hi.val * q_lo.val + (b_lo.val * q_lo.val) / 2^32) % 2^32) % 2^32)
    (h_lt_result :
        let borrow_lo := decide (r_lo.val < b_lo.val)
        let borrow_hi := decide (r_hi.val < b_hi.val)
        let hi_eq := Felt.ofNat (u32OverflowingSub r_hi.val b_hi.val).2 == (0 : Felt)
        (borrow_hi || (hi_eq && borrow_lo)) = true)
    (h_carry_hi_zero : (Felt.ofNat ((r_hi.val +
        (b_lo.val * q_hi.val +
          (b_hi.val * q_lo.val + (b_lo.val * q_lo.val) / 2^32) % 2^32) % 2^32 +
        (r_lo.val + (b_lo.val * q_lo.val) % 2^32) / 2^32) / 2^32) ==
        (0 : Felt)) = true)
    (h_a_hi_eq : a_hi = Felt.ofNat ((r_hi.val +
        (b_lo.val * q_hi.val +
          (b_hi.val * q_lo.val + (b_lo.val * q_lo.val) / 2^32) % 2^32) % 2^32 +
        (r_lo.val + (b_lo.val * q_lo.val) % 2^32) / 2^32) % 2^32))
    (h_a_lo_eq : a_lo = Felt.ofNat ((r_lo.val +
        (b_lo.val * q_lo.val) % 2^32) % 2^32)) :
    execWithEnv u64ProcEnv 51 s Miden.Core.U64.div =
    some { stack := q_lo :: q_hi :: rest,
           memory := s.memory,
           locals := s.locals,
           advice := adv_rest } := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [] at hs ⊢
  simp only [] at hadv
  subst hs; subst hadv
  unfold Miden.Core.U64.div execWithEnv
  simp only [List.foldlM, u64ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  rw [show execWithEnv u64ProcEnv 50
    ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, q_hi :: q_lo :: r_hi :: r_lo :: adv_rest⟩
    Miden.Core.U64.divmod =
    some { stack := r_lo :: r_hi :: q_lo :: q_hi :: rest,
           memory := mem, locals := locs, advice := adv_rest }
    from u64_divmod_correct a_lo a_hi b_lo b_hi rest q_lo q_hi r_lo r_hi adv_rest
      ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, q_hi :: q_lo :: r_hi :: r_lo :: adv_rest⟩
      rfl rfl hq_hi_u32 hq_lo_u32 hr_hi_u32 hr_lo_u32 hb_lo_u32 hb_hi_u32
      p1_hi_val h_p2_hi_zero p2_lo_val h_p3_hi_zero h_qhi_bhi_zero
      p1_lo_val p3_lo_val h_lt_result h_carry_hi_zero h_a_hi_eq h_a_lo_eq]
  simp only []
  miden_step
  rw [stepDrop]; dsimp only [pure, Pure.pure]

end MidenLean.Proofs
