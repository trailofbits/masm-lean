import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.U64.Divmod
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `u64::mod` computes the remainder of two u64 values by calling divmod,
    then rearranging the stack to keep only the remainder.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Advice stack: [q_lo, q_hi, r_lo, r_hi] ++ adv_rest
    Output stack: [r_hi, r_lo] ++ rest
    Same preconditions as divmod. -/
theorem u64_mod_raw
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
    execWithEnv u64ProcEnv 51 s Miden.Core.U64.mod =
    some { stack := r_hi :: r_lo :: rest,
           memory := s.memory,
           locals := s.locals,
           advice := adv_rest } := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [] at hadv
  subst hs; subst hadv
  -- Unfold mod: exec "divmod"; movup 2; drop; movup 2; drop
  unfold Miden.Core.U64.mod execWithEnv
  simp only [List.foldlM, u64ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- The exec "divmod" resolves and calls execWithEnv u64ProcEnv 50 s divmod_body
  rw [show execWithEnv u64ProcEnv 50
    ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, q_lo :: q_hi :: r_lo :: r_hi :: adv_rest⟩
    Miden.Core.U64.divmod =
    some { stack := r_hi :: r_lo :: q_hi :: q_lo :: rest,
           memory := mem, locals := locs, advice := adv_rest }
    from u64_divmod_raw a_lo a_hi b_lo b_hi rest q_lo q_hi r_lo r_hi adv_rest
      ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, q_lo :: q_hi :: r_lo :: r_hi :: adv_rest⟩
      rfl rfl hq_hi_u32 hq_lo_u32 hr_hi_u32 hr_lo_u32 hb_lo_u32 hb_hi_u32
      cross0_hi_val h_madd1_hi_zero madd1_lo_val h_madd2_hi_zero h_bhi_qlo_zero
      cross0_lo_val madd2_lo_val h_lt_result h_add2_hi_zero h_a_hi_eq h_a_lo_eq]
  -- Reduce match (some {...}) to expose execInstruction calls
  simp only []
  -- Now stack is [r_hi, r_lo, q_hi, q_lo | rest]
  -- mod does: movup 2; drop; movup 2; drop
  miden_movup
  miden_step
  miden_movup
  rw [stepDrop]; dsimp only [pure, Pure.pure]

set_option maxHeartbeats 4000000 in
/-- `u64::mod` verifies and returns the remainder of two u64 values.
    Execution succeeds iff the advice-supplied q and r satisfy q * b + r = a and r < b.
    Input stack:  [b.lo, b.hi, a.lo, a.hi] ++ rest
    Advice stack: [q.hi, q.lo, r.hi, r.lo] ++ adv_rest
    Output stack: [r.lo, r.hi] ++ rest -/
theorem u64_mod_correct (a b q r : U64) (rest : List Felt) (adv_rest : List Felt)
    (s : MidenState)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest)
    (hadv : s.advice = q.hi.val :: q.lo.val :: r.hi.val :: r.lo.val :: adv_rest) :
    execWithEnv u64ProcEnv 51 s Miden.Core.U64.mod =
    some { stack := r.lo.val :: r.hi.val :: rest,
           memory := s.memory,
           locals := s.locals,
           advice := adv_rest }
    ↔ (q.toNat * b.toNat + r.toNat = a.toNat ∧ r.toNat < b.toNat) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [] at hs hadv; subst hs; subst hadv
  constructor
  · -- Forward: mod success → conditions
    intro hexec
    unfold Miden.Core.U64.mod execWithEnv at hexec
    simp only [List.foldlM, u64ProcEnv] at hexec
    revert hexec
    cases h_dm : execWithEnv u64ProcEnv 50
      { stack := b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest, memory := mem, locals := locs,
        advice := q.hi.val :: q.lo.val :: r.hi.val :: r.lo.val :: adv_rest }
      Miden.Core.U64.divmod with
    | none => simp [bind, Bind.bind, Option.bind]
    | some val =>
      intro _
      exact divmod_conditions_of_exec a b q r rest adv_rest _ rfl rfl h_dm
  · -- Backward: conditions → mod success
    intro ⟨hdiv, hlt⟩
    have h_divmod := (u64_divmod_correct a b q r rest adv_rest
      ⟨b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest, mem, locs,
       q.hi.val :: q.lo.val :: r.hi.val :: r.lo.val :: adv_rest⟩ rfl rfl).mpr ⟨hdiv, hlt⟩
    unfold Miden.Core.U64.mod execWithEnv
    simp only [List.foldlM, u64ProcEnv]
    dsimp only [bind, Bind.bind, Option.bind]
    rw [h_divmod]
    simp only []
    miden_movup
    miden_step
    miden_movup
    rw [stepDrop]; dsimp only [pure, Pure.pure]

end MidenLean.Proofs
