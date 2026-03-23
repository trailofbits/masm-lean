import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- Execute a concatenation of op lists in two phases. -/
private theorem execWithEnv_append (env : ProcEnv) (fuel : Nat) (s : MidenState) (xs ys : List Op) :
    execWithEnv env fuel s (xs ++ ys) = (do
      let s' ← execWithEnv env fuel s xs
      execWithEnv env fuel s' ys) := by
  unfold execWithEnv
  cases fuel <;> simp [List.foldlM_append]

private def divmod_chunk1a : List Op := [
  .inst (.emitImm 14153021663962350784),
  .inst (.advPush 2),
  .inst (.u32Assert2),
  .inst (.dup 2),
  .inst (.dup 1),
  .inst (.u32WidenMul),
  .inst (.swap 1),
  .inst (.dup 5),
  .inst (.dup 3),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.eqImm 0),
  .inst (.assertWithError "comparison failed: divmod")
]

private def divmod_chunk1b : List Op := [
  .inst (.dup 4),
  .inst (.dup 4),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.eqImm 0),
  .inst (.assertWithError "comparison failed: divmod")
]

private def divmod_chunk1c : List Op := [
  .inst (.dup 5),
  .inst (.dup 4),
  .inst (.mul),
  .inst (.eqImm 0),
  .inst (.assertWithError "comparison failed: divmod"),
  .inst (.advPush 2),
  .inst (.u32Assert2)
]

private def divmod_chunk2 : List Op := [
  .inst (.movup 6),
  .inst (.movup 7),
  .inst (.swap 1),
  .inst (.dup 3),
  .inst (.dup 3),
  .inst (.movup 3),
  .inst (.movup 3),
  .inst (.exec "lt"),
  .inst (.assertWithError "comparison failed: divmod")
]

private def divmod_chunk3a : List Op := [
  .inst (.dup 0),
  .inst (.movup 4),
  .inst (.u32WidenAdd),
  .inst (.swap 1)
]

private def divmod_chunk3b : List Op := [
  .inst (.dup 3),
  .inst (.movup 5),
  .inst (.movup 2),
  .inst (.u32WidenAdd3),
  .inst (.swap 1),
  .inst (.eqImm 0),
  .inst (.assertWithError "comparison failed: divmod"),
  .inst (.movup 7),
  .inst (.assertEqWithError "comparison failed: divmod"),
  .inst (.movup 5),
  .inst (.assertEqWithError "comparison failed: divmod")
]

private theorem divmod_decomp :
    Miden.Core.U64.divmod =
      divmod_chunk1a ++
        (divmod_chunk1b ++ (divmod_chunk1c ++ (divmod_chunk2 ++ (divmod_chunk3a ++ divmod_chunk3b)))) := by
  simp [Miden.Core.U64.divmod, divmod_chunk1a, divmod_chunk1b, divmod_chunk1c, divmod_chunk2,
    divmod_chunk3a, divmod_chunk3b]

set_option maxHeartbeats 12000000 in
private theorem divmod_chunk1a_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt)
    (q_lo q_hi r_lo r_hi : Felt) (adv_rest : List Felt)
    (mem locs : Nat → Felt)
    (hq_hi_u32 : q_hi.isU32 = true)
    (hq_lo_u32 : q_lo.isU32 = true)
    (hb_lo_u32 : b_lo.isU32 = true)
    (hb_hi_u32 : b_hi.isU32 = true)
    (cross0_hi_val : (Felt.ofNat ((b_lo.val * q_hi.val) / 2^32)).val =
        (b_lo.val * q_hi.val) / 2^32)
    (h_madd1_hi_zero : (Felt.ofNat ((b_hi.val * q_hi.val +
        (b_lo.val * q_hi.val) / 2^32) / 2^32) == (0 : Felt)) = true) :
    let cross0_lo := Felt.ofNat ((b_lo.val * q_hi.val) % 2^32)
    let madd1_lo := Felt.ofNat ((b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32)
    execWithEnv u64ProcEnv 50
      { stack := b_lo :: b_hi :: a_lo :: a_hi :: rest,
        memory := mem, locals := locs,
        advice := q_lo :: q_hi :: r_lo :: r_hi :: adv_rest }
      divmod_chunk1a =
    some { stack := madd1_lo :: cross0_lo :: q_hi :: q_lo :: b_lo :: b_hi :: a_lo :: a_hi :: rest,
           memory := mem, locals := locs, advice := r_lo :: r_hi :: adv_rest } := by
  simp only []
  unfold divmod_chunk1a execWithEnv
  simp only [List.foldlM]
  have h_cross0_hi_u32 : (Felt.ofNat ((b_lo.val * q_hi.val) / 2^32)).isU32 = true :=
    u32_prod_div_isU32 b_lo q_hi hb_lo_u32 hq_hi_u32
  have h_madd1_hi_eq : Felt.ofNat ((b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) / 2^32) = 0 :=
    LawfulBEq.eq_of_beq h_madd1_hi_zero
  have h_madd1_assert :
      ((if Felt.ofNat ((b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) / 2^32) = (0 : Felt)
        then (1 : Felt) else 0) : Felt).val = 1 := by
    rw [h_madd1_hi_eq]
    simp
  rw [show execInstruction
      { stack := b_lo :: b_hi :: a_lo :: a_hi :: rest,
        memory := mem,
        locals := locs,
        advice := q_lo :: q_hi :: r_lo :: r_hi :: adv_rest }
      (Instruction.emitImm 14153021663962350784) =
      some { stack := b_lo :: b_hi :: a_lo :: a_hi :: rest,
             memory := mem,
             locals := locs,
             advice := q_lo :: q_hi :: r_lo :: r_hi :: adv_rest } by
      unfold execInstruction
      rfl]
  miden_bind
  rw [stepAdvPush2 (hadv := rfl)]; miden_bind
  rw [stepU32Assert2 (ha := hq_hi_u32) (hb := hq_lo_u32)]; miden_bind
  miden_dup
  miden_dup
  rw [stepU32WidenMul (ha := hb_lo_u32) (hb := hq_hi_u32)]; miden_bind
  miden_swap
  miden_dup
  miden_dup
  rw [stepU32WidenMadd (ha := hb_hi_u32) (hb := hq_hi_u32) (hc := h_cross0_hi_u32)]; miden_bind
  rw [cross0_hi_val]
  miden_swap
  rw [stepEqImm]; miden_bind
  simp only [beq_iff_eq]
  rw [stepAssertWithError (h := h_madd1_assert)]
  miden_bind
  simp only [pure, Pure.pure]

set_option maxHeartbeats 12000000 in
private theorem divmod_chunk1b_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt)
    (q_lo q_hi r_lo r_hi : Felt) (adv_rest : List Felt)
    (mem locs : Nat → Felt)
    (hq_lo_u32 : q_lo.isU32 = true)
    (hb_lo_u32 : b_lo.isU32 = true)
    (madd1_lo_val : (Felt.ofNat ((b_hi.val * q_hi.val +
        (b_lo.val * q_hi.val) / 2^32) % 2^32)).val =
        (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32)
    (h_madd2_hi_zero : (Felt.ofNat ((b_lo.val * q_lo.val +
        (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) / 2^32) ==
        (0 : Felt)) = true) :
    let cross0_lo := Felt.ofNat ((b_lo.val * q_hi.val) % 2^32)
    let madd1_lo := Felt.ofNat ((b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32)
    let madd2_lo := Felt.ofNat ((b_lo.val * q_lo.val +
      (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32)
    execWithEnv u64ProcEnv 50
      { stack := madd1_lo :: cross0_lo :: q_hi :: q_lo :: b_lo :: b_hi :: a_lo :: a_hi :: rest,
        memory := mem, locals := locs, advice := r_lo :: r_hi :: adv_rest }
      divmod_chunk1b =
    some { stack := madd2_lo :: cross0_lo :: q_hi :: q_lo :: b_lo :: b_hi :: a_lo :: a_hi :: rest,
           memory := mem, locals := locs, advice := r_lo :: r_hi :: adv_rest } := by
  simp only []
  unfold divmod_chunk1b execWithEnv
  simp only [List.foldlM]
  have h_madd1_lo_u32 : (Felt.ofNat ((b_hi.val * q_hi.val +
      (b_lo.val * q_hi.val) / 2^32) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  have h_madd2_hi_eq : Felt.ofNat ((b_lo.val * q_lo.val +
      (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) / 2^32) = 0 :=
    LawfulBEq.eq_of_beq h_madd2_hi_zero
  have h_madd2_assert :
      ((if Felt.ofNat ((b_lo.val * q_lo.val +
          (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) / 2^32) = (0 : Felt)
        then (1 : Felt) else 0) : Felt).val = 1 := by
    rw [h_madd2_hi_eq]
    simp
  miden_dup
  miden_dup
  rw [stepU32WidenMadd (ha := hb_lo_u32) (hb := hq_lo_u32) (hc := h_madd1_lo_u32)]; miden_bind
  rw [madd1_lo_val]
  miden_swap
  rw [stepEqImm]; miden_bind
  simp only [beq_iff_eq]
  rw [stepAssertWithError (h := h_madd2_assert)]
  miden_bind
  simp only [pure, Pure.pure]

set_option maxHeartbeats 12000000 in
private theorem divmod_chunk1c_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt)
    (q_lo q_hi r_lo r_hi : Felt) (adv_rest : List Felt)
    (mem locs : Nat → Felt)
    (hr_hi_u32 : r_hi.isU32 = true)
    (hr_lo_u32 : r_lo.isU32 = true)
    (h_bhi_qlo_zero : ((b_hi * q_lo : Felt) == (0 : Felt)) = true) :
    let cross0_lo := Felt.ofNat ((b_lo.val * q_hi.val) % 2^32)
    let madd2_lo := Felt.ofNat ((b_lo.val * q_lo.val +
      (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32)
    execWithEnv u64ProcEnv 50
      { stack := madd2_lo :: cross0_lo :: q_hi :: q_lo :: b_lo :: b_hi :: a_lo :: a_hi :: rest,
        memory := mem, locals := locs, advice := r_lo :: r_hi :: adv_rest }
      divmod_chunk1c =
    some { stack := r_hi :: r_lo :: madd2_lo :: cross0_lo ::
                    q_hi :: q_lo :: b_lo :: b_hi :: a_lo :: a_hi :: rest,
           memory := mem, locals := locs, advice := adv_rest } := by
  simp only []
  unfold divmod_chunk1c execWithEnv
  simp only [List.foldlM]
  have h_bhi_qlo_eq : b_hi * q_lo = 0 :=
    LawfulBEq.eq_of_beq h_bhi_qlo_zero
  have h_bhi_qlo_assert :
      ((if (b_hi * q_lo : Felt) = (0 : Felt) then (1 : Felt) else 0) : Felt).val = 1 := by
    rw [h_bhi_qlo_eq]
    simp
  miden_dup
  miden_dup
  rw [stepMul]; miden_bind
  rw [stepEqImm]; miden_bind
  simp only [beq_iff_eq]
  rw [stepAssertWithError (h := h_bhi_qlo_assert)]
  miden_bind
  rw [stepAdvPush2 (hadv := rfl)]; miden_bind
  rw [stepU32Assert2 (ha := hr_hi_u32) (hb := hr_lo_u32)]; miden_bind
  simp only [pure, Pure.pure]

set_option maxHeartbeats 12000000 in
private theorem divmod_chunk2_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt)
    (q_lo q_hi r_lo r_hi : Felt) (adv_rest : List Felt)
    (mem locs : Nat → Felt)
    (hr_hi_u32 : r_hi.isU32 = true)
    (hr_lo_u32 : r_lo.isU32 = true)
    (hb_lo_u32 : b_lo.isU32 = true)
    (hb_hi_u32 : b_hi.isU32 = true)
    (h_lt_result :
        let borrow_lo := decide (r_hi.val < b_lo.val)
        let borrow_hi := decide (r_lo.val < b_hi.val)
        let hi_eq := Felt.ofNat (u32OverflowingSub r_lo.val b_hi.val).2 == (0 : Felt)
        (borrow_hi || (hi_eq && borrow_lo)) = true) :
    let cross0_lo := Felt.ofNat ((b_lo.val * q_hi.val) % 2^32)
    let madd2_lo := Felt.ofNat ((b_lo.val * q_lo.val +
      (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32)
    execWithEnv u64ProcEnv 50
      { stack := r_hi :: r_lo :: madd2_lo :: cross0_lo ::
                 q_hi :: q_lo :: b_lo :: b_hi :: a_lo :: a_hi :: rest,
        memory := mem, locals := locs, advice := adv_rest }
      divmod_chunk2 =
    some { stack := r_hi :: r_lo :: madd2_lo :: cross0_lo ::
                    q_hi :: q_lo :: a_lo :: a_hi :: rest,
           memory := mem, locals := locs, advice := adv_rest } := by
  simp only []
  unfold divmod_chunk2 execWithEnv
  simp only [List.foldlM]
  miden_movup
  miden_movup
  miden_swap
  miden_dup
  miden_dup
  miden_movup
  miden_movup
  simp only [u64ProcEnv]
  unfold Miden.Core.U64.lt execWithEnv
  simp only [List.foldlM]
  miden_movup
  miden_movup
  miden_movup
  rw [stepU32OverflowSub (ha := hr_hi_u32) (hb := hb_lo_u32)]; miden_bind
  miden_movdn
  rw [stepDrop]; miden_bind
  miden_swap
  rw [stepU32OverflowSub (ha := hr_lo_u32) (hb := hb_hi_u32)]; miden_bind
  miden_swap
  rw [stepEqImm]; miden_bind
  miden_movup
  rw [u32OverflowingSub_borrow_ite r_hi.val b_lo.val]
  rw [stepAndIte]; miden_bind
  rw [u32OverflowingSub_borrow_ite r_lo.val b_hi.val]
  rw [stepOrIte]; miden_bind
  rw [stepAssertWithError (h := by simp [h_lt_result])]; miden_bind
  simp only [pure, Pure.pure]

set_option maxHeartbeats 12000000 in
private theorem divmod_chunk3a_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt)
    (q_lo q_hi r_lo r_hi : Felt) (adv_rest : List Felt)
    (mem locs : Nat → Felt)
    (hr_hi_u32 : r_hi.isU32 = true)
    (cross0_lo_val : (Felt.ofNat ((b_lo.val * q_hi.val) % 2^32)).val =
        (b_lo.val * q_hi.val) % 2^32)
    :
    let cross0_lo := Felt.ofNat ((b_lo.val * q_hi.val) % 2^32)
    let madd2_lo := Felt.ofNat ((b_lo.val * q_lo.val +
      (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32)
    let sum0_lo := Felt.ofNat ((r_hi.val + (b_lo.val * q_hi.val) % 2^32) % 2^32)
    let sum0_hi := Felt.ofNat ((r_hi.val + (b_lo.val * q_hi.val) % 2^32) / 2^32)
    execWithEnv u64ProcEnv 50
      { stack := r_hi :: r_lo :: madd2_lo :: cross0_lo ::
                 q_hi :: q_lo :: a_lo :: a_hi :: rest,
        memory := mem, locals := locs, advice := adv_rest }
      divmod_chunk3a =
    some { stack := sum0_hi :: sum0_lo :: r_hi :: r_lo :: madd2_lo ::
                    q_hi :: q_lo :: a_lo :: a_hi :: rest,
           memory := mem, locals := locs, advice := adv_rest } := by
  simp only []
  unfold divmod_chunk3a execWithEnv
  simp only [List.foldlM]
  have h_cross0_lo_u32 : (Felt.ofNat ((b_lo.val * q_hi.val) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  miden_dup
  miden_movup
  rw [stepU32WidenAdd (ha := hr_hi_u32) (hb := h_cross0_lo_u32)]; miden_bind
  rw [cross0_lo_val]
  miden_swap
  simp only [pure, Pure.pure]

set_option maxHeartbeats 12000000 in
private theorem divmod_chunk3b_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt)
    (q_lo q_hi r_lo r_hi : Felt) (adv_rest : List Felt)
    (mem locs : Nat → Felt)
    (hr_hi_u32 : r_hi.isU32 = true)
    (hr_lo_u32 : r_lo.isU32 = true)
    (cross0_lo_val : (Felt.ofNat ((b_lo.val * q_hi.val) % 2^32)).val =
        (b_lo.val * q_hi.val) % 2^32)
    (madd2_lo_val : (Felt.ofNat ((b_lo.val * q_lo.val +
        (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32)).val =
        (b_lo.val * q_lo.val +
        (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32)
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
    let madd2_lo := Felt.ofNat ((b_lo.val * q_lo.val +
      (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32)
    let sum0_lo := Felt.ofNat ((r_hi.val + (b_lo.val * q_hi.val) % 2^32) % 2^32)
    let sum0_hi := Felt.ofNat ((r_hi.val + (b_lo.val * q_hi.val) % 2^32) / 2^32)
    execWithEnv u64ProcEnv 50
      { stack := sum0_hi :: sum0_lo :: r_hi :: r_lo :: madd2_lo ::
                 q_hi :: q_lo :: a_lo :: a_hi :: rest,
        memory := mem, locals := locs, advice := adv_rest }
      divmod_chunk3b =
    some { stack := r_hi :: r_lo :: q_hi :: q_lo :: rest,
           memory := mem, locals := locs, advice := adv_rest } := by
  simp only []
  unfold divmod_chunk3b execWithEnv
  simp only [List.foldlM]
  have h_madd2_lo_u32 : (Felt.ofNat ((b_lo.val * q_lo.val +
      (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  have h_cross0_lo_u32 : (Felt.ofNat ((b_lo.val * q_hi.val) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  have h_sum0_hi_u32 :
      (Felt.ofNat ((r_hi.val + (b_lo.val * q_hi.val) % 2^32) / 2^32)).isU32 = true := by
    have h :=
      u32_div_2_32_isU32 r_hi (Felt.ofNat ((b_lo.val * q_hi.val) % 2^32)) hr_hi_u32 h_cross0_lo_u32
    rw [cross0_lo_val] at h
    exact h
  have h_sum0_hi_val :
      (Felt.ofNat ((r_hi.val + (b_lo.val * q_hi.val) % 2^32) / 2^32)).val =
        (r_hi.val + (b_lo.val * q_hi.val) % 2^32) / 2^32 := by
    have h : (Felt.ofNat ((r_hi.val + (Felt.ofNat ((b_lo.val * q_hi.val) % 2^32)).val) / 2^32)).val =
        (r_hi.val + (Felt.ofNat ((b_lo.val * q_hi.val) % 2^32)).val) / 2^32 := by
      apply felt_ofNat_val_lt
      exact sum_div_2_32_lt_prime r_hi (Felt.ofNat ((b_lo.val * q_hi.val) % 2^32))
    rw [cross0_lo_val] at h
    exact h
  have h_add2_hi_eq : Felt.ofNat ((r_lo.val +
      (b_lo.val * q_lo.val +
        (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32 +
      (r_hi.val + (b_lo.val * q_hi.val) % 2^32) / 2^32) / 2^32) = 0 :=
    LawfulBEq.eq_of_beq h_add2_hi_zero
  have h_add2_assert :
      ((if Felt.ofNat ((r_lo.val +
          (b_lo.val * q_lo.val +
            (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32 +
          (r_hi.val + (b_lo.val * q_hi.val) % 2^32) / 2^32) / 2^32) = (0 : Felt)
        then (1 : Felt) else 0) : Felt).val = 1 := by
    rw [h_add2_hi_eq]
    simp
  miden_dup
  miden_movup
  miden_movup
  rw [stepU32WidenAdd3 (ha := hr_lo_u32) (hb := h_madd2_lo_u32) (hc := h_sum0_hi_u32)]; miden_bind
  rw [madd2_lo_val, h_sum0_hi_val]
  miden_swap
  rw [stepEqImm]; miden_bind
  simp only [beq_iff_eq]
  rw [stepAssertWithError (h := h_add2_assert)]
  miden_bind
  miden_movup
  rw [h_a_hi_eq]
  rw [stepAssertEqWithError]; miden_bind
  miden_movup
  rw [h_a_lo_eq]
  rw [stepAssertEqWithError]; miden_bind
  simp only [pure, Pure.pure]

set_option maxHeartbeats 16000000 in
/-- Low-level divmod theorem with explicit intermediate hypotheses.
    See `u64_divmod_correct` for the clean client-facing version.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Advice stack: [q_lo, q_hi, r_lo, r_hi] ++ adv_rest
    Output stack: [r_hi, r_lo, q_hi, q_lo] ++ rest. -/
theorem u64_divmod_raw
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
  simp only [] at hadv
  subst hs
  subst hadv
  rw [divmod_decomp, execWithEnv_append]
  rw [divmod_chunk1a_correct a_lo a_hi b_lo b_hi rest q_lo q_hi r_lo r_hi adv_rest mem locs
      hq_hi_u32 hq_lo_u32 hb_lo_u32 hb_hi_u32 cross0_hi_val h_madd1_hi_zero]
  miden_bind
  rw [execWithEnv_append]
  rw [divmod_chunk1b_correct a_lo a_hi b_lo b_hi rest q_lo q_hi r_lo r_hi adv_rest mem locs
      hq_lo_u32 hb_lo_u32 madd1_lo_val h_madd2_hi_zero]
  miden_bind
  rw [execWithEnv_append]
  rw [divmod_chunk1c_correct a_lo a_hi b_lo b_hi rest q_lo q_hi r_lo r_hi adv_rest mem locs
      hr_hi_u32 hr_lo_u32 h_bhi_qlo_zero]
  miden_bind
  rw [execWithEnv_append]
  rw [divmod_chunk2_correct a_lo a_hi b_lo b_hi rest q_lo q_hi r_lo r_hi adv_rest mem locs
      hr_hi_u32 hr_lo_u32 hb_lo_u32 hb_hi_u32 h_lt_result]
  miden_bind
  rw [execWithEnv_append]
  rw [divmod_chunk3a_correct a_lo a_hi b_lo b_hi rest q_lo q_hi r_lo r_hi adv_rest mem locs
      hr_hi_u32 cross0_lo_val]
  miden_bind
  rw [divmod_chunk3b_correct a_lo a_hi b_lo b_hi rest q_lo q_hi r_lo r_hi adv_rest mem locs
      hr_hi_u32 hr_lo_u32 cross0_lo_val madd2_lo_val h_add2_hi_zero h_a_hi_eq h_a_lo_eq]

/-- `u64::divmod` computes quotient and remainder of two u64 values.
    Input stack:  [b.lo, b.hi, a.lo, a.hi] ++ rest
    Advice stack: [q.hi, q.lo, r.hi, r.lo] ++ adv_rest
    Output stack: [r.lo, r.hi, q.lo, q.hi] ++ rest

    The advice ordering has high limbs first for each pair because
    `adv_push.2` pops the first element deeper. -/
theorem u64_divmod_correct (a b q r : U64) (rest : List Felt) (adv_rest : List Felt)
    (s : MidenState)
    (hs : s.stack = b.lo :: b.hi :: a.lo :: a.hi :: rest)
    (hadv : s.advice = q.hi :: q.lo :: r.hi :: r.lo :: adv_rest)
    (hdiv : q.toNat * b.toNat + r.toNat = a.toNat)
    (hrem : r.toNat < b.toNat) :
    execWithEnv u64ProcEnv 50 s Miden.Core.U64.divmod =
    some { stack := r.lo :: r.hi :: q.lo :: q.hi :: rest,
           memory := s.memory,
           locals := s.locals,
           advice := adv_rest } := by
  sorry

end MidenLean.Proofs
