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

set_option maxHeartbeats 12000000 in
private theorem divmod_chunk1a_none
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt)
    (q_lo q_hi r_lo r_hi : Felt) (adv_rest : List Felt)
    (mem locs : Nat → Felt)
    (hq_hi_u32 : q_hi.isU32 = true)
    (hq_lo_u32 : q_lo.isU32 = true)
    (hb_lo_u32 : b_lo.isU32 = true)
    (hb_hi_u32 : b_hi.isU32 = true)
    (h_not : ¬((Felt.ofNat ((b_hi.val * q_hi.val +
        (b_lo.val * q_hi.val) / 2^32) / 2^32) == (0 : Felt)) = true)) :
    execWithEnv u64ProcEnv 50
      { stack := b_lo :: b_hi :: a_lo :: a_hi :: rest,
        memory := mem, locals := locs,
        advice := q_lo :: q_hi :: r_lo :: r_hi :: adv_rest }
      divmod_chunk1a = none := by
  unfold divmod_chunk1a execWithEnv
  simp only [List.foldlM]
  have h_cross0_hi_u32 : (Felt.ofNat ((b_lo.val * q_hi.val) / 2^32)).isU32 = true :=
    u32_prod_div_isU32 b_lo q_hi hb_lo_u32 hq_hi_u32
  have cross0_hi_val : (Felt.ofNat ((b_lo.val * q_hi.val) / 2^32)).val =
      (b_lo.val * q_hi.val) / 2^32 :=
    felt_ofNat_val_lt _ (u32_prod_div_lt_prime b_lo q_hi hb_lo_u32 hq_hi_u32)
  rw [show execInstruction
      { stack := b_lo :: b_hi :: a_lo :: a_hi :: rest,
        memory := mem, locals := locs,
        advice := q_lo :: q_hi :: r_lo :: r_hi :: adv_rest }
      (Instruction.emitImm 14153021663962350784) =
      some { stack := b_lo :: b_hi :: a_lo :: a_hi :: rest,
             memory := mem, locals := locs,
             advice := q_lo :: q_hi :: r_lo :: r_hi :: adv_rest } by
      unfold execInstruction; rfl]
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
  -- Assert fails because condition doesn't hold
  have h_val_ne : (if Felt.ofNat ((b_hi.val * q_hi.val +
      (b_lo.val * q_hi.val) / 2^32) / 2^32) = (0 : Felt) then (1 : Felt) else 0).val ≠ 1 := by
    have h_ne : ¬(Felt.ofNat ((b_hi.val * q_hi.val +
        (b_lo.val * q_hi.val) / 2^32) / 2^32) = (0 : Felt)) := by
      intro heq; exact h_not (beq_iff_eq.mpr heq)
    rw [if_neg h_ne]; simp
  rw [stepAssertWithError_none (h := h_val_ne)]

set_option maxHeartbeats 12000000 in
private theorem divmod_chunk1b_none
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt)
    (q_lo q_hi r_lo r_hi : Felt) (adv_rest : List Felt)
    (mem locs : Nat → Felt)
    (hq_lo_u32 : q_lo.isU32 = true)
    (hb_lo_u32 : b_lo.isU32 = true)
    (madd1_lo_val : (Felt.ofNat ((b_hi.val * q_hi.val +
        (b_lo.val * q_hi.val) / 2^32) % 2^32)).val =
        (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32)
    (h_not : ¬((Felt.ofNat ((b_lo.val * q_lo.val +
        (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) / 2^32) ==
        (0 : Felt)) = true)) :
    let cross0_lo := Felt.ofNat ((b_lo.val * q_hi.val) % 2^32)
    let madd1_lo := Felt.ofNat ((b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32)
    execWithEnv u64ProcEnv 50
      { stack := madd1_lo :: cross0_lo :: q_hi :: q_lo :: b_lo :: b_hi :: a_lo :: a_hi :: rest,
        memory := mem, locals := locs, advice := r_lo :: r_hi :: adv_rest }
      divmod_chunk1b = none := by
  simp only []
  unfold divmod_chunk1b execWithEnv
  simp only [List.foldlM]
  have h_madd1_lo_u32 : (Felt.ofNat ((b_hi.val * q_hi.val +
      (b_lo.val * q_hi.val) / 2^32) % 2^32)).isU32 = true :=
    u32_mod_isU32 _
  miden_dup
  miden_dup
  rw [stepU32WidenMadd (ha := hb_lo_u32) (hb := hq_lo_u32) (hc := h_madd1_lo_u32)]; miden_bind
  rw [madd1_lo_val]
  miden_swap
  rw [stepEqImm]; miden_bind
  simp only [beq_iff_eq]
  have h_val_ne : (if Felt.ofNat ((b_lo.val * q_lo.val +
      (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) / 2^32) = (0 : Felt)
      then (1 : Felt) else 0).val ≠ 1 := by
    have h_ne : ¬(Felt.ofNat ((b_lo.val * q_lo.val +
        (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) / 2^32) = (0 : Felt)) := by
      intro heq; exact h_not (beq_iff_eq.mpr heq)
    rw [if_neg h_ne]; simp
  rw [stepAssertWithError_none (h := h_val_ne)]

set_option maxHeartbeats 12000000 in
private theorem divmod_chunk1c_none
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt)
    (q_lo q_hi r_lo r_hi : Felt) (adv_rest : List Felt)
    (mem locs : Nat → Felt)
    (h_not : ¬(((b_hi * q_lo : Felt) == (0 : Felt)) = true)) :
    let cross0_lo := Felt.ofNat ((b_lo.val * q_hi.val) % 2^32)
    let madd2_lo := Felt.ofNat ((b_lo.val * q_lo.val +
      (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32)
    execWithEnv u64ProcEnv 50
      { stack := madd2_lo :: cross0_lo :: q_hi :: q_lo :: b_lo :: b_hi :: a_lo :: a_hi :: rest,
        memory := mem, locals := locs, advice := r_lo :: r_hi :: adv_rest }
      divmod_chunk1c = none := by
  simp only []
  unfold divmod_chunk1c execWithEnv
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepMul]; miden_bind
  rw [stepEqImm]; miden_bind
  simp only [beq_iff_eq]
  have h_val_ne : (if (b_hi * q_lo : Felt) = (0 : Felt) then (1 : Felt) else 0).val ≠ 1 := by
    have h_ne : ¬((b_hi * q_lo : Felt) = (0 : Felt)) := by
      intro heq; exact h_not (beq_iff_eq.mpr heq)
    rw [if_neg h_ne]; simp
  rw [stepAssertWithError_none (h := h_val_ne)]

set_option maxHeartbeats 12000000 in
private theorem divmod_chunk2_none
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt)
    (q_lo q_hi r_lo r_hi : Felt) (adv_rest : List Felt)
    (mem locs : Nat → Felt)
    (hr_hi_u32 : r_hi.isU32 = true)
    (hr_lo_u32 : r_lo.isU32 = true)
    (hb_lo_u32 : b_lo.isU32 = true)
    (hb_hi_u32 : b_hi.isU32 = true)
    (h_not :
        let borrow_lo := decide (r_hi.val < b_lo.val)
        let borrow_hi := decide (r_lo.val < b_hi.val)
        let hi_eq := Felt.ofNat (u32OverflowingSub r_lo.val b_hi.val).2 == (0 : Felt)
        ¬((borrow_hi || (hi_eq && borrow_lo)) = true)) :
    let cross0_lo := Felt.ofNat ((b_lo.val * q_hi.val) % 2^32)
    let madd2_lo := Felt.ofNat ((b_lo.val * q_lo.val +
      (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32)
    execWithEnv u64ProcEnv 50
      { stack := r_hi :: r_lo :: madd2_lo :: cross0_lo ::
                 q_hi :: q_lo :: b_lo :: b_hi :: a_lo :: a_hi :: rest,
        memory := mem, locals := locs, advice := adv_rest }
      divmod_chunk2 = none := by
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
  have h_val_ne :
      (if (decide (r_lo.val < b_hi.val) || (Felt.ofNat (u32OverflowingSub r_lo.val b_hi.val).2 == 0) &&
          decide (r_hi.val < b_lo.val)) then (1 : Felt) else 0).val ≠ 1 := by
    dsimp only at h_not
    have h_ne : ¬((decide (r_lo.val < b_hi.val) ||
        ((Felt.ofNat (u32OverflowingSub r_lo.val b_hi.val).2 == 0) &&
         decide (r_hi.val < b_lo.val))) = true) := h_not
    rw [if_neg (show ¬((decide (r_lo.val < b_hi.val) || (Felt.ofNat (u32OverflowingSub r_lo.val b_hi.val).2 == 0) &&
        decide (r_hi.val < b_lo.val)) = true) from h_ne)]
    simp
  rw [stepAssertWithError_none (h := h_val_ne)]

set_option maxHeartbeats 12000000 in
private theorem divmod_chunk3b_none_add2
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
    (h_not : ¬((Felt.ofNat ((r_lo.val +
        (b_lo.val * q_lo.val +
          (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32 +
        (r_hi.val + (b_lo.val * q_hi.val) % 2^32) / 2^32) / 2^32) ==
        (0 : Felt)) = true)) :
    let madd2_lo := Felt.ofNat ((b_lo.val * q_lo.val +
      (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32)
    let sum0_lo := Felt.ofNat ((r_hi.val + (b_lo.val * q_hi.val) % 2^32) % 2^32)
    let sum0_hi := Felt.ofNat ((r_hi.val + (b_lo.val * q_hi.val) % 2^32) / 2^32)
    execWithEnv u64ProcEnv 50
      { stack := sum0_hi :: sum0_lo :: r_hi :: r_lo :: madd2_lo ::
                 q_hi :: q_lo :: a_lo :: a_hi :: rest,
        memory := mem, locals := locs, advice := adv_rest }
      divmod_chunk3b = none := by
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
  miden_dup
  miden_movup
  miden_movup
  rw [stepU32WidenAdd3 (ha := hr_lo_u32) (hb := h_madd2_lo_u32) (hc := h_sum0_hi_u32)]; miden_bind
  rw [madd2_lo_val, h_sum0_hi_val]
  miden_swap
  rw [stepEqImm]; miden_bind
  simp only [beq_iff_eq]
  have h_val_ne : (if Felt.ofNat ((r_lo.val +
      (b_lo.val * q_lo.val +
        (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32 +
      (r_hi.val + (b_lo.val * q_hi.val) % 2^32) / 2^32) / 2^32) = (0 : Felt)
      then (1 : Felt) else 0).val ≠ 1 := by
    have h_ne : ¬(Felt.ofNat ((r_lo.val +
        (b_lo.val * q_lo.val +
          (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32 +
        (r_hi.val + (b_lo.val * q_hi.val) % 2^32) / 2^32) / 2^32) = (0 : Felt)) := by
      intro heq; exact h_not (beq_iff_eq.mpr heq)
    rw [if_neg h_ne]; simp
  rw [stepAssertWithError_none (h := h_val_ne)]

set_option maxHeartbeats 12000000 in
private theorem divmod_chunk3b_none_ahi
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
    (h_not : a_hi ≠ Felt.ofNat ((r_lo.val +
        (b_lo.val * q_lo.val +
          (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32 +
        (r_hi.val + (b_lo.val * q_hi.val) % 2^32) / 2^32) % 2^32)) :
    let madd2_lo := Felt.ofNat ((b_lo.val * q_lo.val +
      (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32)
    let sum0_lo := Felt.ofNat ((r_hi.val + (b_lo.val * q_hi.val) % 2^32) % 2^32)
    let sum0_hi := Felt.ofNat ((r_hi.val + (b_lo.val * q_hi.val) % 2^32) / 2^32)
    execWithEnv u64ProcEnv 50
      { stack := sum0_hi :: sum0_lo :: r_hi :: r_lo :: madd2_lo ::
                 q_hi :: q_lo :: a_lo :: a_hi :: rest,
        memory := mem, locals := locs, advice := adv_rest }
      divmod_chunk3b = none := by
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
  rw [stepAssertEqWithError_none (h := h_not.symm)]

set_option maxHeartbeats 12000000 in
private theorem divmod_chunk3b_none_alo
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
    (h_not : a_lo ≠ Felt.ofNat ((r_hi.val +
        (b_lo.val * q_hi.val) % 2^32) % 2^32)) :
    let madd2_lo := Felt.ofNat ((b_lo.val * q_lo.val +
      (b_hi.val * q_hi.val + (b_lo.val * q_hi.val) / 2^32) % 2^32) % 2^32)
    let sum0_lo := Felt.ofNat ((r_hi.val + (b_lo.val * q_hi.val) % 2^32) % 2^32)
    let sum0_hi := Felt.ofNat ((r_hi.val + (b_lo.val * q_hi.val) % 2^32) / 2^32)
    execWithEnv u64ProcEnv 50
      { stack := sum0_hi :: sum0_lo :: r_hi :: r_lo :: madd2_lo ::
                 q_hi :: q_lo :: a_lo :: a_hi :: rest,
        memory := mem, locals := locs, advice := adv_rest }
      divmod_chunk3b = none := by
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
  rw [stepAssertEqWithError_none (h := h_not.symm)]

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

/-- `u64::divmod` verifies and returns quotient and remainder of two u64 values.
    The advice stack supplies candidate q and r; execution succeeds iff q * b + r = a
    and r < b.
    Input stack:  [b.lo, b.hi, a.lo, a.hi] ++ rest
    Advice stack: [q.hi, q.lo, r.hi, r.lo] ++ adv_rest
    Output stack: [r.lo, r.hi, q.lo, q.hi] ++ rest -/
private theorem divmod_bh_qh_zero (ql qh bl bh rl rh al ah : Nat)
    (hql : ql < 2^32) (hqh : qh < 2^32) (hbl : bl < 2^32) (hbh : bh < 2^32)
    (hal : al < 2^32) (hah : ah < 2^32)
    (hdiv : (qh * 2^32 + ql) * (bh * 2^32 + bl) + (rh * 2^32 + rl) = ah * 2^32 + al) :
    bh * qh = 0 := by
  rcases Nat.eq_zero_or_pos qh with rfl | hqh1
  · simp
  rcases Nat.eq_zero_or_pos bh with rfl | hbh1
  · simp
  exfalso
  have : (qh * 2^32 + ql) * (bh * 2^32 + bl) ≥ 2^32 * 2^32 :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

set_option maxHeartbeats 800000 in
private theorem divmod_backward_arith (ql qh bl bh rl rh al ah : Nat)
    (hql : ql < 2^32) (hqh : qh < 2^32) (hbl : bl < 2^32) (hbh : bh < 2^32)
    (hrl : rl < 2^32) (hrh : rh < 2^32) (hal : al < 2^32) (hah : ah < 2^32)
    (hdiv : (qh * 2^32 + ql) * (bh * 2^32 + bl) + (rh * 2^32 + rl) = ah * 2^32 + al)
    (hlt : rh * 2^32 + rl < bh * 2^32 + bl) :
    (bh * ql + bl * ql / 2^32) / 2^32 = 0 ∧
    (bl * qh + (bh * ql + bl * ql / 2^32) % 2^32) / 2^32 = 0 ∧
    (rh + (bl * qh + (bh * ql + bl * ql / 2^32) % 2^32) % 2^32 +
     (rl + bl * ql % 2^32) / 2^32) / 2^32 = 0 ∧
    ah = (rh + (bl * qh + (bh * ql + bl * ql / 2^32) % 2^32) % 2^32 +
          (rl + bl * ql % 2^32) / 2^32) % 2^32 ∧
    al = (rl + bl * ql % 2^32) % 2^32 := by
  have hbq := divmod_bh_qh_zero ql qh bl bh rl rh al ah hql hqh hbl hbh hal hah hdiv
  rcases Nat.eq_zero_or_pos qh with rfl | hqh_pos
  · -- qh = 0: q*b = ql * (bh*2^32 + bl)
    simp only [Nat.zero_mul, Nat.zero_add] at hdiv ⊢
    have hprod : bh * ql * 2^32 + bl * ql + rh * 2^32 + rl = ah * 2^32 + al := by
      nlinarith [Nat.mul_comm ql bh, Nat.mul_comm ql bl]
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  · -- bh = 0 (since bh * qh = 0 and qh > 0)
    have hbh0 : bh = 0 := by
      rcases Nat.eq_zero_or_pos bh with h | h
      · exact h
      · exfalso; have : bh * qh ≥ 1 := Nat.one_le_iff_ne_zero.mpr (by positivity)
        omega
    subst hbh0
    simp only [Nat.zero_mul, Nat.zero_add] at hdiv ⊢
    have hprod : bl * qh * 2^32 + bl * ql + rh * 2^32 + rl = ah * 2^32 + al := by
      nlinarith [Nat.mul_comm qh bl, Nat.mul_comm ql bl]
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 800000 in
private theorem divmod_forward_arith (ql qh bl bh rl rh al ah : Nat)
    (hqh : qh < 2^32) (hbh : bh < 2^32)
    (hbqh : bh * qh = 0)
    (h_madd1 : (bh * ql + bl * ql / 2^32) / 2^32 = 0)
    (h_madd2 : (bl * qh + (bh * ql + bl * ql / 2^32) % 2^32) / 2^32 = 0)
    (h_add2 : (rh + (bl * qh + (bh * ql + bl * ql / 2^32) % 2^32) % 2^32 +
     (rl + bl * ql % 2^32) / 2^32) / 2^32 = 0)
    (h_ah : ah = (rh + (bl * qh + (bh * ql + bl * ql / 2^32) % 2^32) % 2^32 +
          (rl + bl * ql % 2^32) / 2^32) % 2^32)
    (h_al : al = (rl + bl * ql % 2^32) % 2^32) :
    (qh * 2^32 + ql) * (bh * 2^32 + bl) + (rh * 2^32 + rl) = ah * 2^32 + al := by
  rcases Nat.eq_zero_or_pos qh with rfl | hqh_pos
  · simp only [Nat.zero_mul, Nat.mul_zero, Nat.zero_add] at *
    have hprod : ql * (bh * 2^32 + bl) = bh * ql * 2^32 + bl * ql := by ring
    omega
  · have hbh0 : bh = 0 := by
      rcases Nat.eq_zero_or_pos bh with h | h
      · exact h
      · exfalso; have : bh * qh ≥ 1 := Nat.one_le_iff_ne_zero.mpr (by positivity); omega
    subst hbh0
    simp only [Nat.zero_mul, Nat.zero_add] at *
    have hprod : (qh * 2^32 + ql) * bl = bl * qh * 2^32 + bl * ql := by ring
    omega

/-- `u64::divmod` verifies the Euclidean division of two u64 values.
    Execution succeeds iff the advice-supplied quotient q and remainder r
    satisfy q * b + r = a and r < b. -/
theorem u64_divmod_correct (a b q r : U64) (rest : List Felt) (adv_rest : List Felt)
    (s : MidenState)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest)
    (hadv : s.advice = q.hi.val :: q.lo.val :: r.hi.val :: r.lo.val :: adv_rest) :
    execWithEnv u64ProcEnv 50 s Miden.Core.U64.divmod =
    some { stack := r.lo.val :: r.hi.val :: q.lo.val :: q.hi.val :: rest,
           memory := s.memory,
           locals := s.locals,
           advice := adv_rest }
    ↔ (q.toNat * b.toNat + r.toNat = a.toNat ∧ r.toNat < b.toNat) := by
  constructor
  · -- Forward: execution success → q*b+r=a ∧ r<b
    intro hexec
    obtain ⟨stk, mem, locs, adv⟩ := s
    simp only [] at hs hadv; subst hs; subst hadv
    -- Extract u32 bounds
    have hql_b : q.lo.val.val < 2^32 := by
      have := q.lo.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
    have hqh_b : q.hi.val.val < 2^32 := by
      have := q.hi.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
    have hbl_b : b.lo.val.val < 2^32 := by
      have := b.lo.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
    have hbh_b : b.hi.val.val < 2^32 := by
      have := b.hi.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
    have hrl_b : r.lo.val.val < 2^32 := by
      have := r.lo.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
    have hrh_b : r.hi.val.val < 2^32 := by
      have := r.hi.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
    -- Abbreviations (arithmetic meaning: ql = lo limb of q, qh = hi limb)
    -- Note the name swap: advice order q.hi,q.lo maps to raw q_lo,q_hi
    set ql := q.lo.val.val with ql_def
    set qh := q.hi.val.val with qh_def
    set bl := b.lo.val.val with bl_def
    set bh := b.hi.val.val with bh_def
    set rl := r.lo.val.val with rl_def
    set rh := r.hi.val.val with rh_def
    -- Extract condition 1: madd1_hi_zero (from chunk1a assertion)
    have h_cond1 : (Felt.ofNat ((bh * ql + (bl * ql) / 2^32) / 2^32) == (0 : Felt)) = true := by
      by_contra h_not
      have := divmod_chunk1a_none a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest
        mem locs q.lo.isU32 q.hi.isU32 b.lo.isU32 b.hi.isU32 h_not
      rw [divmod_decomp, execWithEnv_append] at hexec
      rw [this] at hexec
      simp [bind, Bind.bind, Option.bind] at hexec
    -- Use chunk1a_correct to determine the intermediate state
    rw [divmod_decomp, execWithEnv_append] at hexec
    rw [divmod_chunk1a_correct a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
        q.lo.isU32 q.hi.isU32 b.lo.isU32 b.hi.isU32
        (felt_ofNat_val_lt _ (u32_prod_div_lt_prime b.lo.val q.lo.val b.lo.isU32 q.lo.isU32))
        h_cond1] at hexec
    simp only [bind, Bind.bind, Option.bind] at hexec
    rw [execWithEnv_append] at hexec
    -- Extract condition 2: madd2_hi_zero (from chunk1b assertion)
    have h_cond2 : (Felt.ofNat ((bl * qh +
        (bh * ql + (bl * ql) / 2^32) % 2^32) / 2^32) == (0 : Felt)) = true := by
      by_contra h_not
      rw [divmod_chunk1b_none a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
          q.hi.isU32 b.lo.isU32 (felt_ofNat_val_lt _ (u32_mod_lt_prime _)) h_not] at hexec
      simp [bind, Bind.bind, Option.bind] at hexec
    rw [divmod_chunk1b_correct a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
        q.hi.isU32 b.lo.isU32 (felt_ofNat_val_lt _ (u32_mod_lt_prime _)) h_cond2] at hexec
    simp only [bind, Bind.bind, Option.bind] at hexec
    rw [execWithEnv_append] at hexec
    -- Extract condition 3: bhi * qhi = 0 (from chunk1c assertion)
    have h_cond3 : ((b.hi.val * q.hi.val : Felt) == (0 : Felt)) = true := by
      by_contra h_not
      rw [divmod_chunk1c_none a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
          h_not] at hexec
      simp [bind, Bind.bind, Option.bind] at hexec
    rw [divmod_chunk1c_correct a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
        r.lo.isU32 r.hi.isU32 h_cond3] at hexec
    simp only [bind, Bind.bind, Option.bind] at hexec
    rw [execWithEnv_append] at hexec
    -- Extract condition 4: lt_result (from chunk2 assertion)
    have h_cond4 :
        let borrow_lo := decide (r.lo.val.val < b.lo.val.val)
        let borrow_hi := decide (r.hi.val.val < b.hi.val.val)
        let hi_eq := Felt.ofNat (u32OverflowingSub r.hi.val.val b.hi.val.val).2 == (0 : Felt)
        (borrow_hi || (hi_eq && borrow_lo)) = true := by
      by_contra h_not
      rw [divmod_chunk2_none a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
          r.lo.isU32 r.hi.isU32 b.lo.isU32 b.hi.isU32 h_not] at hexec
      simp [bind, Bind.bind, Option.bind] at hexec
    rw [divmod_chunk2_correct a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
        r.lo.isU32 r.hi.isU32 b.lo.isU32 b.hi.isU32 h_cond4] at hexec
    simp only [bind, Bind.bind, Option.bind] at hexec
    rw [execWithEnv_append] at hexec
    -- chunk3a: no assertions
    have cross0_lo_val : (Felt.ofNat ((bl * ql) % 2^32)).val = (bl * ql) % 2^32 :=
      felt_ofNat_val_lt _ (u32_mod_lt_prime _)
    rw [divmod_chunk3a_correct a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
        r.lo.isU32 cross0_lo_val] at hexec
    simp only [bind, Bind.bind, Option.bind] at hexec
    -- chunk3b: three assertions
    have madd2_lo_val : (Felt.ofNat ((bl * qh +
        (bh * ql + (bl * ql) / 2^32) % 2^32) % 2^32)).val =
        (bl * qh + (bh * ql + (bl * ql) / 2^32) % 2^32) % 2^32 :=
      felt_ofNat_val_lt _ (u32_mod_lt_prime _)
    -- Condition 5: add2_hi_zero
    have h_cond5 : (Felt.ofNat ((rh +
        (bl * qh + (bh * ql + (bl * ql) / 2^32) % 2^32) % 2^32 +
        (rl + (bl * ql) % 2^32) / 2^32) / 2^32) == (0 : Felt)) = true := by
      by_contra h_not
      rw [divmod_chunk3b_none_add2 a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
          r.lo.isU32 r.hi.isU32 cross0_lo_val madd2_lo_val h_not] at hexec
      simp at hexec
    -- Condition 6: a_hi equality
    have h_cond6 : a.hi.val = Felt.ofNat ((rh +
        (bl * qh + (bh * ql + (bl * ql) / 2^32) % 2^32) % 2^32 +
        (rl + (bl * ql) % 2^32) / 2^32) % 2^32) := by
      by_contra h_not
      rw [divmod_chunk3b_none_ahi a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
          r.lo.isU32 r.hi.isU32 cross0_lo_val madd2_lo_val h_cond5 h_not] at hexec
      simp at hexec
    -- Condition 7: a_lo equality
    have h_cond7 : a.lo.val = Felt.ofNat ((rl + (bl * ql) % 2^32) % 2^32) := by
      by_contra h_not
      rw [divmod_chunk3b_none_alo a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
          r.lo.isU32 r.hi.isU32 cross0_lo_val madd2_lo_val h_cond5 h_cond6 h_not] at hexec
      simp at hexec
    -- Lift conditions to Nat level
    -- Product upper bounds for omega (nonlinear products need explicit hints)
    have hprod_bl_ql := Nat.mul_le_mul (show bl ≤ 2^32 - 1 from by omega)
      (show ql ≤ 2^32 - 1 from by omega)
    have hprod_bl_qh := Nat.mul_le_mul (show bl ≤ 2^32 - 1 from by omega)
      (show qh ≤ 2^32 - 1 from by omega)
    have hprod_bh_ql := Nat.mul_le_mul (show bh ≤ 2^32 - 1 from by omega)
      (show ql ≤ 2^32 - 1 from by omega)
    have hprod_bh_qh := Nat.mul_le_mul (show bh ≤ 2^32 - 1 from by omega)
      (show qh ≤ 2^32 - 1 from by omega)
    -- bh * qh = 0
    have hbq_nat : bh * qh = 0 := by
      have hfelt : b.hi.val * q.hi.val = (0 : Felt) := LawfulBEq.eq_of_beq h_cond3
      have hprod_lt : bh * qh < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; omega
      have h1 := felt_mul_val_no_wrap b.hi.val q.hi.val hprod_lt
      have h2 : (b.hi.val * q.hi.val).val = 0 := by rw [hfelt]; exact Felt.val_zero'
      linarith
    -- Helper: Felt.ofNat n == 0 with n < GOLDILOCKS_PRIME implies n = 0
    have lift_zero : ∀ (n : Nat), n < GOLDILOCKS_PRIME →
        (Felt.ofNat n == (0 : Felt)) = true → n = 0 := by
      intro n hlt h
      have heq : Felt.ofNat n = 0 := LawfulBEq.eq_of_beq h
      have hval : (Felt.ofNat n).val = (0 : Felt).val := congrArg ZMod.val heq
      rw [felt_ofNat_val_lt n hlt, Felt.val_zero'] at hval
      exact hval
    -- madd1_hi = 0
    have h_madd1_nat : (bh * ql + (bl * ql) / 2^32) / 2^32 = 0 :=
      lift_zero _ (by unfold GOLDILOCKS_PRIME; omega) h_cond1
    -- madd2_hi = 0
    have h_madd2_nat : (bl * qh + (bh * ql + (bl * ql) / 2^32) % 2^32) / 2^32 = 0 :=
      lift_zero _ (by unfold GOLDILOCKS_PRIME; omega) h_cond2
    -- add2_hi = 0
    have h_add2_nat : (rh + (bl * qh + (bh * ql + (bl * ql) / 2^32) % 2^32) % 2^32 +
        (rl + (bl * ql) % 2^32) / 2^32) / 2^32 = 0 :=
      lift_zero _ (by unfold GOLDILOCKS_PRIME; omega) h_cond5
    -- a_hi val equality
    have h_ah_nat : a.hi.val.val = (rh + (bl * qh + (bh * ql + (bl * ql) / 2^32) % 2^32) % 2^32 +
        (rl + (bl * ql) % 2^32) / 2^32) % 2^32 := by
      have h := congrArg ZMod.val h_cond6
      rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)] at h
      exact h
    -- a_lo val equality
    have h_al_nat : a.lo.val.val = (rl + (bl * ql) % 2^32) % 2^32 := by
      have h := congrArg ZMod.val h_cond7
      rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)] at h
      exact h
    -- r < b from borrow condition
    have h_lt : r.toNat < b.toNat := by
      have hborrow := u64_borrow_iff_lt r b
      dsimp only at h_cond4
      rw [hborrow] at h_cond4
      exact of_decide_eq_true h_cond4
    constructor
    · -- q*b+r=a
      unfold U64.toNat
      exact divmod_forward_arith ql qh bl bh rl rh a.lo.val.val a.hi.val.val
        hqh_b hbh_b hbq_nat h_madd1_nat h_madd2_nat
        h_add2_nat h_ah_nat h_al_nat
    · exact h_lt
  · -- Backward: derive raw hypotheses from q*b+r=a ∧ r<b, apply u64_divmod_raw
    intro ⟨hdiv, hlt⟩
    -- Extract u32 bounds
    have hql := q.lo.isU32; have hqh := q.hi.isU32
    have hrl := r.lo.isU32; have hrh := r.hi.isU32
    have hbl := b.lo.isU32; have hbh := b.hi.isU32
    have hal := a.lo.isU32; have hah := a.hi.isU32
    simp only [Felt.isU32, decide_eq_true_eq] at *
    -- Set up shorthand for val
    set ql := q.lo.val.val; set qh := q.hi.val.val
    set bl := b.lo.val.val; set bh := b.hi.val.val
    set rl := r.lo.val.val; set rh := r.hi.val.val
    set al := a.lo.val.val; set ah := a.hi.val.val
    -- Rewrite toNat in terms of val
    simp only [U64.toNat] at hdiv hlt
    -- Get all Nat-level conditions from the arithmetic helper
    have harith := divmod_backward_arith ql qh bl bh rl rh al ah
      hql hqh hbl hbh hrl hrh hal hah hdiv hlt
    obtain ⟨h_madd1, h_madd2, h_add2, h_ah, h_al⟩ := harith
    -- bh * qh = 0 at Nat level
    have hbq_nat := divmod_bh_qh_zero ql qh bl bh rl rh al ah
      hql hqh hbl hbh hal hah hdiv
    -- Apply u64_divmod_raw (q_lo=q.hi, q_hi=q.lo, r_lo=r.hi, r_hi=r.lo)
    exact u64_divmod_raw a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest
      s hs hadv q.lo.isU32 q.hi.isU32 r.lo.isU32 r.hi.isU32 b.lo.isU32 b.hi.isU32
      -- cross0_hi_val
      (MidenLean.felt_ofNat_val_lt _ (MidenLean.u32_prod_div_lt_prime b.lo.val q.lo.val b.lo.isU32 q.lo.isU32))
      -- h_madd1_hi_zero
      (MidenLean.felt_ofNat_beq_zero _ h_madd1)
      -- madd1_lo_val
      (MidenLean.felt_ofNat_val_lt _ (MidenLean.u32_mod_lt_prime _))
      -- h_madd2_hi_zero
      (MidenLean.felt_ofNat_beq_zero _ h_madd2)
      -- h_bhi_qlo_zero (b_hi * q_lo = b.hi * q.hi)
      (MidenLean.felt_mul_beq_zero b.hi.val q.hi.val (by omega) (by unfold MidenLean.GOLDILOCKS_PRIME; nlinarith))
      -- cross0_lo_val
      (MidenLean.felt_ofNat_val_lt _ (MidenLean.u32_mod_lt_prime _))
      -- madd2_lo_val
      (MidenLean.felt_ofNat_val_lt _ (MidenLean.u32_mod_lt_prime _))
      -- h_lt_result (r < b in borrow form)
      (by dsimp only; rw [u64_borrow_iff_lt r b]; simp [U64.toNat]; omega)
      -- h_add2_hi_zero
      (MidenLean.felt_ofNat_beq_zero _ h_add2)
      -- h_a_hi_eq
      (MidenLean.felt_eq_ofNat_of_val_eq a.hi.val _ h_ah (MidenLean.u32_mod_lt_prime _))
      -- h_a_lo_eq
      (MidenLean.felt_eq_ofNat_of_val_eq a.lo.val _ h_al (MidenLean.u32_mod_lt_prime _))

/-- If divmod execution returns any result, the arithmetic conditions hold.
    This generalizes the forward direction of `u64_divmod_correct` to an
    arbitrary output state, which is needed by `u64_div_correct` and
    `u64_mod_correct` where the divmod output is only partially observable. -/
theorem divmod_conditions_of_exec (a b q r : U64) (rest : List Felt) (adv_rest : List Felt)
    (s : MidenState)
    (hs : s.stack = b.lo.val :: b.hi.val :: a.lo.val :: a.hi.val :: rest)
    (hadv : s.advice = q.hi.val :: q.lo.val :: r.hi.val :: r.lo.val :: adv_rest)
    {s' : MidenState}
    (hexec : execWithEnv u64ProcEnv 50 s Miden.Core.U64.divmod = some s') :
    q.toNat * b.toNat + r.toNat = a.toNat ∧ r.toNat < b.toNat := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [] at hs hadv; subst hs; subst hadv
  have hql_b : q.lo.val.val < 2^32 := by
    have := q.lo.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
  have hqh_b : q.hi.val.val < 2^32 := by
    have := q.hi.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
  have hbl_b : b.lo.val.val < 2^32 := by
    have := b.lo.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
  have hbh_b : b.hi.val.val < 2^32 := by
    have := b.hi.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
  have hrl_b : r.lo.val.val < 2^32 := by
    have := r.lo.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
  have hrh_b : r.hi.val.val < 2^32 := by
    have := r.hi.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
  set ql := q.lo.val.val with ql_def
  set qh := q.hi.val.val with qh_def
  set bl := b.lo.val.val with bl_def
  set bh := b.hi.val.val with bh_def
  set rl := r.lo.val.val with rl_def
  set rh := r.hi.val.val with rh_def
  have h_cond1 : (Felt.ofNat ((bh * ql + (bl * ql) / 2^32) / 2^32) == (0 : Felt)) = true := by
    by_contra h_not
    have := divmod_chunk1a_none a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest
      mem locs q.lo.isU32 q.hi.isU32 b.lo.isU32 b.hi.isU32 h_not
    rw [divmod_decomp, execWithEnv_append] at hexec
    rw [this] at hexec
    simp [bind, Bind.bind, Option.bind] at hexec
  rw [divmod_decomp, execWithEnv_append] at hexec
  rw [divmod_chunk1a_correct a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
      q.lo.isU32 q.hi.isU32 b.lo.isU32 b.hi.isU32
      (felt_ofNat_val_lt _ (u32_prod_div_lt_prime b.lo.val q.lo.val b.lo.isU32 q.lo.isU32))
      h_cond1] at hexec
  simp only [bind, Bind.bind, Option.bind] at hexec
  rw [execWithEnv_append] at hexec
  have h_cond2 : (Felt.ofNat ((bl * qh +
      (bh * ql + (bl * ql) / 2^32) % 2^32) / 2^32) == (0 : Felt)) = true := by
    by_contra h_not
    rw [divmod_chunk1b_none a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
        q.hi.isU32 b.lo.isU32 (felt_ofNat_val_lt _ (u32_mod_lt_prime _)) h_not] at hexec
    simp [bind, Bind.bind, Option.bind] at hexec
  rw [divmod_chunk1b_correct a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
      q.hi.isU32 b.lo.isU32 (felt_ofNat_val_lt _ (u32_mod_lt_prime _)) h_cond2] at hexec
  simp only [bind, Bind.bind, Option.bind] at hexec
  rw [execWithEnv_append] at hexec
  have h_cond3 : ((b.hi.val * q.hi.val : Felt) == (0 : Felt)) = true := by
    by_contra h_not
    rw [divmod_chunk1c_none a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
        h_not] at hexec
    simp [bind, Bind.bind, Option.bind] at hexec
  rw [divmod_chunk1c_correct a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
      r.lo.isU32 r.hi.isU32 h_cond3] at hexec
  simp only [bind, Bind.bind, Option.bind] at hexec
  rw [execWithEnv_append] at hexec
  have h_cond4 :
      let borrow_lo := decide (r.lo.val.val < b.lo.val.val)
      let borrow_hi := decide (r.hi.val.val < b.hi.val.val)
      let hi_eq := Felt.ofNat (u32OverflowingSub r.hi.val.val b.hi.val.val).2 == (0 : Felt)
      (borrow_hi || (hi_eq && borrow_lo)) = true := by
    by_contra h_not
    rw [divmod_chunk2_none a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
        r.lo.isU32 r.hi.isU32 b.lo.isU32 b.hi.isU32 h_not] at hexec
    simp [bind, Bind.bind, Option.bind] at hexec
  rw [divmod_chunk2_correct a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
      r.lo.isU32 r.hi.isU32 b.lo.isU32 b.hi.isU32 h_cond4] at hexec
  simp only [bind, Bind.bind, Option.bind] at hexec
  rw [execWithEnv_append] at hexec
  have cross0_lo_val : (Felt.ofNat ((bl * ql) % 2^32)).val = (bl * ql) % 2^32 :=
    felt_ofNat_val_lt _ (u32_mod_lt_prime _)
  rw [divmod_chunk3a_correct a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
      r.lo.isU32 cross0_lo_val] at hexec
  simp only [bind, Bind.bind, Option.bind] at hexec
  have madd2_lo_val : (Felt.ofNat ((bl * qh +
      (bh * ql + (bl * ql) / 2^32) % 2^32) % 2^32)).val =
      (bl * qh + (bh * ql + (bl * ql) / 2^32) % 2^32) % 2^32 :=
    felt_ofNat_val_lt _ (u32_mod_lt_prime _)
  have h_cond5 : (Felt.ofNat ((rh +
      (bl * qh + (bh * ql + (bl * ql) / 2^32) % 2^32) % 2^32 +
      (rl + (bl * ql) % 2^32) / 2^32) / 2^32) == (0 : Felt)) = true := by
    by_contra h_not
    rw [divmod_chunk3b_none_add2 a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
        r.lo.isU32 r.hi.isU32 cross0_lo_val madd2_lo_val h_not] at hexec
    simp at hexec
  have h_cond6 : a.hi.val = Felt.ofNat ((rh +
      (bl * qh + (bh * ql + (bl * ql) / 2^32) % 2^32) % 2^32 +
      (rl + (bl * ql) % 2^32) / 2^32) % 2^32) := by
    by_contra h_not
    rw [divmod_chunk3b_none_ahi a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
        r.lo.isU32 r.hi.isU32 cross0_lo_val madd2_lo_val h_cond5 h_not] at hexec
    simp at hexec
  have h_cond7 : a.lo.val = Felt.ofNat ((rl + (bl * ql) % 2^32) % 2^32) := by
    by_contra h_not
    rw [divmod_chunk3b_none_alo a.lo.val a.hi.val b.lo.val b.hi.val rest q.hi.val q.lo.val r.hi.val r.lo.val adv_rest mem locs
        r.lo.isU32 r.hi.isU32 cross0_lo_val madd2_lo_val h_cond5 h_cond6 h_not] at hexec
    simp at hexec
  have hprod_bl_ql := Nat.mul_le_mul (show bl ≤ 2^32 - 1 from by omega)
    (show ql ≤ 2^32 - 1 from by omega)
  have hprod_bl_qh := Nat.mul_le_mul (show bl ≤ 2^32 - 1 from by omega)
    (show qh ≤ 2^32 - 1 from by omega)
  have hprod_bh_ql := Nat.mul_le_mul (show bh ≤ 2^32 - 1 from by omega)
    (show ql ≤ 2^32 - 1 from by omega)
  have hprod_bh_qh := Nat.mul_le_mul (show bh ≤ 2^32 - 1 from by omega)
    (show qh ≤ 2^32 - 1 from by omega)
  have hbq_nat : bh * qh = 0 := by
    have hfelt : b.hi.val * q.hi.val = (0 : Felt) := LawfulBEq.eq_of_beq h_cond3
    have hprod_lt : bh * qh < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; omega
    have h1 := felt_mul_val_no_wrap b.hi.val q.hi.val hprod_lt
    have h2 : (b.hi.val * q.hi.val).val = 0 := by rw [hfelt]; exact Felt.val_zero'
    linarith
  have lift_zero : ∀ (n : Nat), n < GOLDILOCKS_PRIME →
      (Felt.ofNat n == (0 : Felt)) = true → n = 0 := by
    intro n hlt h
    have heq : Felt.ofNat n = 0 := LawfulBEq.eq_of_beq h
    have hval : (Felt.ofNat n).val = (0 : Felt).val := congrArg ZMod.val heq
    rw [felt_ofNat_val_lt n hlt, Felt.val_zero'] at hval
    exact hval
  have h_madd1_nat : (bh * ql + (bl * ql) / 2^32) / 2^32 = 0 :=
    lift_zero _ (by unfold GOLDILOCKS_PRIME; omega) h_cond1
  have h_madd2_nat : (bl * qh + (bh * ql + (bl * ql) / 2^32) % 2^32) / 2^32 = 0 :=
    lift_zero _ (by unfold GOLDILOCKS_PRIME; omega) h_cond2
  have h_add2_nat : (rh + (bl * qh + (bh * ql + (bl * ql) / 2^32) % 2^32) % 2^32 +
      (rl + (bl * ql) % 2^32) / 2^32) / 2^32 = 0 :=
    lift_zero _ (by unfold GOLDILOCKS_PRIME; omega) h_cond5
  have h_ah_nat : a.hi.val.val = (rh + (bl * qh + (bh * ql + (bl * ql) / 2^32) % 2^32) % 2^32 +
      (rl + (bl * ql) % 2^32) / 2^32) % 2^32 := by
    have h := congrArg ZMod.val h_cond6
    rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)] at h
    exact h
  have h_al_nat : a.lo.val.val = (rl + (bl * ql) % 2^32) % 2^32 := by
    have h := congrArg ZMod.val h_cond7
    rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)] at h
    exact h
  have h_lt : r.toNat < b.toNat := by
    have hborrow := u64_borrow_iff_lt r b
    dsimp only at h_cond4
    rw [hborrow] at h_cond4
    exact of_decide_eq_true h_cond4
  constructor
  · unfold U64.toNat
    exact divmod_forward_arith ql qh bl bh rl rh a.lo.val.val a.hi.val.val
      hqh_b hbh_b hbq_nat h_madd1_nat h_madd2_nat
      h_add2_nat h_ah_nat h_al_nat
  · exact h_lt

end MidenLean.Proofs
