import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

private theorem exec_append (fuel : Nat) (s : MidenState) (xs ys : List Op) :
    exec fuel s (xs ++ ys) = (do
      let s' ← exec fuel s xs
      exec fuel s' ys) := by
  unfold exec execWithEnv
  cases fuel <;> simp [List.foldlM_append]

private theorem felt31_val : (31 : Felt).val = 31 :=
  felt_ofNat_val_lt 31 (by unfold GOLDILOCKS_PRIME; omega)

private theorem felt31_isU32 : (31 : Felt).isU32 = true := by
  simp only [Felt.isU32, decide_eq_true_eq]
  rw [felt31_val]
  omega

private theorem felt32_val : (32 : Felt).val = 32 :=
  felt_ofNat_val_lt 32 (by unfold GOLDILOCKS_PRIME; omega)

private theorem felt32_isU32 : (32 : Felt).isU32 = true := by
  simp only [Felt.isU32, decide_eq_true_eq]
  rw [felt32_val]
  omega

private theorem stepU32WrappingSubLocal (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32WrappingSub =
      some ⟨Felt.ofNat (u32OverflowingSub a.val b.val).2 :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32WrappingSub
  simp [ha, hb, MidenState.withStack]

/-- Helper: convert Prop-ite to Bool-ite for boolean step lemmas. -/
private theorem ite_prop_to_decide {p : Prop} [Decidable p] (a b : Felt) :
    (if p then a else b) = if decide p then a else b := by
  cases ‹Decidable p› <;> rfl

/-- The effective shift value in rotr is ≤ 32, hence ≤ 63 for pow2. -/
private theorem rotr_eff_shift_le_63 (shift : Felt) :
    (Felt.ofNat (u32OverflowingSub (32 : Felt).val
        (Felt.ofNat (shift.val &&& (31 : Felt).val)).val).2).val ≤ 63 := by
  rw [felt31_val, felt32_val]
  have h_and_le : shift.val &&& 31 ≤ 31 := Nat.and_le_right
  have h_and_val : (Felt.ofNat (shift.val &&& 31) : Felt).val = shift.val &&& 31 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  rw [h_and_val]
  unfold u32OverflowingSub
  split
  · have h_result_lt : 32 - (shift.val &&& 31) < GOLDILOCKS_PRIME := by
      unfold GOLDILOCKS_PRIME
      omega
    rw [felt_ofNat_val_lt _ h_result_lt]
    omega
  · omega

private def rotr_chunk1 : List Op := [
  .inst (.movup 2),
  .inst (.swap 1),
  .inst (.push 31),
  .inst (.dup 1),
  .inst (.u32Lt)
]

private def rotr_chunk2 : List Op := [
  .inst (.movdn 3),
  .inst (.push 31),
  .inst (.u32And),
  .inst (.push 32),
  .inst (.swap 1),
  .inst (.u32WrappingSub),
  .inst (.pow2)
]

private def rotr_chunk3 : List Op := [
  .inst (.dup 0),
  .inst (.movup 3),
  .inst (.mul),
  .inst (.u32Split),
  .inst (.swap 1),
  .inst (.movup 3),
  .inst (.movup 3),
  .inst (.mul),
  .inst (.add),
  .inst (.u32Split),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.add),
  .inst (.swap 1),
  .inst (.movup 2)
]

private def rotr_chunk4 : List Op := [
  .inst (.not),
  .inst (.cswap),
  .inst (.swap 1)
]

private theorem rotr_decomp :
    Miden.Core.U64.rotr = rotr_chunk1 ++ (rotr_chunk2 ++ (rotr_chunk3 ++ rotr_chunk4)) := by
  simp [Miden.Core.U64.rotr, rotr_chunk1, rotr_chunk2, rotr_chunk3, rotr_chunk4]

set_option maxHeartbeats 12000000 in
private theorem rotr_chunk1_correct
    (shift lo hi : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true) :
    exec 35 ⟨shift :: lo :: hi :: rest, mem, locs, adv⟩ rotr_chunk1 =
      some ⟨(if decide (31 < shift.val) then (1 : Felt) else 0) ::
        shift :: hi :: lo :: rest, mem, locs, adv⟩ := by
  unfold exec rotr_chunk1 execWithEnv
  simp only [List.foldlM]
  miden_movup
  miden_swap
  rw [stepPush]
  miden_bind
  miden_dup
  rw [stepU32Lt (ha := felt31_isU32) (hb := hshift_u32)]
  miden_bind
  rw [felt31_val]
  rw [ite_prop_to_decide (p := 31 < shift.val)]
  simp only [pure, Pure.pure]

set_option maxHeartbeats 12000000 in
private theorem rotr_chunk2_correct
    (shift lo hi : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true) :
    let cmp := decide (31 < shift.val)
    let shiftAnd31 := Felt.ofNat (shift.val &&& 31)
    let effShift := Felt.ofNat (u32OverflowingSub 32 shiftAnd31.val).2
    exec 35
      ⟨(if cmp then (1 : Felt) else 0) :: shift :: hi :: lo :: rest, mem, locs, adv⟩
      rotr_chunk2 =
      some ⟨Felt.ofNat (2 ^ effShift.val) ::
        hi :: lo :: (if cmp then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold exec rotr_chunk2 execWithEnv
  simp only [List.foldlM]
  have h_shiftAnd31_u32 : (Felt.ofNat (shift.val &&& 31)).isU32 = true := by
    apply felt_ofNat_isU32_of_lt
    have h_and_le : shift.val &&& 31 ≤ 31 := Nat.and_le_right
    omega
  have h_effShift_le_63 :
      (Felt.ofNat (u32OverflowingSub 32 (Felt.ofNat (shift.val &&& 31)).val).2).val ≤ 63 := by
    simpa [felt31_val, felt32_val] using rotr_eff_shift_le_63 shift
  miden_movdn
  rw [stepPush]
  miden_bind
  rw [stepU32And (ha := hshift_u32) (hb := felt31_isU32)]
  miden_bind
  rw [felt31_val]
  rw [stepPush]
  miden_bind
  miden_swap
  rw [stepU32WrappingSubLocal (ha := felt32_isU32) (hb := h_shiftAnd31_u32)]
  miden_bind
  rw [felt32_val]
  rw [stepPow2 (ha := h_effShift_le_63)]
  miden_bind
  simp only [pure, Pure.pure]

set_option maxHeartbeats 12000000 in
private theorem rotr_chunk3_correct
    (shift lo hi : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt) :
    let cmp := decide (31 < shift.val)
    let shiftAnd31 := Felt.ofNat (shift.val &&& 31)
    let effShift := Felt.ofNat (u32OverflowingSub 32 shiftAnd31.val).2
    let pow := Felt.ofNat (2 ^ effShift.val)
    let prod1 := pow * lo
    let cross := prod1.hi32 + hi * pow
    exec 35
      ⟨pow :: hi :: lo :: (if cmp then (1 : Felt) else 0) :: rest, mem, locs, adv⟩
      rotr_chunk3 =
      some ⟨(if cmp then (1 : Felt) else 0) ::
        cross.lo32 :: (cross.hi32 + prod1.lo32) :: rest, mem, locs, adv⟩ := by
  unfold exec rotr_chunk3 execWithEnv
  simp only [List.foldlM]
  miden_dup
  miden_movup
  rw [stepMul]
  miden_bind
  rw [stepU32Split]
  miden_bind
  miden_swap
  miden_movup
  miden_movup
  rw [stepMul]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [stepU32Split]
  miden_bind
  miden_swap
  miden_movup
  rw [stepAdd]
  miden_bind
  miden_swap
  miden_movup
  simp only [pure, Pure.pure]

set_option maxHeartbeats 12000000 in
private theorem rotr_chunk4_correct
    (p : Bool) (a b : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt) :
    exec 35 ⟨(if p then (1 : Felt) else 0) :: a :: b :: rest, mem, locs, adv⟩ rotr_chunk4 =
      some ⟨(if !p then a else b) :: (if !p then b else a) :: rest, mem, locs, adv⟩ := by
  unfold exec rotr_chunk4 execWithEnv
  simp only [List.foldlM]
  rw [stepNotIte]
  miden_bind
  rw [stepCswapIte]
  miden_bind
  miden_swap
  cases p <;> simp only [pure, Pure.pure]

set_option maxHeartbeats 16000000 in
/-- u64.rotr correctly right-rotates a u64 value.
    Input stack:  [shift, lo, hi] ++ rest
    Output stack: [result_lo, result_hi] ++ rest
    Requires shift.isU32 (for u32Lt and u32And). -/
theorem u64_rotr_correct
    (lo hi shift : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = shift :: lo :: hi :: rest)
    (hshift_u32 : shift.isU32 = true) :
    let cmp := decide (31 < shift.val)
    let shiftAnd31 := Felt.ofNat (shift.val &&& 31)
    let effShift := Felt.ofNat (u32OverflowingSub 32 shiftAnd31.val).2
    let pow := Felt.ofNat (2 ^ effShift.val)
    let prod1 := pow * lo
    let cross := prod1.hi32 + hi * pow
    exec 35 s Miden.Core.U64.rotr =
      some (s.withStack (
        if !cmp then
          cross.lo32 :: (cross.hi32 + prod1.lo32) :: rest
        else
          (cross.hi32 + prod1.lo32) :: cross.lo32 :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  rw [rotr_decomp, exec_append]
  rw [rotr_chunk1_correct shift lo hi rest mem locs adv hshift_u32]
  miden_bind
  rw [exec_append]
  rw [rotr_chunk2_correct shift lo hi rest mem locs adv hshift_u32]
  miden_bind
  rw [exec_append]
  rw [rotr_chunk3_correct shift lo hi rest mem locs adv]
  miden_bind
  let cmp := decide (31 < shift.val)
  let shiftAnd31 := Felt.ofNat (shift.val &&& 31)
  let effShift := Felt.ofNat (u32OverflowingSub 32 shiftAnd31.val).2
  let pow := Felt.ofNat (2 ^ effShift.val)
  let prod1 := pow * lo
  let cross := prod1.hi32 + hi * pow
  cases hcmp : cmp
  · simpa [cmp, hcmp] using
      (rotr_chunk4_correct cmp cross.lo32 (cross.hi32 + prod1.lo32) rest mem locs adv)
  · simpa [cmp, hcmp] using
      (rotr_chunk4_correct cmp cross.lo32 (cross.hi32 + prod1.lo32) rest mem locs adv)

end MidenLean.Proofs
