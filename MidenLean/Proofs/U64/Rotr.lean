import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

private theorem felt31_val : (31 : Felt).val = 31 :=
  felt_ofNat_val_lt 31 (by unfold GOLDILOCKS_PRIME; omega)

private theorem felt32_val : (32 : Felt).val = 32 :=
  felt_ofNat_val_lt 32 (by unfold GOLDILOCKS_PRIME; omega)

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
  rw [stepU32Lt (ha := U32.felt31_isU32) (hb := hshift_u32)]
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
  rw [stepU32And (ha := hshift_u32) (hb := U32.felt31_isU32)]
  miden_bind
  rw [felt31_val]
  rw [stepPush]
  miden_bind
  miden_swap
  rw [stepU32WrappingSubLocal (ha := U32.felt32_isU32) (hb := h_shiftAnd31_u32)]
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
/-- `u64::rotr` raw: result in terms of field-level multiplication and splitting. -/
theorem u64_rotr_raw
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
  rw [rotr_decomp, MidenLean.exec_append]
  rw [rotr_chunk1_correct shift lo hi rest mem locs adv hshift_u32]
  miden_bind
  rw [MidenLean.exec_append]
  rw [rotr_chunk2_correct shift lo hi rest mem locs adv hshift_u32]
  miden_bind
  rw [MidenLean.exec_append]
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

/-- Nat-level bridging for rotr no-swap case (1 ≤ eff ≤ 31, eff = 32 - shift).
    Shows the schoolbook decomposition matches the rotr formula
    v = a/Q + a*P*2^32 where P = 2^eff, Q = 2^(32-eff). -/
private theorem rotr_nat_case1 (hi lo eff : Nat)
    (hhi : hi < 2 ^ 32) (hlo : lo < 2 ^ 32) (heff_pos : 1 ≤ eff) (heff : eff ≤ 31) :
    let P := 2 ^ eff
    let Q := 2 ^ (32 - eff)
    let c := hi * P + lo / Q
    let v := (hi * 2 ^ 32 + lo) / Q + (hi * 2 ^ 32 + lo) * P * 2 ^ 32
    c % 2 ^ 32 = v % 2 ^ 32 ∧
    c / 2 ^ 32 + P * (lo % Q) = (v / 2 ^ 32) % 2 ^ 32 := by
  simp only
  set P := 2 ^ eff
  set Q := 2 ^ (32 - eff)
  have hPQ : P * Q = 2 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
  have hP_pos : 0 < P := by positivity
  have hQ_pos : 0 < Q := by positivity
  have h_lo_div_lt := lo_div_lt_of_u32 P Q lo hPQ hQ_pos hlo
  have h_xP := schoolbook_mul_eq P Q hi lo hPQ
  have h_cross_div := cross_div_eq P Q hi lo hPQ hQ_pos h_lo_div_lt
  have h_nonoverlap := limb_non_overlap P Q hi lo hPQ hQ_pos hhi
  -- a / Q = hi * P + lo / Q = c
  have h_a_div_Q : (hi * 2 ^ 32 + lo) / Q = hi * P + lo / Q := by
    rw [show hi * 2 ^ 32 = hi * (P * Q) from by rw [hPQ]]
    rw [show hi * (P * Q) + lo = lo + hi * P * Q from by ring_nf]
    rw [Nat.add_mul_div_right _ _ hQ_pos]; omega
  set c := hi * P + lo / Q
  rw [h_a_div_Q, h_xP]
  -- v = c + (c * 2^32 + P*(lo%Q)) * 2^32
  have h_nonoverlap2 : c / 2 ^ 32 + P * (lo % Q) < 2 ^ 32 := by
    rw [h_cross_div]; exact h_nonoverlap
  -- Decompose using Euclidean division of c by 2^32
  have h_decomp : c + (c * 2 ^ 32 + P * (lo % Q)) * 2 ^ 32 =
      c % 2 ^ 32 + (c / 2 ^ 32 + P * (lo % Q) + c * 2 ^ 32) * 2 ^ 32 := by
    have := Nat.div_add_mod c (2 ^ 32); omega
  rw [h_decomp]
  constructor
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Nat.mod_lt c (by positivity))]
  · rw [Nat.add_mul_div_right _ _ (show 0 < 2 ^ 32 from by positivity)]
    rw [Nat.div_eq_of_lt (Nat.mod_lt c (by positivity)), Nat.zero_add]
    have h_rearrange : c / 2 ^ 32 + P * (lo % Q) + c * 2 ^ 32 =
        (c / 2 ^ 32 + P * (lo % Q)) + c * 2 ^ 32 := by omega
    rw [h_rearrange, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h_nonoverlap2]

/-- Nat-level bridging for rotr swap case (33 ≤ shift ≤ 63, eff = 64 - shift).
    Shows the schoolbook decomposition matches the rotr formula
    v = a/(Q*2^32) + a*P where P = 2^eff, Q = 2^(32-eff). -/
private theorem rotr_nat_case2 (hi lo eff : Nat)
    (hhi : hi < 2 ^ 32) (hlo : lo < 2 ^ 32) (heff_pos : 1 ≤ eff) (heff : eff ≤ 31) :
    let P := 2 ^ eff
    let Q := 2 ^ (32 - eff)
    let c := hi * P + lo / Q
    let v := (hi * 2 ^ 32 + lo) / (Q * 2 ^ 32) + (hi * 2 ^ 32 + lo) * P
    c / 2 ^ 32 + P * (lo % Q) = v % 2 ^ 32 ∧
    c % 2 ^ 32 = (v / 2 ^ 32) % 2 ^ 32 := by
  simp only
  set P := 2 ^ eff
  set Q := 2 ^ (32 - eff)
  have hPQ : P * Q = 2 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
  have hP_pos : 0 < P := by positivity
  have hQ_pos : 0 < Q := by positivity
  have h_lo_div_lt := lo_div_lt_of_u32 P Q lo hPQ hQ_pos hlo
  have h_xP := schoolbook_mul_eq P Q hi lo hPQ
  have h_div := u64_div_large_pow hi lo Q hlo
  have h_cross_div := cross_div_eq P Q hi lo hPQ hQ_pos h_lo_div_lt
  have h_nonoverlap := limb_non_overlap P Q hi lo hPQ hQ_pos hhi
  set c := hi * P + lo / Q
  -- Simplify v = hi/Q + a*P = hi/Q + c*2^32 + P*(lo%Q) = (hi/Q + P*(lo%Q)) + c*2^32
  rw [show Q * 2 ^ 32 = 2 ^ 32 * Q from by ring, h_div, h_xP]
  have h_rearrange : hi / Q + (c * 2 ^ 32 + P * (lo % Q)) =
      (hi / Q + P * (lo % Q)) + c * 2 ^ 32 := by omega
  rw [h_rearrange]
  have h_nonoverlap2 : hi / Q + P * (lo % Q) < 2 ^ 32 := h_nonoverlap
  constructor
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h_nonoverlap2, h_cross_div]
  · rw [Nat.add_mul_div_right _ _ (show 0 < 2 ^ 32 from by positivity)]
    rw [Nat.div_eq_of_lt h_nonoverlap2, Nat.zero_add]

/-- When pow.val ≤ 2^31, the Felt-level multiplication and splitting in rotr
    compute the same limbs as nat-level schoolbook multiplication. -/
private theorem rotr_felt_bridge (lo hi pow : Felt)
    (hlo : lo.isU32 = true) (hhi : hi.isU32 = true)
    (hpow : pow.val ≤ 2 ^ 31) :
    let prod1 := pow * lo
    let cross := prod1.hi32 + hi * pow
    let P := pow.val
    let c := hi.val * P + P * lo.val / 2 ^ 32
    cross.lo32 = Felt.ofNat (c % 2 ^ 32) ∧
    cross.hi32 + prod1.lo32 =
      Felt.ofNat (c / 2 ^ 32 + P * lo.val % 2 ^ 32) := by
  simp only
  have hlo_lt : lo.val < 2 ^ 32 := by
    simp only [Felt.isU32, decide_eq_true_eq] at hlo; exact hlo
  have hhi_lt : hi.val < 2 ^ 32 := by
    simp only [Felt.isU32, decide_eq_true_eq] at hhi; exact hhi
  set P := pow.val
  -- Felt mul exact: pow * lo
  have h_prod_lt : P * lo.val < GOLDILOCKS_PRIME := by
    have : P * lo.val ≤ 2 ^ 31 * (2 ^ 32 - 1) :=
      Nat.mul_le_mul hpow (by omega)
    unfold GOLDILOCKS_PRIME; omega
  have h_prod_val : (pow * lo).val = P * lo.val :=
    felt_mul_val_no_wrap pow lo h_prod_lt
  -- Felt mul exact: hi * pow
  have h_hipow_lt : hi.val * P < GOLDILOCKS_PRIME := by
    have : hi.val * P ≤ (2 ^ 32 - 1) * 2 ^ 31 :=
      Nat.mul_le_mul (by omega) hpow
    unfold GOLDILOCKS_PRIME; omega
  have h_hipow_val : (hi * pow).val = hi.val * P :=
    felt_mul_val_no_wrap hi pow h_hipow_lt
  -- Rewrite prod1.hi32, prod1.lo32 using h_prod_val
  have h_prod_hi32_eq : (pow * lo).hi32 = Felt.ofNat (P * lo.val / 2 ^ 32) := by
    unfold Felt.hi32; congr 1; congr 1
  have h_prod_lo32_eq : (pow * lo).lo32 = Felt.ofNat (P * lo.val % 2 ^ 32) := by
    unfold Felt.lo32; congr 1; congr 1
  -- Compute Felt.ofNat(P*lo.val/2^32).val
  have h_hi32_nat_lt : P * lo.val / 2 ^ 32 < GOLDILOCKS_PRIME :=
    Nat.lt_of_le_of_lt (Nat.div_le_self ..) h_prod_lt
  have h_hi32_nat_val : (Felt.ofNat (P * lo.val / 2 ^ 32)).val = P * lo.val / 2 ^ 32 :=
    felt_ofNat_val_lt _ h_hi32_nat_lt
  -- Felt add exact for cross
  have h_cross_sum_lt :
      (Felt.ofNat (P * lo.val / 2 ^ 32)).val + (hi * pow).val < GOLDILOCKS_PRIME := by
    rw [h_hi32_nat_val, h_hipow_val]
    have h1 : P * lo.val / 2 ^ 32 < 2 ^ 31 := by
      calc P * lo.val / 2 ^ 32
          ≤ 2 ^ 31 * (2 ^ 32 - 1) / 2 ^ 32 :=
            Nat.div_le_div_right (Nat.mul_le_mul hpow (by omega))
        _ < 2 ^ 31 := by omega
    have h2 : hi.val * P ≤ (2 ^ 32 - 1) * 2 ^ 31 :=
      Nat.mul_le_mul (by omega) hpow
    unfold GOLDILOCKS_PRIME; omega
  -- cross.val
  have h_cross_val : (Felt.ofNat (P * lo.val / 2 ^ 32) + hi * pow).val =
      P * lo.val / 2 ^ 32 + hi.val * P := by
    rw [felt_add_val_no_wrap _ _ h_cross_sum_lt, h_hi32_nat_val, h_hipow_val]
  -- Rewrite cross using h_prod_hi32_eq
  have h_cross_eq : (pow * lo).hi32 + hi * pow =
      Felt.ofNat (P * lo.val / 2 ^ 32) + hi * pow := by
    rw [h_prod_hi32_eq]
  -- cross.lo32 and cross.hi32
  have h_cross_lo32 : ((pow * lo).hi32 + hi * pow).lo32 =
      Felt.ofNat ((P * lo.val / 2 ^ 32 + hi.val * P) % 2 ^ 32) := by
    rw [h_cross_eq]; unfold Felt.lo32; congr 1; congr 1
  have h_cross_hi32 : ((pow * lo).hi32 + hi * pow).hi32 =
      Felt.ofNat ((P * lo.val / 2 ^ 32 + hi.val * P) / 2 ^ 32) := by
    rw [h_cross_eq]; unfold Felt.hi32; congr 1; congr 1
  constructor
  · -- cross.lo32 = Felt.ofNat(c % 2^32)
    rw [h_cross_lo32]; congr 1; omega
  · -- cross.hi32 + prod1.lo32 = Felt.ofNat(c/2^32 + P*lo.val%2^32)
    rw [h_cross_hi32, h_prod_lo32_eq, ← felt_ofNat_add]; congr 1; omega

set_option maxHeartbeats 16000000 in
/-- `u64::rotr` correctly right-rotates a u64 value by `shift` bits.
    Input stack:  [shift, a.lo, a.hi] ++ rest
    Output stack: [(a.rotr shift).lo, (a.rotr shift).hi] ++ rest

    Note: the MASM implementation has a Goldilocks field overflow when
    `shift % 32 = 0` (i.e. shift = 0 or 32), so we require `shift % 32 ≠ 0`. -/
theorem u64_rotr_correct (a : U64) (shift : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = shift :: a.lo.val :: a.hi.val :: rest)
    (hshift : shift.val ≤ 63)
    (hshift_mod : shift.val % 32 ≠ 0) : -- Because of an implementation error in the MASM code
    exec 35 s Miden.Core.U64.rotr =
    some (s.withStack ((a.rotr shift.val).lo.val :: (a.rotr shift.val).hi.val :: rest)) := by
  have hshift_u32 : shift.isU32 = true := by
    simp only [Felt.isU32, decide_eq_true_eq]; omega
  rw [u64_rotr_raw a.lo.val a.hi.val shift rest s hs hshift_u32]
  -- Recover u32 bounds
  have hlo_lt : a.lo.val.val < 2 ^ 32 := by
    have h := a.lo.isU32; simp [Felt.isU32, decide_eq_true_eq] at h; exact h
  have hhi_lt : a.hi.val.val < 2 ^ 32 := by
    have h := a.hi.isU32; simp [Felt.isU32, decide_eq_true_eq] at h; exact h
  -- Simplify shiftAnd31 and effShift
  have h_and_le : shift.val &&& 31 ≤ 31 := Nat.and_le_right
  have h_and31_val : (Felt.ofNat (shift.val &&& 31)).val = shift.val &&& 31 :=
    felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  have h_eff_eq : (u32OverflowingSub 32 (Felt.ofNat (shift.val &&& 31)).val).2 =
      32 - (shift.val &&& 31) := by
    rw [h_and31_val]; unfold u32OverflowingSub; split <;> omega
  have h_eff_val : (Felt.ofNat (u32OverflowingSub 32
      (Felt.ofNat (shift.val &&& 31)).val).2).val = 32 - (shift.val &&& 31) := by
    rw [h_eff_eq]; exact felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
  -- pow.val
  have h_pow_val : (Felt.ofNat (2 ^ (Felt.ofNat (u32OverflowingSub 32
      (Felt.ofNat (shift.val &&& 31)).val).2).val)).val =
      2 ^ (32 - (shift.val &&& 31)) := by
    rw [h_eff_val]; exact felt_ofNat_val_lt _ (by
      have : 2 ^ (32 - (shift.val &&& 31)) ≤ 2 ^ 32 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      unfold GOLDILOCKS_PRIME; omega)
  -- Case split on shift > 31
  cases h31 : decide (31 < shift.val) <;> simp only [Bool.false_eq_true, ↓reduceIte,
    Bool.not_false, Bool.not_true]
  · -- Case 1: shift ≤ 31 (no swap)
    have hshift_le : shift.val ≤ 31 := by
      simp only [decide_eq_false_iff_not, not_lt] at h31; exact h31
    have hshift_pos : 1 ≤ shift.val := by omega
    have heff : shift.val &&& 31 = shift.val :=
      Nat.and_two_pow_sub_one_of_lt_two_pow (show shift.val < 2 ^ 5 by omega)
    -- P = 2^(32-shift), pow.val ≤ 2^31
    have h_pow_le : (Felt.ofNat (2 ^ (Felt.ofNat (u32OverflowingSub 32
        (Felt.ofNat (shift.val &&& 31)).val).2).val)).val ≤ 2 ^ 31 := by
      rw [h_pow_val, heff]; exact Nat.pow_le_pow_right (by omega) (by omega)
    -- Apply Felt bridge
    have ⟨h_lo_eq, h_hi_eq⟩ := rotr_felt_bridge a.lo.val a.hi.val
      (Felt.ofNat (2 ^ (Felt.ofNat (u32OverflowingSub 32
        (Felt.ofNat (shift.val &&& 31)).val).2).val))
      a.lo.isU32 a.hi.isU32 h_pow_le
    rw [h_pow_val, heff] at h_lo_eq h_hi_eq
    -- Apply nat lemma
    set P := 2 ^ (32 - shift.val)
    set Q := 2 ^ shift.val
    have hPQ : P * Q = 2 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
    have h_lp_div : P * a.lo.val.val / 2 ^ 32 = a.lo.val.val / Q := by
      rw [show (2 : Nat) ^ 32 = P * Q from hPQ.symm]; exact Nat.mul_div_mul_left _ Q (by positivity)
    have h_lp_mod : P * a.lo.val.val % 2 ^ 32 = P * (a.lo.val.val % Q) := by
      rw [show (2 : Nat) ^ 32 = P * Q from hPQ.symm]; exact Nat.mul_mod_mul_left P a.lo.val.val Q
    -- c = hi*P + lo/Q
    have h_c_eq : a.hi.val.val * P + P * a.lo.val.val / 2 ^ 32 = a.hi.val.val * P + a.lo.val.val / Q := by
      rw [h_lp_div]
    rw [h_c_eq] at h_lo_eq h_hi_eq
    rw [h_lp_mod] at h_hi_eq
    have ⟨hnat1, hnat2⟩ := rotr_nat_case1 a.hi.val.val a.lo.val.val (32 - shift.val)
      hhi_lt hlo_lt (by omega) (by omega)
    -- Simplify hnat1/hnat2: 32 - (32 - s) = s, fix associativity
    rw [show 32 - (32 - shift.val) = shift.val from by omega] at hnat1 hnat2
    rw [Nat.mul_assoc] at hnat1 hnat2
    -- Connect to U64.rotr definition
    simp only [U64.rotr, U64.ofNat_lo, U64.ofNat_hi,
      show shift.val % 64 = shift.val from Nat.mod_eq_of_lt (by omega)]
    simp only [U64.toNat]
    rw [show 2 ^ (64 - shift.val) = P * 2 ^ 32 from by
      rw [← Nat.pow_add]; congr 1; omega]
    simp only [heff]
    congr 1; congr 1; congr 1
    · rw [h_lo_eq]; exact congrArg Felt.ofNat hnat1
    · congr 1
      · rw [h_hi_eq]; exact congrArg Felt.ofNat hnat2
  · -- Case 2: 32 ≤ shift ≤ 63 (swap)
    have hshift_gt : 31 < shift.val := by
      simp only [decide_eq_true_eq] at h31; exact h31
    have heff : shift.val &&& 31 = shift.val - 32 := by
      have : shift.val &&& 31 = shift.val % 32 :=
        Nat.and_two_pow_sub_one_eq_mod shift.val 5
      rw [this]; omega
    -- P = 2^(64-shift), pow.val ≤ 2^31
    have h_pow_le : (Felt.ofNat (2 ^ (Felt.ofNat (u32OverflowingSub 32
        (Felt.ofNat (shift.val &&& 31)).val).2).val)).val ≤ 2 ^ 31 := by
      rw [h_pow_val, heff]; apply Nat.pow_le_pow_right (by omega); omega
    -- Apply Felt bridge
    have ⟨h_lo_eq, h_hi_eq⟩ := rotr_felt_bridge a.lo.val a.hi.val
      (Felt.ofNat (2 ^ (Felt.ofNat (u32OverflowingSub 32
        (Felt.ofNat (shift.val &&& 31)).val).2).val))
      a.lo.isU32 a.hi.isU32 h_pow_le
    rw [h_pow_val, heff] at h_lo_eq h_hi_eq
    -- Apply nat lemma
    set eff := 64 - shift.val
    set P := 2 ^ eff
    set Q := 2 ^ (32 - eff)
    have hPQ : P * Q = 2 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
    have h_lp_div : P * a.lo.val.val / 2 ^ 32 = a.lo.val.val / Q := by
      rw [show (2 : Nat) ^ 32 = P * Q from hPQ.symm]; exact Nat.mul_div_mul_left _ Q (by positivity)
    have h_lp_mod : P * a.lo.val.val % 2 ^ 32 = P * (a.lo.val.val % Q) := by
      rw [show (2 : Nat) ^ 32 = P * Q from hPQ.symm]; exact Nat.mul_mod_mul_left P a.lo.val.val Q
    -- Rewrite 32 - (shift.val - 32) = eff
    have h_eff_simp : 32 - (shift.val - 32) = eff := by omega
    rw [h_eff_simp] at h_lo_eq h_hi_eq
    -- c = hi*P + lo/Q
    have h_c_eq : a.hi.val.val * P + P * a.lo.val.val / 2 ^ 32 = a.hi.val.val * P + a.lo.val.val / Q := by
      rw [h_lp_div]
    rw [h_c_eq] at h_lo_eq h_hi_eq
    rw [h_lp_mod] at h_hi_eq
    have ⟨hnat1, hnat2⟩ := rotr_nat_case2 a.hi.val.val a.lo.val.val eff
      hhi_lt hlo_lt (by omega) (by omega)
    -- Connect to U64.rotr definition
    simp only [U64.rotr, U64.ofNat_lo, U64.ofNat_hi,
      show shift.val % 64 = shift.val from Nat.mod_eq_of_lt (by omega)]
    simp only [U64.toNat]
    -- Bridge: 2^shift = Q*2^32 and 2^(64-shift) = P
    conv_rhs =>
      rw [show 2 ^ shift.val = Q * 2 ^ 32 from by
            rw [← Nat.pow_add]; congr 1; omega]
    simp only [heff]
    congr 1; congr 1; congr 1
    · rw [h_hi_eq]; exact congrArg Felt.ofNat hnat1
    · congr 1
      · rw [h_lo_eq]; exact congrArg Felt.ofNat hnat2

end MidenLean.Proofs
