import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

private theorem felt31_val : (31 : Felt).val = 31 :=
  felt_ofNat_val_lt 31 (by unfold GOLDILOCKS_PRIME; omega)

private def rotl_chunk1 : List Op := [
  .inst (.movup 2),
  .inst (.swap 1),
  .inst (.push 31),
  .inst (.dup 1),
  .inst (.u32OverflowSub)
]

private def rotl_chunk2 : List Op := [
  .inst (.swap 1),
  .inst (.drop),
  .inst (.movdn 3),
  .inst (.push 31),
  .inst (.u32And),
  .inst (.pow2)
]

private def rotl_chunk3 : List Op := [
  .inst (.dup 0),
  .inst (.movup 3),
  .inst (.u32WidenMul),
  .inst (.swap 1),
  .inst (.movup 3),
  .inst (.movup 3),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.add),
  .inst (.swap 1),
  .inst (.movup 2)
]

private def rotl_chunk4 : List Op := [
  .inst (.cswap),
  .inst (.swap 1)
]

private theorem rotl_decomp :
    Miden.Core.U64.rotl = rotl_chunk1 ++ (rotl_chunk2 ++ (rotl_chunk3 ++ rotl_chunk4)) := by
  simp [Miden.Core.U64.rotl, rotl_chunk1, rotl_chunk2, rotl_chunk3, rotl_chunk4]

set_option maxHeartbeats 12000000 in
private theorem rotl_chunk1_correct
    (shift lo hi : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true) :
    exec 30 ⟨shift :: lo :: hi :: rest, mem, locs, adv⟩ rotl_chunk1 =
      some ⟨Felt.ofNat (u32OverflowingSub 31 shift.val).1 ::
        Felt.ofNat (u32OverflowingSub 31 shift.val).2 ::
        shift :: hi :: lo :: rest, mem, locs, adv⟩ := by
  unfold exec rotl_chunk1 execWithEnv
  simp only [List.foldlM]
  miden_movup
  miden_swap
  rw [stepPush]
  miden_bind
  miden_dup
  rw [stepU32OverflowSub (ha := U32.felt31_isU32) (hb := hshift_u32)]
  miden_bind
  rw [felt31_val]
  simp only [pure, Pure.pure]

set_option maxHeartbeats 12000000 in
private theorem rotl_chunk2_correct
    (shift lo hi : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true) :
    exec 30
      ⟨Felt.ofNat (u32OverflowingSub 31 shift.val).1 ::
        Felt.ofNat (u32OverflowingSub 31 shift.val).2 ::
        shift :: hi :: lo :: rest, mem, locs, adv⟩
      rotl_chunk2 =
      some ⟨Felt.ofNat (2 ^ (shift.val &&& 31)) ::
        hi :: lo :: Felt.ofNat (u32OverflowingSub 31 shift.val).1 :: rest, mem, locs, adv⟩ := by
  unfold exec rotl_chunk2 execWithEnv
  simp only [List.foldlM]
  have h_eff_bound : shift.val &&& 31 ≤ 31 := Nat.and_le_right
  have h_eff_lt_prime : shift.val &&& 31 < GOLDILOCKS_PRIME := by
    unfold GOLDILOCKS_PRIME
    omega
  have h_eff_val : (Felt.ofNat (shift.val &&& 31)).val = shift.val &&& 31 :=
    felt_ofNat_val_lt _ h_eff_lt_prime
  miden_swap
  rw [stepDrop]
  miden_bind
  miden_movdn
  rw [stepPush]
  miden_bind
  rw [stepU32And (ha := hshift_u32) (hb := U32.felt31_isU32)]
  miden_bind
  rw [felt31_val]
  rw [stepPow2 (ha := by rw [h_eff_val]; omega)]
  miden_bind
  rw [h_eff_val]
  simp only [pure, Pure.pure]

set_option maxHeartbeats 12000000 in
private theorem rotl_chunk3_correct
    (shift lo hi : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (hlo : lo.isU32 = true) (hhi : hi.isU32 = true) :
    let eff := shift.val &&& 31
    let pow := Felt.ofNat (2 ^ eff)
    let lo_prod_lo := Felt.ofNat ((2 ^ eff * lo.val) % 2 ^ 32)
    let cross_lo := Felt.ofNat ((hi.val * 2 ^ eff + (2 ^ eff * lo.val) / 2 ^ 32) % 2 ^ 32)
    let result_hi :=
      Felt.ofNat ((hi.val * 2 ^ eff + (2 ^ eff * lo.val) / 2 ^ 32) / 2 ^ 32) + lo_prod_lo
    exec 30
      ⟨pow :: hi :: lo :: Felt.ofNat (u32OverflowingSub 31 shift.val).1 :: rest, mem, locs, adv⟩
      rotl_chunk3 =
      some ⟨Felt.ofNat (u32OverflowingSub 31 shift.val).1 ::
        cross_lo :: result_hi :: rest, mem, locs, adv⟩ := by
  unfold exec rotl_chunk3 execWithEnv
  simp only [List.foldlM]
  have h_eff_bound : shift.val &&& 31 ≤ 31 := Nat.and_le_right
  have h_pow_lt_prime : 2 ^ (shift.val &&& 31) < GOLDILOCKS_PRIME := by
    have hpow_le : 2 ^ (shift.val &&& 31) ≤ 2 ^ 31 :=
      Nat.pow_le_pow_right (by omega) h_eff_bound
    unfold GOLDILOCKS_PRIME
    omega
  have h_pow_val : (Felt.ofNat (2 ^ (shift.val &&& 31))).val = 2 ^ (shift.val &&& 31) :=
    felt_ofNat_val_lt _ h_pow_lt_prime
  have h_pow_u32 : (Felt.ofNat (2 ^ (shift.val &&& 31))).isU32 = true := by
    simp only [Felt.isU32, decide_eq_true_eq]
    rw [h_pow_val]
    have hpow_le : 2 ^ (shift.val &&& 31) ≤ 2 ^ 31 :=
      Nat.pow_le_pow_right (by omega) h_eff_bound
    omega
  have h_carry_isU32 :
      (Felt.ofNat ((2 ^ (shift.val &&& 31) * lo.val) / 2 ^ 32)).isU32 = true := by
    have h :=
      u32_prod_div_isU32 (Felt.ofNat (2 ^ (shift.val &&& 31))) lo h_pow_u32 hlo
    rw [h_pow_val] at h
    exact h
  have h_carry_val : (Felt.ofNat ((2 ^ (shift.val &&& 31) * lo.val) / 2 ^ 32)).val =
      (2 ^ (shift.val &&& 31) * lo.val) / 2 ^ 32 := by
    have h :=
      felt_ofNat_val_lt _ (u32_prod_div_lt_prime (Felt.ofNat (2 ^ (shift.val &&& 31))) lo h_pow_u32 hlo)
    rw [h_pow_val] at h
    exact h
  miden_dup
  miden_movup
  rw [stepU32WidenMul (ha := by assumption) (hb := by assumption)]
  miden_bind
  rw [h_pow_val]
  miden_swap
  miden_movup
  miden_movup
  rw [stepU32WidenMadd (ha := by assumption) (hb := by assumption) (hc := by assumption)]
  miden_bind
  rw [h_pow_val, h_carry_val]
  miden_swap
  miden_movup
  rw [stepAdd]
  miden_bind
  miden_swap
  miden_movup
  simp only [pure, Pure.pure]

set_option maxHeartbeats 12000000 in
private theorem rotl_chunk4_correct
    (shift lo hi : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt) :
    let eff := shift.val &&& 31
    let lo_prod := 2 ^ eff * lo.val
    let cross := hi.val * 2 ^ eff + lo_prod / 2 ^ 32
    let result_lo := Felt.ofNat (cross % 2 ^ 32)
    let result_hi := Felt.ofNat (cross / 2 ^ 32) + Felt.ofNat (lo_prod % 2 ^ 32)
    exec 30
      ⟨Felt.ofNat (u32OverflowingSub 31 shift.val).1 ::
        result_lo :: result_hi :: rest, mem, locs, adv⟩
      rotl_chunk4 =
      some ⟨(if decide (31 < shift.val) then result_lo else result_hi) ::
        (if decide (31 < shift.val) then result_hi else result_lo) ::
        rest, mem, locs, adv⟩ := by
  unfold exec rotl_chunk4 execWithEnv
  simp only [List.foldlM]
  rw [u32OverflowingSub_borrow_ite 31 shift.val]
  rw [stepCswapIte]
  miden_bind
  miden_swap
  cases decide (31 < shift.val) <;> simp only [pure, Pure.pure]

set_option maxHeartbeats 16000000 in
/-- `u64::rotl` raw: result in terms of schoolbook multiplication of limbs. -/
theorem u64_rotl_raw
    (lo hi shift : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = shift :: lo :: hi :: rest)
    (hshift_u32 : shift.isU32 = true)
    (hlo : lo.isU32 = true)
    (hhi : hi.isU32 = true) :
    let eff := shift.val &&& 31
    let pow := 2 ^ eff
    let lo_prod := pow * lo.val
    let cross := hi.val * pow + lo_prod / 2 ^ 32
    let result_lo := Felt.ofNat (cross % 2 ^ 32)
    let result_hi := Felt.ofNat (cross / 2 ^ 32) + Felt.ofNat (lo_prod % 2 ^ 32)
    exec 30 s Miden.Core.U64.rotl =
      some (s.withStack (
        if decide (31 < shift.val) then
          result_lo :: result_hi :: rest
        else
          result_hi :: result_lo :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  rw [rotl_decomp, MidenLean.exec_append]
  rw [rotl_chunk1_correct shift lo hi rest mem locs adv hshift_u32]
  miden_bind
  rw [MidenLean.exec_append]
  rw [rotl_chunk2_correct shift lo hi rest mem locs adv hshift_u32]
  miden_bind
  rw [MidenLean.exec_append]
  rw [rotl_chunk3_correct shift lo hi rest mem locs adv hlo hhi]
  miden_bind
  rw [rotl_chunk4_correct shift lo hi rest mem locs adv]
  cases decide (31 < shift.val) <;> simp

/-- The schoolbook result matches the rotl formula: no-swap case (eff ≤ 31).
    Returns: lo limb = cross/2^32 + lo_prod%2^32, hi limb = cross%2^32. -/
private theorem rotl_nat_case1 (hi lo eff : Nat)
    (hhi : hi < 2 ^ 32) (hlo : lo < 2 ^ 32) (heff : eff ≤ 31) :
    let P := 2 ^ eff
    let lo_prod := P * lo
    let cross := hi * P + lo_prod / 2 ^ 32
    let v := (hi * 2 ^ 32 + lo) * P + (hi * 2 ^ 32 + lo) / (2 ^ 32 * 2 ^ (32 - eff))
    cross / 2 ^ 32 + lo_prod % 2 ^ 32 = v % 2 ^ 32 ∧
    cross % 2 ^ 32 = (v / 2 ^ 32) % 2 ^ 32 := by
  simp only
  set P := 2 ^ eff
  set Q := 2 ^ (32 - eff)
  have hPQ : P * Q = 2 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
  have hP_pos : 0 < P := by positivity
  have hQ_pos : 0 < Q := by positivity
  have h_lp_div : P * lo / 2 ^ 32 = lo / Q := by
    rw [show (2 : Nat) ^ 32 = P * Q from hPQ.symm]; exact Nat.mul_div_mul_left lo Q hP_pos
  have h_lp_mod : P * lo % 2 ^ 32 = P * (lo % Q) := by
    rw [show (2 : Nat) ^ 32 = P * Q from hPQ.symm]; exact Nat.mul_mod_mul_left P lo Q
  have h_lo_div_lt := lo_div_lt_of_u32 P Q lo hPQ hQ_pos hlo
  have h_xP := schoolbook_mul_eq P Q hi lo hPQ
  have h_div := u64_div_large_pow hi lo Q hlo
  have h_cross_div := cross_div_eq P Q hi lo hPQ hQ_pos h_lo_div_lt
  have h_nonoverlap := limb_non_overlap P Q hi lo hPQ hQ_pos hhi
  -- Simplify cross and lo_prod terms on LHS, and v terms on RHS
  rw [h_lp_div, h_lp_mod, h_cross_div, h_div, h_xP]
  -- v = (hi*P+lo/Q) * 2^32 + P*(lo%Q) + hi/Q
  --   = (hi/Q + P*(lo%Q)) + (hi*P+lo/Q) * 2^32
  set c := hi * P + lo / Q
  have h_rearrange : c * 2 ^ 32 + P * (lo % Q) + hi / Q =
      (hi / Q + P * (lo % Q)) + c * 2 ^ 32 := by omega
  rw [h_rearrange]
  constructor
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h_nonoverlap]
  · rw [Nat.add_mul_div_right _ _ (by positivity : 0 < 2 ^ 32),
        Nat.div_eq_of_lt h_nonoverlap, Nat.zero_add]

/-- The schoolbook result matches the rotl formula: swap case (eff = shift - 32, shift > 31). -/
private theorem rotl_nat_case2 (hi lo eff : Nat)
    (hhi : hi < 2 ^ 32) (hlo : lo < 2 ^ 32) (heff : eff ≤ 31) :
    let P := 2 ^ eff
    let lo_prod := P * lo
    let cross := hi * P + lo_prod / 2 ^ 32
    let v := (hi * 2 ^ 32 + lo) * (P * 2 ^ 32) + (hi * P + lo / 2 ^ (32 - eff))
    cross % 2 ^ 32 = v % 2 ^ 32 ∧
    cross / 2 ^ 32 + lo_prod % 2 ^ 32 = (v / 2 ^ 32) % 2 ^ 32 := by
  simp only
  set P := 2 ^ eff
  set Q := 2 ^ (32 - eff)
  have hPQ : P * Q = 2 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
  have hP_pos : 0 < P := by positivity
  have hQ_pos : 0 < Q := by positivity
  have h_lp_div : P * lo / 2 ^ 32 = lo / Q := by
    rw [show (2 : Nat) ^ 32 = P * Q from hPQ.symm]; exact Nat.mul_div_mul_left lo Q hP_pos
  have h_lp_mod : P * lo % 2 ^ 32 = P * (lo % Q) := by
    rw [show (2 : Nat) ^ 32 = P * Q from hPQ.symm]; exact Nat.mul_mod_mul_left P lo Q
  have h_lo_div_lt := lo_div_lt_of_u32 P Q lo hPQ hQ_pos hlo
  have h_xP := schoolbook_mul_eq P Q hi lo hPQ
  have h_cross_div := cross_div_eq P Q hi lo hPQ hQ_pos h_lo_div_lt
  have h_nonoverlap := limb_non_overlap P Q hi lo hPQ hQ_pos hhi
  -- Simplify cross terms on LHS
  rw [h_lp_div, h_lp_mod, h_cross_div]
  -- Simplify v: (hi*2^32+lo)*(P*2^32) = ((hi*2^32+lo)*P)*2^32
  have h_mul_assoc : (hi * 2 ^ 32 + lo) * (P * 2 ^ 32) =
      ((hi * 2 ^ 32 + lo) * P) * 2 ^ 32 := by ring
  rw [h_mul_assoc, h_xP]
  -- Now v = ((hi*P+lo/Q)*2^32 + P*(lo%Q))*2^32 + (hi*P+lo/Q)
  set c := hi * P + lo / Q
  -- v = (c*2^32 + P*(lo%Q))*2^32 + c = c + (c*2^32 + P*(lo%Q))*2^32
  have h_comm : (c * 2 ^ 32 + P * (lo % Q)) * 2 ^ 32 + c =
      c + (c * 2 ^ 32 + P * (lo % Q)) * 2 ^ 32 := by omega
  rw [h_comm]
  constructor
  · -- v%2^32 = c%2^32
    rw [Nat.add_mul_mod_self_right]
  · -- (v/2^32)%2^32 = hi/Q + P*(lo%Q)
    rw [Nat.add_mul_div_right _ _ (by positivity : 0 < 2 ^ 32)]
    -- Goal: (c/2^32 + (c*2^32 + P*(lo%Q))) % 2^32 = hi/Q + P*(lo%Q)
    have h_reorder : c / 2 ^ 32 + (c * 2 ^ 32 + P * (lo % Q)) =
        (c / 2 ^ 32 + P * (lo % Q)) + c * 2 ^ 32 := by omega
    have h_nonoverlap2 : c / 2 ^ 32 + P * (lo % Q) < 2 ^ 32 := by
      rw [show c / 2 ^ 32 = hi / Q from h_cross_div]; exact h_nonoverlap
    rw [h_reorder, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h_nonoverlap2, h_cross_div]

set_option maxHeartbeats 16000000 in
/-- `u64::rotl` left-rotates a u64 value by `shift` bits.
    Input stack:  [shift, a.lo, a.hi] ++ rest
    Output stack: [(a.rotl shift).lo, (a.rotl shift).hi] ++ rest -/
theorem u64_rotl_correct (a : U64) (shift : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = shift :: a.lo.val :: a.hi.val :: rest)
    (hshift : shift.val ≤ 63) :
    exec 30 s Miden.Core.U64.rotl =
    some (s.withStack ((a.rotl shift.val).lo.val :: (a.rotl shift.val).hi.val :: rest)) := by
  have hshift_u32 : shift.isU32 = true := by
    simp only [Felt.isU32, decide_eq_true_eq]; omega
  rw [u64_rotl_raw a.lo.val a.hi.val shift rest s hs hshift_u32 a.lo.isU32 a.hi.isU32]
  -- Recover u32 bounds
  have hlo_lt : a.lo.val.val < 2 ^ 32 := by
    have h := a.lo.isU32; simp [Felt.isU32, decide_eq_true_eq] at h; exact h
  have hhi_lt : a.hi.val.val < 2 ^ 32 := by
    have h := a.hi.isU32; simp [Felt.isU32, decide_eq_true_eq] at h; exact h
  -- Case split on shift > 31
  cases h31 : decide (31 < shift.val) <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · -- Case 1: shift ≤ 31 (no swap)
    have hshift_le : shift.val ≤ 31 := by
      simp only [decide_eq_false_iff_not, not_lt] at h31; exact h31
    have heff : shift.val &&& 31 = shift.val :=
      Nat.and_two_pow_sub_one_of_lt_two_pow (show shift.val < 2 ^ 5 by omega)
    rw [heff]
    simp only [U64.rotl, U64.ofNat_lo, U64.ofNat_hi,
      show shift.val % 64 = shift.val from Nat.mod_eq_of_lt (by omega)]
    simp only [U64.toNat]
    have ⟨h1, h2⟩ := rotl_nat_case1 a.hi.val.val a.lo.val.val shift.val hhi_lt hlo_lt (by omega)
    rw [show 2 ^ (64 - shift.val) = 2 ^ 32 * 2 ^ (32 - shift.val) from by
      rw [← Nat.pow_add]; congr 1; omega]
    congr 1; congr 1; congr 1
    · rw [← felt_ofNat_add]; exact congrArg Felt.ofNat h1
    · congr 1; exact congrArg Felt.ofNat h2
  · -- Case 2: 32 ≤ shift ≤ 63 (swap)
    have hshift_gt : 31 < shift.val := by
      simp only [decide_eq_true_eq] at h31; exact h31
    have heff : shift.val &&& 31 = shift.val - 32 := by
      have : shift.val &&& 31 = shift.val % 32 :=
        Nat.and_two_pow_sub_one_eq_mod shift.val 5
      rw [this]; omega
    rw [heff]
    simp only [U64.rotl, U64.ofNat_lo, U64.ofNat_hi,
      show shift.val % 64 = shift.val from Nat.mod_eq_of_lt (by omega)]
    simp only [U64.toNat]
    -- Bridge rotl definition to rotl_nat_case2's v (only on RHS)
    conv_rhs =>
      rw [show 2 ^ shift.val = 2 ^ (shift.val - 32) * 2 ^ 32 from by
            rw [← Nat.pow_add]; congr 1; omega,
          show 64 - shift.val = 32 - (shift.val - 32) from by omega,
          show (a.hi.val.val * 2 ^ 32 + a.lo.val.val) / 2 ^ (32 - (shift.val - 32)) =
            a.hi.val.val * 2 ^ (shift.val - 32) + a.lo.val.val / 2 ^ (32 - (shift.val - 32)) from by
            rw [show a.hi.val.val * 2 ^ 32 = a.hi.val.val * 2 ^ (shift.val - 32) * 2 ^ (32 - (shift.val - 32)) from by
              rw [Nat.mul_assoc, show 2 ^ (shift.val - 32) * 2 ^ (32 - (shift.val - 32)) = 2 ^ 32 from by
                rw [← Nat.pow_add]; congr 1; omega],
              show a.hi.val.val * 2 ^ (shift.val - 32) * 2 ^ (32 - (shift.val - 32)) + a.lo.val.val =
                a.lo.val.val + a.hi.val.val * 2 ^ (shift.val - 32) * 2 ^ (32 - (shift.val - 32)) from by omega]
            rw [Nat.add_mul_div_right _ _ (show 0 < 2 ^ (32 - (shift.val - 32)) from by positivity)]
            omega]
    have heff_le : shift.val - 32 ≤ 31 := by omega
    have ⟨h1, h2⟩ := rotl_nat_case2 a.hi.val.val a.lo.val.val (shift.val - 32) hhi_lt hlo_lt heff_le
    congr 1; congr 1; congr 1
    · exact congrArg Felt.ofNat h1
    · congr 1; rw [← felt_ofNat_add]; exact congrArg Felt.ofNat h2

end MidenLean.Proofs
