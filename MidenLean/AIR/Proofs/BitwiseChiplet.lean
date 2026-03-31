import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic
import MidenLean.AIR.BitwiseChiplet
import MidenLean.Proofs.Helpers

namespace MidenLean.AIR.Proofs

open MidenLean
open MidenLean.AIR

private theorem bit_zero_or_one (b : Felt) (hb : b * (b - 1) = 0) :
    b = 0 ∨ b = 1 := by
  rcases mul_eq_zero.mp hb with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

private theorem aggregateNibble_eq_digit (n : Nibble Felt)
    (hbin : n.b0 * (n.b0 - 1) = 0 ∧
      n.b1 * (n.b1 - 1) = 0 ∧
      n.b2 * (n.b2 - 1) = 0 ∧
      n.b3 * (n.b3 - 1) = 0) :
    ∃ k : Fin 16, aggregateNibble n = Felt.ofNat k.val := by
  rcases bit_zero_or_one n.b0 hbin.1 with hb0 | hb0 <;>
  rcases bit_zero_or_one n.b1 hbin.2.1 with hb1 | hb1 <;>
  rcases bit_zero_or_one n.b2 hbin.2.2.1 with hb2 | hb2 <;>
  rcases bit_zero_or_one n.b3 hbin.2.2.2 with hb3 | hb3
  all_goals
    unfold aggregateNibble
    rw [hb0, hb1, hb2, hb3]
    native_decide

set_option maxHeartbeats 10000000 in
private theorem nibbleAnd_eq_digits (a b : Nibble Felt)
    (ha : a.b0 * (a.b0 - 1) = 0 ∧
      a.b1 * (a.b1 - 1) = 0 ∧
      a.b2 * (a.b2 - 1) = 0 ∧
      a.b3 * (a.b3 - 1) = 0)
    (hb : b.b0 * (b.b0 - 1) = 0 ∧
      b.b1 * (b.b1 - 1) = 0 ∧
      b.b2 * (b.b2 - 1) = 0 ∧
      b.b3 * (b.b3 - 1) = 0) :
    ∃ ka kb : Fin 16,
      aggregateNibble a = Felt.ofNat ka.val ∧
      aggregateNibble b = Felt.ofNat kb.val ∧
      nibbleAnd a b = Felt.ofNat (ka.val &&& kb.val) := by
  rcases bit_zero_or_one a.b0 ha.1 with ha0 | ha0 <;>
  rcases bit_zero_or_one a.b1 ha.2.1 with ha1 | ha1 <;>
  rcases bit_zero_or_one a.b2 ha.2.2.1 with ha2 | ha2 <;>
  rcases bit_zero_or_one a.b3 ha.2.2.2 with ha3 | ha3 <;>
  rcases bit_zero_or_one b.b0 hb.1 with hb0 | hb0 <;>
  rcases bit_zero_or_one b.b1 hb.2.1 with hb1 | hb1 <;>
  rcases bit_zero_or_one b.b2 hb.2.2.1 with hb2 | hb2 <;>
  rcases bit_zero_or_one b.b3 hb.2.2.2 with hb3 | hb3
  all_goals
    unfold aggregateNibble nibbleAnd
    rw [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3]
    native_decide

set_option maxHeartbeats 10000000 in
private theorem nibbleXor_eq_digits (a b : Nibble Felt)
    (ha : a.b0 * (a.b0 - 1) = 0 ∧
      a.b1 * (a.b1 - 1) = 0 ∧
      a.b2 * (a.b2 - 1) = 0 ∧
      a.b3 * (a.b3 - 1) = 0)
    (hb : b.b0 * (b.b0 - 1) = 0 ∧
      b.b1 * (b.b1 - 1) = 0 ∧
      b.b2 * (b.b2 - 1) = 0 ∧
      b.b3 * (b.b3 - 1) = 0) :
    ∃ ka kb : Fin 16,
      aggregateNibble a = Felt.ofNat ka.val ∧
      aggregateNibble b = Felt.ofNat kb.val ∧
      nibbleXor a b = Felt.ofNat (ka.val ^^^ kb.val) := by
  rcases bit_zero_or_one a.b0 ha.1 with ha0 | ha0 <;>
  rcases bit_zero_or_one a.b1 ha.2.1 with ha1 | ha1 <;>
  rcases bit_zero_or_one a.b2 ha.2.2.1 with ha2 | ha2 <;>
  rcases bit_zero_or_one a.b3 ha.2.2.2 with ha3 | ha3 <;>
  rcases bit_zero_or_one b.b0 hb.1 with hb0 | hb0 <;>
  rcases bit_zero_or_one b.b1 hb.2.1 with hb1 | hb1 <;>
  rcases bit_zero_or_one b.b2 hb.2.2.1 with hb2 | hb2 <;>
  rcases bit_zero_or_one b.b3 hb.2.2.2 with hb3 | hb3
  all_goals
    unfold aggregateNibble nibbleXor
    rw [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3]
    native_decide

private theorem finDigit_eq_bits (n : Fin 16) :
    ∃ b0 b1 b2 b3, n.val = Nat.bit b0 (Nat.bit b1 (Nat.bit b2 (Nat.bit b3 0))) := by
  fin_cases n <;> native_decide

private theorem append_bits_eq (a : Nat) (b0 b1 b2 b3 : Bool) :
    a * 16 + Nat.bit b0 (Nat.bit b1 (Nat.bit b2 (Nat.bit b3 0))) =
      Nat.bit b0 (Nat.bit b1 (Nat.bit b2 (Nat.bit b3 a))) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> simp [Nat.bit] <;> omega

private theorem and_append_nibble (a b : Nat) (na nb : Fin 16) :
    (a * 16 + na.val) &&& (b * 16 + nb.val) = (a &&& b) * 16 + (na.val &&& nb.val) := by
  rcases finDigit_eq_bits na with ⟨a0, a1, a2, a3, hna⟩
  rcases finDigit_eq_bits nb with ⟨b0, b1, b2, b3, hnb⟩
  rw [hna, hnb, append_bits_eq a a0 a1 a2 a3, append_bits_eq b b0 b1 b2 b3]
  rw [Nat.land_bit, Nat.land_bit, Nat.land_bit, Nat.land_bit]
  conv_rhs => rw [Nat.land_bit, Nat.land_bit, Nat.land_bit, Nat.land_bit]
  rw [← append_bits_eq (a &&& b) (a0 && b0) (a1 && b1) (a2 && b2) (a3 && b3)]
  simp

private theorem xor_append_nibble (a b : Nat) (na nb : Fin 16) :
    (a * 16 + na.val) ^^^ (b * 16 + nb.val) = (a ^^^ b) * 16 + (na.val ^^^ nb.val) := by
  rcases finDigit_eq_bits na with ⟨a0, a1, a2, a3, hna⟩
  rcases finDigit_eq_bits nb with ⟨b0, b1, b2, b3, hnb⟩
  rw [hna, hnb, append_bits_eq a a0 a1 a2 a3, append_bits_eq b b0 b1 b2 b3]
  rw [Nat.xor_bit, Nat.xor_bit, Nat.xor_bit, Nat.xor_bit]
  conv_rhs => rw [Nat.xor_bit, Nat.xor_bit, Nat.xor_bit, Nat.xor_bit]
  rw [← append_bits_eq (a ^^^ b) (a0 != b0) (a1 != b1) (a2 != b2) (a3 != b3)]
  simp

private def andDigit (a b : Fin 16) : Fin 16 := ⟨a.val &&& b.val, by
  have hb : b.val < 2 ^ 4 := by simpa using b.isLt
  exact Nat.and_lt_two_pow a.val hb⟩

private def xorDigit (a b : Fin 16) : Fin 16 := ⟨a.val ^^^ b.val, by
  have ha : a.val < 2 ^ 4 := by simpa using a.isLt
  have hb : b.val < 2 ^ 4 := by simpa using b.isLt
  exact Nat_xor_lt_of_lt ha hb⟩

private def extendDigits (acc : Nat) (d : Fin 16) : Nat := acc * 16 + d.val

private def digitsValue (d0 d1 d2 d3 d4 d5 d6 d7 : Fin 16) : Nat :=
  extendDigits
    (extendDigits
      (extendDigits
        (extendDigits
          (extendDigits
            (extendDigits
              (extendDigits d0.val d1) d2) d3) d4) d5) d6) d7

private theorem digitsValue_lt_u32
    (d0 d1 d2 d3 d4 d5 d6 d7 : Fin 16) :
    digitsValue d0 d1 d2 d3 d4 d5 d6 d7 < 2 ^ 32 := by
  unfold digitsValue extendDigits
  omega

private theorem digitsValue_and
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Fin 16) :
    digitsValue (andDigit a0 b0) (andDigit a1 b1) (andDigit a2 b2) (andDigit a3 b3)
      (andDigit a4 b4) (andDigit a5 b5) (andDigit a6 b6) (andDigit a7 b7) =
      digitsValue a0 a1 a2 a3 a4 a5 a6 a7 &&&
        digitsValue b0 b1 b2 b3 b4 b5 b6 b7 := by
  unfold digitsValue extendDigits
  rw [and_append_nibble, and_append_nibble, and_append_nibble, and_append_nibble,
    and_append_nibble, and_append_nibble, and_append_nibble]
  simp [andDigit]

private theorem digitsValue_xor
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Fin 16) :
    digitsValue (xorDigit a0 b0) (xorDigit a1 b1) (xorDigit a2 b2) (xorDigit a3 b3)
      (xorDigit a4 b4) (xorDigit a5 b5) (xorDigit a6 b6) (xorDigit a7 b7) =
      digitsValue a0 a1 a2 a3 a4 a5 a6 a7 ^^^
        digitsValue b0 b1 b2 b3 b4 b5 b6 b7 := by
  unfold digitsValue extendDigits
  rw [xor_append_nibble, xor_append_nibble, xor_append_nibble, xor_append_nibble,
    xor_append_nibble, xor_append_nibble, xor_append_nibble]
  simp [xorDigit]

private theorem next_input_a_eq
    {row row_next : BitwiseRow} {acc digit : Nat}
    (htr : air_bitwise_transition_constraints row row_next)
    (ha : row.a = Felt.ofNat acc)
    (hagg : aggregateNibble row_next.a_bits = Felt.ofNat digit) :
    row_next.a = Felt.ofNat (acc * 16 + digit) := by
  calc
    row_next.a = row.a * 16 + aggregateNibble row_next.a_bits := htr.2.1.1
    _ = Felt.ofNat (acc * 16 + digit) := by
      rw [ha, hagg]
      simp [Felt.ofNat, Nat.cast_add, Nat.cast_mul, add_comm]

private theorem next_input_b_eq
    {row row_next : BitwiseRow} {acc digit : Nat}
    (htr : air_bitwise_transition_constraints row row_next)
    (hb : row.b = Felt.ofNat acc)
    (hagg : aggregateNibble row_next.b_bits = Felt.ofNat digit) :
    row_next.b = Felt.ofNat (acc * 16 + digit) := by
  calc
    row_next.b = row.b * 16 + aggregateNibble row_next.b_bits := htr.2.1.2
    _ = Felt.ofNat (acc * 16 + digit) := by
      rw [hb, hagg]
      simp [Felt.ofNat, Nat.cast_add, Nat.cast_mul, add_comm]

private theorem next_zp_eq
    {row row_next : BitwiseRow} {acc : Nat}
    (htr : air_bitwise_transition_constraints row row_next)
    (hz : row.z = Felt.ofNat acc) :
    row_next.zp = Felt.ofNat acc := by
  calc
    row_next.zp = row.z := htr.2.2
    _ = Felt.ofNat acc := hz

private theorem output_and_eq
    {row : BitwiseRow} {acc digit : Nat}
    (hrow : air_bitwise_row_constraints row)
    (hflag : row.op_flag = 0)
    (hand : nibbleAnd row.a_bits row.b_bits = Felt.ofNat digit)
    (hzp : row.zp = Felt.ofNat acc) :
    row.z = Felt.ofNat (acc * 16 + digit) := by
  calc
    row.z = row.zp * 16 + nibbleAnd row.a_bits row.b_bits +
        row.op_flag * (nibbleXor row.a_bits row.b_bits - nibbleAnd row.a_bits row.b_bits) := by
          simpa [air_bitwise_output_aggregation] using (hrow.2.2.2 : air_bitwise_output_aggregation row)
    _ = Felt.ofNat (acc * 16 + digit) := by
      rw [hflag, hand, hzp]
      simp [Felt.ofNat, Nat.cast_add, Nat.cast_mul, add_comm]

private theorem output_xor_eq
    {row : BitwiseRow} {acc digit : Nat}
    (hrow : air_bitwise_row_constraints row)
    (hflag : row.op_flag = 1)
    (hxor : nibbleXor row.a_bits row.b_bits = Felt.ofNat digit)
    (hzp : row.zp = Felt.ofNat acc) :
    row.z = Felt.ofNat (acc * 16 + digit) := by
  calc
    row.z = row.zp * 16 + nibbleAnd row.a_bits row.b_bits +
        row.op_flag * (nibbleXor row.a_bits row.b_bits - nibbleAnd row.a_bits row.b_bits) := by
          simpa [air_bitwise_output_aggregation] using (hrow.2.2.2 : air_bitwise_output_aggregation row)
    _ = Felt.ofNat (acc * 16 + digit) := by
      rw [hflag, hxor, hzp]
      simp [Felt.ofNat, Nat.cast_add, Nat.cast_mul, add_comm]

theorem bitwise_cycle_and_sound
    (rows : Fin 8 → BitwiseRow)
    (h_cycle : air_bitwise_full_cycle rows)
    (h_flag : (rows 0).op_flag = 0) :
    (rows 7).a.IsU32 ∧ (rows 7).b.IsU32 ∧
      (rows 7).z = Felt.ofNat ((rows 7).a.val &&& (rows 7).b.val) := by
  rcases h_cycle with ⟨h_first, h_rows, h_trans⟩
  have hrow0 := h_rows 0
  have hrow1 := h_rows 1
  have hrow2 := h_rows 2
  have hrow3 := h_rows 3
  have hrow4 := h_rows 4
  have hrow5 := h_rows 5
  have hrow6 := h_rows 6
  have hrow7 := h_rows 7
  have htr0 := h_trans 0
  have htr1 := h_trans 1
  have htr2 := h_trans 2
  have htr3 := h_trans 3
  have htr4 := h_trans 4
  have htr5 := h_trans 5
  have htr6 := h_trans 6
  obtain ⟨a0, b0, hAagg0, hBagg0, hAnd0⟩ := nibbleAnd_eq_digits (rows 0).a_bits (rows 0).b_bits
    hrow0.2.1 hrow0.2.2.1
  obtain ⟨a1, b1, hAagg1, hBagg1, hAnd1⟩ := nibbleAnd_eq_digits (rows 1).a_bits (rows 1).b_bits
    hrow1.2.1 hrow1.2.2.1
  obtain ⟨a2, b2, hAagg2, hBagg2, hAnd2⟩ := nibbleAnd_eq_digits (rows 2).a_bits (rows 2).b_bits
    hrow2.2.1 hrow2.2.2.1
  obtain ⟨a3, b3, hAagg3, hBagg3, hAnd3⟩ := nibbleAnd_eq_digits (rows 3).a_bits (rows 3).b_bits
    hrow3.2.1 hrow3.2.2.1
  obtain ⟨a4, b4, hAagg4, hBagg4, hAnd4⟩ := nibbleAnd_eq_digits (rows 4).a_bits (rows 4).b_bits
    hrow4.2.1 hrow4.2.2.1
  obtain ⟨a5, b5, hAagg5, hBagg5, hAnd5⟩ := nibbleAnd_eq_digits (rows 5).a_bits (rows 5).b_bits
    hrow5.2.1 hrow5.2.2.1
  obtain ⟨a6, b6, hAagg6, hBagg6, hAnd6⟩ := nibbleAnd_eq_digits (rows 6).a_bits (rows 6).b_bits
    hrow6.2.1 hrow6.2.2.1
  obtain ⟨a7, b7, hAagg7, hBagg7, hAnd7⟩ := nibbleAnd_eq_digits (rows 7).a_bits (rows 7).b_bits
    hrow7.2.1 hrow7.2.2.1
  have hflag1 : (rows 1).op_flag = 0 := by simpa [h_flag] using htr0.1.symm
  have hflag2 : (rows 2).op_flag = 0 := by simpa [hflag1] using htr1.1.symm
  have hflag3 : (rows 3).op_flag = 0 := by simpa [hflag2] using htr2.1.symm
  have hflag4 : (rows 4).op_flag = 0 := by simpa [hflag3] using htr3.1.symm
  have hflag5 : (rows 5).op_flag = 0 := by simpa [hflag4] using htr4.1.symm
  have hflag6 : (rows 6).op_flag = 0 := by simpa [hflag5] using htr5.1.symm
  have hflag7 : (rows 7).op_flag = 0 := by simpa [hflag6] using htr6.1.symm
  have hA0 : (rows 0).a = Felt.ofNat a0.val := by
    calc
      (rows 0).a = aggregateNibble (rows 0).a_bits := h_first.1
      _ = Felt.ofNat a0.val := hAagg0
  have hB0 : (rows 0).b = Felt.ofNat b0.val := by
    calc
      (rows 0).b = aggregateNibble (rows 0).b_bits := h_first.2.1
      _ = Felt.ofNat b0.val := hBagg0
  have hZp0 : (rows 0).zp = Felt.ofNat 0 := by simpa using h_first.2.2
  have hZ0 : (rows 0).z = Felt.ofNat (andDigit a0 b0).val := by
    simpa [andDigit] using output_and_eq hrow0 h_flag hAnd0 hZp0
  have hA1 : (rows 1).a = Felt.ofNat (a0.val * 16 + a1.val) :=
    next_input_a_eq htr0 hA0 hAagg1
  have hB1 : (rows 1).b = Felt.ofNat (b0.val * 16 + b1.val) :=
    next_input_b_eq htr0 hB0 hBagg1
  have hZp1 : (rows 1).zp = Felt.ofNat (andDigit a0 b0).val :=
    next_zp_eq htr0 hZ0
  have hZ1 : (rows 1).z = Felt.ofNat ((andDigit a0 b0).val * 16 + (andDigit a1 b1).val) := by
    simpa [andDigit] using output_and_eq hrow1 hflag1 hAnd1 hZp1
  have hA2 : (rows 2).a = Felt.ofNat ((a0.val * 16 + a1.val) * 16 + a2.val) :=
    next_input_a_eq htr1 hA1 hAagg2
  have hB2 : (rows 2).b = Felt.ofNat ((b0.val * 16 + b1.val) * 16 + b2.val) :=
    next_input_b_eq htr1 hB1 hBagg2
  have hZp2 : (rows 2).zp = Felt.ofNat ((andDigit a0 b0).val * 16 + (andDigit a1 b1).val) :=
    next_zp_eq htr1 hZ1
  have hZ2 : (rows 2).z = Felt.ofNat (((andDigit a0 b0).val * 16 + (andDigit a1 b1).val) * 16 +
      (andDigit a2 b2).val) := by
    simpa [andDigit] using output_and_eq hrow2 hflag2 hAnd2 hZp2
  have hA3 : (rows 3).a = Felt.ofNat (((a0.val * 16 + a1.val) * 16 + a2.val) * 16 + a3.val) :=
    next_input_a_eq htr2 hA2 hAagg3
  have hB3 : (rows 3).b = Felt.ofNat (((b0.val * 16 + b1.val) * 16 + b2.val) * 16 + b3.val) :=
    next_input_b_eq htr2 hB2 hBagg3
  have hZp3 :
      (rows 3).zp = Felt.ofNat ((((andDigit a0 b0).val * 16 + (andDigit a1 b1).val) * 16 +
        (andDigit a2 b2).val)) :=
    next_zp_eq htr2 hZ2
  have hZ3 : (rows 3).z = Felt.ofNat ((((andDigit a0 b0).val * 16 + (andDigit a1 b1).val) * 16 +
      (andDigit a2 b2).val) * 16 + (andDigit a3 b3).val) := by
    simpa [andDigit] using output_and_eq hrow3 hflag3 hAnd3 hZp3
  have hA4 : (rows 4).a = Felt.ofNat ((((a0.val * 16 + a1.val) * 16 + a2.val) * 16 + a3.val) * 16 +
      a4.val) := next_input_a_eq htr3 hA3 hAagg4
  have hB4 : (rows 4).b = Felt.ofNat ((((b0.val * 16 + b1.val) * 16 + b2.val) * 16 + b3.val) * 16 +
      b4.val) := next_input_b_eq htr3 hB3 hBagg4
  have hZp4 :
      (rows 4).zp = Felt.ofNat (((((andDigit a0 b0).val * 16 + (andDigit a1 b1).val) * 16 +
        (andDigit a2 b2).val) * 16 + (andDigit a3 b3).val)) :=
    next_zp_eq htr3 hZ3
  have hZ4 : (rows 4).z = Felt.ofNat (((((andDigit a0 b0).val * 16 + (andDigit a1 b1).val) * 16 +
      (andDigit a2 b2).val) * 16 + (andDigit a3 b3).val) * 16 + (andDigit a4 b4).val) := by
    simpa [andDigit] using output_and_eq hrow4 hflag4 hAnd4 hZp4
  have hA5 : (rows 5).a = Felt.ofNat (((((a0.val * 16 + a1.val) * 16 + a2.val) * 16 + a3.val) * 16 +
      a4.val) * 16 + a5.val) := next_input_a_eq htr4 hA4 hAagg5
  have hB5 : (rows 5).b = Felt.ofNat (((((b0.val * 16 + b1.val) * 16 + b2.val) * 16 + b3.val) * 16 +
      b4.val) * 16 + b5.val) := next_input_b_eq htr4 hB4 hBagg5
  have hZp5 :
      (rows 5).zp = Felt.ofNat ((((((andDigit a0 b0).val * 16 + (andDigit a1 b1).val) * 16 +
        (andDigit a2 b2).val) * 16 + (andDigit a3 b3).val) * 16 + (andDigit a4 b4).val)) :=
    next_zp_eq htr4 hZ4
  have hZ5 : (rows 5).z = Felt.ofNat ((((((andDigit a0 b0).val * 16 + (andDigit a1 b1).val) * 16 +
      (andDigit a2 b2).val) * 16 + (andDigit a3 b3).val) * 16 + (andDigit a4 b4).val) * 16 +
      (andDigit a5 b5).val) := by
    simpa [andDigit] using output_and_eq hrow5 hflag5 hAnd5 hZp5
  have hA6 : (rows 6).a = Felt.ofNat ((((((a0.val * 16 + a1.val) * 16 + a2.val) * 16 + a3.val) * 16 +
      a4.val) * 16 + a5.val) * 16 + a6.val) := next_input_a_eq htr5 hA5 hAagg6
  have hB6 : (rows 6).b = Felt.ofNat ((((((b0.val * 16 + b1.val) * 16 + b2.val) * 16 + b3.val) * 16 +
      b4.val) * 16 + b5.val) * 16 + b6.val) := next_input_b_eq htr5 hB5 hBagg6
  have hZp6 :
      (rows 6).zp = Felt.ofNat (((((((andDigit a0 b0).val * 16 + (andDigit a1 b1).val) * 16 +
        (andDigit a2 b2).val) * 16 + (andDigit a3 b3).val) * 16 + (andDigit a4 b4).val) * 16 +
        (andDigit a5 b5).val)) := next_zp_eq htr5 hZ5
  have hZ6 : (rows 6).z = Felt.ofNat (((((((andDigit a0 b0).val * 16 + (andDigit a1 b1).val) * 16 +
      (andDigit a2 b2).val) * 16 + (andDigit a3 b3).val) * 16 + (andDigit a4 b4).val) * 16 +
      (andDigit a5 b5).val) * 16 + (andDigit a6 b6).val) := by
    simpa [andDigit] using output_and_eq hrow6 hflag6 hAnd6 hZp6
  have hA7 : (rows 7).a = Felt.ofNat (digitsValue a0 a1 a2 a3 a4 a5 a6 a7) := by
    simpa [digitsValue, extendDigits] using next_input_a_eq htr6 hA6 hAagg7
  have hB7 : (rows 7).b = Felt.ofNat (digitsValue b0 b1 b2 b3 b4 b5 b6 b7) := by
    simpa [digitsValue, extendDigits] using next_input_b_eq htr6 hB6 hBagg7
  have hZp7 :
      (rows 7).zp = Felt.ofNat ((((((((andDigit a0 b0).val * 16 + (andDigit a1 b1).val) * 16 +
        (andDigit a2 b2).val) * 16 + (andDigit a3 b3).val) * 16 + (andDigit a4 b4).val) * 16 +
        (andDigit a5 b5).val) * 16 + (andDigit a6 b6).val)) := next_zp_eq htr6 hZ6
  have hZ7 : (rows 7).z = Felt.ofNat (digitsValue
      (andDigit a0 b0) (andDigit a1 b1) (andDigit a2 b2) (andDigit a3 b3)
      (andDigit a4 b4) (andDigit a5 b5) (andDigit a6 b6) (andDigit a7 b7)) := by
    simpa [digitsValue, extendDigits, andDigit] using output_and_eq hrow7 hflag7 hAnd7 hZp7
  have hA7u32 : (rows 7).a.IsU32 := by
    rw [hA7]
    unfold Felt.IsU32
    rw [felt_ofNat_val_lt _ (u32_val_lt_prime _ (digitsValue_lt_u32 _ _ _ _ _ _ _ _))]
    exact digitsValue_lt_u32 _ _ _ _ _ _ _ _
  have hB7u32 : (rows 7).b.IsU32 := by
    rw [hB7]
    unfold Felt.IsU32
    rw [felt_ofNat_val_lt _ (u32_val_lt_prime _ (digitsValue_lt_u32 _ _ _ _ _ _ _ _))]
    exact digitsValue_lt_u32 _ _ _ _ _ _ _ _
  have hA7val :
      (rows 7).a.val = digitsValue a0 a1 a2 a3 a4 a5 a6 a7 := by
    rw [hA7, felt_ofNat_val_lt _ (u32_val_lt_prime _ (digitsValue_lt_u32 _ _ _ _ _ _ _ _))]
  have hB7val :
      (rows 7).b.val = digitsValue b0 b1 b2 b3 b4 b5 b6 b7 := by
    rw [hB7, felt_ofNat_val_lt _ (u32_val_lt_prime _ (digitsValue_lt_u32 _ _ _ _ _ _ _ _))]
  refine ⟨hA7u32, hB7u32, ?_⟩
  rw [hZ7, hA7val, hB7val, digitsValue_and]

theorem bitwise_cycle_xor_sound
    (rows : Fin 8 → BitwiseRow)
    (h_cycle : air_bitwise_full_cycle rows)
    (h_flag : (rows 0).op_flag = 1) :
    (rows 7).a.IsU32 ∧ (rows 7).b.IsU32 ∧
      (rows 7).z = Felt.ofNat ((rows 7).a.val ^^^ (rows 7).b.val) := by
  rcases h_cycle with ⟨h_first, h_rows, h_trans⟩
  have hrow0 := h_rows 0
  have hrow1 := h_rows 1
  have hrow2 := h_rows 2
  have hrow3 := h_rows 3
  have hrow4 := h_rows 4
  have hrow5 := h_rows 5
  have hrow6 := h_rows 6
  have hrow7 := h_rows 7
  have htr0 := h_trans 0
  have htr1 := h_trans 1
  have htr2 := h_trans 2
  have htr3 := h_trans 3
  have htr4 := h_trans 4
  have htr5 := h_trans 5
  have htr6 := h_trans 6
  obtain ⟨a0, b0, hAagg0, hBagg0, hXor0⟩ := nibbleXor_eq_digits (rows 0).a_bits (rows 0).b_bits
    hrow0.2.1 hrow0.2.2.1
  obtain ⟨a1, b1, hAagg1, hBagg1, hXor1⟩ := nibbleXor_eq_digits (rows 1).a_bits (rows 1).b_bits
    hrow1.2.1 hrow1.2.2.1
  obtain ⟨a2, b2, hAagg2, hBagg2, hXor2⟩ := nibbleXor_eq_digits (rows 2).a_bits (rows 2).b_bits
    hrow2.2.1 hrow2.2.2.1
  obtain ⟨a3, b3, hAagg3, hBagg3, hXor3⟩ := nibbleXor_eq_digits (rows 3).a_bits (rows 3).b_bits
    hrow3.2.1 hrow3.2.2.1
  obtain ⟨a4, b4, hAagg4, hBagg4, hXor4⟩ := nibbleXor_eq_digits (rows 4).a_bits (rows 4).b_bits
    hrow4.2.1 hrow4.2.2.1
  obtain ⟨a5, b5, hAagg5, hBagg5, hXor5⟩ := nibbleXor_eq_digits (rows 5).a_bits (rows 5).b_bits
    hrow5.2.1 hrow5.2.2.1
  obtain ⟨a6, b6, hAagg6, hBagg6, hXor6⟩ := nibbleXor_eq_digits (rows 6).a_bits (rows 6).b_bits
    hrow6.2.1 hrow6.2.2.1
  obtain ⟨a7, b7, hAagg7, hBagg7, hXor7⟩ := nibbleXor_eq_digits (rows 7).a_bits (rows 7).b_bits
    hrow7.2.1 hrow7.2.2.1
  have hflag1 : (rows 1).op_flag = 1 := by simpa [h_flag] using htr0.1.symm
  have hflag2 : (rows 2).op_flag = 1 := by simpa [hflag1] using htr1.1.symm
  have hflag3 : (rows 3).op_flag = 1 := by simpa [hflag2] using htr2.1.symm
  have hflag4 : (rows 4).op_flag = 1 := by simpa [hflag3] using htr3.1.symm
  have hflag5 : (rows 5).op_flag = 1 := by simpa [hflag4] using htr4.1.symm
  have hflag6 : (rows 6).op_flag = 1 := by simpa [hflag5] using htr5.1.symm
  have hflag7 : (rows 7).op_flag = 1 := by simpa [hflag6] using htr6.1.symm
  have hA0 : (rows 0).a = Felt.ofNat a0.val := by
    calc
      (rows 0).a = aggregateNibble (rows 0).a_bits := h_first.1
      _ = Felt.ofNat a0.val := hAagg0
  have hB0 : (rows 0).b = Felt.ofNat b0.val := by
    calc
      (rows 0).b = aggregateNibble (rows 0).b_bits := h_first.2.1
      _ = Felt.ofNat b0.val := hBagg0
  have hZp0 : (rows 0).zp = Felt.ofNat 0 := by simpa using h_first.2.2
  have hZ0 : (rows 0).z = Felt.ofNat (xorDigit a0 b0).val := by
    simpa [xorDigit] using output_xor_eq hrow0 h_flag hXor0 hZp0
  have hA1 : (rows 1).a = Felt.ofNat (a0.val * 16 + a1.val) :=
    next_input_a_eq htr0 hA0 hAagg1
  have hB1 : (rows 1).b = Felt.ofNat (b0.val * 16 + b1.val) :=
    next_input_b_eq htr0 hB0 hBagg1
  have hZp1 : (rows 1).zp = Felt.ofNat (xorDigit a0 b0).val :=
    next_zp_eq htr0 hZ0
  have hZ1 : (rows 1).z = Felt.ofNat ((xorDigit a0 b0).val * 16 + (xorDigit a1 b1).val) := by
    simpa [xorDigit] using output_xor_eq hrow1 hflag1 hXor1 hZp1
  have hA2 : (rows 2).a = Felt.ofNat ((a0.val * 16 + a1.val) * 16 + a2.val) :=
    next_input_a_eq htr1 hA1 hAagg2
  have hB2 : (rows 2).b = Felt.ofNat ((b0.val * 16 + b1.val) * 16 + b2.val) :=
    next_input_b_eq htr1 hB1 hBagg2
  have hZp2 : (rows 2).zp = Felt.ofNat ((xorDigit a0 b0).val * 16 + (xorDigit a1 b1).val) :=
    next_zp_eq htr1 hZ1
  have hZ2 : (rows 2).z = Felt.ofNat (((xorDigit a0 b0).val * 16 + (xorDigit a1 b1).val) * 16 +
      (xorDigit a2 b2).val) := by
    simpa [xorDigit] using output_xor_eq hrow2 hflag2 hXor2 hZp2
  have hA3 : (rows 3).a = Felt.ofNat (((a0.val * 16 + a1.val) * 16 + a2.val) * 16 + a3.val) :=
    next_input_a_eq htr2 hA2 hAagg3
  have hB3 : (rows 3).b = Felt.ofNat (((b0.val * 16 + b1.val) * 16 + b2.val) * 16 + b3.val) :=
    next_input_b_eq htr2 hB2 hBagg3
  have hZp3 :
      (rows 3).zp = Felt.ofNat ((((xorDigit a0 b0).val * 16 + (xorDigit a1 b1).val) * 16 +
        (xorDigit a2 b2).val)) :=
    next_zp_eq htr2 hZ2
  have hZ3 : (rows 3).z = Felt.ofNat ((((xorDigit a0 b0).val * 16 + (xorDigit a1 b1).val) * 16 +
      (xorDigit a2 b2).val) * 16 + (xorDigit a3 b3).val) := by
    simpa [xorDigit] using output_xor_eq hrow3 hflag3 hXor3 hZp3
  have hA4 : (rows 4).a = Felt.ofNat ((((a0.val * 16 + a1.val) * 16 + a2.val) * 16 + a3.val) * 16 +
      a4.val) := next_input_a_eq htr3 hA3 hAagg4
  have hB4 : (rows 4).b = Felt.ofNat ((((b0.val * 16 + b1.val) * 16 + b2.val) * 16 + b3.val) * 16 +
      b4.val) := next_input_b_eq htr3 hB3 hBagg4
  have hZp4 :
      (rows 4).zp = Felt.ofNat (((((xorDigit a0 b0).val * 16 + (xorDigit a1 b1).val) * 16 +
        (xorDigit a2 b2).val) * 16 + (xorDigit a3 b3).val)) :=
    next_zp_eq htr3 hZ3
  have hZ4 : (rows 4).z = Felt.ofNat (((((xorDigit a0 b0).val * 16 + (xorDigit a1 b1).val) * 16 +
      (xorDigit a2 b2).val) * 16 + (xorDigit a3 b3).val) * 16 + (xorDigit a4 b4).val) := by
    simpa [xorDigit] using output_xor_eq hrow4 hflag4 hXor4 hZp4
  have hA5 : (rows 5).a = Felt.ofNat (((((a0.val * 16 + a1.val) * 16 + a2.val) * 16 + a3.val) * 16 +
      a4.val) * 16 + a5.val) := next_input_a_eq htr4 hA4 hAagg5
  have hB5 : (rows 5).b = Felt.ofNat (((((b0.val * 16 + b1.val) * 16 + b2.val) * 16 + b3.val) * 16 +
      b4.val) * 16 + b5.val) := next_input_b_eq htr4 hB4 hBagg5
  have hZp5 :
      (rows 5).zp = Felt.ofNat ((((((xorDigit a0 b0).val * 16 + (xorDigit a1 b1).val) * 16 +
        (xorDigit a2 b2).val) * 16 + (xorDigit a3 b3).val) * 16 + (xorDigit a4 b4).val)) :=
    next_zp_eq htr4 hZ4
  have hZ5 : (rows 5).z = Felt.ofNat ((((((xorDigit a0 b0).val * 16 + (xorDigit a1 b1).val) * 16 +
      (xorDigit a2 b2).val) * 16 + (xorDigit a3 b3).val) * 16 + (xorDigit a4 b4).val) * 16 +
      (xorDigit a5 b5).val) := by
    simpa [xorDigit] using output_xor_eq hrow5 hflag5 hXor5 hZp5
  have hA6 : (rows 6).a = Felt.ofNat ((((((a0.val * 16 + a1.val) * 16 + a2.val) * 16 + a3.val) * 16 +
      a4.val) * 16 + a5.val) * 16 + a6.val) := next_input_a_eq htr5 hA5 hAagg6
  have hB6 : (rows 6).b = Felt.ofNat ((((((b0.val * 16 + b1.val) * 16 + b2.val) * 16 + b3.val) * 16 +
      b4.val) * 16 + b5.val) * 16 + b6.val) := next_input_b_eq htr5 hB5 hBagg6
  have hZp6 :
      (rows 6).zp = Felt.ofNat (((((((xorDigit a0 b0).val * 16 + (xorDigit a1 b1).val) * 16 +
        (xorDigit a2 b2).val) * 16 + (xorDigit a3 b3).val) * 16 + (xorDigit a4 b4).val) * 16 +
        (xorDigit a5 b5).val)) := next_zp_eq htr5 hZ5
  have hZ6 : (rows 6).z = Felt.ofNat (((((((xorDigit a0 b0).val * 16 + (xorDigit a1 b1).val) * 16 +
      (xorDigit a2 b2).val) * 16 + (xorDigit a3 b3).val) * 16 + (xorDigit a4 b4).val) * 16 +
      (xorDigit a5 b5).val) * 16 + (xorDigit a6 b6).val) := by
    simpa [xorDigit] using output_xor_eq hrow6 hflag6 hXor6 hZp6
  have hA7 : (rows 7).a = Felt.ofNat (digitsValue a0 a1 a2 a3 a4 a5 a6 a7) := by
    simpa [digitsValue, extendDigits] using next_input_a_eq htr6 hA6 hAagg7
  have hB7 : (rows 7).b = Felt.ofNat (digitsValue b0 b1 b2 b3 b4 b5 b6 b7) := by
    simpa [digitsValue, extendDigits] using next_input_b_eq htr6 hB6 hBagg7
  have hZp7 :
      (rows 7).zp = Felt.ofNat ((((((((xorDigit a0 b0).val * 16 + (xorDigit a1 b1).val) * 16 +
        (xorDigit a2 b2).val) * 16 + (xorDigit a3 b3).val) * 16 + (xorDigit a4 b4).val) * 16 +
        (xorDigit a5 b5).val) * 16 + (xorDigit a6 b6).val)) := next_zp_eq htr6 hZ6
  have hZ7 : (rows 7).z = Felt.ofNat (digitsValue
      (xorDigit a0 b0) (xorDigit a1 b1) (xorDigit a2 b2) (xorDigit a3 b3)
      (xorDigit a4 b4) (xorDigit a5 b5) (xorDigit a6 b6) (xorDigit a7 b7)) := by
    simpa [digitsValue, extendDigits, xorDigit] using output_xor_eq hrow7 hflag7 hXor7 hZp7
  have hA7u32 : (rows 7).a.IsU32 := by
    rw [hA7]
    unfold Felt.IsU32
    rw [felt_ofNat_val_lt _ (u32_val_lt_prime _ (digitsValue_lt_u32 _ _ _ _ _ _ _ _))]
    exact digitsValue_lt_u32 _ _ _ _ _ _ _ _
  have hB7u32 : (rows 7).b.IsU32 := by
    rw [hB7]
    unfold Felt.IsU32
    rw [felt_ofNat_val_lt _ (u32_val_lt_prime _ (digitsValue_lt_u32 _ _ _ _ _ _ _ _))]
    exact digitsValue_lt_u32 _ _ _ _ _ _ _ _
  have hA7val :
      (rows 7).a.val = digitsValue a0 a1 a2 a3 a4 a5 a6 a7 := by
    rw [hA7, felt_ofNat_val_lt _ (u32_val_lt_prime _ (digitsValue_lt_u32 _ _ _ _ _ _ _ _))]
  have hB7val :
      (rows 7).b.val = digitsValue b0 b1 b2 b3 b4 b5 b6 b7 := by
    rw [hB7, felt_ofNat_val_lt _ (u32_val_lt_prime _ (digitsValue_lt_u32 _ _ _ _ _ _ _ _))]
  refine ⟨hA7u32, hB7u32, ?_⟩
  rw [hZ7, hA7val, hB7val, digitsValue_xor]

/-- Helper-level acceptance relation for a concrete lowered `u32and` bitwise
cycle. The last row is the verifier-visible IO boundary. -/
def andCycleAccepts (x y out : Felt) : Prop :=
  ∃ rows : Fin 8 → BitwiseRow,
    air_bitwise_full_cycle rows ∧
    (rows 0).op_flag = 0 ∧
    (rows 7).a = x ∧
    (rows 7).b = y ∧
    (rows 7).z = out

/-- Helper-level acceptance relation for a concrete lowered `u32xor` bitwise
cycle. The last row is the verifier-visible IO boundary. -/
def xorCycleAccepts (x y out : Felt) : Prop :=
  ∃ rows : Fin 8 → BitwiseRow,
    air_bitwise_full_cycle rows ∧
    (rows 0).op_flag = 1 ∧
    (rows 7).a = x ∧
    (rows 7).b = y ∧
    (rows 7).z = out

/-- Any accepted lowered `u32and` cycle enforces `u32` inputs and the correct
bitwise-AND output. -/
theorem andCycleAccepts_sound
    {x y out : Felt} (hacc : andCycleAccepts x y out) :
    x.IsU32 ∧ y.IsU32 ∧ out = Felt.ofNat (x.val &&& y.val) := by
  rcases hacc with ⟨rows, hcycle, hflag, hx, hy, hout⟩
  rcases bitwise_cycle_and_sound rows hcycle hflag with ⟨ha, hb, hz⟩
  rw [← hx, ← hy, ← hout]
  exact ⟨ha, hb, hz⟩

/-- Any accepted lowered `u32xor` cycle enforces `u32` inputs and the correct
bitwise-XOR output. -/
theorem xorCycleAccepts_sound
    {x y out : Felt} (hacc : xorCycleAccepts x y out) :
    x.IsU32 ∧ y.IsU32 ∧ out = Felt.ofNat (x.val ^^^ y.val) := by
  rcases hacc with ⟨rows, hcycle, hflag, hx, hy, hout⟩
  rcases bitwise_cycle_xor_sound rows hcycle hflag with ⟨ha, hb, hz⟩
  rw [← hx, ← hy, ← hout]
  exact ⟨ha, hb, hz⟩

end MidenLean.AIR.Proofs
