import MidenLean.Proofs.U256.Common
import MidenLean.Proofs.U256.Mulstep4
import Mathlib.Tactic.Ring

set_option exponentiation.threshold 512

namespace MidenLean.Proofs

open MidenLean

-- ============================================================================
-- Section 1: Carry-chain telescopes
-- ============================================================================
-- These lemmas show that if c_i * 2^32 + l_i = q_i + c_{i-1} + d_i for each step,
-- then the weighted sum of l_i (plus the final carry) equals the sum of q_i plus d_i.

theorem carry_chain_with_acc_8
    (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ : Nat)
    (l₀ l₁ l₂ l₃ l₄ l₅ l₆ l₇ : Nat)
    (q₀ q₁ q₂ q₃ q₄ q₅ q₆ q₇ : Nat)
    (d₀ d₁ d₂ d₃ d₄ d₅ d₆ d₇ : Nat)
    (h₀ : c₀ * 2^32 + l₀ = q₀ + 0 + d₀)
    (h₁ : c₁ * 2^32 + l₁ = q₁ + c₀ + d₁)
    (h₂ : c₂ * 2^32 + l₂ = q₂ + c₁ + d₂)
    (h₃ : c₃ * 2^32 + l₃ = q₃ + c₂ + d₃)
    (h₄ : c₄ * 2^32 + l₄ = q₄ + c₃ + d₄)
    (h₅ : c₅ * 2^32 + l₅ = q₅ + c₄ + d₅)
    (h₆ : c₆ * 2^32 + l₆ = q₆ + c₅ + d₆)
    (h₇ : c₇ * 2^32 + l₇ = q₇ + c₆ + d₇) :
    c₇ * 2^256 + l₇ * 2^224 + l₆ * 2^192 + l₅ * 2^160 + l₄ * 2^128 +
    l₃ * 2^96 + l₂ * 2^64 + l₁ * 2^32 + l₀ =
    q₇ * 2^224 + q₆ * 2^192 + q₅ * 2^160 + q₄ * 2^128 +
    q₃ * 2^96 + q₂ * 2^64 + q₁ * 2^32 + q₀ +
    d₇ * 2^224 + d₆ * 2^192 + d₅ * 2^160 + d₄ * 2^128 +
    d₃ * 2^96 + d₂ * 2^64 + d₁ * 2^32 + d₀ := by omega

-- ============================================================================
-- Section 1b: Carry-chain telescopes with nonzero carry-in
-- ============================================================================
-- These are the same pattern but the first step has carry-in c_prev instead of 0.
-- Used for rounds 1-7 where the accumulator chain starts with a previous carry.

theorem carry_chain_with_cin_2
    (c₀ c₁ : Nat) (l₀ l₁ : Nat) (q₀ q₁ : Nat) (d₀ d₁ : Nat) (cin : Nat)
    (h₀ : c₀ * 2^32 + l₀ = q₀ + cin + d₀)
    (h₁ : c₁ * 2^32 + l₁ = q₁ + c₀ + d₁) :
    c₁ * 2^64 + l₁ * 2^32 + l₀ =
    q₁ * 2^32 + q₀ + cin + d₁ * 2^32 + d₀ := by omega

theorem carry_chain_with_cin_3
    (c₀ c₁ c₂ : Nat)
    (l₀ l₁ l₂ : Nat)
    (q₀ q₁ q₂ : Nat)
    (d₀ d₁ d₂ : Nat) (cin : Nat)
    (h₀ : c₀ * 2^32 + l₀ = q₀ + cin + d₀)
    (h₁ : c₁ * 2^32 + l₁ = q₁ + c₀ + d₁)
    (h₂ : c₂ * 2^32 + l₂ = q₂ + c₁ + d₂) :
    c₂ * 2^96 + l₂ * 2^64 + l₁ * 2^32 + l₀ =
    q₂ * 2^64 + q₁ * 2^32 + q₀ + cin +
    d₂ * 2^64 + d₁ * 2^32 + d₀ := by omega

theorem carry_chain_with_cin_4
    (c₀ c₁ c₂ c₃ : Nat)
    (l₀ l₁ l₂ l₃ : Nat)
    (q₀ q₁ q₂ q₃ : Nat)
    (d₀ d₁ d₂ d₃ : Nat) (cin : Nat)
    (h₀ : c₀ * 2^32 + l₀ = q₀ + cin + d₀)
    (h₁ : c₁ * 2^32 + l₁ = q₁ + c₀ + d₁)
    (h₂ : c₂ * 2^32 + l₂ = q₂ + c₁ + d₂)
    (h₃ : c₃ * 2^32 + l₃ = q₃ + c₂ + d₃) :
    c₃ * 2^128 + l₃ * 2^96 + l₂ * 2^64 + l₁ * 2^32 + l₀ =
    q₃ * 2^96 + q₂ * 2^64 + q₁ * 2^32 + q₀ + cin +
    d₃ * 2^96 + d₂ * 2^64 + d₁ * 2^32 + d₀ := by omega

theorem carry_chain_with_cin_5
    (c₀ c₁ c₂ c₃ c₄ : Nat)
    (l₀ l₁ l₂ l₃ l₄ : Nat)
    (q₀ q₁ q₂ q₃ q₄ : Nat)
    (d₀ d₁ d₂ d₃ d₄ : Nat) (cin : Nat)
    (h₀ : c₀ * 2^32 + l₀ = q₀ + cin + d₀)
    (h₁ : c₁ * 2^32 + l₁ = q₁ + c₀ + d₁)
    (h₂ : c₂ * 2^32 + l₂ = q₂ + c₁ + d₂)
    (h₃ : c₃ * 2^32 + l₃ = q₃ + c₂ + d₃)
    (h₄ : c₄ * 2^32 + l₄ = q₄ + c₃ + d₄) :
    c₄ * 2^160 + l₄ * 2^128 + l₃ * 2^96 + l₂ * 2^64 + l₁ * 2^32 + l₀ =
    q₄ * 2^128 + q₃ * 2^96 + q₂ * 2^64 + q₁ * 2^32 + q₀ + cin +
    d₄ * 2^128 + d₃ * 2^96 + d₂ * 2^64 + d₁ * 2^32 + d₀ := by omega

theorem carry_chain_with_cin_6
    (c₀ c₁ c₂ c₃ c₄ c₅ : Nat)
    (l₀ l₁ l₂ l₃ l₄ l₅ : Nat)
    (q₀ q₁ q₂ q₃ q₄ q₅ : Nat)
    (d₀ d₁ d₂ d₃ d₄ d₅ : Nat) (cin : Nat)
    (h₀ : c₀ * 2^32 + l₀ = q₀ + cin + d₀)
    (h₁ : c₁ * 2^32 + l₁ = q₁ + c₀ + d₁)
    (h₂ : c₂ * 2^32 + l₂ = q₂ + c₁ + d₂)
    (h₃ : c₃ * 2^32 + l₃ = q₃ + c₂ + d₃)
    (h₄ : c₄ * 2^32 + l₄ = q₄ + c₃ + d₄)
    (h₅ : c₅ * 2^32 + l₅ = q₅ + c₄ + d₅) :
    c₅ * 2^192 + l₅ * 2^160 + l₄ * 2^128 +
    l₃ * 2^96 + l₂ * 2^64 + l₁ * 2^32 + l₀ =
    q₅ * 2^160 + q₄ * 2^128 + q₃ * 2^96 + q₂ * 2^64 + q₁ * 2^32 + q₀ + cin +
    d₅ * 2^160 + d₄ * 2^128 + d₃ * 2^96 + d₂ * 2^64 + d₁ * 2^32 + d₀ := by
  omega

theorem carry_chain_with_cin_7
    (c₀ c₁ c₂ c₃ c₄ c₅ c₆ : Nat)
    (l₀ l₁ l₂ l₃ l₄ l₅ l₆ : Nat)
    (q₀ q₁ q₂ q₃ q₄ q₅ q₆ : Nat)
    (d₀ d₁ d₂ d₃ d₄ d₅ d₆ : Nat) (cin : Nat)
    (h₀ : c₀ * 2^32 + l₀ = q₀ + cin + d₀)
    (h₁ : c₁ * 2^32 + l₁ = q₁ + c₀ + d₁)
    (h₂ : c₂ * 2^32 + l₂ = q₂ + c₁ + d₂)
    (h₃ : c₃ * 2^32 + l₃ = q₃ + c₂ + d₃)
    (h₄ : c₄ * 2^32 + l₄ = q₄ + c₃ + d₄)
    (h₅ : c₅ * 2^32 + l₅ = q₅ + c₄ + d₅)
    (h₆ : c₆ * 2^32 + l₆ = q₆ + c₅ + d₆) :
    c₆ * 2^224 + l₆ * 2^192 + l₅ * 2^160 + l₄ * 2^128 +
    l₃ * 2^96 + l₂ * 2^64 + l₁ * 2^32 + l₀ =
    q₆ * 2^192 + q₅ * 2^160 + q₄ * 2^128 +
    q₃ * 2^96 + q₂ * 2^64 + q₁ * 2^32 + q₀ + cin +
    d₆ * 2^192 + d₅ * 2^160 + d₄ * 2^128 +
    d₃ * 2^96 + d₂ * 2^64 + d₁ * 2^32 + d₀ := by omega

-- ============================================================================
-- Section 2: Per-round value theorems
-- ============================================================================
-- Each round r computes b_r * (a_{7-r} * 2^{32*(7-r)} + ... + a_0), with a
-- carry chain. Round 0 has zero accumulators and zero carry-in. Rounds 1-7
-- have accumulators from the previous round's lo values and carry-in from the
-- previous round's final carry.

set_option maxHeartbeats 400000 in
/-- Round 0: b₀ * A, 8 steps, zero accumulators, zero carry-in.
    The carry chain telescopes to: final_carry * 2^256 + Sigma l_i * 2^(32i) = b₀ * A. -/
theorem round0_val (c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇ l₀ l₁ l₂ l₃ l₄ l₅ l₆ l₇ : Nat)
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₀ : Nat)
    (h₀ : c₀ * 2^32 + l₀ = b₀ * a₀ + 0 + 0)
    (h₁ : c₁ * 2^32 + l₁ = b₀ * a₁ + c₀ + 0)
    (h₂ : c₂ * 2^32 + l₂ = b₀ * a₂ + c₁ + 0)
    (h₃ : c₃ * 2^32 + l₃ = b₀ * a₃ + c₂ + 0)
    (h₄ : c₄ * 2^32 + l₄ = b₀ * a₄ + c₃ + 0)
    (h₅ : c₅ * 2^32 + l₅ = b₀ * a₅ + c₄ + 0)
    (h₆ : c₆ * 2^32 + l₆ = b₀ * a₆ + c₅ + 0)
    (h₇ : c₇ * 2^32 + l₇ = b₀ * a₇ + c₆ + 0) :
    c₇ * 2^256 + l₇ * 2^224 + l₆ * 2^192 + l₅ * 2^160 + l₄ * 2^128 +
    l₃ * 2^96 + l₂ * 2^64 + l₁ * 2^32 + l₀ =
    b₀ * (a₇ * 2^224 + a₆ * 2^192 + a₅ * 2^160 + a₄ * 2^128 +
          a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀) := by
  have hchain := carry_chain_with_acc_8 c₀ c₁ c₂ c₃ c₄ c₅ c₆ c₇
    l₀ l₁ l₂ l₃ l₄ l₅ l₆ l₇
    (b₀ * a₀) (b₀ * a₁) (b₀ * a₂) (b₀ * a₃)
    (b₀ * a₄) (b₀ * a₅) (b₀ * a₆) (b₀ * a₇)
    0 0 0 0 0 0 0 0
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  rw [hchain]; ring

set_option maxHeartbeats 400000 in
/-- Round 1: b₁ * A[0..6], 7 steps, accumulators = prev lo[1..7], carry-in from round 0. -/
theorem round1_val
    (c₀ c₁ c₂ c₃ c₄ c₅ c₆ l₀ l₁ l₂ l₃ l₄ l₅ l₆ : Nat)
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ b₁ : Nat)
    (d₀ d₁ d₂ d₃ d₄ d₅ d₆ : Nat) (cin : Nat)
    (h₀ : c₀ * 2^32 + l₀ = b₁ * a₀ + cin + d₀)
    (h₁ : c₁ * 2^32 + l₁ = b₁ * a₁ + c₀ + d₁)
    (h₂ : c₂ * 2^32 + l₂ = b₁ * a₂ + c₁ + d₂)
    (h₃ : c₃ * 2^32 + l₃ = b₁ * a₃ + c₂ + d₃)
    (h₄ : c₄ * 2^32 + l₄ = b₁ * a₄ + c₃ + d₄)
    (h₅ : c₅ * 2^32 + l₅ = b₁ * a₅ + c₄ + d₅)
    (h₆ : c₆ * 2^32 + l₆ = b₁ * a₆ + c₅ + d₆) :
    c₆ * 2^224 + l₆ * 2^192 + l₅ * 2^160 + l₄ * 2^128 +
    l₃ * 2^96 + l₂ * 2^64 + l₁ * 2^32 + l₀ =
    b₁ * (a₆ * 2^192 + a₅ * 2^160 + a₄ * 2^128 +
          a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀) + cin +
    d₆ * 2^192 + d₅ * 2^160 + d₄ * 2^128 +
    d₃ * 2^96 + d₂ * 2^64 + d₁ * 2^32 + d₀ := by
  have hchain := carry_chain_with_cin_7 c₀ c₁ c₂ c₃ c₄ c₅ c₆
    l₀ l₁ l₂ l₃ l₄ l₅ l₆
    (b₁ * a₀) (b₁ * a₁) (b₁ * a₂) (b₁ * a₃)
    (b₁ * a₄) (b₁ * a₅) (b₁ * a₆)
    d₀ d₁ d₂ d₃ d₄ d₅ d₆ cin
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  rw [hchain]; ring

set_option maxHeartbeats 400000 in
/-- Round 2: b₂ * A[0..5], 6 steps, with accumulators and carry-in. -/
theorem round2_val
    (c₀ c₁ c₂ c₃ c₄ c₅ l₀ l₁ l₂ l₃ l₄ l₅ : Nat)
    (a₀ a₁ a₂ a₃ a₄ a₅ b₂ : Nat)
    (d₀ d₁ d₂ d₃ d₄ d₅ : Nat) (cin : Nat)
    (h₀ : c₀ * 2^32 + l₀ = b₂ * a₀ + cin + d₀)
    (h₁ : c₁ * 2^32 + l₁ = b₂ * a₁ + c₀ + d₁)
    (h₂ : c₂ * 2^32 + l₂ = b₂ * a₂ + c₁ + d₂)
    (h₃ : c₃ * 2^32 + l₃ = b₂ * a₃ + c₂ + d₃)
    (h₄ : c₄ * 2^32 + l₄ = b₂ * a₄ + c₃ + d₄)
    (h₅ : c₅ * 2^32 + l₅ = b₂ * a₅ + c₄ + d₅) :
    c₅ * 2^192 + l₅ * 2^160 + l₄ * 2^128 +
    l₃ * 2^96 + l₂ * 2^64 + l₁ * 2^32 + l₀ =
    b₂ * (a₅ * 2^160 + a₄ * 2^128 +
          a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀) + cin +
    d₅ * 2^160 + d₄ * 2^128 + d₃ * 2^96 + d₂ * 2^64 + d₁ * 2^32 + d₀ := by
  have hchain := carry_chain_with_cin_6 c₀ c₁ c₂ c₃ c₄ c₅
    l₀ l₁ l₂ l₃ l₄ l₅
    (b₂ * a₀) (b₂ * a₁) (b₂ * a₂) (b₂ * a₃) (b₂ * a₄) (b₂ * a₅)
    d₀ d₁ d₂ d₃ d₄ d₅ cin
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [hchain]; ring

set_option maxHeartbeats 400000 in
/-- Round 3: b₃ * A[0..4], 5 steps, with accumulators and carry-in. -/
theorem round3_val
    (c₀ c₁ c₂ c₃ c₄ l₀ l₁ l₂ l₃ l₄ : Nat)
    (a₀ a₁ a₂ a₃ a₄ b₃ : Nat)
    (d₀ d₁ d₂ d₃ d₄ : Nat) (cin : Nat)
    (h₀ : c₀ * 2^32 + l₀ = b₃ * a₀ + cin + d₀)
    (h₁ : c₁ * 2^32 + l₁ = b₃ * a₁ + c₀ + d₁)
    (h₂ : c₂ * 2^32 + l₂ = b₃ * a₂ + c₁ + d₂)
    (h₃ : c₃ * 2^32 + l₃ = b₃ * a₃ + c₂ + d₃)
    (h₄ : c₄ * 2^32 + l₄ = b₃ * a₄ + c₃ + d₄) :
    c₄ * 2^160 + l₄ * 2^128 + l₃ * 2^96 + l₂ * 2^64 + l₁ * 2^32 + l₀ =
    b₃ * (a₄ * 2^128 + a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀) + cin +
    d₄ * 2^128 + d₃ * 2^96 + d₂ * 2^64 + d₁ * 2^32 + d₀ := by
  have hchain := carry_chain_with_cin_5 c₀ c₁ c₂ c₃ c₄
    l₀ l₁ l₂ l₃ l₄
    (b₃ * a₀) (b₃ * a₁) (b₃ * a₂) (b₃ * a₃) (b₃ * a₄)
    d₀ d₁ d₂ d₃ d₄ cin
    (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [hchain]; ring

set_option maxHeartbeats 400000 in
/-- Round 4: b₄ * A[0..3], 4 steps, with accumulators and carry-in. -/
theorem round4_val
    (c₀ c₁ c₂ c₃ l₀ l₁ l₂ l₃ : Nat)
    (a₀ a₁ a₂ a₃ b₄ : Nat)
    (d₀ d₁ d₂ d₃ : Nat) (cin : Nat)
    (h₀ : c₀ * 2^32 + l₀ = b₄ * a₀ + cin + d₀)
    (h₁ : c₁ * 2^32 + l₁ = b₄ * a₁ + c₀ + d₁)
    (h₂ : c₂ * 2^32 + l₂ = b₄ * a₂ + c₁ + d₂)
    (h₃ : c₃ * 2^32 + l₃ = b₄ * a₃ + c₂ + d₃) :
    c₃ * 2^128 + l₃ * 2^96 + l₂ * 2^64 + l₁ * 2^32 + l₀ =
    b₄ * (a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀) + cin +
    d₃ * 2^96 + d₂ * 2^64 + d₁ * 2^32 + d₀ := by
  have hchain := carry_chain_with_cin_4 c₀ c₁ c₂ c₃
    l₀ l₁ l₂ l₃
    (b₄ * a₀) (b₄ * a₁) (b₄ * a₂) (b₄ * a₃)
    d₀ d₁ d₂ d₃ cin
    (by omega) (by omega) (by omega) (by omega)
  rw [hchain]; ring

set_option maxHeartbeats 400000 in
/-- Round 5: b₅ * A[0..2], 3 steps, with accumulators and carry-in. -/
theorem round5_val
    (c₀ c₁ c₂ l₀ l₁ l₂ : Nat)
    (a₀ a₁ a₂ b₅ : Nat)
    (d₀ d₁ d₂ : Nat) (cin : Nat)
    (h₀ : c₀ * 2^32 + l₀ = b₅ * a₀ + cin + d₀)
    (h₁ : c₁ * 2^32 + l₁ = b₅ * a₁ + c₀ + d₁)
    (h₂ : c₂ * 2^32 + l₂ = b₅ * a₂ + c₁ + d₂) :
    c₂ * 2^96 + l₂ * 2^64 + l₁ * 2^32 + l₀ =
    b₅ * (a₂ * 2^64 + a₁ * 2^32 + a₀) + cin +
    d₂ * 2^64 + d₁ * 2^32 + d₀ := by
  have hchain := carry_chain_with_cin_3 c₀ c₁ c₂
    l₀ l₁ l₂
    (b₅ * a₀) (b₅ * a₁) (b₅ * a₂)
    d₀ d₁ d₂ cin
    (by omega) (by omega) (by omega)
  rw [hchain]; ring

set_option maxHeartbeats 400000 in
/-- Round 6: b₆ * A[0..1], 2 steps, with accumulators and carry-in. -/
theorem round6_val
    (c₀ c₁ l₀ l₁ : Nat)
    (a₀ a₁ b₆ : Nat)
    (d₀ d₁ : Nat) (cin : Nat)
    (h₀ : c₀ * 2^32 + l₀ = b₆ * a₀ + cin + d₀)
    (h₁ : c₁ * 2^32 + l₁ = b₆ * a₁ + c₀ + d₁) :
    c₁ * 2^64 + l₁ * 2^32 + l₀ =
    b₆ * (a₁ * 2^32 + a₀) + cin +
    d₁ * 2^32 + d₀ := by
  have hchain := carry_chain_with_cin_2 c₀ c₁
    l₀ l₁
    (b₆ * a₀) (b₆ * a₁)
    d₀ d₁ cin
    (by omega) (by omega)
  rw [hchain]; ring

/-- Round 7: b₇ * a₀, 1 step, with accumulator and carry-in. -/
theorem round7_val
    (c₀ l₀ : Nat) (a₀ b₇ : Nat) (d₀ : Nat) (cin : Nat)
    (h₀ : c₀ * 2^32 + l₀ = b₇ * a₀ + cin + d₀) :
    c₀ * 2^32 + l₀ = b₇ * a₀ + cin + d₀ := h₀

-- ============================================================================
-- Section 3: Limb extraction from a weighted sum
-- ============================================================================

/-- If `l₇ * 2^224 + ... + l₀ = N` and each `l_i < 2^32`, then each limb
    is the corresponding 32-bit slice of N. -/
theorem extract_limbs
    (l₀ l₁ l₂ l₃ l₄ l₅ l₆ l₇ N : Nat)
    (hl₀ : l₀ < 2^32) (hl₁ : l₁ < 2^32) (hl₂ : l₂ < 2^32) (hl₃ : l₃ < 2^32)
    (hl₄ : l₄ < 2^32) (hl₅ : l₅ < 2^32) (hl₆ : l₆ < 2^32) (hl₇ : l₇ < 2^32)
    (hsum : l₇ * 2^224 + l₆ * 2^192 + l₅ * 2^160 + l₄ * 2^128 +
            l₃ * 2^96 + l₂ * 2^64 + l₁ * 2^32 + l₀ = N) :
    l₀ = N % 2^32 ∧
    l₁ = (N / 2^32) % 2^32 ∧
    l₂ = (N / 2^64) % 2^32 ∧
    l₃ = (N / 2^96) % 2^32 ∧
    l₄ = (N / 2^128) % 2^32 ∧
    l₅ = (N / 2^160) % 2^32 ∧
    l₆ = (N / 2^192) % 2^32 ∧
    l₇ = (N / 2^224) % 2^32 := by omega

/-- Variant: total value less than 2^256 from limb bounds. -/
theorem limb_sum_lt_2_256
    (l₀ l₁ l₂ l₃ l₄ l₅ l₆ l₇ : Nat)
    (hl₀ : l₀ < 2^32) (hl₁ : l₁ < 2^32) (hl₂ : l₂ < 2^32) (hl₃ : l₃ < 2^32)
    (hl₄ : l₄ < 2^32) (hl₅ : l₅ < 2^32) (hl₆ : l₆ < 2^32) (hl₇ : l₇ < 2^32) :
    l₇ * 2^224 + l₆ * 2^192 + l₅ * 2^160 + l₄ * 2^128 +
    l₃ * 2^96 + l₂ * 2^64 + l₁ * 2^32 + l₀ < 2^256 := by omega

-- ============================================================================
-- Section 4: Column-sum reorganization
-- ============================================================================
-- The schoolbook product, when reduced mod 2^256, only depends on columns 0-7.
-- Columns 8-14 contribute to the overflow.

/-- The low 8 columns of a schoolbook product (mod 2^256 contribution). -/
def schoolbook_low (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇
                    b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : Nat) : Nat :=
  (a₀*b₀) +
  (a₁*b₀ + a₀*b₁) * 2^32 +
  (a₂*b₀ + a₁*b₁ + a₀*b₂) * 2^64 +
  (a₃*b₀ + a₂*b₁ + a₁*b₂ + a₀*b₃) * 2^96 +
  (a₄*b₀ + a₃*b₁ + a₂*b₂ + a₁*b₃ + a₀*b₄) * 2^128 +
  (a₅*b₀ + a₄*b₁ + a₃*b₂ + a₂*b₃ + a₁*b₄ + a₀*b₅) * 2^160 +
  (a₆*b₀ + a₅*b₁ + a₄*b₂ + a₃*b₃ + a₂*b₄ + a₁*b₅ + a₀*b₆) * 2^192 +
  (a₇*b₀ + a₆*b₁ + a₅*b₂ + a₄*b₃ + a₃*b₄ + a₂*b₅ + a₁*b₆ + a₀*b₇) * 2^224

/-- The high columns (8-14) of a schoolbook product (overflow contribution).
    Note: `a₀` and `b₀` do not appear in the high columns but are included
    for a uniform signature with `schoolbook_low`. -/
def schoolbook_high (_a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇
                     _b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : Nat) : Nat :=
  (a₇*b₁ + a₆*b₂ + a₅*b₃ + a₄*b₄ + a₃*b₅ + a₂*b₆ + a₁*b₇) * 2^256 +
  (a₇*b₂ + a₆*b₃ + a₅*b₄ + a₄*b₅ + a₃*b₆ + a₂*b₇) * 2^288 +
  (a₇*b₃ + a₆*b₄ + a₅*b₅ + a₄*b₆ + a₃*b₇) * 2^320 +
  (a₇*b₄ + a₆*b₅ + a₅*b₆ + a₄*b₇) * 2^352 +
  (a₇*b₅ + a₆*b₆ + a₅*b₇) * 2^384 +
  (a₇*b₆ + a₆*b₇) * 2^416 +
  (a₇*b₇) * 2^448

/-- The full product equals low + high. -/
theorem schoolbook_split (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇
                          b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : Nat) :
    (a₇ * 2^224 + a₆ * 2^192 + a₅ * 2^160 + a₄ * 2^128 +
     a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀) *
    (b₇ * 2^224 + b₆ * 2^192 + b₅ * 2^160 + b₄ * 2^128 +
     b₃ * 2^96 + b₂ * 2^64 + b₁ * 2^32 + b₀) =
    schoolbook_low a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ +
    schoolbook_high a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ := by
  unfold schoolbook_low schoolbook_high; ring

-- ============================================================================
-- Section 5: Row-to-column reorganization
-- ============================================================================
-- The MASM procedure computes the product row-by-row (round r = b_r * a[...]).
-- We need to reorganize from row sums to column sums.
-- Each round r produces contributions to columns r through r+7 (or fewer
-- for later rounds where r+j > 7 is dropped for mod 2^256).

set_option maxHeartbeats 1600000 in
/-- Row-to-column identity: the sum of all truncated rows exactly equals
    the `schoolbook_low` value. The wrapping multiplication procedure truncates
    each row to avoid computing cross-terms that would land in columns >= 8.
    As a result, the sum of the truncated rows precisely captures columns 0-7
    of the schoolbook product, with no overflow terms. -/
theorem row_to_column (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇
                       b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : Nat) :
    -- Row 0: b₀ * A (all 8 limbs) -- contributes to columns 0-7
    b₀ * (a₇ * 2^224 + a₆ * 2^192 + a₅ * 2^160 + a₄ * 2^128 +
          a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀) +
    -- Row 1: b₁ * A[0..6] * 2^32 -- contributes to columns 1-7
    b₁ * (a₆ * 2^192 + a₅ * 2^160 + a₄ * 2^128 +
          a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀) * 2^32 +
    -- Row 2: b₂ * A[0..5] * 2^64 -- contributes to columns 2-7
    b₂ * (a₅ * 2^160 + a₄ * 2^128 +
          a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀) * 2^64 +
    -- Row 3
    b₃ * (a₄ * 2^128 + a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀) * 2^96 +
    -- Row 4
    b₄ * (a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀) * 2^128 +
    -- Row 5
    b₅ * (a₂ * 2^64 + a₁ * 2^32 + a₀) * 2^160 +
    -- Row 6
    b₆ * (a₁ * 2^32 + a₀) * 2^192 +
    -- Row 7
    b₇ * a₀ * 2^224 =
    schoolbook_low a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ := by
  unfold schoolbook_low; ring

-- ============================================================================
-- Section 6: Final assembly theorem
-- ============================================================================

/-- The main bridge theorem: if 8 rounds of mulstep4/mulstep calls produce
    final limbs l_0..l_7 (each < 2^32) and some overflow, and the carry-chain
    hypotheses hold for each round, then
    `l_7 * 2^224 + ... + l_0 = (A * B) % 2^256`.

    This is stated abstractly in terms of the final limbs and the original
    limb values of A and B. The concrete instantiation connects to the
    MASM execution proof. -/
theorem wrapping_mul_bridge
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : Nat)
    (b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : Nat)
    (l₀ l₁ l₂ l₃ l₄ l₅ l₆ l₇ : Nat)
    (D : Nat)
    (hl₀ : l₀ < 2^32) (hl₁ : l₁ < 2^32) (hl₂ : l₂ < 2^32) (hl₃ : l₃ < 2^32)
    (hl₄ : l₄ < 2^32) (hl₅ : l₅ < 2^32) (hl₆ : l₆ < 2^32) (hl₇ : l₇ < 2^32)
    (hprod : l₇ * 2^224 + l₆ * 2^192 + l₅ * 2^160 + l₄ * 2^128 +
             l₃ * 2^96 + l₂ * 2^64 + l₁ * 2^32 + l₀ + D * 2^256 =
             (a₇ * 2^224 + a₆ * 2^192 + a₅ * 2^160 + a₄ * 2^128 +
              a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀) *
             (b₇ * 2^224 + b₆ * 2^192 + b₅ * 2^160 + b₄ * 2^128 +
              b₃ * 2^96 + b₂ * 2^64 + b₁ * 2^32 + b₀)) :
    l₇ * 2^224 + l₆ * 2^192 + l₅ * 2^160 + l₄ * 2^128 +
    l₃ * 2^96 + l₂ * 2^64 + l₁ * 2^32 + l₀ =
    ((a₇ * 2^224 + a₆ * 2^192 + a₅ * 2^160 + a₄ * 2^128 +
      a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀) *
     (b₇ * 2^224 + b₆ * 2^192 + b₅ * 2^160 + b₄ * 2^128 +
      b₃ * 2^96 + b₂ * 2^64 + b₁ * 2^32 + b₀)) % 2^256 := by
  have hlt := limb_sum_lt_2_256 l₀ l₁ l₂ l₃ l₄ l₅ l₆ l₇ hl₀ hl₁ hl₂ hl₃ hl₄ hl₅ hl₆ hl₇
  omega

-- ============================================================================
-- Section 7: Round combination (linear telescoping)
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- Linear telescoping: given 8 round equations with abstract row products,
    the accumulator terms cancel, leaving output limbs + overflow = row sums. -/
theorem combine_rounds
    (R₀ R₁ R₂ R₃ R₄ R₅ R₆ R₇ : Nat)
    -- Intermediate column values from round 0 (columns 1-7)
    (v₁₀ v₂₀ v₃₀ v₄₀ v₅₀ v₆₀ v₇₀ : Nat)
    -- Intermediate column values from round 1 (columns 2-7)
    (v₂₁ v₃₁ v₄₁ v₅₁ v₆₁ v₇₁ : Nat)
    -- Intermediate from round 2 (columns 3-7)
    (v₃₂ v₄₂ v₅₂ v₆₂ v₇₂ : Nat)
    -- Intermediate from round 3 (columns 4-7)
    (v₄₃ v₅₃ v₆₃ v₇₃ : Nat)
    -- Intermediate from round 4 (columns 5-7)
    (v₅₄ v₆₄ v₇₄ : Nat)
    -- Intermediate from round 5 (columns 6-7)
    (v₆₅ v₇₅ : Nat)
    -- Intermediate from round 6 (column 7)
    (v₇₆ : Nat)
    -- Final carries (overflow from each round)
    (cf₀ cf₁ cf₂ cf₃ cf₄ cf₅ cf₆ cf₇ : Nat)
    -- Abstract row products
    (P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ : Nat)
    -- Round 0 (8 steps, zero accumulators)
    (hr0 : cf₀ * 2^256 + v₇₀ * 2^224 + v₆₀ * 2^192 + v₅₀ * 2^160 + v₄₀ * 2^128 +
            v₃₀ * 2^96 + v₂₀ * 2^64 + v₁₀ * 2^32 + R₀ = P₀)
    -- Round 1 (7 steps, accumulators from round 0)
    (hr1 : cf₁ * 2^224 + v₇₁ * 2^192 + v₆₁ * 2^160 + v₅₁ * 2^128 +
            v₄₁ * 2^96 + v₃₁ * 2^64 + v₂₁ * 2^32 + R₁ =
            P₁ + v₇₀ * 2^192 + v₆₀ * 2^160 + v₅₀ * 2^128 + v₄₀ * 2^96 +
            v₃₀ * 2^64 + v₂₀ * 2^32 + v₁₀)
    -- Round 2 (6 steps, accumulators from round 1)
    (hr2 : cf₂ * 2^192 + v₇₂ * 2^160 + v₆₂ * 2^128 + v₅₂ * 2^96 +
            v₄₂ * 2^64 + v₃₂ * 2^32 + R₂ =
            P₂ + v₇₁ * 2^160 + v₆₁ * 2^128 + v₅₁ * 2^96 + v₄₁ * 2^64 +
            v₃₁ * 2^32 + v₂₁)
    -- Round 3 (5 steps)
    (hr3 : cf₃ * 2^160 + v₇₃ * 2^128 + v₆₃ * 2^96 + v₅₃ * 2^64 +
            v₄₃ * 2^32 + R₃ =
            P₃ + v₇₂ * 2^128 + v₆₂ * 2^96 + v₅₂ * 2^64 + v₄₂ * 2^32 + v₃₂)
    -- Round 4 (4 steps)
    (hr4 : cf₄ * 2^128 + v₇₄ * 2^96 + v₆₄ * 2^64 + v₅₄ * 2^32 + R₄ =
            P₄ + v₇₃ * 2^96 + v₆₃ * 2^64 + v₅₃ * 2^32 + v₄₃)
    -- Round 5 (3 steps)
    (hr5 : cf₅ * 2^96 + v₇₅ * 2^64 + v₆₅ * 2^32 + R₅ =
            P₅ + v₇₄ * 2^64 + v₆₄ * 2^32 + v₅₄)
    -- Round 6 (2 steps)
    (hr6 : cf₆ * 2^64 + v₇₆ * 2^32 + R₆ =
            P₆ + v₇₅ * 2^32 + v₆₅)
    -- Round 7 (1 step)
    (hr7 : cf₇ * 2^32 + R₇ = P₇ + v₇₆) :
    R₇ * 2^224 + R₆ * 2^192 + R₅ * 2^160 + R₄ * 2^128 +
    R₃ * 2^96 + R₂ * 2^64 + R₁ * 2^32 + R₀ +
    (cf₀ + cf₁ + cf₂ + cf₃ + cf₄ + cf₅ + cf₆ + cf₇) * 2^256 =
    P₀ + P₁ * 2^32 + P₂ * 2^64 + P₃ * 2^96 + P₄ * 2^128 +
    P₅ * 2^160 + P₆ * 2^192 + P₇ * 2^224 := by omega

-- ============================================================================
-- Section 8: Full chain correctness
-- ============================================================================

set_option maxHeartbeats 3200000 in
/-- Complete chain: 8 round equations with concrete row products yield
    `limb_sum + D * 2^256 = A * B`. -/
theorem chain_rounds_eq_product
    (R₀ R₁ R₂ R₃ R₄ R₅ R₆ R₇ : Nat)
    (v₁₀ v₂₀ v₃₀ v₄₀ v₅₀ v₆₀ v₇₀ : Nat)
    (v₂₁ v₃₁ v₄₁ v₅₁ v₆₁ v₇₁ : Nat)
    (v₃₂ v₄₂ v₅₂ v₆₂ v₇₂ : Nat)
    (v₄₃ v₅₃ v₆₃ v₇₃ : Nat)
    (v₅₄ v₆₄ v₇₄ : Nat)
    (v₆₅ v₇₅ : Nat)
    (v₇₆ : Nat)
    (cf₀ cf₁ cf₂ cf₃ cf₄ cf₅ cf₆ cf₇ : Nat)
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : Nat)
    (b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : Nat)
    (hr0 : cf₀ * 2^256 + v₇₀ * 2^224 + v₆₀ * 2^192 + v₅₀ * 2^160 + v₄₀ * 2^128 +
            v₃₀ * 2^96 + v₂₀ * 2^64 + v₁₀ * 2^32 + R₀ =
            b₀ * (a₇ * 2^224 + a₆ * 2^192 + a₅ * 2^160 + a₄ * 2^128 +
                   a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀))
    (hr1 : cf₁ * 2^224 + v₇₁ * 2^192 + v₆₁ * 2^160 + v₅₁ * 2^128 +
            v₄₁ * 2^96 + v₃₁ * 2^64 + v₂₁ * 2^32 + R₁ =
            b₁ * (a₆ * 2^192 + a₅ * 2^160 + a₄ * 2^128 +
                   a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀) +
            v₇₀ * 2^192 + v₆₀ * 2^160 + v₅₀ * 2^128 + v₄₀ * 2^96 +
            v₃₀ * 2^64 + v₂₀ * 2^32 + v₁₀)
    (hr2 : cf₂ * 2^192 + v₇₂ * 2^160 + v₆₂ * 2^128 + v₅₂ * 2^96 +
            v₄₂ * 2^64 + v₃₂ * 2^32 + R₂ =
            b₂ * (a₅ * 2^160 + a₄ * 2^128 + a₃ * 2^96 + a₂ * 2^64 +
                   a₁ * 2^32 + a₀) +
            v₇₁ * 2^160 + v₆₁ * 2^128 + v₅₁ * 2^96 + v₄₁ * 2^64 +
            v₃₁ * 2^32 + v₂₁)
    (hr3 : cf₃ * 2^160 + v₇₃ * 2^128 + v₆₃ * 2^96 + v₅₃ * 2^64 +
            v₄₃ * 2^32 + R₃ =
            b₃ * (a₄ * 2^128 + a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀) +
            v₇₂ * 2^128 + v₆₂ * 2^96 + v₅₂ * 2^64 + v₄₂ * 2^32 + v₃₂)
    (hr4 : cf₄ * 2^128 + v₇₄ * 2^96 + v₆₄ * 2^64 + v₅₄ * 2^32 + R₄ =
            b₄ * (a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀) +
            v₇₃ * 2^96 + v₆₃ * 2^64 + v₅₃ * 2^32 + v₄₃)
    (hr5 : cf₅ * 2^96 + v₇₅ * 2^64 + v₆₅ * 2^32 + R₅ =
            b₅ * (a₂ * 2^64 + a₁ * 2^32 + a₀) +
            v₇₄ * 2^64 + v₆₄ * 2^32 + v₅₄)
    (hr6 : cf₆ * 2^64 + v₇₆ * 2^32 + R₆ =
            b₆ * (a₁ * 2^32 + a₀) +
            v₇₅ * 2^32 + v₆₅)
    (hr7 : cf₇ * 2^32 + R₇ = b₇ * a₀ + v₇₆) :
    ∃ D, R₇ * 2^224 + R₆ * 2^192 + R₅ * 2^160 + R₄ * 2^128 +
         R₃ * 2^96 + R₂ * 2^64 + R₁ * 2^32 + R₀ + D * 2^256 =
         (a₇ * 2^224 + a₆ * 2^192 + a₅ * 2^160 + a₄ * 2^128 +
          a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀) *
         (b₇ * 2^224 + b₆ * 2^192 + b₅ * 2^160 + b₄ * 2^128 +
          b₃ * 2^96 + b₂ * 2^64 + b₁ * 2^32 + b₀) := by
  have hcomb := combine_rounds R₀ R₁ R₂ R₃ R₄ R₅ R₆ R₇
    v₁₀ v₂₀ v₃₀ v₄₀ v₅₀ v₆₀ v₇₀
    v₂₁ v₃₁ v₄₁ v₅₁ v₆₁ v₇₁
    v₃₂ v₄₂ v₅₂ v₆₂ v₇₂
    v₄₃ v₅₃ v₆₃ v₇₃
    v₅₄ v₆₄ v₇₄ v₆₅ v₇₅ v₇₆
    cf₀ cf₁ cf₂ cf₃ cf₄ cf₅ cf₆ cf₇
    (b₀ * (a₇ * 2^224 + a₆ * 2^192 + a₅ * 2^160 + a₄ * 2^128 +
            a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀))
    (b₁ * (a₆ * 2^192 + a₅ * 2^160 + a₄ * 2^128 +
            a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀))
    (b₂ * (a₅ * 2^160 + a₄ * 2^128 + a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀))
    (b₃ * (a₄ * 2^128 + a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀))
    (b₄ * (a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀))
    (b₅ * (a₂ * 2^64 + a₁ * 2^32 + a₀))
    (b₆ * (a₁ * 2^32 + a₀))
    (b₇ * a₀)
    hr0 (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) hr7
  -- hcomb: limb_sum + carries = row_sums
  -- Use row_to_column to show row_sums = schoolbook_low
  have hrow := row_to_column a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇
  -- Combine: limb_sum + cf_sum * 2^256 = schoolbook_low
  have h12 : R₇ * 2^224 + R₆ * 2^192 + R₅ * 2^160 + R₄ * 2^128 +
    R₃ * 2^96 + R₂ * 2^64 + R₁ * 2^32 + R₀ +
    (cf₀ + cf₁ + cf₂ + cf₃ + cf₄ + cf₅ + cf₆ + cf₇) * 2^256 =
    schoolbook_low a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ := by
    linarith [hcomb, hrow]
  -- Use schoolbook_split: A * B = schoolbook_low + schoolbook_high
  have hsplit := schoolbook_split a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇
  -- Factor schoolbook_high as H * 2^256
  have hsh : schoolbook_high a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ =
    ((a₇*b₁ + a₆*b₂ + a₅*b₃ + a₄*b₄ + a₃*b₅ + a₂*b₆ + a₁*b₇) +
     (a₇*b₂ + a₆*b₃ + a₅*b₄ + a₄*b₅ + a₃*b₆ + a₂*b₇) * 2^32 +
     (a₇*b₃ + a₆*b₄ + a₅*b₅ + a₄*b₆ + a₃*b₇) * 2^64 +
     (a₇*b₄ + a₆*b₅ + a₅*b₆ + a₄*b₇) * 2^96 +
     (a₇*b₅ + a₆*b₆ + a₅*b₇) * 2^128 +
     (a₇*b₆ + a₆*b₇) * 2^160 +
     (a₇*b₇) * 2^192) * 2^256 := by unfold schoolbook_high; ring
  -- D = cf_sum + schoolbook_high_nat
  set H := (a₇*b₁ + a₆*b₂ + a₅*b₃ + a₄*b₄ + a₃*b₅ + a₂*b₆ + a₁*b₇) +
     (a₇*b₂ + a₆*b₃ + a₅*b₄ + a₄*b₅ + a₃*b₆ + a₂*b₇) * 2^32 +
     (a₇*b₃ + a₆*b₄ + a₅*b₅ + a₄*b₆ + a₃*b₇) * 2^64 +
     (a₇*b₄ + a₆*b₅ + a₅*b₆ + a₄*b₇) * 2^96 +
     (a₇*b₅ + a₆*b₆ + a₅*b₇) * 2^128 +
     (a₇*b₆ + a₆*b₇) * 2^160 +
     (a₇*b₇) * 2^192 with hH_def
  rw [hsh] at hsplit
  -- hsplit : A * B = schoolbook_low ... + H * 2^256
  refine ⟨cf₀ + cf₁ + cf₂ + cf₃ + cf₄ + cf₅ + cf₆ + cf₇ + H, ?_⟩
  -- Distribute (cf_sum + H) * 2^256 = cf_sum * 2^256 + H * 2^256
  have hdist : (cf₀ + cf₁ + cf₂ + cf₃ + cf₄ + cf₅ + cf₆ + cf₇ + H) * 2^256 =
    (cf₀ + cf₁ + cf₂ + cf₃ + cf₄ + cf₅ + cf₆ + cf₇) * 2^256 + H * 2^256 := by ring
  linarith [h12, hsplit, hdist]

-- ============================================================================
-- Section 9: Per-limb Nat equalities from chain
-- ============================================================================

set_option maxHeartbeats 1600000 in
/-- From round equations to per-limb Nat equalities with the product.
    Composes `chain_rounds_eq_product`, `wrapping_mul_bridge`, and `extract_limbs`. -/
theorem chain_rounds_to_limb_eq
    (R₀ R₁ R₂ R₃ R₄ R₅ R₆ R₇ : Nat)
    (v₁₀ v₂₀ v₃₀ v₄₀ v₅₀ v₆₀ v₇₀ : Nat)
    (v₂₁ v₃₁ v₄₁ v₅₁ v₆₁ v₇₁ : Nat)
    (v₃₂ v₄₂ v₅₂ v₆₂ v₇₂ : Nat)
    (v₄₃ v₅₃ v₆₃ v₇₃ : Nat)
    (v₅₄ v₆₄ v₇₄ : Nat)
    (v₆₅ v₇₅ : Nat)
    (v₇₆ : Nat)
    (cf₀ cf₁ cf₂ cf₃ cf₄ cf₅ cf₆ cf₇ : Nat)
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : Nat)
    (b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇ : Nat)
    (hR₀ : R₀ < 2^32) (hR₁ : R₁ < 2^32) (hR₂ : R₂ < 2^32) (hR₃ : R₃ < 2^32)
    (hR₄ : R₄ < 2^32) (hR₅ : R₅ < 2^32) (hR₆ : R₆ < 2^32) (hR₇ : R₇ < 2^32)
    (hr0 : cf₀ * 2^256 + v₇₀ * 2^224 + v₆₀ * 2^192 + v₅₀ * 2^160 + v₄₀ * 2^128 +
            v₃₀ * 2^96 + v₂₀ * 2^64 + v₁₀ * 2^32 + R₀ =
            b₀ * (a₇ * 2^224 + a₆ * 2^192 + a₅ * 2^160 + a₄ * 2^128 +
                   a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀))
    (hr1 : cf₁ * 2^224 + v₇₁ * 2^192 + v₆₁ * 2^160 + v₅₁ * 2^128 +
            v₄₁ * 2^96 + v₃₁ * 2^64 + v₂₁ * 2^32 + R₁ =
            b₁ * (a₆ * 2^192 + a₅ * 2^160 + a₄ * 2^128 +
                   a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀) +
            v₇₀ * 2^192 + v₆₀ * 2^160 + v₅₀ * 2^128 + v₄₀ * 2^96 +
            v₃₀ * 2^64 + v₂₀ * 2^32 + v₁₀)
    (hr2 : cf₂ * 2^192 + v₇₂ * 2^160 + v₆₂ * 2^128 + v₅₂ * 2^96 +
            v₄₂ * 2^64 + v₃₂ * 2^32 + R₂ =
            b₂ * (a₅ * 2^160 + a₄ * 2^128 + a₃ * 2^96 + a₂ * 2^64 +
                   a₁ * 2^32 + a₀) +
            v₇₁ * 2^160 + v₆₁ * 2^128 + v₅₁ * 2^96 + v₄₁ * 2^64 +
            v₃₁ * 2^32 + v₂₁)
    (hr3 : cf₃ * 2^160 + v₇₃ * 2^128 + v₆₃ * 2^96 + v₅₃ * 2^64 +
            v₄₃ * 2^32 + R₃ =
            b₃ * (a₄ * 2^128 + a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀) +
            v₇₂ * 2^128 + v₆₂ * 2^96 + v₅₂ * 2^64 + v₄₂ * 2^32 + v₃₂)
    (hr4 : cf₄ * 2^128 + v₇₄ * 2^96 + v₆₄ * 2^64 + v₅₄ * 2^32 + R₄ =
            b₄ * (a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀) +
            v₇₃ * 2^96 + v₆₃ * 2^64 + v₅₃ * 2^32 + v₄₃)
    (hr5 : cf₅ * 2^96 + v₇₅ * 2^64 + v₆₅ * 2^32 + R₅ =
            b₅ * (a₂ * 2^64 + a₁ * 2^32 + a₀) +
            v₇₄ * 2^64 + v₆₄ * 2^32 + v₅₄)
    (hr6 : cf₆ * 2^64 + v₇₆ * 2^32 + R₆ =
            b₆ * (a₁ * 2^32 + a₀) +
            v₇₅ * 2^32 + v₆₅)
    (hr7 : cf₇ * 2^32 + R₇ = b₇ * a₀ + v₇₆) :
    let AB := (a₇ * 2^224 + a₆ * 2^192 + a₅ * 2^160 + a₄ * 2^128 +
               a₃ * 2^96 + a₂ * 2^64 + a₁ * 2^32 + a₀) *
              (b₇ * 2^224 + b₆ * 2^192 + b₅ * 2^160 + b₄ * 2^128 +
               b₃ * 2^96 + b₂ * 2^64 + b₁ * 2^32 + b₀)
    R₀ = AB % 2^32 ∧
    R₁ = (AB / 2^32) % 2^32 ∧
    R₂ = (AB / 2^64) % 2^32 ∧
    R₃ = (AB / 2^96) % 2^32 ∧
    R₄ = (AB / 2^128) % 2^32 ∧
    R₅ = (AB / 2^160) % 2^32 ∧
    R₆ = (AB / 2^192) % 2^32 ∧
    R₇ = (AB / 2^224) % 2^32 := by
  intro AB
  obtain ⟨D, hprod⟩ := chain_rounds_eq_product
    R₀ R₁ R₂ R₃ R₄ R₅ R₆ R₇
    v₁₀ v₂₀ v₃₀ v₄₀ v₅₀ v₆₀ v₇₀
    v₂₁ v₃₁ v₄₁ v₅₁ v₆₁ v₇₁
    v₃₂ v₄₂ v₅₂ v₆₂ v₇₂
    v₄₃ v₅₃ v₆₃ v₇₃ v₅₄ v₆₄ v₇₄ v₆₅ v₇₅ v₇₆
    cf₀ cf₁ cf₂ cf₃ cf₄ cf₅ cf₆ cf₇
    a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₀ b₁ b₂ b₃ b₄ b₅ b₆ b₇
    hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
  -- hprod : limb_sum + D * 2^256 = AB
  -- Direct extraction: omega can derive per-limb equalities from limb_sum + D * 2^256 = AB
  exact ⟨by omega, by omega, by omega, by omega,
         by omega, by omega, by omega, by omega⟩

-- ============================================================================
-- Section 10: Concrete wrapping_mul limb correctness
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- The wrapping_mul procedure produces the correct product limbs.
    Given two U256 values `a` and `b`, the 8 mulstepLo output limbs from the
    schoolbook long multiplication carry chains equal the limbs of `a * b`. -/
theorem wrapping_mul_limbs_correct (a b : U256) :
    -- Round 0: b.a0 × [a.a0..a.a7], zero accumulators, zero carry-in
    let c00 := mulstepCarry 0 a.a0.val b.a0.val 0
    let l00 := mulstepLo    0 a.a0.val b.a0.val 0
    let c01 := mulstepCarry c00 a.a1.val b.a0.val 0
    let l01 := mulstepLo    c00 a.a1.val b.a0.val 0
    let c02 := mulstepCarry c01 a.a2.val b.a0.val 0
    let l02 := mulstepLo    c01 a.a2.val b.a0.val 0
    let c03 := mulstepCarry c02 a.a3.val b.a0.val 0
    let l03 := mulstepLo    c02 a.a3.val b.a0.val 0
    let c04 := mulstepCarry c03 a.a4.val b.a0.val 0
    let l04 := mulstepLo    c03 a.a4.val b.a0.val 0
    let c05 := mulstepCarry c04 a.a5.val b.a0.val 0
    let l05 := mulstepLo    c04 a.a5.val b.a0.val 0
    let c06 := mulstepCarry c05 a.a6.val b.a0.val 0
    let l06 := mulstepLo    c05 a.a6.val b.a0.val 0
    let l07 := mulstepLo    c06 a.a7.val b.a0.val 0
    -- Round 1: b.a1 × [a.a0..a.a6], accumulators from round 0
    let c10 := mulstepCarry 0   a.a0.val b.a1.val l01
    let l10 := mulstepLo    0   a.a0.val b.a1.val l01
    let c11 := mulstepCarry c10 a.a1.val b.a1.val l02
    let l11 := mulstepLo    c10 a.a1.val b.a1.val l02
    let c12 := mulstepCarry c11 a.a2.val b.a1.val l03
    let l12 := mulstepLo    c11 a.a2.val b.a1.val l03
    let c13 := mulstepCarry c12 a.a3.val b.a1.val l04
    let l13 := mulstepLo    c12 a.a3.val b.a1.val l04
    let c14 := mulstepCarry c13 a.a4.val b.a1.val l05
    let l14 := mulstepLo    c13 a.a4.val b.a1.val l05
    let c15 := mulstepCarry c14 a.a5.val b.a1.val l06
    let l15 := mulstepLo    c14 a.a5.val b.a1.val l06
    let l16 := mulstepLo    c15 a.a6.val b.a1.val l07
    -- Round 2: b.a2 × [a.a0..a.a5], accumulators from round 1
    let c20 := mulstepCarry 0   a.a0.val b.a2.val l11
    let l20 := mulstepLo    0   a.a0.val b.a2.val l11
    let c21 := mulstepCarry c20 a.a1.val b.a2.val l12
    let l21 := mulstepLo    c20 a.a1.val b.a2.val l12
    let c22 := mulstepCarry c21 a.a2.val b.a2.val l13
    let l22 := mulstepLo    c21 a.a2.val b.a2.val l13
    let c23 := mulstepCarry c22 a.a3.val b.a2.val l14
    let l23 := mulstepLo    c22 a.a3.val b.a2.val l14
    let c24 := mulstepCarry c23 a.a4.val b.a2.val l15
    let l24 := mulstepLo    c23 a.a4.val b.a2.val l15
    let l25 := mulstepLo    c24 a.a5.val b.a2.val l16
    -- Round 3: b.a3 × [a.a0..a.a4], accumulators from round 2
    let c30 := mulstepCarry 0   a.a0.val b.a3.val l21
    let l30 := mulstepLo    0   a.a0.val b.a3.val l21
    let c31 := mulstepCarry c30 a.a1.val b.a3.val l22
    let l31 := mulstepLo    c30 a.a1.val b.a3.val l22
    let c32 := mulstepCarry c31 a.a2.val b.a3.val l23
    let l32 := mulstepLo    c31 a.a2.val b.a3.val l23
    let c33 := mulstepCarry c32 a.a3.val b.a3.val l24
    let l33 := mulstepLo    c32 a.a3.val b.a3.val l24
    let l34 := mulstepLo    c33 a.a4.val b.a3.val l25
    -- Round 4: b.a4 × [a.a0..a.a3], accumulators from round 3
    let c40 := mulstepCarry 0   a.a0.val b.a4.val l31
    let l40 := mulstepLo    0   a.a0.val b.a4.val l31
    let c41 := mulstepCarry c40 a.a1.val b.a4.val l32
    let l41 := mulstepLo    c40 a.a1.val b.a4.val l32
    let c42 := mulstepCarry c41 a.a2.val b.a4.val l33
    let l42 := mulstepLo    c41 a.a2.val b.a4.val l33
    let l43 := mulstepLo    c42 a.a3.val b.a4.val l34
    -- Round 5: b.a5 × [a.a0..a.a2], accumulators from round 4
    let c50 := mulstepCarry 0   a.a0.val b.a5.val l41
    let l50 := mulstepLo    0   a.a0.val b.a5.val l41
    let c51 := mulstepCarry c50 a.a1.val b.a5.val l42
    let l51 := mulstepLo    c50 a.a1.val b.a5.val l42
    let l52 := mulstepLo    c51 a.a2.val b.a5.val l43
    -- Round 6: b.a6 × [a.a0..a.a1], accumulators from round 5
    let c60 := mulstepCarry 0   a.a0.val b.a6.val l51
    let l60 := mulstepLo    0   a.a0.val b.a6.val l51
    let l61 := mulstepLo    c60 a.a1.val b.a6.val l52
    -- Round 7: b.a7 × [a.a0], accumulator from round 6
    let l70 := mulstepLo    0   a.a0.val b.a7.val l61
    -- Conclusion: output limbs equal product limbs
    l00 = (a * b).a0.val ∧
    l10 = (a * b).a1.val ∧
    l20 = (a * b).a2.val ∧
    l30 = (a * b).a3.val ∧
    l40 = (a * b).a4.val ∧
    l50 = (a * b).a5.val ∧
    l60 = (a * b).a6.val ∧
    l70 = (a * b).a7.val := by
  -- Introduce all let bindings
  intro c00 l00 c01 l01 c02 l02 c03 l03 c04 l04 c05 l05 c06 l06 l07
    c10 l10 c11 l11 c12 l12 c13 l13 c14 l14 c15 l15 l16
    c20 l20 c21 l21 c22 l22 c23 l23 c24 l24 l25
    c30 l30 c31 l31 c32 l32 c33 l33 l34
    c40 l40 c41 l41 c42 l42 l43
    c50 l50 c51 l51 l52
    c60 l60 l61 l70
  -- Define final carries (used in proof but not needed in statement)
  let c07 := mulstepCarry c06 a.a7.val b.a0.val 0
  let c16 := mulstepCarry c15 a.a6.val b.a1.val l07
  let c25 := mulstepCarry c24 a.a5.val b.a2.val l16
  let c34 := mulstepCarry c33 a.a4.val b.a3.val l25
  let c43 := mulstepCarry c42 a.a3.val b.a4.val l34
  let c52 := mulstepCarry c51 a.a2.val b.a5.val l43
  let c61 := mulstepCarry c60 a.a1.val b.a6.val l52
  let c70 := mulstepCarry 0   a.a0.val b.a7.val l61
  -- Zero-Felt properties
  have h0u : (0 : Felt).isU32 = true := by simp [Felt.isU32]
  have h0v : (0 : Felt).val = 0 := Felt.val_zero'
  -- U256 limb isU32 conditions
  have ha0u := U256.a0_isU32 a; have ha1u := U256.a1_isU32 a
  have ha2u := U256.a2_isU32 a; have ha3u := U256.a3_isU32 a
  have ha4u := U256.a4_isU32 a; have ha5u := U256.a5_isU32 a
  have ha6u := U256.a6_isU32 a; have ha7u := U256.a7_isU32 a
  have hb0u := U256.a0_isU32 b; have hb1u := U256.a1_isU32 b
  have hb2u := U256.a2_isU32 b; have hb3u := U256.a3_isU32 b
  have hb4u := U256.a4_isU32 b; have hb5u := U256.a5_isU32 b
  have hb6u := U256.a6_isU32 b; have hb7u := U256.a7_isU32 b
  -- Round 0 carry isU32 conditions (cascading)
  have hc00u := mulstep_carry_isU32 0 a.a0.val b.a0.val 0 h0u ha0u hb0u h0u
  have hc01u := mulstep_carry_isU32 c00 a.a1.val b.a0.val 0 hc00u ha1u hb0u h0u
  have hc02u := mulstep_carry_isU32 c01 a.a2.val b.a0.val 0 hc01u ha2u hb0u h0u
  have hc03u := mulstep_carry_isU32 c02 a.a3.val b.a0.val 0 hc02u ha3u hb0u h0u
  have hc04u := mulstep_carry_isU32 c03 a.a4.val b.a0.val 0 hc03u ha4u hb0u h0u
  have hc05u := mulstep_carry_isU32 c04 a.a5.val b.a0.val 0 hc04u ha5u hb0u h0u
  have hc06u := mulstep_carry_isU32 c05 a.a6.val b.a0.val 0 hc05u ha6u hb0u h0u
  -- Round 0 lo isU32 conditions
  have hl01u := mulstepLo_isU32 c00 a.a1.val b.a0.val 0
  have hl02u := mulstepLo_isU32 c01 a.a2.val b.a0.val 0
  have hl03u := mulstepLo_isU32 c02 a.a3.val b.a0.val 0
  have hl04u := mulstepLo_isU32 c03 a.a4.val b.a0.val 0
  have hl05u := mulstepLo_isU32 c04 a.a5.val b.a0.val 0
  have hl06u := mulstepLo_isU32 c05 a.a6.val b.a0.val 0
  have hl07u := mulstepLo_isU32 c06 a.a7.val b.a0.val 0
  -- Round 1 carry isU32 conditions
  have hc10u := mulstep_carry_isU32 0 a.a0.val b.a1.val l01 h0u ha0u hb1u hl01u
  have hc11u := mulstep_carry_isU32 c10 a.a1.val b.a1.val l02 hc10u ha1u hb1u hl02u
  have hc12u := mulstep_carry_isU32 c11 a.a2.val b.a1.val l03 hc11u ha2u hb1u hl03u
  have hc13u := mulstep_carry_isU32 c12 a.a3.val b.a1.val l04 hc12u ha3u hb1u hl04u
  have hc14u := mulstep_carry_isU32 c13 a.a4.val b.a1.val l05 hc13u ha4u hb1u hl05u
  have hc15u := mulstep_carry_isU32 c14 a.a5.val b.a1.val l06 hc14u ha5u hb1u hl06u
  -- Round 1 lo isU32 conditions
  have hl11u := mulstepLo_isU32 c10 a.a1.val b.a1.val l02
  have hl12u := mulstepLo_isU32 c11 a.a2.val b.a1.val l03
  have hl13u := mulstepLo_isU32 c12 a.a3.val b.a1.val l04
  have hl14u := mulstepLo_isU32 c13 a.a4.val b.a1.val l05
  have hl15u := mulstepLo_isU32 c14 a.a5.val b.a1.val l06
  have hl16u := mulstepLo_isU32 c15 a.a6.val b.a1.val l07
  -- Round 2 carry isU32 conditions
  have hc20u := mulstep_carry_isU32 0 a.a0.val b.a2.val l11 h0u ha0u hb2u hl11u
  have hc21u := mulstep_carry_isU32 c20 a.a1.val b.a2.val l12 hc20u ha1u hb2u hl12u
  have hc22u := mulstep_carry_isU32 c21 a.a2.val b.a2.val l13 hc21u ha2u hb2u hl13u
  have hc23u := mulstep_carry_isU32 c22 a.a3.val b.a2.val l14 hc22u ha3u hb2u hl14u
  have hc24u := mulstep_carry_isU32 c23 a.a4.val b.a2.val l15 hc23u ha4u hb2u hl15u
  -- Round 2 lo isU32
  have hl21u := mulstepLo_isU32 c20 a.a1.val b.a2.val l12
  have hl22u := mulstepLo_isU32 c21 a.a2.val b.a2.val l13
  have hl23u := mulstepLo_isU32 c22 a.a3.val b.a2.val l14
  have hl24u := mulstepLo_isU32 c23 a.a4.val b.a2.val l15
  have hl25u := mulstepLo_isU32 c24 a.a5.val b.a2.val l16
  -- Round 3 carry isU32 conditions
  have hc30u := mulstep_carry_isU32 0 a.a0.val b.a3.val l21 h0u ha0u hb3u hl21u
  have hc31u := mulstep_carry_isU32 c30 a.a1.val b.a3.val l22 hc30u ha1u hb3u hl22u
  have hc32u := mulstep_carry_isU32 c31 a.a2.val b.a3.val l23 hc31u ha2u hb3u hl23u
  have hc33u := mulstep_carry_isU32 c32 a.a3.val b.a3.val l24 hc32u ha3u hb3u hl24u
  -- Round 3 lo isU32
  have hl31u := mulstepLo_isU32 c30 a.a1.val b.a3.val l22
  have hl32u := mulstepLo_isU32 c31 a.a2.val b.a3.val l23
  have hl33u := mulstepLo_isU32 c32 a.a3.val b.a3.val l24
  have hl34u := mulstepLo_isU32 c33 a.a4.val b.a3.val l25
  -- Round 4 carry isU32 conditions
  have hc40u := mulstep_carry_isU32 0 a.a0.val b.a4.val l31 h0u ha0u hb4u hl31u
  have hc41u := mulstep_carry_isU32 c40 a.a1.val b.a4.val l32 hc40u ha1u hb4u hl32u
  have hc42u := mulstep_carry_isU32 c41 a.a2.val b.a4.val l33 hc41u ha2u hb4u hl33u
  -- Round 4 lo isU32
  have hl41u := mulstepLo_isU32 c40 a.a1.val b.a4.val l32
  have hl42u := mulstepLo_isU32 c41 a.a2.val b.a4.val l33
  have hl43u := mulstepLo_isU32 c42 a.a3.val b.a4.val l34
  -- Round 5 carry isU32 conditions
  have hc50u := mulstep_carry_isU32 0 a.a0.val b.a5.val l41 h0u ha0u hb5u hl41u
  have hc51u := mulstep_carry_isU32 c50 a.a1.val b.a5.val l42 hc50u ha1u hb5u hl42u
  -- Round 5 lo isU32
  have hl51u := mulstepLo_isU32 c50 a.a1.val b.a5.val l42
  have hl52u := mulstepLo_isU32 c51 a.a2.val b.a5.val l43
  -- Round 6 carry isU32 conditions
  have hc60u := mulstep_carry_isU32 0 a.a0.val b.a6.val l51 h0u ha0u hb6u hl51u
  -- Round 6 lo isU32
  have hl61u := mulstepLo_isU32 c60 a.a1.val b.a6.val l52
  -- ========================================================================
  -- Step equations from mulstep_val_sum (36 total)
  -- Each: carry.val * 2^32 + lo.val = multiplier.val * multiplicand.val + carry_in.val + acc.val
  -- ========================================================================
  -- Round 0 step equations
  have hs00 := mulstep_val_sum 0 a.a0.val b.a0.val 0 h0u ha0u hb0u h0u
  have hs01 := mulstep_val_sum c00 a.a1.val b.a0.val 0 hc00u ha1u hb0u h0u
  have hs02 := mulstep_val_sum c01 a.a2.val b.a0.val 0 hc01u ha2u hb0u h0u
  have hs03 := mulstep_val_sum c02 a.a3.val b.a0.val 0 hc02u ha3u hb0u h0u
  have hs04 := mulstep_val_sum c03 a.a4.val b.a0.val 0 hc03u ha4u hb0u h0u
  have hs05 := mulstep_val_sum c04 a.a5.val b.a0.val 0 hc04u ha5u hb0u h0u
  have hs06 := mulstep_val_sum c05 a.a6.val b.a0.val 0 hc05u ha6u hb0u h0u
  have hs07 := mulstep_val_sum c06 a.a7.val b.a0.val 0 hc06u ha7u hb0u h0u
  -- Round 1 step equations
  have hs10 := mulstep_val_sum 0   a.a0.val b.a1.val l01 h0u ha0u hb1u hl01u
  have hs11 := mulstep_val_sum c10 a.a1.val b.a1.val l02 hc10u ha1u hb1u hl02u
  have hs12 := mulstep_val_sum c11 a.a2.val b.a1.val l03 hc11u ha2u hb1u hl03u
  have hs13 := mulstep_val_sum c12 a.a3.val b.a1.val l04 hc12u ha3u hb1u hl04u
  have hs14 := mulstep_val_sum c13 a.a4.val b.a1.val l05 hc13u ha4u hb1u hl05u
  have hs15 := mulstep_val_sum c14 a.a5.val b.a1.val l06 hc14u ha5u hb1u hl06u
  have hs16 := mulstep_val_sum c15 a.a6.val b.a1.val l07 hc15u ha6u hb1u hl07u
  -- Round 2 step equations
  have hs20 := mulstep_val_sum 0   a.a0.val b.a2.val l11 h0u ha0u hb2u hl11u
  have hs21 := mulstep_val_sum c20 a.a1.val b.a2.val l12 hc20u ha1u hb2u hl12u
  have hs22 := mulstep_val_sum c21 a.a2.val b.a2.val l13 hc21u ha2u hb2u hl13u
  have hs23 := mulstep_val_sum c22 a.a3.val b.a2.val l14 hc22u ha3u hb2u hl14u
  have hs24 := mulstep_val_sum c23 a.a4.val b.a2.val l15 hc23u ha4u hb2u hl15u
  have hs25 := mulstep_val_sum c24 a.a5.val b.a2.val l16 hc24u ha5u hb2u hl16u
  -- Round 3 step equations
  have hs30 := mulstep_val_sum 0   a.a0.val b.a3.val l21 h0u ha0u hb3u hl21u
  have hs31 := mulstep_val_sum c30 a.a1.val b.a3.val l22 hc30u ha1u hb3u hl22u
  have hs32 := mulstep_val_sum c31 a.a2.val b.a3.val l23 hc31u ha2u hb3u hl23u
  have hs33 := mulstep_val_sum c32 a.a3.val b.a3.val l24 hc32u ha3u hb3u hl24u
  have hs34 := mulstep_val_sum c33 a.a4.val b.a3.val l25 hc33u ha4u hb3u hl25u
  -- Round 4 step equations
  have hs40 := mulstep_val_sum 0   a.a0.val b.a4.val l31 h0u ha0u hb4u hl31u
  have hs41 := mulstep_val_sum c40 a.a1.val b.a4.val l32 hc40u ha1u hb4u hl32u
  have hs42 := mulstep_val_sum c41 a.a2.val b.a4.val l33 hc41u ha2u hb4u hl33u
  have hs43 := mulstep_val_sum c42 a.a3.val b.a4.val l34 hc42u ha3u hb4u hl34u
  -- Round 5 step equations
  have hs50 := mulstep_val_sum 0   a.a0.val b.a5.val l41 h0u ha0u hb5u hl41u
  have hs51 := mulstep_val_sum c50 a.a1.val b.a5.val l42 hc50u ha1u hb5u hl42u
  have hs52 := mulstep_val_sum c51 a.a2.val b.a5.val l43 hc51u ha2u hb5u hl43u
  -- Round 6 step equations
  have hs60 := mulstep_val_sum 0   a.a0.val b.a6.val l51 h0u ha0u hb6u hl51u
  have hs61 := mulstep_val_sum c60 a.a1.val b.a6.val l52 hc60u ha1u hb6u hl52u
  -- Round 7 step equation
  have hs70 := mulstep_val_sum 0   a.a0.val b.a7.val l61 h0u ha0u hb7u hl61u
  -- Rewrite (0 : Felt).val = 0 in all step equations
  simp only [h0v] at hs00 hs01 hs02 hs03 hs04 hs05 hs06 hs07 hs10 hs11 hs12 hs13 hs14 hs15 hs16 hs20 hs21 hs22 hs23 hs24 hs25 hs30 hs31 hs32 hs33 hs34 hs40 hs41 hs42 hs43 hs50 hs51 hs52 hs60 hs61 hs70
  -- ========================================================================
  -- Combine step equations into round equations via round_val theorems
  -- ========================================================================
  -- Round 0: all accumulators are 0
  have hr0 := round0_val c00.val c01.val c02.val c03.val c04.val c05.val c06.val c07.val
    l00.val l01.val l02.val l03.val l04.val l05.val l06.val l07.val
    a.a0.val.val a.a1.val.val a.a2.val.val a.a3.val.val
    a.a4.val.val a.a5.val.val a.a6.val.val a.a7.val.val
    b.a0.val.val
    hs00 hs01 hs02 hs03 hs04 hs05 hs06 hs07
  -- Round 1: accumulators are l01..l07, cin = 0
  have hr1' := round1_val c10.val c11.val c12.val c13.val c14.val c15.val c16.val
    l10.val l11.val l12.val l13.val l14.val l15.val l16.val
    a.a0.val.val a.a1.val.val a.a2.val.val a.a3.val.val
    a.a4.val.val a.a5.val.val a.a6.val.val
    b.a1.val.val
    l01.val l02.val l03.val l04.val l05.val l06.val l07.val 0
    hs10 hs11 hs12 hs13 hs14 hs15 hs16
  have hr1 : c16.val * 2 ^ 224 + l16.val * 2 ^ 192 + l15.val * 2 ^ 160 +
    l14.val * 2 ^ 128 + l13.val * 2 ^ 96 + l12.val * 2 ^ 64 +
    l11.val * 2 ^ 32 + l10.val =
    b.a1.val.val * (a.a6.val.val * 2 ^ 192 + a.a5.val.val * 2 ^ 160 +
    a.a4.val.val * 2 ^ 128 + a.a3.val.val * 2 ^ 96 + a.a2.val.val * 2 ^ 64 +
    a.a1.val.val * 2 ^ 32 + a.a0.val.val) +
    l07.val * 2 ^ 192 + l06.val * 2 ^ 160 + l05.val * 2 ^ 128 +
    l04.val * 2 ^ 96 + l03.val * 2 ^ 64 + l02.val * 2 ^ 32 + l01.val := by omega
  -- Round 2: accumulators are l11..l16, cin = 0
  have hr2' := round2_val c20.val c21.val c22.val c23.val c24.val c25.val
    l20.val l21.val l22.val l23.val l24.val l25.val
    a.a0.val.val a.a1.val.val a.a2.val.val a.a3.val.val
    a.a4.val.val a.a5.val.val
    b.a2.val.val
    l11.val l12.val l13.val l14.val l15.val l16.val 0
    hs20 hs21 hs22 hs23 hs24 hs25
  have hr2 : c25.val * 2 ^ 192 + l25.val * 2 ^ 160 + l24.val * 2 ^ 128 +
    l23.val * 2 ^ 96 + l22.val * 2 ^ 64 + l21.val * 2 ^ 32 + l20.val =
    b.a2.val.val * (a.a5.val.val * 2 ^ 160 + a.a4.val.val * 2 ^ 128 +
    a.a3.val.val * 2 ^ 96 + a.a2.val.val * 2 ^ 64 + a.a1.val.val * 2 ^ 32 +
    a.a0.val.val) +
    l16.val * 2 ^ 160 + l15.val * 2 ^ 128 + l14.val * 2 ^ 96 +
    l13.val * 2 ^ 64 + l12.val * 2 ^ 32 + l11.val := by omega
  -- Round 3: accumulators are l21..l25, cin = 0
  have hr3' := round3_val c30.val c31.val c32.val c33.val c34.val
    l30.val l31.val l32.val l33.val l34.val
    a.a0.val.val a.a1.val.val a.a2.val.val a.a3.val.val a.a4.val.val
    b.a3.val.val
    l21.val l22.val l23.val l24.val l25.val 0
    hs30 hs31 hs32 hs33 hs34
  have hr3 : c34.val * 2 ^ 160 + l34.val * 2 ^ 128 + l33.val * 2 ^ 96 +
    l32.val * 2 ^ 64 + l31.val * 2 ^ 32 + l30.val =
    b.a3.val.val * (a.a4.val.val * 2 ^ 128 + a.a3.val.val * 2 ^ 96 +
    a.a2.val.val * 2 ^ 64 + a.a1.val.val * 2 ^ 32 + a.a0.val.val) +
    l25.val * 2 ^ 128 + l24.val * 2 ^ 96 + l23.val * 2 ^ 64 +
    l22.val * 2 ^ 32 + l21.val := by omega
  -- Round 4: accumulators are l31..l34, cin = 0
  have hr4' := round4_val c40.val c41.val c42.val c43.val
    l40.val l41.val l42.val l43.val
    a.a0.val.val a.a1.val.val a.a2.val.val a.a3.val.val
    b.a4.val.val
    l31.val l32.val l33.val l34.val 0
    hs40 hs41 hs42 hs43
  have hr4 : c43.val * 2 ^ 128 + l43.val * 2 ^ 96 + l42.val * 2 ^ 64 +
    l41.val * 2 ^ 32 + l40.val =
    b.a4.val.val * (a.a3.val.val * 2 ^ 96 + a.a2.val.val * 2 ^ 64 +
    a.a1.val.val * 2 ^ 32 + a.a0.val.val) +
    l34.val * 2 ^ 96 + l33.val * 2 ^ 64 + l32.val * 2 ^ 32 + l31.val := by omega
  -- Round 5: accumulators are l41..l43, cin = 0
  have hr5' := round5_val c50.val c51.val c52.val
    l50.val l51.val l52.val
    a.a0.val.val a.a1.val.val a.a2.val.val
    b.a5.val.val
    l41.val l42.val l43.val 0
    hs50 hs51 hs52
  have hr5 : c52.val * 2 ^ 96 + l52.val * 2 ^ 64 + l51.val * 2 ^ 32 + l50.val =
    b.a5.val.val * (a.a2.val.val * 2 ^ 64 + a.a1.val.val * 2 ^ 32 +
    a.a0.val.val) +
    l43.val * 2 ^ 64 + l42.val * 2 ^ 32 + l41.val := by omega
  -- Round 6: accumulators are l51..l52, cin = 0
  have hr6' := round6_val c60.val c61.val
    l60.val l61.val
    a.a0.val.val a.a1.val.val
    b.a6.val.val
    l51.val l52.val 0
    hs60 hs61
  have hr6 : c61.val * 2 ^ 64 + l61.val * 2 ^ 32 + l60.val =
    b.a6.val.val * (a.a1.val.val * 2 ^ 32 + a.a0.val.val) +
    l52.val * 2 ^ 32 + l51.val := by omega
  -- Round 7: accumulator is l61, cin = 0
  have hr7 := round7_val c70.val l70.val a.a0.val.val b.a7.val.val l61.val 0 (by omega)
  -- ========================================================================
  -- Apply chain_rounds_to_limb_eq to get per-limb Nat equalities
  -- ========================================================================
  have hlimbs := chain_rounds_to_limb_eq
    l00.val l10.val l20.val l30.val l40.val l50.val l60.val l70.val
    -- v from round 0 (columns 1-7)
    l01.val l02.val l03.val l04.val l05.val l06.val l07.val
    -- v from round 1 (columns 2-7)
    l11.val l12.val l13.val l14.val l15.val l16.val
    -- v from round 2 (columns 3-7)
    l21.val l22.val l23.val l24.val l25.val
    -- v from round 3 (columns 4-7)
    l31.val l32.val l33.val l34.val
    -- v from round 4 (columns 5-7)
    l41.val l42.val l43.val
    -- v from round 5 (columns 6-7)
    l51.val l52.val
    -- v from round 6 (column 7)
    l61.val
    -- final carries
    c07.val c16.val c25.val c34.val c43.val c52.val c61.val c70.val
    -- a limbs
    a.a0.val.val a.a1.val.val a.a2.val.val a.a3.val.val
    a.a4.val.val a.a5.val.val a.a6.val.val a.a7.val.val
    -- b limbs
    b.a0.val.val b.a1.val.val b.a2.val.val b.a3.val.val
    b.a4.val.val b.a5.val.val b.a6.val.val b.a7.val.val
    -- R_k < 2^32 (from mulstepLo_isU32)
    (by have := mulstepLo_isU32 0 a.a0.val b.a0.val 0; simp [Felt.isU32, decide_eq_true_eq] at this; exact this)
    (by have := mulstepLo_isU32 0 a.a0.val b.a1.val l01; simp [Felt.isU32, decide_eq_true_eq] at this; exact this)
    (by have := mulstepLo_isU32 0 a.a0.val b.a2.val l11; simp [Felt.isU32, decide_eq_true_eq] at this; exact this)
    (by have := mulstepLo_isU32 0 a.a0.val b.a3.val l21; simp [Felt.isU32, decide_eq_true_eq] at this; exact this)
    (by have := mulstepLo_isU32 0 a.a0.val b.a4.val l31; simp [Felt.isU32, decide_eq_true_eq] at this; exact this)
    (by have := mulstepLo_isU32 0 a.a0.val b.a5.val l41; simp [Felt.isU32, decide_eq_true_eq] at this; exact this)
    (by have := mulstepLo_isU32 0 a.a0.val b.a6.val l51; simp [Felt.isU32, decide_eq_true_eq] at this; exact this)
    (by have := mulstepLo_isU32 0 a.a0.val b.a7.val l61; simp [Felt.isU32, decide_eq_true_eq] at this; exact this)
    -- Round equations
    hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
  -- hlimbs gives us 8 Nat equalities for the product AB = a.toNat * b.toNat
  obtain ⟨heq0, heq1, heq2, heq3, heq4, heq5, heq6, heq7⟩ := hlimbs
  -- Convert Nat equalities to Felt equalities
  -- Strategy: show l_k.val = (a * b).ak.val.val, then use ZMod.val_injective
  -- (a * b).ak.val = Felt.ofNat ((a.toNat * b.toNat / 2^(32k)) % 2^32)
  -- and (Felt.ofNat m).val = m when m < GOLDILOCKS_PRIME
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> {
    apply ZMod.val_injective
    simp only [HMul.hMul, Mul.mul, U256.ofNat]
    rw [felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)]
    assumption
  }

end MidenLean.Proofs
