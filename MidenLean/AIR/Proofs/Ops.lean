import MidenLean.AIR.Constraints.Ops
/-!
# AIR Constraint Soundness Proofs: Stack Operations

Soundness proofs for all 31 operations in the `ops` constraint module:
PAD, DUP variants, MOVUP/MOVDN, CSWAP/CSWAPW, ASSERT, SDEPTH.

Each theorem proves: constraint satisfaction → correct output relationship.
-/

namespace MidenLean.AIR.Proofs.Ops

open MidenLean MidenLean.AIR MidenLean.AIR.Constraints

-- Reuse the sat1 helper from StackArith proofs
private theorem sat1 (f : Frame) (c : Constraint) :
    f.satisfies [c] ↔ c f = 0 := by
  simp [Frame.satisfies]

-- ============================================================================
-- PAD
-- ============================================================================

theorem air_pad_sound (f : Frame) (hsat : f.satisfies pad) :
    f.s' 0 = 0 := by
  rw [pad, sat1] at hsat; exact hsat

-- ============================================================================
-- DUP variants
-- ============================================================================

theorem air_dup_sound (f : Frame) (hsat : f.satisfies dup) :
    f.s' 0 = f.s 0 := by
  rw [dup, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_dup1_sound (f : Frame) (hsat : f.satisfies dup1) :
    f.s' 0 = f.s 1 := by
  rw [dup1, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_dup2_sound (f : Frame) (hsat : f.satisfies dup2) :
    f.s' 0 = f.s 2 := by
  rw [dup2, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_dup3_sound (f : Frame) (hsat : f.satisfies dup3) :
    f.s' 0 = f.s 3 := by
  rw [dup3, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_dup4_sound (f : Frame) (hsat : f.satisfies dup4) :
    f.s' 0 = f.s 4 := by
  rw [dup4, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_dup5_sound (f : Frame) (hsat : f.satisfies dup5) :
    f.s' 0 = f.s 5 := by
  rw [dup5, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_dup6_sound (f : Frame) (hsat : f.satisfies dup6) :
    f.s' 0 = f.s 6 := by
  rw [dup6, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_dup7_sound (f : Frame) (hsat : f.satisfies dup7) :
    f.s' 0 = f.s 7 := by
  rw [dup7, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_dup9_sound (f : Frame) (hsat : f.satisfies dup9) :
    f.s' 0 = f.s 9 := by
  rw [dup9, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_dup11_sound (f : Frame) (hsat : f.satisfies dup11) :
    f.s' 0 = f.s 11 := by
  rw [dup11, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_dup13_sound (f : Frame) (hsat : f.satisfies dup13) :
    f.s' 0 = f.s 13 := by
  rw [dup13, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_dup15_sound (f : Frame) (hsat : f.satisfies dup15) :
    f.s' 0 = f.s 15 := by
  rw [dup15, sat1] at hsat; exact sub_eq_zero.mp hsat

-- ============================================================================
-- MOVUP variants: s0' = s[N]
-- ============================================================================

theorem air_movup2_sound (f : Frame) (hsat : f.satisfies movup2) :
    f.s' 0 = f.s 2 := by
  rw [movup2, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_movup3_sound (f : Frame) (hsat : f.satisfies movup3) :
    f.s' 0 = f.s 3 := by
  rw [movup3, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_movup4_sound (f : Frame) (hsat : f.satisfies movup4) :
    f.s' 0 = f.s 4 := by
  rw [movup4, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_movup5_sound (f : Frame) (hsat : f.satisfies movup5) :
    f.s' 0 = f.s 5 := by
  rw [movup5, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_movup6_sound (f : Frame) (hsat : f.satisfies movup6) :
    f.s' 0 = f.s 6 := by
  rw [movup6, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_movup7_sound (f : Frame) (hsat : f.satisfies movup7) :
    f.s' 0 = f.s 7 := by
  rw [movup7, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_movup8_sound (f : Frame) (hsat : f.satisfies movup8) :
    f.s' 0 = f.s 8 := by
  rw [movup8, sat1] at hsat; exact sub_eq_zero.mp hsat

-- ============================================================================
-- MOVDN variants: s'[N] = s0
-- ============================================================================

theorem air_movdn2_sound (f : Frame) (hsat : f.satisfies movdn2) :
    f.s' 2 = f.s 0 := by
  rw [movdn2, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_movdn3_sound (f : Frame) (hsat : f.satisfies movdn3) :
    f.s' 3 = f.s 0 := by
  rw [movdn3, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_movdn4_sound (f : Frame) (hsat : f.satisfies movdn4) :
    f.s' 4 = f.s 0 := by
  rw [movdn4, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_movdn5_sound (f : Frame) (hsat : f.satisfies movdn5) :
    f.s' 5 = f.s 0 := by
  rw [movdn5, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_movdn6_sound (f : Frame) (hsat : f.satisfies movdn6) :
    f.s' 6 = f.s 0 := by
  rw [movdn6, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_movdn7_sound (f : Frame) (hsat : f.satisfies movdn7) :
    f.s' 7 = f.s 0 := by
  rw [movdn7, sat1] at hsat; exact sub_eq_zero.mp hsat

theorem air_movdn8_sound (f : Frame) (hsat : f.satisfies movdn8) :
    f.s' 8 = f.s 0 := by
  rw [movdn8, sat1] at hsat; exact sub_eq_zero.mp hsat

-- ============================================================================
-- CSWAP / CSWAPW: s0 is boolean (condition)
-- ============================================================================

private theorem sat3 (f : Frame) (c1 c2 c3 : Constraint) :
    f.satisfies [c1, c2, c3] ↔ c1 f = 0 ∧ c2 f = 0 ∧ c3 f = 0 := by
  unfold Frame.satisfies; constructor
  · intro h; exact ⟨h _ (by simp), h _ (by simp), h _ (by simp)⟩
  · intro ⟨h1, h2, h3⟩ c hc; simp at hc; rcases hc with rfl | rfl | rfl <;> assumption

private theorem sat9 (f : Frame) (c1 c2 c3 c4 c5 c6 c7 c8 c9 : Constraint) :
    f.satisfies [c1, c2, c3, c4, c5, c6, c7, c8, c9] →
    c1 f = 0 ∧ c2 f = 0 ∧ c3 f = 0 := by
  unfold Frame.satisfies; intro h
  exact ⟨h _ (by simp), h _ (by simp), h _ (by simp)⟩

theorem air_cswap_sound (f : Frame) (hsat : f.satisfies cswap) :
    f.s 0 * (f.s 0 - 1) = 0
    ∧ f.s' 0 = f.s 0 * f.s 2 + (1 - f.s 0) * f.s 1
    ∧ f.s' 1 = f.s 0 * f.s 1 + (1 - f.s 0) * f.s 2 := by
  rw [cswap, sat3] at hsat
  exact ⟨hsat.1, by linear_combination hsat.2.1, by linear_combination hsat.2.2⟩

theorem air_cswapw_sound (f : Frame) (hsat : f.satisfies cswapw) :
    f.s 0 * (f.s 0 - 1) = 0 := by
  have := sat9 f _ _ _ _ _ _ _ _ _ (by rw [cswapw] at hsat; exact hsat)
  exact this.1

-- ============================================================================
-- ASSERT: s0 must equal 1
-- ============================================================================

theorem air_assert_sound (f : Frame) (hsat : f.satisfies assert_op) :
    f.s 0 = 1 := by
  rw [assert_op, sat1] at hsat; exact sub_eq_zero.mp hsat

-- ============================================================================
-- SDEPTH: s0' = stack depth (b0)
-- ============================================================================

theorem air_sdepth_sound (f : Frame) (hsat : f.satisfies sdepth) :
    f.s' 0 = f.b0 := by
  rw [sdepth, sat1] at hsat; exact sub_eq_zero.mp hsat

end MidenLean.AIR.Proofs.Ops
