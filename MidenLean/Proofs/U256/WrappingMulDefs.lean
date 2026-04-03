import MidenLean.Proofs.U256.Common
import MidenLean.Proofs.U256.U256LeToBePair
import MidenLean.Proofs.U256.Mulstep
import MidenLean.Proofs.U256.Mulstep4
import MidenLean.Proofs.U256.WrappingMulBridge
import MidenLean.Proofs.Tactics
import MidenLean.Proofs.Helpers

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Precomputed alignment/bounds proofs
-- ============================================================================

theorem wm_align_0  : 0  % 4 = 0 := by decide
theorem wm_align_4  : 4  % 4 = 0 := by decide
theorem wm_align_8  : 8  % 4 = 0 := by decide
theorem wm_align_12 : 12 % 4 = 0 := by decide
theorem wm_align_16 : 16 % 4 = 0 := by decide
theorem wm_align_20 : 20 % 4 = 0 := by decide
theorem wm_bound_0  {n : Nat} (h : n ≥ 24) : 0  + 4 ≤ n := by omega
theorem wm_bound_4  {n : Nat} (h : n ≥ 24) : 4  + 4 ≤ n := by omega
theorem wm_bound_8  {n : Nat} (h : n ≥ 24) : 8  + 4 ≤ n := by omega
theorem wm_bound_12 {n : Nat} (h : n ≥ 24) : 12 + 4 ≤ n := by omega
theorem wm_bound_16 {n : Nat} (h : n ≥ 24) : 16 + 4 ≤ n := by omega
theorem wm_bound_20 {n : Nat} (h : n ≥ 24) : 20 + 4 ≤ n := by omega

-- ============================================================================
-- mem_simp tactic macro
-- ============================================================================

macro "mem_simp" : tactic =>
  `(tactic| (
    simp only [
      LocalFrame.localAddr_add_eq_localAddr_add_iff,
      LocalFrame.localAddr_eq_localAddr_add_iff,
      LocalFrame.localAddr_add_eq_localAddr_iff,
      LocalFrame.localAddr_eq_localAddr_iff]
    norm_num))

-- ============================================================================
-- Phase 1: Setup (LE→BE + store operands + init accumulators)
-- ============================================================================

def wm_setup : List Op := [
  .inst (.exec "u256_le_to_be_pair"),
  .inst (.locStorewBe 0),
  .inst (.dropw),
  .inst (.locStorewBe 4),
  .inst (.push 0),
  .inst (.dropw),
  .inst (.movdn 8),
  .inst (.locStorewBe 8),
  .inst (.swapw 1),
  .inst (.locStorewBe 12),
  .inst (.padw),
  .inst (.locStorewBe 16),
  .inst (.locStorewBe 20),
  .inst (.dropw),
  .inst (.swapw 1)
]

-- The rest of the body (everything after setup)
def wm_rest : List Op :=
  [.inst (.padw),
  .inst (.locLoadwBe 16),
  .inst (.movdnw 2),
  .inst (.movup 12),
  .inst (.exec "mulstep4"),
  .inst (.movdn 9),
  .inst (.movdn 9),
  .inst (.swapw 1),
  .inst (.locStorewBe 16),
  .inst (.dropw),
  .inst (.padw),
  .inst (.locLoadwBe 20),
  .inst (.swapw 1),
  .inst (.movup 9),
  .inst (.movup 9),
  .inst (.dup 1),
  .inst (.movup 6),
  .inst (.movup 10),
  .inst (.swap 3),
  .inst (.exec "mulstep"),
  .inst (.swap 1),
  .inst (.movdn 5),
  .inst (.dup 1),
  .inst (.movup 5),
  .inst (.movup 9),
  .inst (.swap 3),
  .inst (.exec "mulstep"),
  .inst (.swap 1),
  .inst (.movdn 4),
  .inst (.dup 1),
  .inst (.movup 4),
  .inst (.movup 8),
  .inst (.swap 3),
  .inst (.exec "mulstep"),
  .inst (.swap 1),
  .inst (.movdn 3),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.movup 6),
  .inst (.swap 3),
  .inst (.exec "mulstep"),
  .inst (.drop),
  .inst (.locStorewBe 20),
  .inst (.dropw),
  .inst (.padw),
  .inst (.locLoadwBe 16),
  .inst (.padw),
  .inst (.locLoadwBe 20),
  .inst (.movup 7),
  .inst (.dropw),
  .inst (.padw),
  .inst (.locLoadwBe 12),
  .inst (.padw),
  .inst (.locLoadwBe 8),
  .inst (.padw),
  .inst (.locLoadwBe 4),
  .inst (.movup 2),
  .inst (.movdn 3),
  .inst (.push 0),
  .inst (.dropw),
  .inst (.exec "mulstep4"),
  .inst (.movdn 9),
  .inst (.movdn 9),
  .inst (.swapw 1),
  .inst (.movdn 3),
  .inst (.padw),
  .inst (.locLoadwBe 16),
  .inst (.push 0),
  .inst (.dropw),
  .inst (.movdn 3),
  .inst (.locStorewBe 16),
  .inst (.dropw),
  .inst (.padw),
  .inst (.locLoadwBe 20),
  .inst (.movup 3),
  .inst (.drop),
  .inst (.swapw 1),
  .inst (.movup 9),
  .inst (.movup 9),
  .inst (.dup 1),
  .inst (.movup 6),
  .inst (.movup 9),
  .inst (.swap 3),
  .inst (.exec "mulstep"),
  .inst (.swap 1),
  .inst (.movdn 7),
  .inst (.dup 1),
  .inst (.movup 5),
  .inst (.movup 7),
  .inst (.swap 3),
  .inst (.exec "mulstep"),
  .inst (.swap 1),
  .inst (.movdn 5),
  .inst (.swap 1),
  .inst (.movup 3),
  .inst (.movup 4),
  .inst (.swap 3),
  .inst (.exec "mulstep"),
  .inst (.drop),
  .inst (.swap 1),
  .inst (.drop),
  .inst (.locStorewBe 20),
  .inst (.dropw),
  .inst (.padw),
  .inst (.locLoadwBe 16),
  .inst (.padw),
  .inst (.locLoadwBe 20),
  .inst (.movup 7),
  .inst (.movup 7),
  .inst (.dropw),
  .inst (.padw),
  .inst (.locLoadwBe 12),
  .inst (.padw),
  .inst (.locLoadwBe 8),
  .inst (.padw),
  .inst (.locLoadwBe 4),
  .inst (.swap 1),
  .inst (.movdn 3),
  .inst (.push 0),
  .inst (.dropw),
  .inst (.exec "mulstep4"),
  .inst (.movdn 9),
  .inst (.movdn 9),
  .inst (.swapw 1),
  .inst (.movdn 3),
  .inst (.movdn 3),
  .inst (.padw),
  .inst (.locLoadwBe 16),
  .inst (.drop),
  .inst (.drop),
  .inst (.movdn 3),
  .inst (.movdn 3),
  .inst (.locStorewBe 16),
  .inst (.dropw),
  .inst (.padw),
  .inst (.locLoadwBe 20),
  .inst (.movup 3),
  .inst (.movup 3),
  .inst (.drop),
  .inst (.drop),
  .inst (.swapw 1),
  .inst (.movup 9),
  .inst (.movup 9),
  .inst (.dup 1),
  .inst (.movup 6),
  .inst (.movup 8),
  .inst (.swap 3),
  .inst (.exec "mulstep"),
  .inst (.swap 1),
  .inst (.movdn 6),
  .inst (.dup 1),
  .inst (.movup 5),
  .inst (.movup 6),
  .inst (.swap 3),
  .inst (.exec "mulstep"),
  .inst (.swap 1),
  .inst (.swap 1),
  .inst (.drop),
  .inst (.movdn 3),
  .inst (.drop),
  .inst (.drop),
  .inst (.drop),
  .inst (.locStorewBe 20),
  .inst (.dropw),
  .inst (.padw),
  .inst (.locLoadwBe 16),
  .inst (.padw),
  .inst (.locLoadwBe 20),
  .inst (.movup 7),
  .inst (.movup 7),
  .inst (.movup 7),
  .inst (.dropw),
  .inst (.padw),
  .inst (.locLoadwBe 12),
  .inst (.padw),
  .inst (.locLoadwBe 8),
  .inst (.padw),
  .inst (.locLoadwBe 4),
  .inst (.movdn 3),
  .inst (.push 0),
  .inst (.dropw),
  .inst (.exec "mulstep4"),
  .inst (.movdn 9),
  .inst (.movdn 9),
  .inst (.swapw 1),
  .inst (.movup 3),
  .inst (.padw),
  .inst (.locLoadwBe 16),
  .inst (.drop),
  .inst (.movup 3),
  .inst (.locStorewBe 16),
  .inst (.dropw),
  .inst (.padw),
  .inst (.locLoadwBe 20),
  .inst (.movdn 3),
  .inst (.push 0),
  .inst (.dropw),
  .inst (.swapw 1),
  .inst (.movup 9),
  .inst (.movup 9),
  .inst (.swap 1),
  .inst (.movup 5),
  .inst (.movup 6),
  .inst (.swap 3),
  .inst (.exec "mulstep"),
  .inst (.drop),
  .inst (.movdn 3),
  .inst (.push 0),
  .inst (.dropw),
  .inst (.padw),
  .inst (.locLoadwBe 12),
  .inst (.padw),
  .inst (.locLoadwBe 8),
  .inst (.padw),
  .inst (.locLoadwBe 0),
  .inst (.push 0),
  .inst (.dropw),
  .inst (.exec "mulstep4"),
  .inst (.dropw),
  .inst (.drop),
  .inst (.drop),
  .inst (.padw),
  .inst (.locLoadwBe 12),
  .inst (.padw),
  .inst (.locLoadwBe 0),
  .inst (.movup 2),
  .inst (.movdn 3),
  .inst (.push 0),
  .inst (.dropw),
  .inst (.movup 7),
  .inst (.dup 1),
  .inst (.movup 6),
  .inst (.push 0),
  .inst (.exec "mulstep"),
  .inst (.swap 1),
  .inst (.movdn 7),
  .inst (.movup 4),
  .inst (.dup 2),
  .inst (.movup 7),
  .inst (.swap 3),
  .inst (.exec "mulstep"),
  .inst (.swap 1),
  .inst (.movdn 5),
  .inst (.swap 1),
  .inst (.movup 3),
  .inst (.movup 4),
  .inst (.swap 3),
  .inst (.exec "mulstep"),
  .inst (.drop),
  .inst (.swap 1),
  .inst (.drop),
  .inst (.padw),
  .inst (.locLoadwBe 12),
  .inst (.padw),
  .inst (.locLoadwBe 0),
  .inst (.swap 1),
  .inst (.movdn 3),
  .inst (.push 0),
  .inst (.dropw),
  .inst (.movup 6),
  .inst (.dup 1),
  .inst (.movup 6),
  .inst (.push 0),
  .inst (.exec "mulstep"),
  .inst (.swap 1),
  .inst (.movdn 6),
  .inst (.swap 1),
  .inst (.movup 4),
  .inst (.movup 5),
  .inst (.swap 3),
  .inst (.exec "mulstep"),
  .inst (.drop),
  .inst (.movdn 2),
  .inst (.drop),
  .inst (.drop),
  .inst (.padw),
  .inst (.locLoadwBe 12),
  .inst (.padw),
  .inst (.locLoadwBe 0),
  .inst (.movdn 3),
  .inst (.push 0),
  .inst (.dropw),
  .inst (.movup 4),
  .inst (.movup 5),
  .inst (.movdn 2),
  .inst (.push 0),
  .inst (.exec "mulstep"),
  .inst (.drop),
  .inst (.movdn 3),
  .inst (.drop),
  .inst (.drop),
  .inst (.drop),
  .inst (.padw),
  .inst (.locLoadwBe 16),
  .inst (.swapw 1),
  .inst (.exec "u256_le_to_be"),
  .inst (.swapdw),
  .inst (.dropw),
  .inst (.dropw),
  .inst (.swapdw),
  .inst (.dropw),
  .inst (.dropw)]

-- ============================================================================
-- Round 1: multiply b0 × a[0..7] — 44 ops
-- ============================================================================

def wm_round1 : List Op := [
  -- Part A: mulstep4 for b0 × a[0..3]
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.movdnw 2), .inst (.movup 12),
  .inst (.exec "mulstep4"),
  .inst (.movdn 9), .inst (.movdn 9), .inst (.swapw 1),
  .inst (.locStorewBe 16), .inst (.dropw),
  -- Part B: 4 individual mulsteps for b0 × a[4..7]
  .inst (.padw), .inst (.locLoadwBe 20), .inst (.swapw 1),
  .inst (.movup 9), .inst (.movup 9),
  .inst (.dup 1), .inst (.movup 6), .inst (.movup 10), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 5),
  .inst (.dup 1), .inst (.movup 5), .inst (.movup 9), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 4),
  .inst (.dup 1), .inst (.movup 4), .inst (.movup 8), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 3),
  .inst (.swap 1), .inst (.movup 2), .inst (.movup 6), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop),
  .inst (.locStorewBe 20), .inst (.dropw)
]

-- Everything after round 1 (258 ops)
def wm_rest_after_r1 : List Op := [
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movup 7), .inst (.dropw), .inst (.padw), .inst (.locLoadwBe 12),
  .inst (.padw), .inst (.locLoadwBe 8), .inst (.padw), .inst (.locLoadwBe 4),
  .inst (.movup 2), .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.exec "mulstep4"),
  .inst (.movdn 9), .inst (.movdn 9), .inst (.swapw 1), .inst (.movdn 3),
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.push 0), .inst (.dropw),
  .inst (.movdn 3), .inst (.locStorewBe 16), .inst (.dropw),
  .inst (.padw), .inst (.locLoadwBe 20), .inst (.movup 3), .inst (.drop),
  .inst (.swapw 1), .inst (.movup 9), .inst (.movup 9),
  .inst (.dup 1), .inst (.movup 6), .inst (.movup 9), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 7),
  .inst (.dup 1), .inst (.movup 5), .inst (.movup 7), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 5),
  .inst (.swap 1), .inst (.movup 3), .inst (.movup 4), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop), .inst (.swap 1), .inst (.drop),
  .inst (.locStorewBe 20), .inst (.dropw),
  -- Round 3
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movup 7), .inst (.movup 7), .inst (.dropw),
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 8),
  .inst (.padw), .inst (.locLoadwBe 4),
  .inst (.swap 1), .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.exec "mulstep4"),
  .inst (.movdn 9), .inst (.movdn 9), .inst (.swapw 1),
  .inst (.movdn 3), .inst (.movdn 3),
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.drop), .inst (.drop),
  .inst (.movdn 3), .inst (.movdn 3), .inst (.locStorewBe 16), .inst (.dropw),
  .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movup 3), .inst (.movup 3), .inst (.drop), .inst (.drop),
  .inst (.swapw 1), .inst (.movup 9), .inst (.movup 9),
  .inst (.dup 1), .inst (.movup 6), .inst (.movup 8), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 6),
  .inst (.dup 1), .inst (.movup 5), .inst (.movup 6), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.swap 1), .inst (.drop),
  .inst (.movdn 3), .inst (.drop), .inst (.drop), .inst (.drop),
  .inst (.locStorewBe 20), .inst (.dropw),
  -- Round 4
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movup 7), .inst (.movup 7), .inst (.movup 7), .inst (.dropw),
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 8),
  .inst (.padw), .inst (.locLoadwBe 4),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.exec "mulstep4"),
  .inst (.movdn 9), .inst (.movdn 9), .inst (.swapw 1),
  .inst (.movup 3),
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.drop), .inst (.movup 3),
  .inst (.locStorewBe 16), .inst (.dropw),
  .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.swapw 1), .inst (.movup 9), .inst (.movup 9),
  .inst (.swap 1), .inst (.movup 5), .inst (.movup 6), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  -- Round 5 (mulstep4 only)
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 8),
  .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.push 0), .inst (.dropw),
  .inst (.exec "mulstep4"),
  .inst (.dropw), .inst (.drop), .inst (.drop),
  -- Epilogue: b5 × a[0..2]
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.movup 2), .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 7), .inst (.dup 1), .inst (.movup 6), .inst (.push 0),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 7),
  .inst (.movup 4), .inst (.dup 2), .inst (.movup 7), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 5),
  .inst (.swap 1), .inst (.movup 3), .inst (.movup 4), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop), .inst (.swap 1), .inst (.drop),
  -- Epilogue: b6 × a[0..1]
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.swap 1), .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 6), .inst (.dup 1), .inst (.movup 6), .inst (.push 0),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 6),
  .inst (.swap 1), .inst (.movup 4), .inst (.movup 5), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop),
  .inst (.movdn 2), .inst (.drop), .inst (.drop),
  -- Epilogue: b7 × a0
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 4), .inst (.movup 5), .inst (.movdn 2),
  .inst (.push 0), .inst (.exec "mulstep"), .inst (.drop),
  .inst (.movdn 3), .inst (.drop), .inst (.drop), .inst (.drop),
  -- Final: load accumulated results, convert, cleanup
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.swapw 1),
  .inst (.exec "u256_le_to_be"),
  .inst (.swapdw), .inst (.dropw), .inst (.dropw),
  .inst (.swapdw), .inst (.dropw), .inst (.dropw)
]

-- ============================================================================
-- Body and round decomposition
-- ============================================================================

set_option maxRecDepth 1024 in
theorem wm_body_decomp :
    Miden.Core.U256.wrapping_mul.body = wm_setup ++ wm_rest := by
  unfold Miden.Core.U256.wrapping_mul wm_setup wm_rest; rfl

set_option maxRecDepth 1024 in
theorem wm_rest_eq_r1_append :
    wm_rest = wm_round1 ++ wm_rest_after_r1 := by
  unfold wm_rest wm_round1 wm_rest_after_r1; rfl

-- Round 2: b1 × a[0..6] (mulstep4 + 3 individual mulsteps, 59 ops)
def wm_round2 : List Op := [
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movup 7), .inst (.dropw), .inst (.padw), .inst (.locLoadwBe 12),
  .inst (.padw), .inst (.locLoadwBe 8), .inst (.padw), .inst (.locLoadwBe 4),
  .inst (.movup 2), .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.exec "mulstep4"),
  .inst (.movdn 9), .inst (.movdn 9), .inst (.swapw 1), .inst (.movdn 3),
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.push 0), .inst (.dropw),
  .inst (.movdn 3), .inst (.locStorewBe 16), .inst (.dropw),
  .inst (.padw), .inst (.locLoadwBe 20), .inst (.movup 3), .inst (.drop),
  .inst (.swapw 1), .inst (.movup 9), .inst (.movup 9),
  .inst (.dup 1), .inst (.movup 6), .inst (.movup 9), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 7),
  .inst (.dup 1), .inst (.movup 5), .inst (.movup 7), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 5),
  .inst (.swap 1), .inst (.movup 3), .inst (.movup 4), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop), .inst (.swap 1), .inst (.drop),
  .inst (.locStorewBe 20), .inst (.dropw)
]

-- Everything after Round 2 (Rounds 3-5 + epilogue + final, 199 ops)
def wm_rest_after_r2 : List Op := [
  -- Round 3
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movup 7), .inst (.movup 7), .inst (.dropw),
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 8),
  .inst (.padw), .inst (.locLoadwBe 4),
  .inst (.swap 1), .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.exec "mulstep4"),
  .inst (.movdn 9), .inst (.movdn 9), .inst (.swapw 1),
  .inst (.movdn 3), .inst (.movdn 3),
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.drop), .inst (.drop),
  .inst (.movdn 3), .inst (.movdn 3), .inst (.locStorewBe 16), .inst (.dropw),
  .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movup 3), .inst (.movup 3), .inst (.drop), .inst (.drop),
  .inst (.swapw 1), .inst (.movup 9), .inst (.movup 9),
  .inst (.dup 1), .inst (.movup 6), .inst (.movup 8), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 6),
  .inst (.dup 1), .inst (.movup 5), .inst (.movup 6), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.swap 1), .inst (.drop),
  .inst (.movdn 3), .inst (.drop), .inst (.drop), .inst (.drop),
  .inst (.locStorewBe 20), .inst (.dropw),
  -- Round 4
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movup 7), .inst (.movup 7), .inst (.movup 7), .inst (.dropw),
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 8),
  .inst (.padw), .inst (.locLoadwBe 4),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.exec "mulstep4"),
  .inst (.movdn 9), .inst (.movdn 9), .inst (.swapw 1),
  .inst (.movup 3),
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.drop), .inst (.movup 3),
  .inst (.locStorewBe 16), .inst (.dropw),
  .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.swapw 1), .inst (.movup 9), .inst (.movup 9),
  .inst (.swap 1), .inst (.movup 5), .inst (.movup 6), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  -- Round 5 (mulstep4 only)
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 8),
  .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.push 0), .inst (.dropw),
  .inst (.exec "mulstep4"),
  .inst (.dropw), .inst (.drop), .inst (.drop),
  -- Epilogue: b5 × a[0..2]
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.movup 2), .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 7), .inst (.dup 1), .inst (.movup 6), .inst (.push 0),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 7),
  .inst (.movup 4), .inst (.dup 2), .inst (.movup 7), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 5),
  .inst (.swap 1), .inst (.movup 3), .inst (.movup 4), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop), .inst (.swap 1), .inst (.drop),
  -- Epilogue: b6 × a[0..1]
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.swap 1), .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 6), .inst (.dup 1), .inst (.movup 6), .inst (.push 0),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 6),
  .inst (.swap 1), .inst (.movup 4), .inst (.movup 5), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop),
  .inst (.movdn 2), .inst (.drop), .inst (.drop),
  -- Epilogue: b7 × a0
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 4), .inst (.movup 5), .inst (.movdn 2),
  .inst (.push 0), .inst (.exec "mulstep"), .inst (.drop),
  .inst (.movdn 3), .inst (.drop), .inst (.drop), .inst (.drop),
  -- Final: load accumulated results, convert, cleanup
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.swapw 1),
  .inst (.exec "u256_le_to_be"),
  .inst (.swapdw), .inst (.dropw), .inst (.dropw),
  .inst (.swapdw), .inst (.dropw), .inst (.dropw)
]

set_option maxRecDepth 2048 in
theorem wm_rest_after_r1_eq_r2_append :
    wm_rest_after_r1 = wm_round2 ++ wm_rest_after_r2 := by
  unfold wm_rest_after_r1 wm_round2 wm_rest_after_r2; rfl

-- ============================================================================
-- Round 2 sub-chunks
-- ============================================================================

-- Round 2 Part A pre: load operands + partial products, prepare stack for mulstep4 (16 ops)
def wm_r2a_pre : List Op := [
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movup 7), .inst (.dropw), .inst (.padw), .inst (.locLoadwBe 12),
  .inst (.padw), .inst (.locLoadwBe 8), .inst (.padw), .inst (.locLoadwBe 4),
  .inst (.movup 2), .inst (.movdn 3), .inst (.push 0), .inst (.dropw)
]

-- Round 2 Part A post: mulstep4 + post-shuffle + store la(16) (12 ops)
def wm_r2a_post : List Op := [
  .inst (.exec "mulstep4"),
  .inst (.movdn 9), .inst (.movdn 9), .inst (.swapw 1), .inst (.movdn 3),
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.push 0), .inst (.dropw),
  .inst (.movdn 3), .inst (.locStorewBe 16), .inst (.dropw)
]

-- Round 2 Part A: mulstep4 phase (28 ops)
def wm_r2a : List Op := wm_r2a_pre ++ wm_r2a_post

-- Round 2 Part B: reload la(20) + 3 individual mulsteps + store la(20) (31 ops)
def wm_r2b : List Op := [
  .inst (.padw), .inst (.locLoadwBe 20), .inst (.movup 3), .inst (.drop),
  .inst (.swapw 1), .inst (.movup 9), .inst (.movup 9),
  .inst (.dup 1), .inst (.movup 6), .inst (.movup 9), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 7),
  .inst (.dup 1), .inst (.movup 5), .inst (.movup 7), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 5),
  .inst (.swap 1), .inst (.movup 3), .inst (.movup 4), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop), .inst (.swap 1), .inst (.drop),
  .inst (.locStorewBe 20), .inst (.dropw)
]

set_option maxRecDepth 1024 in
theorem wm_round2_eq_r2a_r2b : wm_round2 = wm_r2a ++ wm_r2b := by
  unfold wm_round2 wm_r2a wm_r2a_pre wm_r2a_post wm_r2b; rfl

-- Round 2 Part B sub-chunks
-- r2b1: load la(20) + extract + rearrange + 1st mulstep (14 ops)
def wm_r2b1 : List Op := [
  .inst (.padw), .inst (.locLoadwBe 20), .inst (.movup 3), .inst (.drop),
  .inst (.swapw 1), .inst (.movup 9), .inst (.movup 9),
  .inst (.dup 1), .inst (.movup 6), .inst (.movup 9), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 7)
]

-- r2b2: 2nd + 3rd mulsteps + cleanup + store (17 ops)
def wm_r2b2 : List Op := [
  .inst (.dup 1), .inst (.movup 5), .inst (.movup 7), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 5),
  .inst (.swap 1), .inst (.movup 3), .inst (.movup 4), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop), .inst (.swap 1), .inst (.drop),
  .inst (.locStorewBe 20), .inst (.dropw)
]

theorem wm_r2b_eq_b1_b2 : wm_r2b = wm_r2b1 ++ wm_r2b2 := by
  unfold wm_r2b wm_r2b1 wm_r2b2; rfl

-- ============================================================================
-- Round 3 sub-chunks
-- ============================================================================

-- Round 3 ops (61 ops): b₂ × a[0..5] with mulstep4 + 2 individual mulsteps
def wm_round3 : List Op := [
  -- Pre-load accumulators from la(16)/la(20), extract middle 4
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movup 7), .inst (.movup 7), .inst (.dropw),
  -- Load operands
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 8),
  .inst (.padw), .inst (.locLoadwBe 4),
  -- Extract b₂ as multiplier
  .inst (.swap 1), .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  -- mulstep4: b₂ × a[0..3]
  .inst (.exec "mulstep4"),
  -- Post-shuffle and store la(16)
  .inst (.movdn 9), .inst (.movdn 9), .inst (.swapw 1),
  .inst (.movdn 3), .inst (.movdn 3),
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.drop), .inst (.drop),
  .inst (.movdn 3), .inst (.movdn 3), .inst (.locStorewBe 16), .inst (.dropw),
  -- Load la(20) and extract 2 remaining accumulators
  .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movup 3), .inst (.movup 3), .inst (.drop), .inst (.drop),
  -- 2 individual mulsteps
  .inst (.swapw 1), .inst (.movup 9), .inst (.movup 9),
  .inst (.dup 1), .inst (.movup 6), .inst (.movup 8), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 6),
  .inst (.dup 1), .inst (.movup 5), .inst (.movup 6), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.swap 1), .inst (.drop),
  .inst (.movdn 3), .inst (.drop), .inst (.drop), .inst (.drop),
  .inst (.locStorewBe 20), .inst (.dropw)
]

-- Everything after Round 3
def wm_rest_after_r3 : List Op := [
  -- Round 4
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movup 7), .inst (.movup 7), .inst (.movup 7), .inst (.dropw),
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 8),
  .inst (.padw), .inst (.locLoadwBe 4),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.exec "mulstep4"),
  .inst (.movdn 9), .inst (.movdn 9), .inst (.swapw 1),
  .inst (.movup 3),
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.drop), .inst (.movup 3),
  .inst (.locStorewBe 16), .inst (.dropw),
  .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.swapw 1), .inst (.movup 9), .inst (.movup 9),
  .inst (.swap 1), .inst (.movup 5), .inst (.movup 6), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  -- Round 5 (mulstep4 only)
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 8),
  .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.push 0), .inst (.dropw),
  .inst (.exec "mulstep4"),
  .inst (.dropw), .inst (.drop), .inst (.drop),
  -- Epilogue: b5 × a[0..2]
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.movup 2), .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 7), .inst (.dup 1), .inst (.movup 6), .inst (.push 0),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 7),
  .inst (.movup 4), .inst (.dup 2), .inst (.movup 7), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 5),
  .inst (.swap 1), .inst (.movup 3), .inst (.movup 4), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop), .inst (.swap 1), .inst (.drop),
  -- Epilogue: b6 × a[0..1]
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.swap 1), .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 6), .inst (.dup 1), .inst (.movup 6), .inst (.push 0),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 6),
  .inst (.swap 1), .inst (.movup 4), .inst (.movup 5), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop),
  .inst (.movdn 2), .inst (.drop), .inst (.drop),
  -- Epilogue: b7 × a0
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 4), .inst (.movup 5), .inst (.movdn 2),
  .inst (.push 0), .inst (.exec "mulstep"), .inst (.drop),
  .inst (.movdn 3), .inst (.drop), .inst (.drop), .inst (.drop),
  -- Final: load accumulated results, convert, cleanup
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.swapw 1),
  .inst (.exec "u256_le_to_be"),
  .inst (.swapdw), .inst (.dropw), .inst (.dropw),
  .inst (.swapdw), .inst (.dropw), .inst (.dropw)
]

set_option maxRecDepth 2048 in
theorem wm_rest_after_r2_eq_r3_append :
    wm_rest_after_r2 = wm_round3 ++ wm_rest_after_r3 := by
  unfold wm_rest_after_r2 wm_round3 wm_rest_after_r3; rfl

-- Round 3 Part A: pre-load + mulstep4 + store la(16) (32 ops)
def wm_r3a_pre : List Op := [
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movup 7), .inst (.movup 7), .inst (.dropw),
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 8),
  .inst (.padw), .inst (.locLoadwBe 4),
  .inst (.swap 1), .inst (.movdn 3), .inst (.push 0), .inst (.dropw)
]

def wm_r3a_post : List Op := [
  .inst (.exec "mulstep4"),
  .inst (.movdn 9), .inst (.movdn 9), .inst (.swapw 1),
  .inst (.movdn 3), .inst (.movdn 3),
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.drop), .inst (.drop),
  .inst (.movdn 3), .inst (.movdn 3), .inst (.locStorewBe 16), .inst (.dropw)
]

def wm_r3a : List Op := wm_r3a_pre ++ wm_r3a_post

-- Round 3 Part B: load la(20) + 2 individual mulsteps + store la(20) (29 ops)
def wm_r3b : List Op := [
  .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movup 3), .inst (.movup 3), .inst (.drop), .inst (.drop),
  .inst (.swapw 1), .inst (.movup 9), .inst (.movup 9),
  .inst (.dup 1), .inst (.movup 6), .inst (.movup 8), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 6),
  .inst (.dup 1), .inst (.movup 5), .inst (.movup 6), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.swap 1), .inst (.drop),
  .inst (.movdn 3), .inst (.drop), .inst (.drop), .inst (.drop),
  .inst (.locStorewBe 20), .inst (.dropw)
]

set_option maxRecDepth 1024 in
theorem wm_round3_eq_r3a_r3b : wm_round3 = wm_r3a ++ wm_r3b := by
  unfold wm_round3 wm_r3a wm_r3a_pre wm_r3a_post wm_r3b; rfl

-- ============================================================================
-- Round 4 sub-chunks
-- ============================================================================

-- Round 4 ops: b₃ × a[0..4] with mulstep4 + 1 individual mulstep
def wm_round4 : List Op := [
  -- Pre-load: extract [q₂, q₁, q₀, p₃] from la(16)/la(20)
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movup 7), .inst (.movup 7), .inst (.movup 7), .inst (.dropw),
  -- Load operands
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 8),
  .inst (.padw), .inst (.locLoadwBe 4),
  -- Extract b₃ as multiplier
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  -- mulstep4
  .inst (.exec "mulstep4"),
  -- Post-shuffle + store la(16)
  .inst (.movdn 9), .inst (.movdn 9), .inst (.swapw 1),
  .inst (.movup 3),
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.drop), .inst (.movup 3),
  .inst (.locStorewBe 16), .inst (.dropw),
  -- Load la(20), extract q₃, 1 mulstep, cleanup
  .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.swapw 1), .inst (.movup 9), .inst (.movup 9),
  .inst (.swap 1), .inst (.movup 5), .inst (.movup 6), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw)
]

-- Everything after Round 4 (Round 5 + epilogue + final)
def wm_rest_after_r4 : List Op := [
  -- Round 5 (mulstep4 only)
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 8),
  .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.push 0), .inst (.dropw),
  .inst (.exec "mulstep4"),
  .inst (.dropw), .inst (.drop), .inst (.drop),
  -- Epilogue: b5 × a[0..2]
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.movup 2), .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 7), .inst (.dup 1), .inst (.movup 6), .inst (.push 0),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 7),
  .inst (.movup 4), .inst (.dup 2), .inst (.movup 7), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 5),
  .inst (.swap 1), .inst (.movup 3), .inst (.movup 4), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop), .inst (.swap 1), .inst (.drop),
  -- Epilogue: b6 × a[0..1]
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.swap 1), .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 6), .inst (.dup 1), .inst (.movup 6), .inst (.push 0),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 6),
  .inst (.swap 1), .inst (.movup 4), .inst (.movup 5), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop),
  .inst (.movdn 2), .inst (.drop), .inst (.drop),
  -- Epilogue: b7 × a0
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 4), .inst (.movup 5), .inst (.movdn 2),
  .inst (.push 0), .inst (.exec "mulstep"), .inst (.drop),
  .inst (.movdn 3), .inst (.drop), .inst (.drop), .inst (.drop),
  -- Final: load accumulated results, convert, cleanup
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.swapw 1),
  .inst (.exec "u256_le_to_be"),
  .inst (.swapdw), .inst (.dropw), .inst (.dropw),
  .inst (.swapdw), .inst (.dropw), .inst (.dropw)
]

set_option maxRecDepth 2048 in
theorem wm_rest_after_r3_eq_r4_append :
    wm_rest_after_r3 = wm_round4 ++ wm_rest_after_r4 := by
  unfold wm_rest_after_r3 wm_round4 wm_rest_after_r4; rfl

-- Round 4 Part A: pre-load + mulstep4 + store la(16) (33 ops)
def wm_r4a_pre : List Op := [
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movup 7), .inst (.movup 7), .inst (.movup 7), .inst (.dropw),
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 8),
  .inst (.padw), .inst (.locLoadwBe 4),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw)
]

def wm_r4a_post : List Op := [
  .inst (.exec "mulstep4"),
  .inst (.movdn 9), .inst (.movdn 9), .inst (.swapw 1),
  .inst (.movup 3),
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.drop), .inst (.movup 3),
  .inst (.locStorewBe 16), .inst (.dropw)
]

def wm_r4a : List Op := wm_r4a_pre ++ wm_r4a_post

-- Round 4 Part B: load la(20), extract q₃, 1 mulstep, cleanup (16 ops)
def wm_r4b : List Op := [
  .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.swapw 1), .inst (.movup 9), .inst (.movup 9),
  .inst (.swap 1), .inst (.movup 5), .inst (.movup 6), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw)
]

set_option maxRecDepth 1024 in
theorem wm_round4_eq_r4a_r4b : wm_round4 = wm_r4a ++ wm_r4b := by
  unfold wm_round4 wm_r4a wm_r4a_pre wm_r4a_post wm_r4b; rfl

-- ============================================================================
-- Round 5 + Epilogue + Final definitions
-- ============================================================================

-- Round 5: mulstep4 only for b₄ × a[0..3] (12 ops)
def wm_round5 : List Op := [
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 8),
  .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.push 0), .inst (.dropw),
  .inst (.exec "mulstep4"),
  .inst (.dropw), .inst (.drop), .inst (.drop)
]

-- Everything after Round 5 (epilogue + final)
def wm_epilogue_and_final : List Op := [
  -- Epilogue: b5 × a[0..2]
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.movup 2), .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 7), .inst (.dup 1), .inst (.movup 6), .inst (.push 0),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 7),
  .inst (.movup 4), .inst (.dup 2), .inst (.movup 7), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 5),
  .inst (.swap 1), .inst (.movup 3), .inst (.movup 4), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop), .inst (.swap 1), .inst (.drop),
  -- Epilogue: b6 × a[0..1]
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.swap 1), .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 6), .inst (.dup 1), .inst (.movup 6), .inst (.push 0),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 6),
  .inst (.swap 1), .inst (.movup 4), .inst (.movup 5), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop),
  .inst (.movdn 2), .inst (.drop), .inst (.drop),
  -- Epilogue: b7 × a0
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 4), .inst (.movup 5), .inst (.movdn 2),
  .inst (.push 0), .inst (.exec "mulstep"), .inst (.drop),
  .inst (.movdn 3), .inst (.drop), .inst (.drop), .inst (.drop),
  -- Final: load accumulated results, convert, cleanup
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.swapw 1),
  .inst (.exec "u256_le_to_be"),
  .inst (.swapdw), .inst (.dropw), .inst (.dropw),
  .inst (.swapdw), .inst (.dropw), .inst (.dropw)
]

set_option maxRecDepth 2048 in
theorem wm_rest_after_r4_eq_r5_append :
    wm_rest_after_r4 = wm_round5 ++ wm_epilogue_and_final := by
  unfold wm_rest_after_r4 wm_round5 wm_epilogue_and_final; rfl

-- Epilogue sub-chunks
def wm_ep_b5 : List Op := [
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.movup 2), .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 7), .inst (.dup 1), .inst (.movup 6), .inst (.push 0),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 7),
  .inst (.movup 4), .inst (.dup 2), .inst (.movup 7), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 5),
  .inst (.swap 1), .inst (.movup 3), .inst (.movup 4), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop), .inst (.swap 1), .inst (.drop)
]

def wm_ep_b6 : List Op := [
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.swap 1), .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 6), .inst (.dup 1), .inst (.movup 6), .inst (.push 0),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 6),
  .inst (.swap 1), .inst (.movup 4), .inst (.movup 5), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop),
  .inst (.movdn 2), .inst (.drop), .inst (.drop)
]

def wm_ep_b7 : List Op := [
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 4), .inst (.movup 5), .inst (.movdn 2),
  .inst (.push 0), .inst (.exec "mulstep"), .inst (.drop),
  .inst (.movdn 3), .inst (.drop), .inst (.drop), .inst (.drop)
]

def wm_final : List Op := [
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.swapw 1),
  .inst (.exec "u256_le_to_be"),
  .inst (.swapdw), .inst (.dropw), .inst (.dropw),
  .inst (.swapdw), .inst (.dropw), .inst (.dropw)
]

-- ============================================================================
-- Round 1 sub-chunks
-- ============================================================================

-- Part A: mulstep4 for b0 × a[0..3], store to locals 16 (10 ops)
def wm_r1a : List Op := [
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.movdnw 2), .inst (.movup 12),
  .inst (.exec "mulstep4"),
  .inst (.movdn 9), .inst (.movdn 9), .inst (.swapw 1),
  .inst (.locStorewBe 16), .inst (.dropw)
]

-- Part B: 4 individual mulsteps for b0 × a[4..7], store to locals 20 (34 ops)
def wm_r1b : List Op := [
  .inst (.padw), .inst (.locLoadwBe 20), .inst (.swapw 1),
  .inst (.movup 9), .inst (.movup 9),
  .inst (.dup 1), .inst (.movup 6), .inst (.movup 10), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 5),
  .inst (.dup 1), .inst (.movup 5), .inst (.movup 9), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 4),
  .inst (.dup 1), .inst (.movup 4), .inst (.movup 8), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 3),
  .inst (.swap 1), .inst (.movup 2), .inst (.movup 6), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop),
  .inst (.locStorewBe 20), .inst (.dropw)
]

theorem wm_round1_eq_r1a_r1b : wm_round1 = wm_r1a ++ wm_r1b := by
  unfold wm_round1 wm_r1a wm_r1b; rfl

-- Split Part B into two halves for proof manageability
-- Part B1: setup + first 2 individual mulsteps (19 ops)
def wm_r1b1 : List Op := [
  .inst (.padw), .inst (.locLoadwBe 20), .inst (.swapw 1),
  .inst (.movup 9), .inst (.movup 9),
  .inst (.dup 1), .inst (.movup 6), .inst (.movup 10), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 5),
  .inst (.dup 1), .inst (.movup 5), .inst (.movup 9), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 4)
]

-- Part B2: last 2 individual mulsteps + store + cleanup (15 ops)
def wm_r1b2 : List Op := [
  .inst (.dup 1), .inst (.movup 4), .inst (.movup 8), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 3),
  .inst (.swap 1), .inst (.movup 2), .inst (.movup 6), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop),
  .inst (.locStorewBe 20), .inst (.dropw)
]

theorem wm_r1b_eq_b1_b2 : wm_r1b = wm_r1b1 ++ wm_r1b2 := by
  unfold wm_r1b wm_r1b1 wm_r1b2; rfl

-- ============================================================================
-- Epilogue decomposition helpers
-- ============================================================================

def wm_ep_b6_b7_final : List Op := wm_ep_b6 ++ wm_ep_b7 ++ wm_final
def wm_ep_b7_final : List Op := wm_ep_b7 ++ wm_final

set_option maxRecDepth 2048 in
theorem wm_epilogue_split_b5 :
    wm_epilogue_and_final = wm_ep_b5 ++ wm_ep_b6_b7_final := by
  unfold wm_epilogue_and_final wm_ep_b5 wm_ep_b6_b7_final wm_ep_b6 wm_ep_b7 wm_final; rfl

set_option maxRecDepth 2048 in
theorem wm_ep_b6_b7_final_split :
    wm_ep_b6_b7_final = wm_ep_b6 ++ wm_ep_b7_final := by
  unfold wm_ep_b6_b7_final wm_ep_b6 wm_ep_b7_final wm_ep_b7 wm_final; rfl

set_option maxRecDepth 2048 in
theorem wm_ep_b7_final_split :
    wm_ep_b7_final = wm_ep_b7 ++ wm_final := by
  unfold wm_ep_b7_final wm_ep_b7 wm_final; rfl

end MidenLean.Proofs
