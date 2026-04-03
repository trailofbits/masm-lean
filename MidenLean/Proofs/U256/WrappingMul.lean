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
-- Phase 1: Setup (LE→BE + store operands + init accumulators)
-- ============================================================================

private def wm_setup : List Op := [
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
private def wm_rest : List Op :=
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

private def wm_round1 : List Op := [
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
private def wm_rest_after_r1 : List Op := [
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
private theorem wm_body_decomp :
    Miden.Core.U256.wrapping_mul.body = wm_setup ++ wm_rest := by
  unfold Miden.Core.U256.wrapping_mul wm_setup wm_rest; rfl

set_option maxRecDepth 1024 in
private theorem wm_rest_eq_r1_append :
    wm_rest = wm_round1 ++ wm_rest_after_r1 := by
  unfold wm_rest wm_round1 wm_rest_after_r1; rfl

-- Round 2: b1 × a[0..6] (mulstep4 + 3 individual mulsteps, 59 ops)
private def wm_round2 : List Op := [
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
private def wm_rest_after_r2 : List Op := [
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
private theorem wm_rest_after_r1_eq_r2_append :
    wm_rest_after_r1 = wm_round2 ++ wm_rest_after_r2 := by
  unfold wm_rest_after_r1 wm_round2 wm_rest_after_r2; rfl

-- ============================================================================
-- Round 2 sub-chunks
-- ============================================================================

-- Round 2 Part A pre: load operands + partial products, prepare stack for mulstep4 (16 ops)
private def wm_r2a_pre : List Op := [
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movup 7), .inst (.dropw), .inst (.padw), .inst (.locLoadwBe 12),
  .inst (.padw), .inst (.locLoadwBe 8), .inst (.padw), .inst (.locLoadwBe 4),
  .inst (.movup 2), .inst (.movdn 3), .inst (.push 0), .inst (.dropw)
]

-- Round 2 Part A post: mulstep4 + post-shuffle + store la(16) (12 ops)
private def wm_r2a_post : List Op := [
  .inst (.exec "mulstep4"),
  .inst (.movdn 9), .inst (.movdn 9), .inst (.swapw 1), .inst (.movdn 3),
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.push 0), .inst (.dropw),
  .inst (.movdn 3), .inst (.locStorewBe 16), .inst (.dropw)
]

-- Round 2 Part A: mulstep4 phase (28 ops)
private def wm_r2a : List Op := wm_r2a_pre ++ wm_r2a_post

-- Round 2 Part B: reload la(20) + 3 individual mulsteps + store la(20) (31 ops)
private def wm_r2b : List Op := [
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
private theorem wm_round2_eq_r2a_r2b : wm_round2 = wm_r2a ++ wm_r2b := by
  unfold wm_round2 wm_r2a wm_r2a_pre wm_r2a_post wm_r2b; rfl

-- Round 2 Part B sub-chunks
-- r2b1: load la(20) + extract + rearrange + 1st mulstep (14 ops)
private def wm_r2b1 : List Op := [
  .inst (.padw), .inst (.locLoadwBe 20), .inst (.movup 3), .inst (.drop),
  .inst (.swapw 1), .inst (.movup 9), .inst (.movup 9),
  .inst (.dup 1), .inst (.movup 6), .inst (.movup 9), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 7)
]

-- r2b2: 2nd + 3rd mulsteps + cleanup + store (17 ops)
private def wm_r2b2 : List Op := [
  .inst (.dup 1), .inst (.movup 5), .inst (.movup 7), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 5),
  .inst (.swap 1), .inst (.movup 3), .inst (.movup 4), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop), .inst (.swap 1), .inst (.drop),
  .inst (.locStorewBe 20), .inst (.dropw)
]

private theorem wm_r2b_eq_b1_b2 : wm_r2b = wm_r2b1 ++ wm_r2b2 := by
  unfold wm_r2b wm_r2b1 wm_r2b2; rfl

-- ============================================================================
-- Round 3 sub-chunks
-- ============================================================================

-- Round 3 ops (61 ops): b₂ × a[0..5] with mulstep4 + 2 individual mulsteps
private def wm_round3 : List Op := [
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
private def wm_rest_after_r3 : List Op := [
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
private theorem wm_rest_after_r2_eq_r3_append :
    wm_rest_after_r2 = wm_round3 ++ wm_rest_after_r3 := by
  unfold wm_rest_after_r2 wm_round3 wm_rest_after_r3; rfl

-- Round 3 Part A: pre-load + mulstep4 + store la(16) (32 ops)
private def wm_r3a_pre : List Op := [
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movup 7), .inst (.movup 7), .inst (.dropw),
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 8),
  .inst (.padw), .inst (.locLoadwBe 4),
  .inst (.swap 1), .inst (.movdn 3), .inst (.push 0), .inst (.dropw)
]

private def wm_r3a_post : List Op := [
  .inst (.exec "mulstep4"),
  .inst (.movdn 9), .inst (.movdn 9), .inst (.swapw 1),
  .inst (.movdn 3), .inst (.movdn 3),
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.drop), .inst (.drop),
  .inst (.movdn 3), .inst (.movdn 3), .inst (.locStorewBe 16), .inst (.dropw)
]

private def wm_r3a : List Op := wm_r3a_pre ++ wm_r3a_post

-- Round 3 Part B: load la(20) + 2 individual mulsteps + store la(20) (29 ops)
private def wm_r3b : List Op := [
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
private theorem wm_round3_eq_r3a_r3b : wm_round3 = wm_r3a ++ wm_r3b := by
  unfold wm_round3 wm_r3a wm_r3a_pre wm_r3a_post wm_r3b; rfl

-- ============================================================================
-- Round 4 sub-chunks
-- ============================================================================

-- Round 4 ops: b₃ × a[0..4] with mulstep4 + 1 individual mulstep
private def wm_round4 : List Op := [
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
private def wm_rest_after_r4 : List Op := [
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
private theorem wm_rest_after_r3_eq_r4_append :
    wm_rest_after_r3 = wm_round4 ++ wm_rest_after_r4 := by
  unfold wm_rest_after_r3 wm_round4 wm_rest_after_r4; rfl

-- Round 4 Part A: pre-load + mulstep4 + store la(16) (33 ops)
private def wm_r4a_pre : List Op := [
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movup 7), .inst (.movup 7), .inst (.movup 7), .inst (.dropw),
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 8),
  .inst (.padw), .inst (.locLoadwBe 4),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw)
]

private def wm_r4a_post : List Op := [
  .inst (.exec "mulstep4"),
  .inst (.movdn 9), .inst (.movdn 9), .inst (.swapw 1),
  .inst (.movup 3),
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.drop), .inst (.movup 3),
  .inst (.locStorewBe 16), .inst (.dropw)
]

private def wm_r4a : List Op := wm_r4a_pre ++ wm_r4a_post

-- Round 4 Part B: load la(20), extract q₃, 1 mulstep, cleanup (16 ops)
private def wm_r4b : List Op := [
  .inst (.padw), .inst (.locLoadwBe 20),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.swapw 1), .inst (.movup 9), .inst (.movup 9),
  .inst (.swap 1), .inst (.movup 5), .inst (.movup 6), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw)
]

set_option maxRecDepth 1024 in
private theorem wm_round4_eq_r4a_r4b : wm_round4 = wm_r4a ++ wm_r4b := by
  unfold wm_round4 wm_r4a wm_r4a_pre wm_r4a_post wm_r4b; rfl

-- ============================================================================
-- Round 5 + Epilogue + Final definitions
-- ============================================================================

-- Round 5: mulstep4 only for b₄ × a[0..3] (12 ops)
private def wm_round5 : List Op := [
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 8),
  .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.push 0), .inst (.dropw),
  .inst (.exec "mulstep4"),
  .inst (.dropw), .inst (.drop), .inst (.drop)
]

-- Everything after Round 5 (epilogue + final)
private def wm_epilogue_and_final : List Op := [
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
private theorem wm_rest_after_r4_eq_r5_append :
    wm_rest_after_r4 = wm_round5 ++ wm_epilogue_and_final := by
  unfold wm_rest_after_r4 wm_round5 wm_epilogue_and_final; rfl

-- Epilogue sub-chunks
private def wm_ep_b5 : List Op := [
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.movup 2), .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 7), .inst (.dup 1), .inst (.movup 6), .inst (.push 0),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 7),
  .inst (.movup 4), .inst (.dup 2), .inst (.movup 7), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 5),
  .inst (.swap 1), .inst (.movup 3), .inst (.movup 4), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop), .inst (.swap 1), .inst (.drop)
]

private def wm_ep_b6 : List Op := [
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.swap 1), .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 6), .inst (.dup 1), .inst (.movup 6), .inst (.push 0),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 6),
  .inst (.swap 1), .inst (.movup 4), .inst (.movup 5), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop),
  .inst (.movdn 2), .inst (.drop), .inst (.drop)
]

private def wm_ep_b7 : List Op := [
  .inst (.padw), .inst (.locLoadwBe 12), .inst (.padw), .inst (.locLoadwBe 0),
  .inst (.movdn 3), .inst (.push 0), .inst (.dropw),
  .inst (.movup 4), .inst (.movup 5), .inst (.movdn 2),
  .inst (.push 0), .inst (.exec "mulstep"), .inst (.drop),
  .inst (.movdn 3), .inst (.drop), .inst (.drop), .inst (.drop)
]

private def wm_final : List Op := [
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.swapw 1),
  .inst (.exec "u256_le_to_be"),
  .inst (.swapdw), .inst (.dropw), .inst (.dropw),
  .inst (.swapdw), .inst (.dropw), .inst (.dropw)
]

set_option maxRecDepth 2048 in
private theorem wm_epilogue_and_final_eq :
    wm_epilogue_and_final = wm_ep_b5 ++ wm_ep_b6 ++ wm_ep_b7 ++ wm_final := by
  unfold wm_epilogue_and_final wm_ep_b5 wm_ep_b6 wm_ep_b7 wm_final; rfl

-- ============================================================================
-- Setup chunk correctness
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- The setup phase converts LE→BE, stores operands to locals 0-15,
    and initializes accumulators at locals 16-23 to zero.
    Output stack: [a7, a6, a5, a4, a3, a2, a1, a0, b0] ++ rest -/
private theorem wm_setup_correct (a b : U256) (rest : List Felt) (mem : Nat → Felt)
    (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt) (fuel : Nat)
    (hnl : frame.numLocals ≥ 24) :
    let la := frame.localAddr
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
       b.a4.val :: b.a5.val :: b.a6.val :: b.a7.val ::
       a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
       a.a4.val :: a.a5.val :: a.a6.val :: a.a7.val :: rest,
       mem, frame :: frames, adv⟩
      wm_setup =
    some ⟨a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
          a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: b.a0.val :: rest,
          fun i =>
            if i = la 20 + 3 then 0 else if i = la 20 + 2 then 0
            else if i = la 20 + 1 then 0 else if i = la 20 then 0
            else if i = la 16 + 3 then 0 else if i = la 16 + 2 then 0
            else if i = la 16 + 1 then 0 else if i = la 16 then 0
            else if i = la 12 + 3 then a.a3.val else if i = la 12 + 2 then a.a2.val
            else if i = la 12 + 1 then a.a1.val else if i = la 12 then a.a0.val
            else if i = la 8 + 3 then a.a7.val else if i = la 8 + 2 then a.a6.val
            else if i = la 8 + 1 then a.a5.val else if i = la 8 then a.a4.val
            else if i = la 4 + 3 then b.a3.val else if i = la 4 + 2 then b.a2.val
            else if i = la 4 + 1 then b.a1.val else if i = la 4 then b.a0.val
            else if i = la 0 + 3 then b.a7.val else if i = la 0 + 2 then b.a6.val
            else if i = la 0 + 1 then b.a5.val else if i = la 0 then b.a4.val
            else mem i,
          frame :: frames, adv⟩ := by
  unfold wm_setup execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  -- Step 1: exec "u256_le_to_be_pair"
  dsimp only [bind, Bind.bind, Option.bind]
  rw [u256_u256_le_to_be_pair_raw]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 2: locStorewBe 0
  rw [stepLocStorewBe (halign := by decide) (hbound := by omega)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 3: dropw
  rw [stepDropw]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 4: locStorewBe 4
  rw [stepLocStorewBe (halign := by decide) (hbound := by omega)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 5: push 0
  miden_step
  -- Step 6: dropw
  rw [stepDropw]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 7: movdn 8
  miden_movdn
  -- Step 8: locStorewBe 8
  rw [stepLocStorewBe (halign := by decide) (hbound := by omega)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 9: swapw 1
  rw [stepSwapw1]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 10: locStorewBe 12
  rw [stepLocStorewBe (halign := by decide) (hbound := by omega)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 11: padw
  rw [stepPadw]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 12: locStorewBe 16
  rw [stepLocStorewBe (halign := by decide) (hbound := by omega)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 13: locStorewBe 20
  rw [stepLocStorewBe (halign := by decide) (hbound := by omega)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 14: dropw
  rw [stepDropw]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Step 15: swapw 1
  rw [stepSwapw1]
  simp only [pure, Pure.pure]

-- ============================================================================
-- Round 1 sub-chunks
-- ============================================================================

-- Part A: mulstep4 for b0 × a[0..3], store to locals 16 (10 ops)
private def wm_r1a : List Op := [
  .inst (.padw), .inst (.locLoadwBe 16), .inst (.movdnw 2), .inst (.movup 12),
  .inst (.exec "mulstep4"),
  .inst (.movdn 9), .inst (.movdn 9), .inst (.swapw 1),
  .inst (.locStorewBe 16), .inst (.dropw)
]

-- Part B: 4 individual mulsteps for b0 × a[4..7], store to locals 20 (34 ops)
private def wm_r1b : List Op := [
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

private theorem wm_round1_eq_r1a_r1b : wm_round1 = wm_r1a ++ wm_r1b := by
  unfold wm_round1 wm_r1a wm_r1b; rfl

-- ============================================================================
-- Round 1 Part A: mulstep4 phase
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- Part A: padw, locLoadwBe 16, movdnw 2, movup 12, exec mulstep4,
    movdn 9, movdn 9, swapw 1, locStorewBe 16, dropw.
    Computes b0 × a[0..3] and stores low results to locals 16. -/
private theorem wm_r1a_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (h16_3 : mem (frame.localAddr 16 + 3) = 0)
    (h16_2 : mem (frame.localAddr 16 + 2) = 0)
    (h16_1 : mem (frame.localAddr 16 + 1) = 0)
    (h16_0 : mem (frame.localAddr 16) = 0) :
    let la := frame.localAddr
    let c₁ := mulstepCarry 0 a.a0.val b.a0.val 0
    let c₂ := mulstepCarry c₁ a.a1.val b.a0.val 0
    let c₃ := mulstepCarry c₂ a.a2.val b.a0.val 0
    let c₄ := mulstepCarry c₃ a.a3.val b.a0.val 0
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
       a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: b.a0.val :: rest,
       mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_r1a) =
    some ⟨a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val :: c₄ :: b.a0.val :: rest,
          fun i =>
            if i = la 16 + 3 then mulstepLo c₃ a.a3.val b.a0.val 0
            else if i = la 16 + 2 then mulstepLo c₂ a.a2.val b.a0.val 0
            else if i = la 16 + 1 then mulstepLo c₁ a.a1.val b.a0.val 0
            else if i = la 16 then mulstepLo 0 a.a0.val b.a0.val 0
            else mem i,
          frame :: frames, adv⟩ := by
  unfold wm_r1a execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  -- 1. padw
  dsimp only [bind, Bind.bind, Option.bind]
  rw [stepPadw]
  dsimp only [bind, Bind.bind, Option.bind]
  -- 2. locLoadwBe 16
  rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
  rw [h16_3, h16_2, h16_1, h16_0]
  dsimp only [bind, Bind.bind, Option.bind]
  -- 3. movdnw 2
  rw [stepMovdnw2]
  dsimp only [bind, Bind.bind, Option.bind]
  -- 4. movup 12
  miden_movup
  -- 5. exec "mulstep4"
  have h0u : (0 : Felt).isU32 = true := by simp [Felt.isU32]
  have hmul4 := u256_mulstep4_correct
    b.a0.val a.a7.val a.a6.val a.a5.val a.a4.val
    a.a3.val a.a2.val a.a1.val a.a0.val
    (0 : Felt) (0 : Felt) (0 : Felt) (0 : Felt) rest
    ⟨b.a0.val :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
     a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val ::
     (0 : Felt) :: (0 : Felt) :: (0 : Felt) :: (0 : Felt) :: rest,
     mem, frame :: frames, adv⟩
    rfl
    (U256.a0_isU32 b) (U256.a3_isU32 a) (U256.a2_isU32 a) (U256.a1_isU32 a) (U256.a0_isU32 a)
    h0u h0u h0u h0u fuel
  simp only [MidenState.withStack] at hmul4
  rw [hmul4]; clear hmul4
  dsimp only [bind, Bind.bind, Option.bind]
  -- 6. movdn 9
  miden_movdn
  -- 7. movdn 9
  miden_movdn
  -- 8. swapw 1
  rw [stepSwapw1]
  dsimp only [bind, Bind.bind, Option.bind]
  -- 9. locStorewBe 16
  rw [stepLocStorewBe (halign := by decide) (hbound := by omega)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- 10. dropw
  rw [stepDropw]
  simp only [pure, Pure.pure]

-- ============================================================================
-- Round 1 Part B: individual mulsteps (sorry for now)
-- ============================================================================

-- Split Part B into two halves for proof manageability
-- Part B1: setup + first 2 individual mulsteps (19 ops)
private def wm_r1b1 : List Op := [
  .inst (.padw), .inst (.locLoadwBe 20), .inst (.swapw 1),
  .inst (.movup 9), .inst (.movup 9),
  .inst (.dup 1), .inst (.movup 6), .inst (.movup 10), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 5),
  .inst (.dup 1), .inst (.movup 5), .inst (.movup 9), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 4)
]

-- Part B2: last 2 individual mulsteps + store + cleanup (15 ops)
private def wm_r1b2 : List Op := [
  .inst (.dup 1), .inst (.movup 4), .inst (.movup 8), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.swap 1), .inst (.movdn 3),
  .inst (.swap 1), .inst (.movup 2), .inst (.movup 6), .inst (.swap 3),
  .inst (.exec "mulstep"), .inst (.drop),
  .inst (.locStorewBe 20), .inst (.dropw)
]

private theorem wm_r1b_eq_b1_b2 : wm_r1b = wm_r1b1 ++ wm_r1b2 := by
  unfold wm_r1b wm_r1b1 wm_r1b2; rfl

set_option maxHeartbeats 32000000 in
/-- Part B1: setup + first 2 individual mulsteps for b0 × a[4..5].
    Input stack:  [a7, a6, a5, a4, c₄, b0] ++ rest
    Output stack: [c₆, b0, a7, a6, l₅, l₄, 0, 0] ++ rest -/
private theorem wm_r1b1_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (c₄ : Felt) (hc₄ : c₄.isU32 = true)
    (h20_3 : mem (frame.localAddr 20 + 3) = 0)
    (h20_2 : mem (frame.localAddr 20 + 2) = 0)
    (h20_1 : mem (frame.localAddr 20 + 1) = 0)
    (h20_0 : mem (frame.localAddr 20) = 0) :
    let c₅ := mulstepCarry c₄ a.a4.val b.a0.val 0
    let c₆ := mulstepCarry c₅ a.a5.val b.a0.val 0
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val :: c₄ :: b.a0.val :: rest,
       mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_r1b1) =
    some ⟨c₆ :: b.a0.val :: a.a7.val :: a.a6.val ::
          mulstepLo c₅ a.a5.val b.a0.val 0 :: mulstepLo c₄ a.a4.val b.a0.val 0 ::
          (0 : Felt) :: (0 : Felt) :: rest,
          mem, frame :: frames, adv⟩ := by
  unfold wm_r1b1 execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  have h0u : (0 : Felt).isU32 = true := by simp [Felt.isU32]
  -- Setup: padw
  dsimp only [bind, Bind.bind, Option.bind]
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 20 (replaces top 4)
  rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
  rw [h20_3, h20_2, h20_1, h20_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- swapw 1
  rw [stepSwapw1]; dsimp only [bind, Bind.bind, Option.bind]
  -- movup 9 (brings b0 to top)
  miden_movup
  -- movup 9 (brings c₄ to top)
  miden_movup
  -- Stack: [c₄, b0, a7, a6, a5, a4, 0, 0, 0, 0] ++ rest
  -- === Mulstep 1: c₄ × a4 ===
  miden_dup    -- dup 1
  miden_movup  -- movup 6
  miden_movup  -- movup 10
  miden_swap   -- swap 3
  -- Stack: [c₄, a4, b0, 0, b0, a7, a6, a5, 0, 0, 0] ++ rest
  have hms1 := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    c₄ (a.a4.val) (b.a0.val) (0 : Felt)
    (b.a0.val :: a.a7.val :: a.a6.val :: a.a5.val :: (0 : Felt) :: (0 : Felt) :: (0 : Felt) :: rest)
    ⟨c₄ :: a.a4.val :: b.a0.val :: (0 : Felt) ::
     b.a0.val :: a.a7.val :: a.a6.val :: a.a5.val :: (0 : Felt) :: (0 : Felt) :: (0 : Felt) :: rest,
     mem, frame :: frames, adv⟩
    rfl hc₄ (U256.a4_isU32 a) (U256.a0_isU32 b) h0u
  simp only [MidenState.withStack] at hms1
  rw [hms1]; clear hms1; dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1, movdn 5
  miden_swap
  miden_movdn
  -- Stack: [c₅, b0, a7, a6, a5, l₄, 0, 0, 0] ++ rest
  -- === Mulstep 2: c₅ × a5 ===
  have hc₅u : (mulstepCarry c₄ a.a4.val b.a0.val 0).isU32 = true :=
    mulstep_carry_isU32 c₄ a.a4.val b.a0.val 0 hc₄ (U256.a4_isU32 a) (U256.a0_isU32 b) h0u
  miden_dup    -- dup 1
  miden_movup  -- movup 5
  miden_movup  -- movup 9
  miden_swap   -- swap 3
  -- Stack: [c₅, a5, b0, 0, b0, a7, a6, l₄, 0, 0] ++ rest
  have hms2 := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    (mulstepCarry c₄ a.a4.val b.a0.val 0) (a.a5.val) (b.a0.val) (0 : Felt)
    (b.a0.val :: a.a7.val :: a.a6.val ::
     mulstepLo c₄ a.a4.val b.a0.val 0 :: (0 : Felt) :: (0 : Felt) :: rest)
    ⟨mulstepCarry c₄ a.a4.val b.a0.val 0 :: a.a5.val :: b.a0.val :: (0 : Felt) ::
     b.a0.val :: a.a7.val :: a.a6.val ::
     mulstepLo c₄ a.a4.val b.a0.val 0 :: (0 : Felt) :: (0 : Felt) :: rest,
     mem, frame :: frames, adv⟩
    rfl hc₅u (U256.a5_isU32 a) (U256.a0_isU32 b) h0u
  simp only [MidenState.withStack] at hms2
  rw [hms2]; clear hms2; dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1, movdn 4
  miden_swap
  miden_movdn
  simp only [pure, Pure.pure]

set_option maxHeartbeats 32000000 in
/-- Part B2: last 2 individual mulsteps for b0 × a[6..7], store to locals 20.
    Input stack:  [c₆, b0, a7, a6, l₅, l₄, 0, 0] ++ rest
    Output stack: rest -/
private theorem wm_r1b2_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (c₆ : Felt) (hc₆ : c₆.isU32 = true) (l₅ l₄ : Felt) :
    let la := frame.localAddr
    let c₇ := mulstepCarry c₆ a.a6.val b.a0.val 0
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨c₆ :: b.a0.val :: a.a7.val :: a.a6.val :: l₅ :: l₄ :: (0 : Felt) :: (0 : Felt) :: rest,
       mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_r1b2) =
    some ⟨rest,
          fun i =>
            if i = la 20 + 3 then mulstepLo c₇ a.a7.val b.a0.val 0
            else if i = la 20 + 2 then mulstepLo c₆ a.a6.val b.a0.val 0
            else if i = la 20 + 1 then l₅
            else if i = la 20 then l₄
            else mem i,
          frame :: frames, adv⟩ := by
  unfold wm_r1b2 execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  have h0u : (0 : Felt).isU32 = true := by simp [Felt.isU32]
  -- === Mulstep 3: c₆ × a6 ===
  dsimp only [bind, Bind.bind, Option.bind]
  miden_dup    -- dup 1
  miden_movup  -- movup 4
  miden_movup  -- movup 8
  miden_swap   -- swap 3
  -- Stack: [c₆, a6, b0, 0, b0, a7, l₅, l₄, 0] ++ rest
  have hms3 := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    c₆ (a.a6.val) (b.a0.val) (0 : Felt)
    (b.a0.val :: a.a7.val :: l₅ :: l₄ :: (0 : Felt) :: rest)
    ⟨c₆ :: a.a6.val :: b.a0.val :: (0 : Felt) ::
     b.a0.val :: a.a7.val :: l₅ :: l₄ :: (0 : Felt) :: rest,
     mem, frame :: frames, adv⟩
    rfl hc₆ (U256.a6_isU32 a) (U256.a0_isU32 b) h0u
  simp only [MidenState.withStack] at hms3
  rw [hms3]; clear hms3; dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1, movdn 3
  miden_swap
  miden_movdn
  -- Stack: [c₇, b0, a7, l₆, l₅, l₄, 0] ++ rest
  -- === Mulstep 4: c₇ × a7 ===
  have hc₇u : (mulstepCarry c₆ a.a6.val b.a0.val 0).isU32 = true :=
    mulstep_carry_isU32 c₆ a.a6.val b.a0.val 0 hc₆ (U256.a6_isU32 a) (U256.a0_isU32 b) h0u
  miden_swap   -- swap 1
  miden_movup  -- movup 2
  miden_movup  -- movup 6
  miden_swap   -- swap 3
  -- Stack: [c₇, a7, b0, 0, l₆, l₅, l₄] ++ rest
  have hms4 := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    (mulstepCarry c₆ a.a6.val b.a0.val 0) (a.a7.val) (b.a0.val) (0 : Felt)
    (mulstepLo c₆ a.a6.val b.a0.val 0 :: l₅ :: l₄ :: rest)
    ⟨mulstepCarry c₆ a.a6.val b.a0.val 0 :: a.a7.val :: b.a0.val :: (0 : Felt) ::
     mulstepLo c₆ a.a6.val b.a0.val 0 :: l₅ :: l₄ :: rest,
     mem, frame :: frames, adv⟩
    rfl hc₇u (U256.a7_isU32 a) (U256.a0_isU32 b) h0u
  simp only [MidenState.withStack] at hms4
  rw [hms4]; clear hms4; dsimp only [bind, Bind.bind, Option.bind]
  -- drop (remove carry)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- locStorewBe 20
  rw [stepLocStorewBe (halign := by decide) (hbound := by omega)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- dropw
  rw [stepDropw]; simp only [pure, Pure.pure]

set_option maxHeartbeats 16000000 in
/-- Part B: 4 individual mulsteps for b0 × a[4..7], stored to locals 20.
    Input stack:  [a7, a6, a5, a4, c₄, b0] ++ rest
    Output stack: rest -/
private theorem wm_r1b_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (c₄ : Felt) (hc₄ : c₄.isU32 = true)
    (h20_3 : mem (frame.localAddr 20 + 3) = 0)
    (h20_2 : mem (frame.localAddr 20 + 2) = 0)
    (h20_1 : mem (frame.localAddr 20 + 1) = 0)
    (h20_0 : mem (frame.localAddr 20) = 0) :
    let la := frame.localAddr
    let c₅ := mulstepCarry c₄ a.a4.val b.a0.val 0
    let c₆ := mulstepCarry c₅ a.a5.val b.a0.val 0
    let c₇ := mulstepCarry c₆ a.a6.val b.a0.val 0
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val :: c₄ :: b.a0.val :: rest,
       mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_r1b) =
    some ⟨rest,
          fun i =>
            if i = la 20 + 3 then mulstepLo c₇ a.a7.val b.a0.val 0
            else if i = la 20 + 2 then mulstepLo c₆ a.a6.val b.a0.val 0
            else if i = la 20 + 1 then mulstepLo c₅ a.a5.val b.a0.val 0
            else if i = la 20 then mulstepLo c₄ a.a4.val b.a0.val 0
            else mem i,
          frame :: frames, adv⟩ := by
  -- Decompose into two halves
  rw [show (wm_r1b : List Op) = wm_r1b1 ++ wm_r1b2 from wm_r1b_eq_b1_b2]
  rw [execWithEnv_append]
  -- Apply Part B1
  have hc₅u : (mulstepCarry c₄ a.a4.val b.a0.val 0).isU32 = true :=
    mulstep_carry_isU32 c₄ a.a4.val b.a0.val 0 hc₄ (U256.a4_isU32 a) (U256.a0_isU32 b)
      (by simp [Felt.isU32])
  have hc₆u : (mulstepCarry (mulstepCarry c₄ a.a4.val b.a0.val 0) a.a5.val b.a0.val 0).isU32 = true :=
    mulstep_carry_isU32 _ a.a5.val b.a0.val 0 hc₅u (U256.a5_isU32 a) (U256.a0_isU32 b)
      (by simp [Felt.isU32])
  rw [wm_r1b1_correct a b rest mem frame frames adv fuel hnl c₄ hc₄ h20_3 h20_2 h20_1 h20_0]
  simp only [bind, Bind.bind, Option.bind]
  -- Apply Part B2
  rw [wm_r1b2_correct a b rest mem frame frames adv fuel hnl _ hc₆u
    (mulstepLo (mulstepCarry c₄ a.a4.val b.a0.val 0) a.a5.val b.a0.val 0)
    (mulstepLo c₄ a.a4.val b.a0.val 0)]

-- ============================================================================
-- Round 1 correctness (composed from Parts A and B)
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- Round 1: multiply b0 × a[0..7], storing partial products to locals 16 and 20.
    Input stack:  [a7, a6, a5, a4, a3, a2, a1, a0, b0] ++ rest
    Output stack: rest -/
private theorem wm_round1_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (h16_3 : mem (frame.localAddr 16 + 3) = 0)
    (h16_2 : mem (frame.localAddr 16 + 2) = 0)
    (h16_1 : mem (frame.localAddr 16 + 1) = 0)
    (h16_0 : mem (frame.localAddr 16) = 0)
    (h20_3 : mem (frame.localAddr 20 + 3) = 0)
    (h20_2 : mem (frame.localAddr 20 + 2) = 0)
    (h20_1 : mem (frame.localAddr 20 + 1) = 0)
    (h20_0 : mem (frame.localAddr 20) = 0) :
    let la := frame.localAddr
    let c₁ := mulstepCarry 0 a.a0.val b.a0.val 0
    let c₂ := mulstepCarry c₁ a.a1.val b.a0.val 0
    let c₃ := mulstepCarry c₂ a.a2.val b.a0.val 0
    let c₄ := mulstepCarry c₃ a.a3.val b.a0.val 0
    let c₅ := mulstepCarry c₄ a.a4.val b.a0.val 0
    let c₆ := mulstepCarry c₅ a.a5.val b.a0.val 0
    let c₇ := mulstepCarry c₆ a.a6.val b.a0.val 0
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
       a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: b.a0.val :: rest,
       mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_round1) =
    some ⟨rest,
          fun i =>
            if i = la 20 + 3 then mulstepLo c₇ a.a7.val b.a0.val 0
            else if i = la 20 + 2 then mulstepLo c₆ a.a6.val b.a0.val 0
            else if i = la 20 + 1 then mulstepLo c₅ a.a5.val b.a0.val 0
            else if i = la 20 then mulstepLo c₄ a.a4.val b.a0.val 0
            else if i = la 16 + 3 then mulstepLo c₃ a.a3.val b.a0.val 0
            else if i = la 16 + 2 then mulstepLo c₂ a.a2.val b.a0.val 0
            else if i = la 16 + 1 then mulstepLo c₁ a.a1.val b.a0.val 0
            else if i = la 16 then mulstepLo 0 a.a0.val b.a0.val 0
            else mem i,
          frame :: frames, adv⟩ := by
  -- Split into Part A (mulstep4) and Part B (individual mulsteps)
  rw [show (wm_round1 : List Op) = wm_r1a ++ wm_r1b from wm_round1_eq_r1a_r1b]
  rw [execWithEnv_append]
  -- Apply Part A
  rw [wm_r1a_correct a b rest mem frame frames adv fuel hnl h16_3 h16_2 h16_1 h16_0]
  simp only [bind, Bind.bind, Option.bind]
  -- Apply Part B (memory at la(20) passes through the la(16) updates)
  have hc₄u : (mulstepCarry
    (mulstepCarry (mulstepCarry (mulstepCarry 0 a.a0.val b.a0.val 0)
      a.a1.val b.a0.val 0) a.a2.val b.a0.val 0) a.a3.val b.a0.val 0).isU32 = true := by
    apply mulstep_carry_isU32
    · apply mulstep_carry_isU32
      · apply mulstep_carry_isU32
        · apply mulstep_carry_isU32
          · simp [Felt.isU32]
          · exact U256.a0_isU32 a
          · exact U256.a0_isU32 b
          · simp [Felt.isU32]
        · exact U256.a1_isU32 a
        · exact U256.a0_isU32 b
        · simp [Felt.isU32]
      · exact U256.a2_isU32 a
      · exact U256.a0_isU32 b
      · simp [Felt.isU32]
    · exact U256.a3_isU32 a
    · exact U256.a0_isU32 b
    · simp [Felt.isU32]
  rw [wm_r1b_correct a b rest _ frame frames adv fuel hnl _ hc₄u
      (by simp [h20_3]) (by simp [h20_2]) (by simp [h20_1]) (by simp [h20_0])]

-- ============================================================================
-- Round 2 Part A: load + mulstep4 + store la(16) (28 ops)
-- ============================================================================

set_option maxHeartbeats 64000000 in
/-- Round 2 Part A: load partial products and operands, run mulstep4 for b₁ × a[0..3],
    store updated partial products to la(16).
    Input stack: rest
    Output stack: [lo4, a₇, a₆, a₅, a₄, carry4, b₁] ++ rest -/
private theorem wm_r2a_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ : Felt)
    (hp₁ : p₁.isU32 = true) (hp₂ : p₂.isU32 = true) (hp₃ : p₃.isU32 = true)
    (hq₀ : q₀.isU32 = true)
    (h16_3 : mem (frame.localAddr 16 + 3) = p₃)
    (h16_2 : mem (frame.localAddr 16 + 2) = p₂)
    (h16_1 : mem (frame.localAddr 16 + 1) = p₁)
    (h16_0 : mem (frame.localAddr 16) = p₀)
    (h20_3 : mem (frame.localAddr 20 + 3) = q₃)
    (h20_2 : mem (frame.localAddr 20 + 2) = q₂)
    (h20_1 : mem (frame.localAddr 20 + 1) = q₁)
    (h20_0 : mem (frame.localAddr 20) = q₀)
    (h12_3 : mem (frame.localAddr 12 + 3) = a.a3.val)
    (h12_2 : mem (frame.localAddr 12 + 2) = a.a2.val)
    (h12_1 : mem (frame.localAddr 12 + 1) = a.a1.val)
    (h12_0 : mem (frame.localAddr 12) = a.a0.val)
    (h8_3 : mem (frame.localAddr 8 + 3) = a.a7.val)
    (h8_2 : mem (frame.localAddr 8 + 2) = a.a6.val)
    (h8_1 : mem (frame.localAddr 8 + 1) = a.a5.val)
    (h8_0 : mem (frame.localAddr 8) = a.a4.val)
    (h4_3 : mem (frame.localAddr 4 + 3) = b.a3.val)
    (h4_2 : mem (frame.localAddr 4 + 2) = b.a2.val)
    (h4_1 : mem (frame.localAddr 4 + 1) = b.a1.val)
    (h4_0 : mem (frame.localAddr 4) = b.a0.val) :
    let la := frame.localAddr
    let carry1 := mulstepCarry 0 a.a0.val b.a1.val p₁
    let lo1 := mulstepLo 0 a.a0.val b.a1.val p₁
    let carry2 := mulstepCarry carry1 a.a1.val b.a1.val p₂
    let lo2 := mulstepLo carry1 a.a1.val b.a1.val p₂
    let carry3 := mulstepCarry carry2 a.a2.val b.a1.val p₃
    let lo3 := mulstepLo carry2 a.a2.val b.a1.val p₃
    let carry4 := mulstepCarry carry3 a.a3.val b.a1.val q₀
    let lo4 := mulstepLo carry3 a.a3.val b.a1.val q₀
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨rest, mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_r2a) =
    some ⟨lo4 :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val :: carry4 :: b.a1.val :: rest,
          fun i =>
            if i = la 16 + 3 then lo3
            else if i = la 16 + 2 then lo2
            else if i = la 16 + 1 then lo1
            else if i = la 16 then p₀
            else mem i,
          frame :: frames, adv⟩ := by
  -- Split into pre (loads) + post (mulstep4 + store)
  rw [show (wm_r2a : List Op) = wm_r2a_pre ++ wm_r2a_post from rfl]
  rw [execWithEnv_append]
  -- Part A pre: load operands and partial products
  show (do
    let s ← execWithEnv u256ProcEnv (fuel + 3)
      ⟨rest, mem, frame :: frames, adv⟩ (Procedure.ofOps wm_r2a_pre)
    execWithEnv u256ProcEnv (fuel + 3) s (Procedure.ofOps wm_r2a_post)) = _
  -- Prove the pre part
  conv_lhs => rw [show execWithEnv u256ProcEnv (fuel + 3)
      ⟨rest, mem, frame :: frames, adv⟩ (Procedure.ofOps wm_r2a_pre) =
    some ⟨b.a1.val :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
          a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: q₀ :: p₃ :: p₂ :: p₁ :: rest,
          mem, frame :: frames, adv⟩ from by
    unfold wm_r2a_pre execWithEnv Procedure.ofOps
    simp only [List.foldlM, u256ProcEnv]
    dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
    rw [h16_3, h16_2, h16_1, h16_0]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
    rw [h20_3, h20_2, h20_1, h20_0]; dsimp only [bind, Bind.bind, Option.bind]
    miden_movup
    rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
    rw [h12_3, h12_2, h12_1, h12_0]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
    rw [h8_3, h8_2, h8_1, h8_0]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
    rw [h4_3, h4_2, h4_1, h4_0]; dsimp only [bind, Bind.bind, Option.bind]
    miden_movup; miden_movdn; miden_step
    rw [stepDropw]; simp only [pure, Pure.pure]]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Part A post: mulstep4 + post-shuffle + store la(16)
  unfold wm_r2a_post execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- exec "mulstep4"
  have hmul4 := u256_mulstep4_correct
    b.a1.val a.a7.val a.a6.val a.a5.val a.a4.val
    a.a3.val a.a2.val a.a1.val a.a0.val
    q₀ p₃ p₂ p₁ rest
    ⟨b.a1.val :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
     a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: q₀ :: p₃ :: p₂ :: p₁ :: rest,
     mem, frame :: frames, adv⟩
    rfl (U256.a1_isU32 b) (U256.a3_isU32 a) (U256.a2_isU32 a) (U256.a1_isU32 a) (U256.a0_isU32 a)
    hq₀ hp₃ hp₂ hp₁ fuel
  simp only [MidenState.withStack] at hmul4
  rw [hmul4]; clear hmul4; dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 9, movdn 9
  miden_movdn; miden_movdn
  -- swapw 1
  rw [stepSwapw1]; dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 3
  miden_movdn
  -- padw
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 16 (re-load original values)
  rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
  rw [h16_3, h16_2, h16_1, h16_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- push 0
  miden_step
  -- dropw
  rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 3
  miden_movdn
  -- locStorewBe 16
  rw [stepLocStorewBe (halign := by decide) (hbound := by omega)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- dropw
  rw [stepDropw]; simp only [pure, Pure.pure]

-- ============================================================================
-- Round 2 Part B: 3 individual mulsteps for b₁ × a[4..6]
-- ============================================================================

set_option maxHeartbeats 32000000 in
/-- Round 2 Part B1: load la(20), extract, rearrange, 1st individual mulstep.
    Input stack: [lo4, a₇, a₆, a₅, a₄, carry4, b₁] ++ rest
    Output stack: [c₅, b₁, a₇, a₆, a₅, q₃, q₂, l₅, lo4] ++ rest -/
private theorem wm_r2b1_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (lo4 carry4 : Felt) (hcarry4 : carry4.isU32 = true)
    (q₀ q₁ q₂ q₃ : Felt) (hq₁ : q₁.isU32 = true)
    (h20_3 : mem (frame.localAddr 20 + 3) = q₃)
    (h20_2 : mem (frame.localAddr 20 + 2) = q₂)
    (h20_1 : mem (frame.localAddr 20 + 1) = q₁)
    (h20_0 : mem (frame.localAddr 20) = q₀) :
    let c₅ := mulstepCarry carry4 a.a4.val b.a1.val q₁
    let l₅ := mulstepLo carry4 a.a4.val b.a1.val q₁
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨lo4 :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val :: carry4 :: b.a1.val :: rest,
       mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_r2b1) =
    some ⟨c₅ :: b.a1.val :: a.a7.val :: a.a6.val :: a.a5.val :: q₃ :: q₂ :: l₅ :: lo4 :: rest,
          mem, frame :: frames, adv⟩ := by
  unfold wm_r2b1 execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- padw
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 20
  rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
  rw [h20_3, h20_2, h20_1, h20_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- movup 3
  miden_movup
  -- drop
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- swapw 1
  rw [stepSwapw1]; dsimp only [bind, Bind.bind, Option.bind]
  -- movup 9
  miden_movup
  -- movup 9
  miden_movup
  -- dup 1
  miden_dup
  -- movup 6
  miden_movup
  -- movup 9
  miden_movup
  -- swap 3
  miden_swap
  -- exec "mulstep"
  have hms := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    carry4 a.a4.val b.a1.val q₁
    (b.a1.val :: a.a7.val :: a.a6.val :: a.a5.val :: q₃ :: q₂ :: lo4 :: rest)
    ⟨carry4 :: a.a4.val :: b.a1.val :: q₁ ::
     b.a1.val :: a.a7.val :: a.a6.val :: a.a5.val :: q₃ :: q₂ :: lo4 :: rest,
     mem, frame :: frames, adv⟩
    rfl hcarry4 (U256.a4_isU32 a) (U256.a1_isU32 b) hq₁
  simp only [MidenState.withStack] at hms
  rw [hms]; clear hms; dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1
  miden_swap
  -- movdn 7
  miden_movdn
  simp only [pure, Pure.pure]

set_option maxHeartbeats 32000000 in
/-- Round 2 Part B2: 2nd + 3rd individual mulsteps + store to la(20).
    Input stack: [c₅, b₁, a₇, a₆, a₅, q₃, q₂, l₅, lo4] ++ rest
    Output stack: rest -/
private theorem wm_r2b2_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (c₅ q₂ q₃ l₅ lo4 : Felt) (hc₅ : c₅.isU32 = true)
    (hq₂ : q₂.isU32 = true) (hq₃ : q₃.isU32 = true) :
    let la := frame.localAddr
    let c₆ := mulstepCarry c₅ a.a5.val b.a1.val q₂
    let l₆ := mulstepLo c₅ a.a5.val b.a1.val q₂
    let l₇ := mulstepLo c₆ a.a6.val b.a1.val q₃
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨c₅ :: b.a1.val :: a.a7.val :: a.a6.val :: a.a5.val :: q₃ :: q₂ :: l₅ :: lo4 :: rest,
       mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_r2b2) =
    some ⟨rest,
          fun i =>
            if i = la 20 + 3 then l₇
            else if i = la 20 + 2 then l₆
            else if i = la 20 + 1 then l₅
            else if i = la 20 then lo4
            else mem i,
          frame :: frames, adv⟩ := by
  unfold wm_r2b2 execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- === Mulstep 2: c₅ × a₅ with accumulator q₂ ===
  miden_dup    -- dup 1
  miden_movup  -- movup 5
  miden_movup  -- movup 7
  miden_swap   -- swap 3
  have hms2 := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    c₅ a.a5.val b.a1.val q₂
    (b.a1.val :: a.a7.val :: a.a6.val :: q₃ :: l₅ :: lo4 :: rest)
    ⟨c₅ :: a.a5.val :: b.a1.val :: q₂ ::
     b.a1.val :: a.a7.val :: a.a6.val :: q₃ :: l₅ :: lo4 :: rest,
     mem, frame :: frames, adv⟩
    rfl hc₅ (U256.a5_isU32 a) (U256.a1_isU32 b) hq₂
  simp only [MidenState.withStack] at hms2
  rw [hms2]; clear hms2; dsimp only [bind, Bind.bind, Option.bind]
  miden_swap   -- swap 1
  miden_movdn  -- movdn 5
  -- === Mulstep 3: c₆ × a₆ with accumulator q₃ ===
  have hc₆u : (mulstepCarry c₅ a.a5.val b.a1.val q₂).isU32 = true :=
    mulstep_carry_isU32 c₅ a.a5.val b.a1.val q₂ hc₅ (U256.a5_isU32 a) (U256.a1_isU32 b) hq₂
  miden_swap   -- swap 1
  miden_movup  -- movup 3
  miden_movup  -- movup 4
  miden_swap   -- swap 3
  have hms3 := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    (mulstepCarry c₅ a.a5.val b.a1.val q₂) a.a6.val b.a1.val q₃
    (a.a7.val :: mulstepLo c₅ a.a5.val b.a1.val q₂ :: l₅ :: lo4 :: rest)
    ⟨mulstepCarry c₅ a.a5.val b.a1.val q₂ :: a.a6.val :: b.a1.val :: q₃ ::
     a.a7.val :: mulstepLo c₅ a.a5.val b.a1.val q₂ :: l₅ :: lo4 :: rest,
     mem, frame :: frames, adv⟩
    rfl hc₆u (U256.a6_isU32 a) (U256.a1_isU32 b) hq₃
  simp only [MidenState.withStack] at hms3
  rw [hms3]; clear hms3; dsimp only [bind, Bind.bind, Option.bind]
  -- drop (remove carry), swap 1, drop (remove a₇)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  miden_swap
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- locStorewBe 20
  rw [stepLocStorewBe (halign := by decide) (hbound := by omega)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- dropw
  rw [stepDropw]; simp only [pure, Pure.pure]

-- ============================================================================
-- Round 2 Part B composition
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- Round 2 Part B: 3 individual mulsteps for b₁ × a[4..6], store to la(20).
    Input stack: [lo4, a₇, a₆, a₅, a₄, carry4, b₁] ++ rest
    Output stack: rest -/
private theorem wm_r2b_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (lo4 carry4 : Felt) (hcarry4 : carry4.isU32 = true)
    (q₀ q₁ q₂ q₃ : Felt) (hq₁ : q₁.isU32 = true) (hq₂ : q₂.isU32 = true) (hq₃ : q₃.isU32 = true)
    (h20_3 : mem (frame.localAddr 20 + 3) = q₃)
    (h20_2 : mem (frame.localAddr 20 + 2) = q₂)
    (h20_1 : mem (frame.localAddr 20 + 1) = q₁)
    (h20_0 : mem (frame.localAddr 20) = q₀) :
    let la := frame.localAddr
    let c₅ := mulstepCarry carry4 a.a4.val b.a1.val q₁
    let c₆ := mulstepCarry c₅ a.a5.val b.a1.val q₂
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨lo4 :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val :: carry4 :: b.a1.val :: rest,
       mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_r2b) =
    some ⟨rest,
          fun i =>
            if i = la 20 + 3 then mulstepLo c₆ a.a6.val b.a1.val q₃
            else if i = la 20 + 2 then mulstepLo c₅ a.a5.val b.a1.val q₂
            else if i = la 20 + 1 then mulstepLo carry4 a.a4.val b.a1.val q₁
            else if i = la 20 then lo4
            else mem i,
          frame :: frames, adv⟩ := by
  rw [show (wm_r2b : List Op) = wm_r2b1 ++ wm_r2b2 from wm_r2b_eq_b1_b2]
  rw [execWithEnv_append]
  have hc₅u : (mulstepCarry carry4 a.a4.val b.a1.val q₁).isU32 = true :=
    mulstep_carry_isU32 carry4 a.a4.val b.a1.val q₁ hcarry4 (U256.a4_isU32 a) (U256.a1_isU32 b) hq₁
  rw [wm_r2b1_correct a b rest mem frame frames adv fuel hnl lo4 carry4 hcarry4
      q₀ q₁ q₂ q₃ hq₁ h20_3 h20_2 h20_1 h20_0]
  simp only [bind, Bind.bind, Option.bind]
  rw [wm_r2b2_correct a b rest mem frame frames adv fuel hnl _ _ _ _ _ hc₅u hq₂ hq₃]

-- ============================================================================
-- Round 2 correctness
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- Round 2: b₁ × a[0..6] with accumulators from Round 1.
    Input stack: rest
    Output stack: rest
    Memory: la(16) and la(20) updated with Round 2 partial products. -/
private theorem wm_round2_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ : Felt)
    (hp₁ : p₁.isU32 = true) (hp₂ : p₂.isU32 = true) (hp₃ : p₃.isU32 = true)
    (hq₀ : q₀.isU32 = true) (hq₁ : q₁.isU32 = true) (hq₂ : q₂.isU32 = true) (hq₃ : q₃.isU32 = true)
    (h16_3 : mem (frame.localAddr 16 + 3) = p₃)
    (h16_2 : mem (frame.localAddr 16 + 2) = p₂)
    (h16_1 : mem (frame.localAddr 16 + 1) = p₁)
    (h16_0 : mem (frame.localAddr 16) = p₀)
    (h20_3 : mem (frame.localAddr 20 + 3) = q₃)
    (h20_2 : mem (frame.localAddr 20 + 2) = q₂)
    (h20_1 : mem (frame.localAddr 20 + 1) = q₁)
    (h20_0 : mem (frame.localAddr 20) = q₀)
    (h12_3 : mem (frame.localAddr 12 + 3) = a.a3.val)
    (h12_2 : mem (frame.localAddr 12 + 2) = a.a2.val)
    (h12_1 : mem (frame.localAddr 12 + 1) = a.a1.val)
    (h12_0 : mem (frame.localAddr 12) = a.a0.val)
    (h8_3 : mem (frame.localAddr 8 + 3) = a.a7.val)
    (h8_2 : mem (frame.localAddr 8 + 2) = a.a6.val)
    (h8_1 : mem (frame.localAddr 8 + 1) = a.a5.val)
    (h8_0 : mem (frame.localAddr 8) = a.a4.val)
    (h4_3 : mem (frame.localAddr 4 + 3) = b.a3.val)
    (h4_2 : mem (frame.localAddr 4 + 2) = b.a2.val)
    (h4_1 : mem (frame.localAddr 4 + 1) = b.a1.val)
    (h4_0 : mem (frame.localAddr 4) = b.a0.val) :
    let la := frame.localAddr
    let carry1 := mulstepCarry 0 a.a0.val b.a1.val p₁
    let carry2 := mulstepCarry carry1 a.a1.val b.a1.val p₂
    let carry3 := mulstepCarry carry2 a.a2.val b.a1.val p₃
    let carry4 := mulstepCarry carry3 a.a3.val b.a1.val q₀
    let c₅ := mulstepCarry carry4 a.a4.val b.a1.val q₁
    let c₆ := mulstepCarry c₅ a.a5.val b.a1.val q₂
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨rest, mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_round2) =
    some ⟨rest,
          fun i =>
            if i = la 20 + 3 then mulstepLo c₆ a.a6.val b.a1.val q₃
            else if i = la 20 + 2 then mulstepLo c₅ a.a5.val b.a1.val q₂
            else if i = la 20 + 1 then mulstepLo carry4 a.a4.val b.a1.val q₁
            else if i = la 20 then mulstepLo carry3 a.a3.val b.a1.val q₀
            else if i = la 16 + 3 then mulstepLo carry2 a.a2.val b.a1.val p₃
            else if i = la 16 + 2 then mulstepLo carry1 a.a1.val b.a1.val p₂
            else if i = la 16 + 1 then mulstepLo 0 a.a0.val b.a1.val p₁
            else if i = la 16 then p₀
            else mem i,
          frame :: frames, adv⟩ := by
  rw [show (wm_round2 : List Op) = wm_r2a ++ wm_r2b from wm_round2_eq_r2a_r2b]
  rw [execWithEnv_append]
  -- Apply Part A
  rw [wm_r2a_correct a b rest mem frame frames adv fuel hnl
      p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ hp₁ hp₂ hp₃ hq₀
      h16_3 h16_2 h16_1 h16_0 h20_3 h20_2 h20_1 h20_0
      h12_3 h12_2 h12_1 h12_0 h8_3 h8_2 h8_1 h8_0
      h4_3 h4_2 h4_1 h4_0]
  simp only [bind, Bind.bind, Option.bind]
  -- Apply Part B (la(20) reads pass through la(16) updates)
  have hcarry4u : (mulstepCarry
    (mulstepCarry (mulstepCarry (mulstepCarry 0 a.a0.val b.a1.val p₁)
      a.a1.val b.a1.val p₂) a.a2.val b.a1.val p₃) a.a3.val b.a1.val q₀).isU32 = true := by
    apply mulstep_carry_isU32
    · apply mulstep_carry_isU32
      · apply mulstep_carry_isU32
        · apply mulstep_carry_isU32
          · simp [Felt.isU32]
          · exact U256.a0_isU32 a
          · exact U256.a1_isU32 b
          · exact hp₁
        · exact U256.a1_isU32 a
        · exact U256.a1_isU32 b
        · exact hp₂
      · exact U256.a2_isU32 a
      · exact U256.a1_isU32 b
      · exact hp₃
    · exact U256.a3_isU32 a
    · exact U256.a1_isU32 b
    · exact hq₀
  rw [wm_r2b_correct a b rest _ frame frames adv fuel hnl _ _ hcarry4u
      q₀ q₁ q₂ q₃ hq₁ hq₂ hq₃
      (by simp [h20_3]) (by simp [h20_2]) (by simp [h20_1]) (by simp [h20_0])]

-- ============================================================================
-- Round 3 Part A: pre-load + mulstep4 + store la(16)
-- ============================================================================

set_option maxHeartbeats 64000000 in
/-- Round 3 Part A: load accumulators [q₁, q₀, p₃, p₂] and operands, run mulstep4 for b₂ × a[0..3],
    store updated partial products to la(16).
    Input stack: rest
    Output stack: [lo4, lo3, a₇, a₆, a₅, a₄, carry4, b₂] ++ rest -/
private theorem wm_r3a_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ : Felt)
    (hp₂ : p₂.isU32 = true) (hp₃ : p₃.isU32 = true)
    (hq₀ : q₀.isU32 = true) (hq₁ : q₁.isU32 = true)
    (h16_3 : mem (frame.localAddr 16 + 3) = p₃)
    (h16_2 : mem (frame.localAddr 16 + 2) = p₂)
    (h16_1 : mem (frame.localAddr 16 + 1) = p₁)
    (h16_0 : mem (frame.localAddr 16) = p₀)
    (h20_3 : mem (frame.localAddr 20 + 3) = q₃)
    (h20_2 : mem (frame.localAddr 20 + 2) = q₂)
    (h20_1 : mem (frame.localAddr 20 + 1) = q₁)
    (h20_0 : mem (frame.localAddr 20) = q₀)
    (h12_3 : mem (frame.localAddr 12 + 3) = a.a3.val)
    (h12_2 : mem (frame.localAddr 12 + 2) = a.a2.val)
    (h12_1 : mem (frame.localAddr 12 + 1) = a.a1.val)
    (h12_0 : mem (frame.localAddr 12) = a.a0.val)
    (h8_3 : mem (frame.localAddr 8 + 3) = a.a7.val)
    (h8_2 : mem (frame.localAddr 8 + 2) = a.a6.val)
    (h8_1 : mem (frame.localAddr 8 + 1) = a.a5.val)
    (h8_0 : mem (frame.localAddr 8) = a.a4.val)
    (h4_3 : mem (frame.localAddr 4 + 3) = b.a3.val)
    (h4_2 : mem (frame.localAddr 4 + 2) = b.a2.val)
    (h4_1 : mem (frame.localAddr 4 + 1) = b.a1.val)
    (h4_0 : mem (frame.localAddr 4) = b.a0.val) :
    let la := frame.localAddr
    let carry1 := mulstepCarry 0 a.a0.val b.a2.val p₂
    let lo1 := mulstepLo 0 a.a0.val b.a2.val p₂
    let carry2 := mulstepCarry carry1 a.a1.val b.a2.val p₃
    let lo2 := mulstepLo carry1 a.a1.val b.a2.val p₃
    let carry3 := mulstepCarry carry2 a.a2.val b.a2.val q₀
    let lo3 := mulstepLo carry2 a.a2.val b.a2.val q₀
    let carry4 := mulstepCarry carry3 a.a3.val b.a2.val q₁
    let lo4 := mulstepLo carry3 a.a3.val b.a2.val q₁
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨rest, mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_r3a) =
    some ⟨lo4 :: lo3 :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val :: carry4 :: b.a2.val :: rest,
          fun i =>
            if i = la 16 + 3 then lo2
            else if i = la 16 + 2 then lo1
            else if i = la 16 + 1 then p₁
            else if i = la 16 then p₀
            else mem i,
          frame :: frames, adv⟩ := by
  -- Split into pre (loads) + post (mulstep4 + store)
  rw [show (wm_r3a : List Op) = wm_r3a_pre ++ wm_r3a_post from rfl]
  rw [execWithEnv_append]
  -- Part A pre: load accumulators, operands, extract b₂
  show (do
    let s ← execWithEnv u256ProcEnv (fuel + 3)
      ⟨rest, mem, frame :: frames, adv⟩ (Procedure.ofOps wm_r3a_pre)
    execWithEnv u256ProcEnv (fuel + 3) s (Procedure.ofOps wm_r3a_post)) = _
  conv_lhs => rw [show execWithEnv u256ProcEnv (fuel + 3)
      ⟨rest, mem, frame :: frames, adv⟩ (Procedure.ofOps wm_r3a_pre) =
    some ⟨b.a2.val :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
          a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: q₁ :: q₀ :: p₃ :: p₂ :: rest,
          mem, frame :: frames, adv⟩ from by
    unfold wm_r3a_pre execWithEnv Procedure.ofOps
    simp only [List.foldlM, u256ProcEnv]
    dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
    rw [h16_3, h16_2, h16_1, h16_0]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
    rw [h20_3, h20_2, h20_1, h20_0]; dsimp only [bind, Bind.bind, Option.bind]
    miden_movup; miden_movup
    rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
    rw [h12_3, h12_2, h12_1, h12_0]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
    rw [h8_3, h8_2, h8_1, h8_0]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
    rw [h4_3, h4_2, h4_1, h4_0]; dsimp only [bind, Bind.bind, Option.bind]
    miden_swap; miden_movdn; miden_step
    rw [stepDropw]; simp only [pure, Pure.pure]]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Part A post: mulstep4 + post-shuffle + store la(16)
  unfold wm_r3a_post execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- exec "mulstep4"
  have hmul4 := u256_mulstep4_correct
    b.a2.val a.a7.val a.a6.val a.a5.val a.a4.val
    a.a3.val a.a2.val a.a1.val a.a0.val
    q₁ q₀ p₃ p₂ rest
    ⟨b.a2.val :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
     a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: q₁ :: q₀ :: p₃ :: p₂ :: rest,
     mem, frame :: frames, adv⟩
    rfl (U256.a2_isU32 b) (U256.a3_isU32 a) (U256.a2_isU32 a) (U256.a1_isU32 a) (U256.a0_isU32 a)
    hq₁ hq₀ hp₃ hp₂ fuel
  simp only [MidenState.withStack] at hmul4
  rw [hmul4]; clear hmul4; dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 9, movdn 9
  miden_movdn; miden_movdn
  -- swapw 1
  rw [stepSwapw1]; dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 3, movdn 3
  miden_movdn; miden_movdn
  -- padw
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 16 (re-load original values)
  rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
  rw [h16_3, h16_2, h16_1, h16_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- drop, drop (remove p₃, p₂)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 3, movdn 3
  miden_movdn; miden_movdn
  -- locStorewBe 16
  rw [stepLocStorewBe (halign := by decide) (hbound := by omega)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- dropw
  rw [stepDropw]; simp only [pure, Pure.pure]

-- ============================================================================
-- Round 3 Part B: 2 individual mulsteps for b₂ × a[4..5]
-- ============================================================================

set_option maxHeartbeats 32000000 in
/-- Round 3 Part B: load la(20), extract q₂/q₃, run 2 individual mulsteps, store to la(20).
    Input stack: [lo4, lo3, a₇, a₆, a₅, a₄, carry4, b₂] ++ rest
    Output stack: rest -/
private theorem wm_r3b_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (lo4 lo3 carry4 : Felt) (hcarry4 : carry4.isU32 = true)
    (q₀ q₁ q₂ q₃ : Felt) (hq₂ : q₂.isU32 = true) (hq₃ : q₃.isU32 = true)
    (h20_3 : mem (frame.localAddr 20 + 3) = q₃)
    (h20_2 : mem (frame.localAddr 20 + 2) = q₂)
    (h20_1 : mem (frame.localAddr 20 + 1) = q₁)
    (h20_0 : mem (frame.localAddr 20) = q₀) :
    let la := frame.localAddr
    let c₅ := mulstepCarry carry4 a.a4.val b.a2.val q₂
    let c₆ := mulstepCarry c₅ a.a5.val b.a2.val q₃
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨lo4 :: lo3 :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val :: carry4 :: b.a2.val :: rest,
       mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_r3b) =
    some ⟨rest,
          fun i =>
            if i = la 20 + 3 then mulstepLo c₅ a.a5.val b.a2.val q₃
            else if i = la 20 + 2 then mulstepLo carry4 a.a4.val b.a2.val q₂
            else if i = la 20 + 1 then lo4
            else if i = la 20 then lo3
            else mem i,
          frame :: frames, adv⟩ := by
  unfold wm_r3b execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- padw
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 20
  rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
  rw [h20_3, h20_2, h20_1, h20_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- movup 3, movup 3 (bring q₀, q₁ to top)
  miden_movup; miden_movup
  -- drop, drop (remove q₀, q₁)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- swapw 1
  rw [stepSwapw1]; dsimp only [bind, Bind.bind, Option.bind]
  -- movup 9, movup 9
  miden_movup; miden_movup
  -- === Mulstep 1: carry4 × a₄ with accumulator q₂ ===
  miden_dup    -- dup 1
  miden_movup  -- movup 6
  miden_movup  -- movup 8
  miden_swap   -- swap 3
  have hms1 := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    carry4 a.a4.val b.a2.val q₂
    (b.a2.val :: a.a7.val :: a.a6.val :: a.a5.val :: q₃ :: lo4 :: lo3 :: rest)
    ⟨carry4 :: a.a4.val :: b.a2.val :: q₂ ::
     b.a2.val :: a.a7.val :: a.a6.val :: a.a5.val :: q₃ :: lo4 :: lo3 :: rest,
     mem, frame :: frames, adv⟩
    rfl hcarry4 (U256.a4_isU32 a) (U256.a2_isU32 b) hq₂
  simp only [MidenState.withStack] at hms1
  rw [hms1]; clear hms1; dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1, movdn 6
  miden_swap
  miden_movdn
  -- === Mulstep 2: c₅ × a₅ with accumulator q₃ ===
  have hc₅u : (mulstepCarry carry4 a.a4.val b.a2.val q₂).isU32 = true :=
    mulstep_carry_isU32 carry4 a.a4.val b.a2.val q₂ hcarry4 (U256.a4_isU32 a) (U256.a2_isU32 b) hq₂
  miden_dup    -- dup 1
  miden_movup  -- movup 5
  miden_movup  -- movup 6
  miden_swap   -- swap 3
  have hms2 := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    (mulstepCarry carry4 a.a4.val b.a2.val q₂) a.a5.val b.a2.val q₃
    (b.a2.val :: a.a7.val :: a.a6.val :: mulstepLo carry4 a.a4.val b.a2.val q₂ :: lo4 :: lo3 :: rest)
    ⟨mulstepCarry carry4 a.a4.val b.a2.val q₂ :: a.a5.val :: b.a2.val :: q₃ ::
     b.a2.val :: a.a7.val :: a.a6.val :: mulstepLo carry4 a.a4.val b.a2.val q₂ :: lo4 :: lo3 :: rest,
     mem, frame :: frames, adv⟩
    rfl hc₅u (U256.a5_isU32 a) (U256.a2_isU32 b) hq₃
  simp only [MidenState.withStack] at hms2
  rw [hms2]; clear hms2; dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1, swap 1 (net no-op), drop (remove carry)
  miden_swap; miden_swap
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 3
  miden_movdn
  -- drop, drop, drop (remove b₂, a₇, a₆)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- locStorewBe 20
  rw [stepLocStorewBe (halign := by decide) (hbound := by omega)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- dropw
  rw [stepDropw]; simp only [pure, Pure.pure]

-- ============================================================================
-- Round 3 correctness
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- Round 3: b₂ × a[0..5] with accumulators from Round 2.
    Input stack: rest
    Output stack: rest
    Memory: la(16) and la(20) updated with Round 3 partial products. -/
private theorem wm_round3_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ : Felt)
    (hp₂ : p₂.isU32 = true) (hp₃ : p₃.isU32 = true)
    (hq₀ : q₀.isU32 = true) (hq₁ : q₁.isU32 = true)
    (hq₂ : q₂.isU32 = true) (hq₃ : q₃.isU32 = true)
    (h16_3 : mem (frame.localAddr 16 + 3) = p₃)
    (h16_2 : mem (frame.localAddr 16 + 2) = p₂)
    (h16_1 : mem (frame.localAddr 16 + 1) = p₁)
    (h16_0 : mem (frame.localAddr 16) = p₀)
    (h20_3 : mem (frame.localAddr 20 + 3) = q₃)
    (h20_2 : mem (frame.localAddr 20 + 2) = q₂)
    (h20_1 : mem (frame.localAddr 20 + 1) = q₁)
    (h20_0 : mem (frame.localAddr 20) = q₀)
    (h12_3 : mem (frame.localAddr 12 + 3) = a.a3.val)
    (h12_2 : mem (frame.localAddr 12 + 2) = a.a2.val)
    (h12_1 : mem (frame.localAddr 12 + 1) = a.a1.val)
    (h12_0 : mem (frame.localAddr 12) = a.a0.val)
    (h8_3 : mem (frame.localAddr 8 + 3) = a.a7.val)
    (h8_2 : mem (frame.localAddr 8 + 2) = a.a6.val)
    (h8_1 : mem (frame.localAddr 8 + 1) = a.a5.val)
    (h8_0 : mem (frame.localAddr 8) = a.a4.val)
    (h4_3 : mem (frame.localAddr 4 + 3) = b.a3.val)
    (h4_2 : mem (frame.localAddr 4 + 2) = b.a2.val)
    (h4_1 : mem (frame.localAddr 4 + 1) = b.a1.val)
    (h4_0 : mem (frame.localAddr 4) = b.a0.val) :
    let la := frame.localAddr
    let carry1 := mulstepCarry 0 a.a0.val b.a2.val p₂
    let carry2 := mulstepCarry carry1 a.a1.val b.a2.val p₃
    let carry3 := mulstepCarry carry2 a.a2.val b.a2.val q₀
    let carry4 := mulstepCarry carry3 a.a3.val b.a2.val q₁
    let c₅ := mulstepCarry carry4 a.a4.val b.a2.val q₂
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨rest, mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_round3) =
    some ⟨rest,
          fun i =>
            if i = la 20 + 3 then mulstepLo c₅ a.a5.val b.a2.val q₃
            else if i = la 20 + 2 then mulstepLo carry4 a.a4.val b.a2.val q₂
            else if i = la 20 + 1 then mulstepLo carry3 a.a3.val b.a2.val q₁
            else if i = la 20 then mulstepLo carry2 a.a2.val b.a2.val q₀
            else if i = la 16 + 3 then mulstepLo carry1 a.a1.val b.a2.val p₃
            else if i = la 16 + 2 then mulstepLo 0 a.a0.val b.a2.val p₂
            else if i = la 16 + 1 then p₁
            else if i = la 16 then p₀
            else mem i,
          frame :: frames, adv⟩ := by
  rw [show (wm_round3 : List Op) = wm_r3a ++ wm_r3b from wm_round3_eq_r3a_r3b]
  rw [execWithEnv_append]
  -- Apply Part A
  rw [wm_r3a_correct a b rest mem frame frames adv fuel hnl
      p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ hp₂ hp₃ hq₀ hq₁
      h16_3 h16_2 h16_1 h16_0 h20_3 h20_2 h20_1 h20_0
      h12_3 h12_2 h12_1 h12_0 h8_3 h8_2 h8_1 h8_0
      h4_3 h4_2 h4_1 h4_0]
  simp only [bind, Bind.bind, Option.bind]
  -- Apply Part B (la(20) reads pass through la(16) updates)
  have hcarry4u : (mulstepCarry
    (mulstepCarry (mulstepCarry (mulstepCarry 0 a.a0.val b.a2.val p₂)
      a.a1.val b.a2.val p₃) a.a2.val b.a2.val q₀) a.a3.val b.a2.val q₁).isU32 = true := by
    apply mulstep_carry_isU32
    · apply mulstep_carry_isU32
      · apply mulstep_carry_isU32
        · apply mulstep_carry_isU32
          · simp [Felt.isU32]
          · exact U256.a0_isU32 a
          · exact U256.a2_isU32 b
          · exact hp₂
        · exact U256.a1_isU32 a
        · exact U256.a2_isU32 b
        · exact hp₃
      · exact U256.a2_isU32 a
      · exact U256.a2_isU32 b
      · exact hq₀
    · exact U256.a3_isU32 a
    · exact U256.a2_isU32 b
    · exact hq₁
  rw [wm_r3b_correct a b rest _ frame frames adv fuel hnl _ _ _ hcarry4u
      q₀ q₁ q₂ q₃ hq₂ hq₃
      (by simp [h20_3]) (by simp [h20_2]) (by simp [h20_1]) (by simp [h20_0])]

-- ============================================================================
-- Round 4 Part A: pre-load + mulstep4 + store la(16)
-- ============================================================================

set_option maxHeartbeats 64000000 in
/-- Round 4 Part A: load accumulators [q₂, q₁, q₀, p₃] and operands, run mulstep4 for b₃ × a[0..3],
    store updated partial products to la(16).
    Input stack: rest
    Output stack: [lo4, lo3, lo2, a₇, a₆, a₅, a₄, carry4, b₃] ++ rest -/
private theorem wm_r4a_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ : Felt)
    (hp₃ : p₃.isU32 = true)
    (hq₀ : q₀.isU32 = true) (hq₁ : q₁.isU32 = true) (hq₂ : q₂.isU32 = true)
    (h16_3 : mem (frame.localAddr 16 + 3) = p₃)
    (h16_2 : mem (frame.localAddr 16 + 2) = p₂)
    (h16_1 : mem (frame.localAddr 16 + 1) = p₁)
    (h16_0 : mem (frame.localAddr 16) = p₀)
    (h20_3 : mem (frame.localAddr 20 + 3) = q₃)
    (h20_2 : mem (frame.localAddr 20 + 2) = q₂)
    (h20_1 : mem (frame.localAddr 20 + 1) = q₁)
    (h20_0 : mem (frame.localAddr 20) = q₀)
    (h12_3 : mem (frame.localAddr 12 + 3) = a.a3.val)
    (h12_2 : mem (frame.localAddr 12 + 2) = a.a2.val)
    (h12_1 : mem (frame.localAddr 12 + 1) = a.a1.val)
    (h12_0 : mem (frame.localAddr 12) = a.a0.val)
    (h8_3 : mem (frame.localAddr 8 + 3) = a.a7.val)
    (h8_2 : mem (frame.localAddr 8 + 2) = a.a6.val)
    (h8_1 : mem (frame.localAddr 8 + 1) = a.a5.val)
    (h8_0 : mem (frame.localAddr 8) = a.a4.val)
    (h4_3 : mem (frame.localAddr 4 + 3) = b.a3.val)
    (h4_2 : mem (frame.localAddr 4 + 2) = b.a2.val)
    (h4_1 : mem (frame.localAddr 4 + 1) = b.a1.val)
    (h4_0 : mem (frame.localAddr 4) = b.a0.val) :
    let la := frame.localAddr
    let carry1 := mulstepCarry 0 a.a0.val b.a3.val p₃
    let lo1 := mulstepLo 0 a.a0.val b.a3.val p₃
    let carry2 := mulstepCarry carry1 a.a1.val b.a3.val q₀
    let carry3 := mulstepCarry carry2 a.a2.val b.a3.val q₁
    let lo3 := mulstepLo carry2 a.a2.val b.a3.val q₁
    let carry4 := mulstepCarry carry3 a.a3.val b.a3.val q₂
    let lo4 := mulstepLo carry3 a.a3.val b.a3.val q₂
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨rest, mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_r4a) =
    some ⟨lo4 :: lo3 :: mulstepLo carry1 a.a1.val b.a3.val q₀ ::
          a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val :: carry4 :: b.a3.val :: rest,
          fun i =>
            if i = la 16 + 3 then lo1
            else if i = la 16 + 2 then p₂
            else if i = la 16 + 1 then p₁
            else if i = la 16 then p₀
            else mem i,
          frame :: frames, adv⟩ := by
  -- Split into pre (loads) + post (mulstep4 + store)
  rw [show (wm_r4a : List Op) = wm_r4a_pre ++ wm_r4a_post from rfl]
  rw [execWithEnv_append]
  -- Part A pre: load accumulators, operands, extract b₃
  show (do
    let s ← execWithEnv u256ProcEnv (fuel + 3)
      ⟨rest, mem, frame :: frames, adv⟩ (Procedure.ofOps wm_r4a_pre)
    execWithEnv u256ProcEnv (fuel + 3) s (Procedure.ofOps wm_r4a_post)) = _
  conv_lhs => rw [show execWithEnv u256ProcEnv (fuel + 3)
      ⟨rest, mem, frame :: frames, adv⟩ (Procedure.ofOps wm_r4a_pre) =
    some ⟨b.a3.val :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
          a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: q₂ :: q₁ :: q₀ :: p₃ :: rest,
          mem, frame :: frames, adv⟩ from by
    unfold wm_r4a_pre execWithEnv Procedure.ofOps
    simp only [List.foldlM, u256ProcEnv]
    dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
    rw [h16_3, h16_2, h16_1, h16_0]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
    rw [h20_3, h20_2, h20_1, h20_0]; dsimp only [bind, Bind.bind, Option.bind]
    miden_movup; miden_movup; miden_movup
    rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
    rw [h12_3, h12_2, h12_1, h12_0]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
    rw [h8_3, h8_2, h8_1, h8_0]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
    rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
    rw [h4_3, h4_2, h4_1, h4_0]; dsimp only [bind, Bind.bind, Option.bind]
    miden_movdn; miden_step
    rw [stepDropw]; simp only [pure, Pure.pure]]
  dsimp only [bind, Bind.bind, Option.bind]
  -- Part A post: mulstep4 + post-shuffle + store la(16)
  unfold wm_r4a_post execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- exec "mulstep4"
  have hmul4 := u256_mulstep4_correct
    b.a3.val a.a7.val a.a6.val a.a5.val a.a4.val
    a.a3.val a.a2.val a.a1.val a.a0.val
    q₂ q₁ q₀ p₃ rest
    ⟨b.a3.val :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
     a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: q₂ :: q₁ :: q₀ :: p₃ :: rest,
     mem, frame :: frames, adv⟩
    rfl (U256.a3_isU32 b) (U256.a3_isU32 a) (U256.a2_isU32 a) (U256.a1_isU32 a) (U256.a0_isU32 a)
    hq₂ hq₁ hq₀ hp₃ fuel
  simp only [MidenState.withStack] at hmul4
  rw [hmul4]; clear hmul4; dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 9, movdn 9
  miden_movdn; miden_movdn
  -- swapw 1
  rw [stepSwapw1]; dsimp only [bind, Bind.bind, Option.bind]
  -- movup 3
  miden_movup
  -- padw
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 16 (re-load original values)
  rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
  rw [h16_3, h16_2, h16_1, h16_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- drop (remove p₃)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- movup 3
  miden_movup
  -- locStorewBe 16
  rw [stepLocStorewBe (halign := by decide) (hbound := by omega)]
  dsimp only [bind, Bind.bind, Option.bind]
  -- dropw
  rw [stepDropw]; simp only [pure, Pure.pure]

-- ============================================================================
-- Round 4 Part B: 1 individual mulstep for b₃ × a₄
-- ============================================================================

set_option maxHeartbeats 32000000 in
/-- Round 4 Part B: load la(20), extract q₃, run 1 mulstep, cleanup.
    Input stack: [lo4, lo3, lo2, a₇, a₆, a₅, a₄, carry4, b₃] ++ rest
    Output stack: [l₅, lo4, lo3, lo2] ++ rest -/
private theorem wm_r4b_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (lo4 lo3 lo2 carry4 : Felt) (hcarry4 : carry4.isU32 = true)
    (q₀ q₁ q₂ q₃ : Felt) (hq₃ : q₃.isU32 = true)
    (h20_3 : mem (frame.localAddr 20 + 3) = q₃)
    (h20_2 : mem (frame.localAddr 20 + 2) = q₂)
    (h20_1 : mem (frame.localAddr 20 + 1) = q₁)
    (h20_0 : mem (frame.localAddr 20) = q₀) :
    let l₅ := mulstepLo carry4 a.a4.val b.a3.val q₃
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨lo4 :: lo3 :: lo2 :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
       carry4 :: b.a3.val :: rest,
       mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_r4b) =
    some ⟨l₅ :: lo4 :: lo3 :: lo2 :: rest,
          mem, frame :: frames, adv⟩ := by
  unfold wm_r4b execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- padw
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 20
  rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
  rw [h20_3, h20_2, h20_1, h20_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 3 (q₃ to position 3)
  miden_movdn
  -- push 0
  miden_step
  -- dropw (removes 0, q₂, q₁, q₀ → keeps q₃)
  rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
  -- swapw 1
  rw [stepSwapw1]; dsimp only [bind, Bind.bind, Option.bind]
  -- movup 9, movup 9
  miden_movup; miden_movup
  -- swap 1
  miden_swap
  -- movup 5
  miden_movup
  -- movup 6
  miden_movup
  -- swap 3
  miden_swap
  -- exec "mulstep"
  have hms := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    carry4 a.a4.val b.a3.val q₃
    (a.a7.val :: a.a6.val :: a.a5.val :: lo4 :: lo3 :: lo2 :: rest)
    ⟨carry4 :: a.a4.val :: b.a3.val :: q₃ ::
     a.a7.val :: a.a6.val :: a.a5.val :: lo4 :: lo3 :: lo2 :: rest,
     mem, frame :: frames, adv⟩
    rfl hcarry4 (U256.a4_isU32 a) (U256.a3_isU32 b) hq₃
  simp only [MidenState.withStack] at hms
  rw [hms]; clear hms; dsimp only [bind, Bind.bind, Option.bind]
  -- drop (remove carry)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 3
  miden_movdn
  -- push 0
  miden_step
  -- dropw (removes 0, a₇, a₆, a₅)
  rw [stepDropw]; simp only [pure, Pure.pure]

-- ============================================================================
-- Round 4 correctness
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- Round 4: b₃ × a[0..4] with accumulators from Round 3.
    Input stack: rest
    Output stack: [l₅, lo4, lo3, lo2] ++ rest
    Memory: la(16) position 3 updated. -/
private theorem wm_round4_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ : Felt)
    (hp₃ : p₃.isU32 = true)
    (hq₀ : q₀.isU32 = true) (hq₁ : q₁.isU32 = true)
    (hq₂ : q₂.isU32 = true) (hq₃ : q₃.isU32 = true)
    (h16_3 : mem (frame.localAddr 16 + 3) = p₃)
    (h16_2 : mem (frame.localAddr 16 + 2) = p₂)
    (h16_1 : mem (frame.localAddr 16 + 1) = p₁)
    (h16_0 : mem (frame.localAddr 16) = p₀)
    (h20_3 : mem (frame.localAddr 20 + 3) = q₃)
    (h20_2 : mem (frame.localAddr 20 + 2) = q₂)
    (h20_1 : mem (frame.localAddr 20 + 1) = q₁)
    (h20_0 : mem (frame.localAddr 20) = q₀)
    (h12_3 : mem (frame.localAddr 12 + 3) = a.a3.val)
    (h12_2 : mem (frame.localAddr 12 + 2) = a.a2.val)
    (h12_1 : mem (frame.localAddr 12 + 1) = a.a1.val)
    (h12_0 : mem (frame.localAddr 12) = a.a0.val)
    (h8_3 : mem (frame.localAddr 8 + 3) = a.a7.val)
    (h8_2 : mem (frame.localAddr 8 + 2) = a.a6.val)
    (h8_1 : mem (frame.localAddr 8 + 1) = a.a5.val)
    (h8_0 : mem (frame.localAddr 8) = a.a4.val)
    (h4_3 : mem (frame.localAddr 4 + 3) = b.a3.val)
    (h4_2 : mem (frame.localAddr 4 + 2) = b.a2.val)
    (h4_1 : mem (frame.localAddr 4 + 1) = b.a1.val)
    (h4_0 : mem (frame.localAddr 4) = b.a0.val) :
    let la := frame.localAddr
    let carry1 := mulstepCarry 0 a.a0.val b.a3.val p₃
    let carry2 := mulstepCarry carry1 a.a1.val b.a3.val q₀
    let carry3 := mulstepCarry carry2 a.a2.val b.a3.val q₁
    let carry4 := mulstepCarry carry3 a.a3.val b.a3.val q₂
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨rest, mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_round4) =
    some ⟨mulstepLo carry4 a.a4.val b.a3.val q₃ ::
          mulstepLo carry3 a.a3.val b.a3.val q₂ ::
          mulstepLo carry2 a.a2.val b.a3.val q₁ ::
          mulstepLo carry1 a.a1.val b.a3.val q₀ :: rest,
          fun i =>
            if i = la 16 + 3 then mulstepLo 0 a.a0.val b.a3.val p₃
            else if i = la 16 + 2 then p₂
            else if i = la 16 + 1 then p₁
            else if i = la 16 then p₀
            else mem i,
          frame :: frames, adv⟩ := by
  rw [show (wm_round4 : List Op) = wm_r4a ++ wm_r4b from wm_round4_eq_r4a_r4b]
  rw [execWithEnv_append]
  -- Apply Part A
  rw [wm_r4a_correct a b rest mem frame frames adv fuel hnl
      p₀ p₁ p₂ p₃ q₀ q₁ q₂ q₃ hp₃ hq₀ hq₁ hq₂
      h16_3 h16_2 h16_1 h16_0 h20_3 h20_2 h20_1 h20_0
      h12_3 h12_2 h12_1 h12_0 h8_3 h8_2 h8_1 h8_0
      h4_3 h4_2 h4_1 h4_0]
  simp only [bind, Bind.bind, Option.bind]
  -- Apply Part B (la(20) reads pass through la(16) updates)
  have hcarry4u : (mulstepCarry
    (mulstepCarry (mulstepCarry (mulstepCarry 0 a.a0.val b.a3.val p₃)
      a.a1.val b.a3.val q₀) a.a2.val b.a3.val q₁) a.a3.val b.a3.val q₂).isU32 = true := by
    apply mulstep_carry_isU32
    · apply mulstep_carry_isU32
      · apply mulstep_carry_isU32
        · apply mulstep_carry_isU32
          · simp [Felt.isU32]
          · exact U256.a0_isU32 a
          · exact U256.a3_isU32 b
          · exact hp₃
        · exact U256.a1_isU32 a
        · exact U256.a3_isU32 b
        · exact hq₀
      · exact U256.a2_isU32 a
      · exact U256.a3_isU32 b
      · exact hq₁
    · exact U256.a3_isU32 a
    · exact U256.a3_isU32 b
    · exact hq₂
  rw [wm_r4b_correct a b rest _ frame frames adv fuel hnl _ _ _ _ hcarry4u
      q₀ q₁ q₂ q₃ hq₃
      (by simp [h20_3]) (by simp [h20_2]) (by simp [h20_1]) (by simp [h20_0])]

-- ============================================================================
-- Round 5 correctness
-- ============================================================================

set_option maxHeartbeats 32000000 in
/-- Round 5: b₄ × a[0..3] using mulstep4 with stack accumulators.
    Input stack: [l₅, lo4, lo3, lo2] ++ rest
    Output stack: [lo4', lo3', lo2', lo1'] ++ rest -/
private theorem wm_round5_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (l₅ lo4 lo3 lo2 : Felt)
    (hl₅ : l₅.isU32 = true) (hlo4 : lo4.isU32 = true)
    (hlo3 : lo3.isU32 = true) (hlo2 : lo2.isU32 = true)
    (h12_3 : mem (frame.localAddr 12 + 3) = a.a3.val)
    (h12_2 : mem (frame.localAddr 12 + 2) = a.a2.val)
    (h12_1 : mem (frame.localAddr 12 + 1) = a.a1.val)
    (h12_0 : mem (frame.localAddr 12) = a.a0.val)
    (h8_3 : mem (frame.localAddr 8 + 3) = a.a7.val)
    (h8_2 : mem (frame.localAddr 8 + 2) = a.a6.val)
    (h8_1 : mem (frame.localAddr 8 + 1) = a.a5.val)
    (h8_0 : mem (frame.localAddr 8) = a.a4.val)
    (h0_3 : mem (frame.localAddr 0 + 3) = b.a7.val)
    (h0_2 : mem (frame.localAddr 0 + 2) = b.a6.val)
    (h0_1 : mem (frame.localAddr 0 + 1) = b.a5.val)
    (h0_0 : mem (frame.localAddr 0) = b.a4.val) :
    let carry1 := mulstepCarry 0 a.a0.val b.a4.val lo2
    let carry2 := mulstepCarry carry1 a.a1.val b.a4.val lo3
    let carry3 := mulstepCarry carry2 a.a2.val b.a4.val lo4
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨l₅ :: lo4 :: lo3 :: lo2 :: rest, mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_round5) =
    some ⟨mulstepLo carry3 a.a3.val b.a4.val l₅ ::
          mulstepLo carry2 a.a2.val b.a4.val lo4 ::
          mulstepLo carry1 a.a1.val b.a4.val lo3 ::
          mulstepLo 0 a.a0.val b.a4.val lo2 :: rest,
          mem, frame :: frames, adv⟩ := by
  unfold wm_round5 execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- padw
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 12
  rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
  rw [h12_3, h12_2, h12_1, h12_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- padw
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 8
  rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
  rw [h8_3, h8_2, h8_1, h8_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- padw
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 0
  rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
  rw [h0_3, h0_2, h0_1, h0_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- push 0
  miden_step
  -- dropw
  rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
  -- exec "mulstep4"
  have hmul4 := u256_mulstep4_correct
    b.a4.val a.a7.val a.a6.val a.a5.val a.a4.val
    a.a3.val a.a2.val a.a1.val a.a0.val
    l₅ lo4 lo3 lo2 rest
    ⟨b.a4.val :: a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
     a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: l₅ :: lo4 :: lo3 :: lo2 :: rest,
     mem, frame :: frames, adv⟩
    rfl (U256.a4_isU32 b) (U256.a3_isU32 a) (U256.a2_isU32 a) (U256.a1_isU32 a) (U256.a0_isU32 a)
    hl₅ hlo4 hlo3 hlo2 fuel
  simp only [MidenState.withStack] at hmul4
  rw [hmul4]; clear hmul4; dsimp only [bind, Bind.bind, Option.bind]
  -- dropw (removes carry4, b₄, a₇, a₆)
  rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
  -- drop (removes a₅)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- drop (removes a₄)
  rw [stepDrop]; simp only [pure, Pure.pure]

-- ============================================================================
-- Epilogue: b₅ × a[0..2] correctness
-- ============================================================================

set_option maxHeartbeats 32000000 in
/-- Epilogue b₅: 3 individual mulsteps for b₅ × a[0..2].
    Input stack: [L₇, L₆, L₅, L₄] ++ rest
    Output stack: [l₇', l₆', l₅', L₄] ++ rest -/
private theorem wm_ep_b5_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (L₇ L₆ L₅ L₄ : Felt)
    (hL₅ : L₅.isU32 = true) (hL₆ : L₆.isU32 = true) (hL₇ : L₇.isU32 = true)
    (h12_3 : mem (frame.localAddr 12 + 3) = a.a3.val)
    (h12_2 : mem (frame.localAddr 12 + 2) = a.a2.val)
    (h12_1 : mem (frame.localAddr 12 + 1) = a.a1.val)
    (h12_0 : mem (frame.localAddr 12) = a.a0.val)
    (h0_3 : mem (frame.localAddr 0 + 3) = b.a7.val)
    (h0_2 : mem (frame.localAddr 0 + 2) = b.a6.val)
    (h0_1 : mem (frame.localAddr 0 + 1) = b.a5.val)
    (h0_0 : mem (frame.localAddr 0) = b.a4.val) :
    let c₁ := mulstepCarry 0 a.a0.val b.a5.val L₅
    let c₂ := mulstepCarry c₁ b.a5.val a.a1.val L₆
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨L₇ :: L₆ :: L₅ :: L₄ :: rest, mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_ep_b5) =
    some ⟨mulstepLo c₂ a.a2.val b.a5.val L₇ ::
          mulstepLo c₁ b.a5.val a.a1.val L₆ ::
          mulstepLo 0 a.a0.val b.a5.val L₅ :: L₄ :: rest,
          mem, frame :: frames, adv⟩ := by
  unfold wm_ep_b5 execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- padw
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 12
  rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
  rw [h12_3, h12_2, h12_1, h12_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- padw
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 0
  rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
  rw [h0_3, h0_2, h0_1, h0_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- movup 2 (bring b₅ to top)
  miden_movup
  -- movdn 3
  miden_movdn
  -- push 0
  miden_step
  -- dropw (removes [0, b₇, b₆, b₄])
  rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
  -- Stack: [b₅, a₃, a₂, a₁, a₀, L₇, L₆, L₅, L₄] ++ rest
  -- movup 7 (bring L₅ to top)
  miden_movup
  -- dup 1 (duplicate b₅)
  miden_dup
  -- movup 6 (bring a₀)
  miden_movup
  -- push 0
  miden_step
  -- Stack: [0, a₀, b₅, L₅, b₅, a₃, a₂, a₁, L₇, L₆, L₄] ++ rest
  -- === Mulstep 1: mulstep(0, a₀, b₅, L₅) ===
  have h0u : (0 : Felt).isU32 = true := by simp [Felt.isU32]
  have hms1 := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    (0 : Felt) a.a0.val b.a5.val L₅
    (b.a5.val :: a.a3.val :: a.a2.val :: a.a1.val :: L₇ :: L₆ :: L₄ :: rest)
    ⟨(0 : Felt) :: a.a0.val :: b.a5.val :: L₅ ::
     b.a5.val :: a.a3.val :: a.a2.val :: a.a1.val :: L₇ :: L₆ :: L₄ :: rest,
     mem, frame :: frames, adv⟩
    rfl h0u (U256.a0_isU32 a) (U256.a5_isU32 b) hL₅
  simp only [MidenState.withStack] at hms1
  rw [hms1]; clear hms1; dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1, movdn 7
  miden_swap
  miden_movdn
  -- Stack: [c₁, b₅, a₃, a₂, a₁, L₇, L₆, l₅', L₄] ++ rest
  -- === Mulstep 2 setup: movup 4, dup 2, movup 7, swap 3 ===
  have hc₁u : (mulstepCarry 0 a.a0.val b.a5.val L₅).isU32 = true :=
    mulstep_carry_isU32 0 a.a0.val b.a5.val L₅ h0u (U256.a0_isU32 a) (U256.a5_isU32 b) hL₅
  miden_movup  -- movup 4 (bring a₁)
  miden_dup    -- dup 2 (duplicate b₅)
  miden_movup  -- movup 7 (bring L₆)
  miden_swap   -- swap 3
  -- Stack: [c₁, b₅, a₁, L₆, b₅, a₃, a₂, L₇, l₅', L₄] ++ rest
  -- === Mulstep 2: mulstep(c₁, b₅, a₁, L₆) ===
  have hms2 := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    (mulstepCarry 0 a.a0.val b.a5.val L₅) b.a5.val a.a1.val L₆
    (b.a5.val :: a.a3.val :: a.a2.val :: L₇ ::
     mulstepLo 0 a.a0.val b.a5.val L₅ :: L₄ :: rest)
    ⟨mulstepCarry 0 a.a0.val b.a5.val L₅ :: b.a5.val :: a.a1.val :: L₆ ::
     b.a5.val :: a.a3.val :: a.a2.val :: L₇ ::
     mulstepLo 0 a.a0.val b.a5.val L₅ :: L₄ :: rest,
     mem, frame :: frames, adv⟩
    rfl hc₁u (U256.a5_isU32 b) (U256.a1_isU32 a) hL₆
  simp only [MidenState.withStack] at hms2
  rw [hms2]; clear hms2; dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1, movdn 5
  miden_swap
  miden_movdn
  -- Stack: [c₂, b₅, a₃, a₂, L₇, l₆', l₅', L₄] ++ rest
  -- === Mulstep 3 setup: swap 1, movup 3, movup 4, swap 3 ===
  have hc₂u : (mulstepCarry (mulstepCarry 0 a.a0.val b.a5.val L₅) b.a5.val a.a1.val L₆).isU32 = true :=
    mulstep_carry_isU32 _ b.a5.val a.a1.val L₆ hc₁u (U256.a5_isU32 b) (U256.a1_isU32 a) hL₆
  miden_swap   -- swap 1
  miden_movup  -- movup 3 (bring a₂)
  miden_movup  -- movup 4 (bring L₇)
  miden_swap   -- swap 3
  -- Stack: [c₂, a₂, b₅, L₇, a₃, l₆', l₅', L₄] ++ rest
  -- === Mulstep 3: mulstep(c₂, a₂, b₅, L₇) ===
  have hms3 := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    (mulstepCarry (mulstepCarry 0 a.a0.val b.a5.val L₅) b.a5.val a.a1.val L₆)
    a.a2.val b.a5.val L₇
    (a.a3.val :: mulstepLo (mulstepCarry 0 a.a0.val b.a5.val L₅) b.a5.val a.a1.val L₆ ::
     mulstepLo 0 a.a0.val b.a5.val L₅ :: L₄ :: rest)
    ⟨mulstepCarry (mulstepCarry 0 a.a0.val b.a5.val L₅) b.a5.val a.a1.val L₆ ::
     a.a2.val :: b.a5.val :: L₇ ::
     a.a3.val :: mulstepLo (mulstepCarry 0 a.a0.val b.a5.val L₅) b.a5.val a.a1.val L₆ ::
     mulstepLo 0 a.a0.val b.a5.val L₅ :: L₄ :: rest,
     mem, frame :: frames, adv⟩
    rfl hc₂u (U256.a2_isU32 a) (U256.a5_isU32 b) hL₇
  simp only [MidenState.withStack] at hms3
  rw [hms3]; clear hms3; dsimp only [bind, Bind.bind, Option.bind]
  -- drop (remove carry)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1
  miden_swap
  -- drop (remove a₃)
  rw [stepDrop]; simp only [pure, Pure.pure]

-- ============================================================================
-- Epilogue: b₆ × a[0..1] correctness
-- ============================================================================

set_option maxHeartbeats 32000000 in
/-- Epilogue b₆: 2 individual mulsteps for b₆ × a[0..1].
    Input stack: [L₇, L₆, L₅, L₄] ++ rest
    Output stack: [l₇', l₆', L₅, L₄] ++ rest -/
private theorem wm_ep_b6_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (L₇ L₆ L₅ L₄ : Felt) (hL₆ : L₆.isU32 = true) (hL₇ : L₇.isU32 = true)
    (h12_3 : mem (frame.localAddr 12 + 3) = a.a3.val)
    (h12_2 : mem (frame.localAddr 12 + 2) = a.a2.val)
    (h12_1 : mem (frame.localAddr 12 + 1) = a.a1.val)
    (h12_0 : mem (frame.localAddr 12) = a.a0.val)
    (h0_3 : mem (frame.localAddr 0 + 3) = b.a7.val)
    (h0_2 : mem (frame.localAddr 0 + 2) = b.a6.val)
    (h0_1 : mem (frame.localAddr 0 + 1) = b.a5.val)
    (h0_0 : mem (frame.localAddr 0) = b.a4.val) :
    let c₁ := mulstepCarry 0 a.a0.val b.a6.val L₆
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨L₇ :: L₆ :: L₅ :: L₄ :: rest, mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_ep_b6) =
    some ⟨mulstepLo c₁ a.a1.val b.a6.val L₇ ::
          mulstepLo 0 a.a0.val b.a6.val L₆ :: L₅ :: L₄ :: rest,
          mem, frame :: frames, adv⟩ := by
  unfold wm_ep_b6 execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- padw + locLoadwBe 12
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
  rw [h12_3, h12_2, h12_1, h12_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- padw + locLoadwBe 0
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
  rw [h0_3, h0_2, h0_1, h0_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1 (bring b₆ to top)
  miden_swap
  -- movdn 3
  miden_movdn
  -- push 0
  miden_step
  -- dropw (removes [0, b₇, b₅, b₄])
  rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
  -- Stack: [b₆, a₃, a₂, a₁, a₀, L₇, L₆, L₅, L₄] ++ rest
  -- movup 6 (bring L₆)
  miden_movup
  -- dup 1 (duplicate b₆)
  miden_dup
  -- movup 6 (bring a₀)
  miden_movup
  -- push 0
  miden_step
  -- Stack: [0, a₀, b₆, L₆, b₆, a₃, a₂, a₁, L₇, L₅, L₄] ++ rest
  -- === Mulstep 1: mulstep(0, a₀, b₆, L₆) ===
  have h0u : (0 : Felt).isU32 = true := by simp [Felt.isU32]
  have hms1 := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    (0 : Felt) a.a0.val b.a6.val L₆
    (b.a6.val :: a.a3.val :: a.a2.val :: a.a1.val :: L₇ :: L₅ :: L₄ :: rest)
    ⟨(0 : Felt) :: a.a0.val :: b.a6.val :: L₆ ::
     b.a6.val :: a.a3.val :: a.a2.val :: a.a1.val :: L₇ :: L₅ :: L₄ :: rest,
     mem, frame :: frames, adv⟩
    rfl h0u (U256.a0_isU32 a) (U256.a6_isU32 b) hL₆
  simp only [MidenState.withStack] at hms1
  rw [hms1]; clear hms1; dsimp only [bind, Bind.bind, Option.bind]
  -- swap 1, movdn 6
  miden_swap
  miden_movdn
  -- Stack: [c₁, b₆, a₃, a₂, a₁, L₇, l₆', L₅, L₄] ++ rest
  -- === Mulstep 2 setup: swap 1, movup 4, movup 5, swap 3 ===
  have hc₁u : (mulstepCarry 0 a.a0.val b.a6.val L₆).isU32 = true :=
    mulstep_carry_isU32 0 a.a0.val b.a6.val L₆ h0u (U256.a0_isU32 a) (U256.a6_isU32 b) hL₆
  miden_swap   -- swap 1
  miden_movup  -- movup 4 (bring a₁)
  miden_movup  -- movup 5 (bring L₇)
  miden_swap   -- swap 3
  -- Stack: [c₁, a₁, b₆, L₇, a₃, a₂, l₆', L₅, L₄] ++ rest
  -- === Mulstep 2: mulstep(c₁, a₁, b₆, L₇) ===
  have hms2 := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    (mulstepCarry 0 a.a0.val b.a6.val L₆) a.a1.val b.a6.val L₇
    (a.a3.val :: a.a2.val :: mulstepLo 0 a.a0.val b.a6.val L₆ :: L₅ :: L₄ :: rest)
    ⟨mulstepCarry 0 a.a0.val b.a6.val L₆ :: a.a1.val :: b.a6.val :: L₇ ::
     a.a3.val :: a.a2.val :: mulstepLo 0 a.a0.val b.a6.val L₆ :: L₅ :: L₄ :: rest,
     mem, frame :: frames, adv⟩
    rfl hc₁u (U256.a1_isU32 a) (U256.a6_isU32 b) hL₇
  simp only [MidenState.withStack] at hms2
  rw [hms2]; clear hms2; dsimp only [bind, Bind.bind, Option.bind]
  -- drop (remove carry)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 2
  miden_movdn
  -- drop (remove a₃)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- drop (remove a₂)
  rw [stepDrop]; simp only [pure, Pure.pure]

-- ============================================================================
-- Epilogue: b₇ × a₀ correctness
-- ============================================================================

set_option maxHeartbeats 32000000 in
/-- Epilogue b₇: 1 mulstep for b₇ × a₀.
    Input stack: [L₇, L₆, L₅, L₄] ++ rest
    Output stack: [mulstepLo(0, a₀, b₇, L₇), L₆, L₅, L₄] ++ rest -/
private theorem wm_ep_b7_correct (a b : U256) (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (L₇ L₆ L₅ L₄ : Felt) (hL₇ : L₇.isU32 = true)
    (h12_3 : mem (frame.localAddr 12 + 3) = a.a3.val)
    (h12_2 : mem (frame.localAddr 12 + 2) = a.a2.val)
    (h12_1 : mem (frame.localAddr 12 + 1) = a.a1.val)
    (h12_0 : mem (frame.localAddr 12) = a.a0.val)
    (h0_3 : mem (frame.localAddr 0 + 3) = b.a7.val)
    (h0_2 : mem (frame.localAddr 0 + 2) = b.a6.val)
    (h0_1 : mem (frame.localAddr 0 + 1) = b.a5.val)
    (h0_0 : mem (frame.localAddr 0) = b.a4.val) :
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨L₇ :: L₆ :: L₅ :: L₄ :: rest, mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_ep_b7) =
    some ⟨mulstepLo 0 a.a0.val b.a7.val L₇ :: L₆ :: L₅ :: L₄ :: rest,
          mem, frame :: frames, adv⟩ := by
  unfold wm_ep_b7 execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- padw + locLoadwBe 12
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
  rw [h12_3, h12_2, h12_1, h12_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- padw + locLoadwBe 0
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
  rw [h0_3, h0_2, h0_1, h0_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 3 (b₇ goes to position 3)
  miden_movdn
  -- push 0
  miden_step
  -- dropw (removes [0, b₆, b₅, b₄])
  rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
  -- Stack: [b₇, a₃, a₂, a₁, a₀, L₇, L₆, L₅, L₄] ++ rest
  -- movup 4 (bring a₀)
  miden_movup
  -- movup 5 (bring L₇)
  miden_movup
  -- movdn 2
  miden_movdn
  -- push 0
  miden_step
  -- Stack: [0, a₀, b₇, L₇, a₃, a₂, a₁, L₆, L₅, L₄] ++ rest
  -- === Mulstep: mulstep(0, a₀, b₇, L₇) ===
  have h0u : (0 : Felt).isU32 = true := by simp [Felt.isU32]
  have hms := mulstep_execWithEnv u256ProcEnv (fuel + 1)
    (0 : Felt) a.a0.val b.a7.val L₇
    (a.a3.val :: a.a2.val :: a.a1.val :: L₆ :: L₅ :: L₄ :: rest)
    ⟨(0 : Felt) :: a.a0.val :: b.a7.val :: L₇ ::
     a.a3.val :: a.a2.val :: a.a1.val :: L₆ :: L₅ :: L₄ :: rest,
     mem, frame :: frames, adv⟩
    rfl h0u (U256.a0_isU32 a) (U256.a7_isU32 b) hL₇
  simp only [MidenState.withStack] at hms
  rw [hms]; clear hms; dsimp only [bind, Bind.bind, Option.bind]
  -- drop (remove carry)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- movdn 3
  miden_movdn
  -- drop (remove a₃)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- drop (remove a₂)
  rw [stepDrop]; dsimp only [bind, Bind.bind, Option.bind]
  -- drop (remove a₁)
  rw [stepDrop]; simp only [pure, Pure.pure]

-- ============================================================================
-- Epilogue decomposition helpers
-- ============================================================================

private def wm_ep_b6_b7_final : List Op := wm_ep_b6 ++ wm_ep_b7 ++ wm_final
private def wm_ep_b7_final : List Op := wm_ep_b7 ++ wm_final

set_option maxRecDepth 2048 in
private theorem wm_epilogue_split_b5 :
    wm_epilogue_and_final = wm_ep_b5 ++ wm_ep_b6_b7_final := by
  unfold wm_epilogue_and_final wm_ep_b5 wm_ep_b6_b7_final wm_ep_b6 wm_ep_b7 wm_final; rfl

set_option maxRecDepth 2048 in
private theorem wm_ep_b6_b7_final_split :
    wm_ep_b6_b7_final = wm_ep_b6 ++ wm_ep_b7_final := by
  unfold wm_ep_b6_b7_final wm_ep_b6 wm_ep_b7_final wm_ep_b7 wm_final; rfl

set_option maxRecDepth 2048 in
private theorem wm_ep_b7_final_split :
    wm_ep_b7_final = wm_ep_b7 ++ wm_final := by
  unfold wm_ep_b7_final wm_ep_b7 wm_final; rfl

-- ============================================================================
-- Final phase: load la(16), le_to_be, swapdw cleanup
-- ============================================================================

set_option maxHeartbeats 8000000 in
/-- Final phase: load accumulated low 4 limbs from la(16), convert to LE via le_to_be,
    then use swapdw/dropw cleanup to remove the 16 dummy elements below the result.
    Input stack:  [L₇, L₆, L₅, L₄, d0..d15] ++ rest
    Output stack: [R₀, R₁, R₂, R₃, L₄, L₅, L₆, L₇] ++ rest -/
private theorem wm_final_correct
    (rest : List Felt)
    (mem : Nat → Felt) (frame : LocalFrame) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) (hnl : frame.numLocals ≥ 24)
    (L₇ L₆ L₅ L₄ : Felt)
    (R₀ R₁ R₂ R₃ : Felt)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 : Felt)
    (h16_3 : mem (frame.localAddr 16 + 3) = R₃)
    (h16_2 : mem (frame.localAddr 16 + 2) = R₂)
    (h16_1 : mem (frame.localAddr 16 + 1) = R₁)
    (h16_0 : mem (frame.localAddr 16) = R₀) :
    execWithEnv u256ProcEnv (fuel + 3)
      ⟨L₇ :: L₆ :: L₅ :: L₄ :: d0 :: d1 :: d2 :: d3 ::
       d4 :: d5 :: d6 :: d7 :: d8 :: d9 :: d10 :: d11 ::
       d12 :: d13 :: d14 :: d15 :: rest, mem, frame :: frames, adv⟩
      (Procedure.ofOps wm_final) =
    some ⟨R₀ :: R₁ :: R₂ :: R₃ :: L₄ :: L₅ :: L₆ :: L₇ :: rest,
          mem, frame :: frames, adv⟩ := by
  unfold wm_final execWithEnv Procedure.ofOps
  simp only [List.foldlM, u256ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  -- padw
  rw [stepPadw]; dsimp only [bind, Bind.bind, Option.bind]
  -- locLoadwBe 16
  rw [stepLocLoadwBe (halign := by decide) (hbound := by omega)]
  rw [h16_3, h16_2, h16_1, h16_0]; dsimp only [bind, Bind.bind, Option.bind]
  -- swapw 1: swap [R₃, R₂, R₁, R₀] with [L₇, L₆, L₅, L₄]
  rw [stepSwapw1]; dsimp only [bind, Bind.bind, Option.bind]
  -- exec u256_le_to_be: reverse top 8
  -- Stack before: [L₇, L₆, L₅, L₄, R₃, R₂, R₁, R₀, d0..d15, rest]
  -- Stack after:  [R₀, R₁, R₂, R₃, L₄, L₅, L₆, L₇, d0..d15, rest]
  rw [le_to_be_env]; dsimp only [bind, Bind.bind, Option.bind]
  -- swapdw (first): swap [R₀..L₇] with [d0..d7]
  rw [stepSwapdw]; dsimp only [bind, Bind.bind, Option.bind]
  -- dropw: removes [d0, d1, d2, d3]
  rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
  -- dropw: removes [d4, d5, d6, d7]
  rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
  -- swapdw (second): swap [R₀..L₇] with [d8..d15]
  rw [stepSwapdw]; dsimp only [bind, Bind.bind, Option.bind]
  -- dropw: removes [d8, d9, d10, d11]
  rw [stepDropw]; dsimp only [bind, Bind.bind, Option.bind]
  -- dropw: removes [d12, d13, d14, d15]
  rw [stepDropw]; simp only [pure, Pure.pure]

-- ============================================================================
-- Main theorem
-- ============================================================================

set_option maxHeartbeats 32000000 in
/-- `u256::wrapping_mul` computes `(a * b) mod 2^256` for two 256-bit values.
    Input stack:  [b.a0, ..., b.a7, a.a0, ..., a.a7, d0, ..., d15] ++ rest  (LE limbs)
    Output stack: [(a*b).a0, ..., (a*b).a7] ++ rest
    The 16 elements d0..d15 below the inputs are consumed by the swapdw cleanup. -/
theorem u256_wrapping_mul_correct
    (a b : U256) (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 : Felt)
    (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (fuel : Nat) :
    ∃ mem', execWithEnv u256ProcEnv (fuel + 3)
      ⟨b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
       b.a4.val :: b.a5.val :: b.a6.val :: b.a7.val ::
       a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
       a.a4.val :: a.a5.val :: a.a6.val :: a.a7.val ::
       d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 ::
       d8 :: d9 :: d10 :: d11 :: d12 :: d13 :: d14 :: d15 :: rest, mem, frames, adv⟩
      Miden.Core.U256.wrapping_mul =
    some ⟨(a * b).a0.val :: (a * b).a1.val :: (a * b).a2.val :: (a * b).a3.val ::
          (a * b).a4.val :: (a * b).a5.val :: (a * b).a6.val :: (a * b).a7.val :: rest,
          mem', frames, adv⟩ := by
  -- Step 1: Handle frame allocation (numLocals = 24 = 23 + 1)
  rw [execWithEnv_body_eq_withLocals u256ProcEnv (fuel + 3) _ _ _ 23 rfl rfl]
  dsimp only
  -- Step 2: Reduce to proving body execution under the allocated frame
  set frame : LocalFrame :=
    { base := nextFrameBase frames, numLocals := 23 + 1,
      alignedNumLocals := alignLocals (23 + 1) } with hframe_def
  -- Abbreviate the 16 dummy elements appended to rest
  set drest : List Felt := d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 ::
    d8 :: d9 :: d10 :: d11 :: d12 :: d13 :: d14 :: d15 :: rest with hdrest
  suffices h : ∃ mem', execWithEnv u256ProcEnv (fuel + 3)
      ⟨b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
       b.a4.val :: b.a5.val :: b.a6.val :: b.a7.val ::
       a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
       a.a4.val :: a.a5.val :: a.a6.val :: a.a7.val :: drest,
       mem, frame :: frames, adv⟩
      (Procedure.ofOps Miden.Core.U256.wrapping_mul.body) =
      some ⟨(a * b).a0.val :: (a * b).a1.val :: (a * b).a2.val :: (a * b).a3.val ::
            (a * b).a4.val :: (a * b).a5.val :: (a * b).a6.val :: (a * b).a7.val :: rest,
            mem', frame :: frames, adv⟩ by
    obtain ⟨mem', hmem'⟩ := h
    exact ⟨mem', by rw [hmem']⟩
  -- Step 3: Decompose body into setup ++ rest
  rw [show Miden.Core.U256.wrapping_mul.body = wm_setup ++ wm_rest from wm_body_decomp]
  rw [execWithEnv_append]
  -- Step 4: Apply setup correctness
  rw [wm_setup_correct a b drest mem frame frames adv fuel (by simp only [frame]; omega)]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 5: Decompose wm_rest into round 1 + remaining
  rw [show (wm_rest : List Op) = wm_round1 ++ wm_rest_after_r1 from wm_rest_eq_r1_append]
  rw [execWithEnv_append]
  -- Step 6: Apply Round 1 correctness
  rw [wm_round1_correct a b drest _ frame frames adv fuel
      (by simp only [frame]; omega)
      (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 7: Decompose rest_after_r1 into round 2 + rest_after_r2
  rw [show (wm_rest_after_r1 : List Op) = wm_round2 ++ wm_rest_after_r2 from wm_rest_after_r1_eq_r2_append]
  rw [execWithEnv_append]
  -- Step 8: Apply Round 2 correctness (b₁ × a[0..6])
  -- Abbreviate Round 1 carry chain in the goal
  set c₁₀ := mulstepCarry 0 a.a0.val b.a0.val 0
  set c₂₀ := mulstepCarry c₁₀ a.a1.val b.a0.val 0
  set c₃₀ := mulstepCarry c₂₀ a.a2.val b.a0.val 0
  set c₄₀ := mulstepCarry c₃₀ a.a3.val b.a0.val 0
  set c₅₀ := mulstepCarry c₄₀ a.a4.val b.a0.val 0
  set c₆₀ := mulstepCarry c₅₀ a.a5.val b.a0.val 0
  set c₇₀ := mulstepCarry c₆₀ a.a6.val b.a0.val 0
  rw [wm_round2_correct a b drest _ frame frames adv fuel
      (by simp only [frame]; omega)
      (mulstepLo 0 a.a0.val b.a0.val 0)
      (mulstepLo c₁₀ a.a1.val b.a0.val 0)
      (mulstepLo c₂₀ a.a2.val b.a0.val 0)
      (mulstepLo c₃₀ a.a3.val b.a0.val 0)
      (mulstepLo c₄₀ a.a4.val b.a0.val 0)
      (mulstepLo c₅₀ a.a5.val b.a0.val 0)
      (mulstepLo c₆₀ a.a6.val b.a0.val 0)
      (mulstepLo c₇₀ a.a7.val b.a0.val 0)
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 9: Decompose rest_after_r2 into round 3 + rest_after_r3
  rw [show (wm_rest_after_r2 : List Op) = wm_round3 ++ wm_rest_after_r3 from wm_rest_after_r2_eq_r3_append]
  rw [execWithEnv_append]
  -- Step 10: Apply Round 3 correctness (b₂ × a[0..5])
  -- Abbreviate Round 2 carry chain
  set c₁₁ := mulstepCarry 0 a.a0.val b.a1.val (mulstepLo c₁₀ a.a1.val b.a0.val 0)
  set c₂₁ := mulstepCarry c₁₁ a.a1.val b.a1.val (mulstepLo c₂₀ a.a2.val b.a0.val 0)
  set c₃₁ := mulstepCarry c₂₁ a.a2.val b.a1.val (mulstepLo c₃₀ a.a3.val b.a0.val 0)
  set c₄₁ := mulstepCarry c₃₁ a.a3.val b.a1.val (mulstepLo c₄₀ a.a4.val b.a0.val 0)
  set c₅₁ := mulstepCarry c₄₁ a.a4.val b.a1.val (mulstepLo c₅₀ a.a5.val b.a0.val 0)
  rw [wm_round3_correct a b drest _ frame frames adv fuel
      (by simp only [frame]; omega)
      (mulstepLo 0 a.a0.val b.a0.val 0)
      (mulstepLo 0 a.a0.val b.a1.val (mulstepLo c₁₀ a.a1.val b.a0.val 0))
      (mulstepLo c₁₁ a.a1.val b.a1.val (mulstepLo c₂₀ a.a2.val b.a0.val 0))
      (mulstepLo c₂₁ a.a2.val b.a1.val (mulstepLo c₃₀ a.a3.val b.a0.val 0))
      (mulstepLo c₃₁ a.a3.val b.a1.val (mulstepLo c₄₀ a.a4.val b.a0.val 0))
      (mulstepLo c₄₁ a.a4.val b.a1.val (mulstepLo c₅₀ a.a5.val b.a0.val 0))
      (mulstepLo c₅₁ a.a5.val b.a1.val (mulstepLo c₆₀ a.a6.val b.a0.val 0))
      (mulstepLo (mulstepCarry c₅₁ a.a5.val b.a1.val (mulstepLo c₆₀ a.a6.val b.a0.val 0))
        a.a6.val b.a1.val (mulstepLo c₇₀ a.a7.val b.a0.val 0))
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 11: Decompose rest_after_r3 into round 4 + rest_after_r4
  rw [show (wm_rest_after_r3 : List Op) = wm_round4 ++ wm_rest_after_r4 from wm_rest_after_r3_eq_r4_append]
  rw [execWithEnv_append]
  -- Step 12: Apply Round 4 correctness (b₃ × a[0..4])
  -- Abbreviate Round 3 carry chain
  set c₁₂ := mulstepCarry 0 a.a0.val b.a2.val
    (mulstepLo c₁₁ a.a1.val b.a1.val (mulstepLo c₂₀ a.a2.val b.a0.val 0))
  set c₂₂ := mulstepCarry c₁₂ a.a1.val b.a2.val
    (mulstepLo c₂₁ a.a2.val b.a1.val (mulstepLo c₃₀ a.a3.val b.a0.val 0))
  set c₃₂ := mulstepCarry c₂₂ a.a2.val b.a2.val
    (mulstepLo c₃₁ a.a3.val b.a1.val (mulstepLo c₄₀ a.a4.val b.a0.val 0))
  set c₄₂ := mulstepCarry c₃₂ a.a3.val b.a2.val
    (mulstepLo c₄₁ a.a4.val b.a1.val (mulstepLo c₅₀ a.a5.val b.a0.val 0))
  rw [wm_round4_correct a b drest _ frame frames adv fuel
      (by simp only [frame]; omega)
      (mulstepLo 0 a.a0.val b.a0.val 0)
      (mulstepLo 0 a.a0.val b.a1.val (mulstepLo c₁₀ a.a1.val b.a0.val 0))
      (mulstepLo 0 a.a0.val b.a2.val
        (mulstepLo c₁₁ a.a1.val b.a1.val (mulstepLo c₂₀ a.a2.val b.a0.val 0)))
      (mulstepLo c₁₂ a.a1.val b.a2.val
        (mulstepLo c₂₁ a.a2.val b.a1.val (mulstepLo c₃₀ a.a3.val b.a0.val 0)))
      (mulstepLo c₂₂ a.a2.val b.a2.val
        (mulstepLo c₃₁ a.a3.val b.a1.val (mulstepLo c₄₀ a.a4.val b.a0.val 0)))
      (mulstepLo c₃₂ a.a3.val b.a2.val
        (mulstepLo c₄₁ a.a4.val b.a1.val (mulstepLo c₅₀ a.a5.val b.a0.val 0)))
      (mulstepLo c₄₂ a.a4.val b.a2.val
        (mulstepLo c₅₁ a.a5.val b.a1.val (mulstepLo c₆₀ a.a6.val b.a0.val 0)))
      (mulstepLo (mulstepCarry c₄₂ a.a4.val b.a2.val
          (mulstepLo c₅₁ a.a5.val b.a1.val (mulstepLo c₆₀ a.a6.val b.a0.val 0)))
        a.a5.val b.a2.val
        (mulstepLo (mulstepCarry c₅₁ a.a5.val b.a1.val (mulstepLo c₆₀ a.a6.val b.a0.val 0))
          a.a6.val b.a1.val (mulstepLo c₇₀ a.a7.val b.a0.val 0)))
      (mulstepLo_isU32 _ _ _ _)
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 13: Decompose rest_after_r4 into round 5 + epilogue_and_final
  rw [show (wm_rest_after_r4 : List Op) = wm_round5 ++ wm_epilogue_and_final from wm_rest_after_r4_eq_r5_append]
  rw [execWithEnv_append]
  -- Step 14: Apply Round 5 correctness (b₄ × a[0..3])
  -- Abbreviate Round 4 carry chain
  set c₁₃ := mulstepCarry 0 a.a0.val b.a3.val
    (mulstepLo c₁₂ a.a1.val b.a2.val
      (mulstepLo c₂₁ a.a2.val b.a1.val (mulstepLo c₃₀ a.a3.val b.a0.val 0)))
  set c₂₃ := mulstepCarry c₁₃ a.a1.val b.a3.val
    (mulstepLo c₂₂ a.a2.val b.a2.val
      (mulstepLo c₃₁ a.a3.val b.a1.val (mulstepLo c₄₀ a.a4.val b.a0.val 0)))
  set c₃₃ := mulstepCarry c₂₃ a.a2.val b.a3.val
    (mulstepLo c₃₂ a.a3.val b.a2.val
      (mulstepLo c₄₁ a.a4.val b.a1.val (mulstepLo c₅₀ a.a5.val b.a0.val 0)))
  rw [wm_round5_correct a b drest _ frame frames adv fuel
      (by simp only [frame]; omega)
      _ _ _ _
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 15: Decompose epilogue_and_final into ep_b5 + rest
  rw [show (wm_epilogue_and_final : List Op) = wm_ep_b5 ++ wm_ep_b6_b7_final from wm_epilogue_split_b5]
  rw [execWithEnv_append]
  -- Step 16: Apply epilogue b₅ correctness
  rw [wm_ep_b5_correct a b drest _ frame frames adv fuel
      (by simp only [frame]; omega) _ _ _ _
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 17: Decompose remaining into ep_b6 + ep_b7_final
  rw [show (wm_ep_b6_b7_final : List Op) = wm_ep_b6 ++ wm_ep_b7_final from wm_ep_b6_b7_final_split]
  rw [execWithEnv_append]
  -- Step 18: Apply epilogue b₆ correctness
  rw [wm_ep_b6_correct a b drest _ frame frames adv fuel
      (by simp only [frame]; omega) _ _ _ _
      (mulstepLo_isU32 _ _ _ _) (mulstepLo_isU32 _ _ _ _)
      (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 19: Decompose remaining into ep_b7 + final
  rw [show (wm_ep_b7_final : List Op) = wm_ep_b7 ++ wm_final from wm_ep_b7_final_split]
  rw [execWithEnv_append]
  -- Step 20: Apply epilogue b₇ correctness
  rw [wm_ep_b7_correct a b drest _ frame frames adv fuel
      (by simp only [frame]; omega) _ _ _ _
      (mulstepLo_isU32 _ _ _ _)
      (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 21: Apply final phase correctness (unfold drest for explicit dummy elements)
  rw [show (drest : List Felt) = d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 ::
    d8 :: d9 :: d10 :: d11 :: d12 :: d13 :: d14 :: d15 :: rest from hdrest]
  rw [wm_final_correct rest _ frame frames adv fuel
      (by simp only [frame]; omega) _ _ _ _ _ _ _ _
      d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
      (by simp; rfl) (by simp; rfl) (by simp; rfl) (by simp; rfl)]
  -- Semantic bridge: mulstep chain = (a * b) mod 2^256
  have hlimbs := wrapping_mul_limbs_correct a b
  exact ⟨_, by
    congr 1
    congr 1
    exact List.cons_eq_cons.mpr ⟨hlimbs.1, List.cons_eq_cons.mpr ⟨hlimbs.2.1,
      List.cons_eq_cons.mpr ⟨hlimbs.2.2.1, List.cons_eq_cons.mpr ⟨hlimbs.2.2.2.1,
      List.cons_eq_cons.mpr ⟨hlimbs.2.2.2.2.1, List.cons_eq_cons.mpr ⟨hlimbs.2.2.2.2.2.1,
      List.cons_eq_cons.mpr ⟨hlimbs.2.2.2.2.2.2.1, List.cons_eq_cons.mpr
        ⟨hlimbs.2.2.2.2.2.2.2, rfl⟩⟩⟩⟩⟩⟩⟩⟩⟩

end MidenLean.Proofs
