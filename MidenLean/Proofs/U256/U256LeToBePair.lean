import MidenLean.Proofs.U256.Common
import MidenLean.Proofs.Tactics

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Helper step lemma
-- ============================================================================

private theorem stepSwapdw (mem locs : Nat → Felt) (adv : List Felt)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 : Felt) (rest : List Felt) :
    execInstruction ⟨a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        c0 :: c1 :: c2 :: c3 :: d0 :: d1 :: d2 :: d3 :: rest, mem, locs, adv⟩ .swapdw =
      some ⟨c0 :: c1 :: c2 :: c3 :: d0 :: d1 :: d2 :: d3 ::
        a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execSwapdw; simp [MidenState.withStack]

-- ============================================================================
-- u256_le_to_be helper for execWithEnv context
-- ============================================================================

private theorem le_to_be_env (fuel : Nat)
    (x0 x1 x2 x3 x4 x5 x6 x7 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv u256ProcEnv (fuel + 1)
      ⟨x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest, mem, locs, adv⟩
      Miden.Core.U256.u256_le_to_be =
    some ⟨x7 :: x6 :: x5 :: x4 :: x3 :: x2 :: x1 :: x0 :: rest, mem, locs, adv⟩ := by
  unfold Miden.Core.U256.u256_le_to_be execWithEnv
  simp only [List.foldlM]
  rw [stepReversew]; miden_bind
  rw [stepSwapw1]; miden_bind
  rw [stepReversew]
  simp only [pure, Pure.pure]

-- ============================================================================
-- Main theorems
-- ============================================================================

set_option maxHeartbeats 8000000 in
theorem u256_u256_le_to_be_pair_raw (fuel : Nat)
    (x0 x1 x2 x3 x4 x5 x6 x7 y0 y1 y2 y3 y4 y5 y6 y7 : Felt)
    (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv u256ProcEnv (fuel + 2)
      ⟨x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 ::
       y0 :: y1 :: y2 :: y3 :: y4 :: y5 :: y6 :: y7 :: rest, mem, locs, adv⟩
      Miden.Core.U256.u256_le_to_be_pair =
    some ⟨x7 :: x6 :: x5 :: x4 :: x3 :: x2 :: x1 :: x0 ::
          y7 :: y6 :: y5 :: y4 :: y3 :: y2 :: y1 :: y0 :: rest, mem, locs, adv⟩ := by
  unfold Miden.Core.U256.u256_le_to_be_pair execWithEnv
  simp only [List.foldlM, u256ProcEnv]
  -- exec "u256_le_to_be" on [x0..x7, y0..y7]
  dsimp only [bind, Bind.bind, Option.bind]
  rw [le_to_be_env]
  dsimp only [bind, Bind.bind, Option.bind]
  -- swapdw: swap [x7..x0] with [y0..y7]
  rw [stepSwapdw]
  dsimp only [bind, Bind.bind, Option.bind]
  -- exec "u256_le_to_be" on [y0..y7, x7..x0]
  rw [le_to_be_env]
  dsimp only [bind, Bind.bind, Option.bind]
  -- swapdw: swap back
  rw [stepSwapdw]
  simp only [pure, Pure.pure]

/-- `u256::u256_le_to_be_pair` reverses each of the two 8-element groups on the stack.
    Input stack:  [x0, ..., x7, y0, ..., y7] ++ rest
    Output stack: [x7, ..., x0, y7, ..., y0] ++ rest -/
theorem u256_u256_le_to_be_pair_correct (fuel : Nat) (a b : U256)
    (rest : List Felt) (s : MidenState)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                    b.a4.val :: b.a5.val :: b.a6.val :: b.a7.val ::
                    a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
                    a.a4.val :: a.a5.val :: a.a6.val :: a.a7.val :: rest) :
    execWithEnv u256ProcEnv (fuel + 2) s Miden.Core.U256.u256_le_to_be_pair =
    some { stack := b.a7.val :: b.a6.val :: b.a5.val :: b.a4.val ::
                    b.a3.val :: b.a2.val :: b.a1.val :: b.a0.val ::
                    a.a7.val :: a.a6.val :: a.a5.val :: a.a4.val ::
                    a.a3.val :: a.a2.val :: a.a1.val :: a.a0.val :: rest,
           memory := s.memory, locals := s.locals, advice := s.advice } := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  subst hs
  exact u256_u256_le_to_be_pair_raw fuel
    b.a0.val b.a1.val b.a2.val b.a3.val b.a4.val b.a5.val b.a6.val b.a7.val
    a.a0.val a.a1.val a.a2.val a.a3.val a.a4.val a.a5.val a.a6.val a.a7.val
    rest mem locs adv

end MidenLean.Proofs
