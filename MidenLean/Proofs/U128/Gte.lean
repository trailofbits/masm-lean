import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.U128.Lt
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
theorem u128_gte_run
    (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execWithEnv u128ProcEnv (fuel + 3)
      ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      Miden.Core.U128.gte =
    some ⟨(if !(u128LtBool a0 a1 a2 a3 b0 b1 b2 b3) then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold Miden.Core.U128.gte execWithEnv
  simp only [List.foldlM, u128ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  rw [u128_lt_run fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3]
  miden_bind
  rw [stepNotIte]
  simp [pure, Pure.pure]

set_option maxHeartbeats 8000000 in
/-- `u128::gte` correctly compares two u128 values (raw limb version).
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff `a ≥ b`, else 0. -/
theorem u128_gte_raw
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execWithEnv u128ProcEnv 31 s Miden.Core.U128.gte =
    some (s.withStack ((if !(u128LtBool a0 a1 a2 a3 b0 b1 b2 b3) then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  simpa using u128_gte_run 28 a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3

/-- `u128::gte` pushes 1 iff `b ≤ a` (i.e. `a ≥ b`).
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [(if b ≤ a then 1 else 0)] ++ rest -/
theorem u128_gte_correct (a b : U128) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest) :
    execWithEnv u128ProcEnv 31 s Miden.Core.U128.gte =
    some (s.withStack (
      (if decide (b ≤ a) then (1 : Felt) else 0) :: rest)) := by
  rw [u128_gte_raw a.a0.val a.a1.val a.a2.val a.a3.val b.a0.val b.a1.val b.a2.val b.a3.val rest s hs
    a.a0.isU32 a.a1.isU32 a.a2.isU32 a.a3.isU32 b.a0.isU32 b.a1.isU32 b.a2.isU32 b.a3.isU32]
  simp only [u128LtBool_iff_lt a b]
  congr 1; congr 1; congr 1; congr 1
  cases h : decide (a < b) <;> simp_all

end MidenLean.Proofs
