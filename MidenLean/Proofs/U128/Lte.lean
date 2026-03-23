import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.U128.Gt
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
theorem u128_lte_run
    (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execWithEnv u128ProcEnv (fuel + 3)
      ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      Miden.Core.U128.lte =
    some ⟨(if !(u128GtBool a0 a1 a2 a3 b0 b1 b2 b3) then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold Miden.Core.U128.lte execWithEnv
  simp only [List.foldlM, u128ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  rw [u128_gt_run fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3]
  miden_bind
  rw [stepNotIte]
  simp [pure, Pure.pure]

set_option maxHeartbeats 8000000 in
/-- `u128::lte` correctly compares two u128 values (raw limb version).
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff `a ≤ b`, else 0. -/
theorem u128_lte_raw
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execWithEnv u128ProcEnv 31 s Miden.Core.U128.lte =
    some (s.withStack ((if !(u128GtBool a0 a1 a2 a3 b0 b1 b2 b3) then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  simpa using u128_lte_run 28 a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3

/-- `u128::lte` pushes 1 iff `a.toNat ≤ b.toNat`.
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [(if a ≤ b then 1 else 0)] ++ rest -/
theorem u128_lte_correct (a b : U128) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b.a0 :: b.a1 :: b.a2 :: b.a3 :: a.a0 :: a.a1 :: a.a2 :: a.a3 :: rest) :
    execWithEnv u128ProcEnv 31 s Miden.Core.U128.lte =
    some (s.withStack (
      (if decide (a.toNat ≤ b.toNat) then (1 : Felt) else 0) :: rest)) := by
  rw [u128_lte_raw a.a0 a.a1 a.a2 a.a3 b.a0 b.a1 b.a2 b.a3 rest s hs
    a.a0_u32 a.a1_u32 a.a2_u32 a.a3_u32 b.a0_u32 b.a1_u32 b.a2_u32 b.a3_u32]
  simp only [u128GtBool, u128LtBool_iff_lt b a]
  congr 1; congr 1; congr 1; congr 1
  cases h : decide (b.toNat < a.toNat) <;> simp_all

end MidenLean.Proofs
