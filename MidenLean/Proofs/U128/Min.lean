import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.U128.Gt
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
theorem u128_min_run
    (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execWithEnv u128ProcEnv (fuel + 3)
      ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      Miden.Core.U128.min =
    some ⟨
      (if u128GtBool a0 a1 a2 a3 b0 b1 b2 b3 then b0 else a0) ::
      (if u128GtBool a0 a1 a2 a3 b0 b1 b2 b3 then b1 else a1) ::
      (if u128GtBool a0 a1 a2 a3 b0 b1 b2 b3 then b2 else a2) ::
      (if u128GtBool a0 a1 a2 a3 b0 b1 b2 b3 then b3 else a3) ::
      rest,
      mem, locs, adv⟩ := by
  unfold Miden.Core.U128.min execWithEnv
  simp only [List.foldlM, u128ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind]
  rw [stepDupw1]
  miden_bind
  rw [stepDupw1]
  miden_bind
  rw [u128_gt_run fuel a0 a1 a2 a3 b0 b1 b2 b3
    (b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest) mem locs adv
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3]
  miden_bind
  rw [stepCdropwIte]
  simp [pure, Pure.pure]

set_option maxHeartbeats 8000000 in
/-- `u128::min` correctly computes the minimum of two u128 values (raw limb version).
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [m0, m1, m2, m3] ++ rest
    where `m0..m3` are the low-to-high limbs of `min(a, b)`. -/
theorem u128_min_raw
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execWithEnv u128ProcEnv 37 s Miden.Core.U128.min =
    some (s.withStack (
      (if u128GtBool a0 a1 a2 a3 b0 b1 b2 b3 then b0 else a0) ::
      (if u128GtBool a0 a1 a2 a3 b0 b1 b2 b3 then b1 else a1) ::
      (if u128GtBool a0 a1 a2 a3 b0 b1 b2 b3 then b2 else a2) ::
      (if u128GtBool a0 a1 a2 a3 b0 b1 b2 b3 then b3 else a3) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  simpa using u128_min_run 34 a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3

/-- `u128::min` pushes the limbs of `min(a, b)`.
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [m0, m1, m2, m3] ++ rest
    Selects a if b > a (i.e. a < b is false and b < a is true), otherwise b. -/
theorem u128_min_correct (a b : U128) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b.a0 :: b.a1 :: b.a2 :: b.a3 :: a.a0 :: a.a1 :: a.a2 :: a.a3 :: rest) :
    execWithEnv u128ProcEnv 37 s Miden.Core.U128.min =
    some (s.withStack (
      (if decide (b.toNat < a.toNat) then b.a0 else a.a0) ::
      (if decide (b.toNat < a.toNat) then b.a1 else a.a1) ::
      (if decide (b.toNat < a.toNat) then b.a2 else a.a2) ::
      (if decide (b.toNat < a.toNat) then b.a3 else a.a3) :: rest)) := by
  rw [u128_min_raw a.a0 a.a1 a.a2 a.a3 b.a0 b.a1 b.a2 b.a3 rest s hs
    a.a0_u32 a.a1_u32 a.a2_u32 a.a3_u32 b.a0_u32 b.a1_u32 b.a2_u32 b.a3_u32]
  simp only [u128GtBool, u128LtBool_iff_lt b a]

end MidenLean.Proofs
