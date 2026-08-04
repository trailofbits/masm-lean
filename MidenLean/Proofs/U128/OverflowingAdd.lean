import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 1000000 in
/-- `u128::overflowing_add` computes addition of two 128-bit values with carry.
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [overflow, c0, c1, c2, c3] ++ rest
    where `c0..c3` are the low-to-high limbs of `a + b` and `overflow` is the final carry.
    Parametric in `env` and `fuel` so this lemma serves both as a callee
    summary for reflective callers and as the basis for `u128_overflowing_add_correct`. -/
@[miden_exec_summary]
theorem u128_overflowing_add_exec
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execProcedure env (fuel + 1) s Miden.Core.U128.overflowing_add =
    some (s.withStack (
      let sum0 := b0.val + a0.val
      let carry0 := sum0 / 2 ^ 32
      let sum1 := carry0 + a1.val + b1.val
      let carry1 := sum1 / 2 ^ 32
      let sum2 := carry1 + a2.val + b2.val
      let carry2 := sum2 / 2 ^ 32
      let sum3 := carry2 + a3.val + b3.val
      Felt.ofNat (sum3 / 2 ^ 32) ::
      Felt.ofNat (sum0 % 2 ^ 32) ::
      Felt.ofNat (sum1 % 2 ^ 32) ::
      Felt.ofNat (sum2 % 2 ^ 32) ::
      Felt.ofNat (sum3 % 2 ^ 32) :: rest)) := by
  miden_vcg

/-- `u128::overflowing_add` computes `a + b` with overflow detection.
    Input stack:  [b.a0, b.a1, b.a2, b.a3, a.a0, a.a1, a.a2, a.a3] ++ rest
    Output stack: [overflow, (a+b).a0, (a+b).a1, (a+b).a2, (a+b).a3] ++ rest
    where overflow = `(a.toNat + b.toNat) / 2^128` (0 or 1). -/
theorem u128_overflowing_add_correct (a b : U128) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                    a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest) :
    execProcedure emptyEnv 20 s Miden.Core.U128.overflowing_add =
    some (s.withStack (
      Felt.ofNat ((a.toNat + b.toNat) / 2^128) ::
      (a + b).a0.val :: (a + b).a1.val :: (a + b).a2.val :: (a + b).a3.val :: rest)) := by
  have h := u128_overflowing_add_exec emptyEnv 19
    a.a0.val a.a1.val a.a2.val a.a3.val
    b.a0.val b.a1.val b.a2.val b.a3.val rest s hs
    a.a0.isU32 a.a1.isU32 a.a2.isU32 a.a3.isU32
    b.a0.isU32 b.a1.isU32 b.a2.isU32 b.a3.isU32
  rw [h]; congr 1; congr 1
  obtain ⟨br0, br1, br2, br3, bro⟩ := u128_add_carry_bridge a b
  simp only [bro, br0, br1, br2, br3]

end MidenLean.Proofs
