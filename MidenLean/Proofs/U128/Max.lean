import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.U128.Lt
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- `u128::max` computes the maximum of two u128 values (raw limb version).
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [m0, m1, m2, m3] ++ rest
    where `m0..m3` are the low-to-high limbs of `max(a, b)`.
    Parametric in `fuel` so this lemma serves both as a callee summary for
    reflective callers and as the basis for `u128_max_correct`. -/
@[miden_exec_summary]
theorem u128_max_exec
    (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execProcedure u128ProcEnv (fuel + 3) s Miden.Core.U128.max =
    some (s.withStack (
      (if u128LtBool a0 a1 a2 a3 b0 b1 b2 b3 then b0 else a0) ::
      (if u128LtBool a0 a1 a2 a3 b0 b1 b2 b3 then b1 else a1) ::
      (if u128LtBool a0 a1 a2 a3 b0 b1 b2 b3 then b2 else a2) ::
      (if u128LtBool a0 a1 a2 a3 b0 b1 b2 b3 then b3 else a3) :: rest)) := by
  miden_vcg
  all_goals simp_all [Symbolic.Expr.eval]

/-- `u128::max` pushes the limbs of `max(a, b)`.
    Input stack:  [b.a0, b.a1, b.a2, b.a3, a.a0, a.a1, a.a2, a.a3] ++ rest
    Output stack: [(max a b).a0, (max a b).a1, (max a b).a2, (max a b).a3] ++ rest -/
theorem u128_max_correct (a b : U128) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                    a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest) :
    execProcedure u128ProcEnv 37 s Miden.Core.U128.max =
    some (s.withStack (
      (max a b).a0.val :: (max a b).a1.val ::
      (max a b).a2.val :: (max a b).a3.val :: rest)) := by
  rw [U128.max_eq_ite_lt]
  rw [u128_max_exec 34 a.a0.val a.a1.val a.a2.val a.a3.val b.a0.val b.a1.val b.a2.val b.a3.val rest s hs
    a.a0.isU32 a.a1.isU32 a.a2.isU32 a.a3.isU32 b.a0.isU32 b.a1.isU32 b.a2.isU32 b.a3.isU32]
  simp only [u128LtBool_iff_lt a b, U128.lt_iff_toNat_lt, decide_eq_true_eq]
  split <;> rfl

end MidenLean.Proofs
