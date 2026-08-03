import MidenLean.Proofs.U256.U256LeToBePair
import MidenLean.Symbolic.Tactic

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 8000000 in
/-- `u256::eq` tests equality of two 256-bit values (raw limb version).
    Input stack:  [b0, ..., b7, a0, ..., a7] ++ rest
    Output stack: [result] ++ rest
    where result = 1 iff all eight limb pairs agree, else 0.
    Parametric in `fuel` so this lemma serves both as a callee summary for
    reflective callers and as the basis for `u256_eq_correct`. -/
@[miden_exec_summary]
theorem u256_eq_exec (fuel : Nat)
    (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : Felt)
    (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::
                    a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest) :
    execProcedure u256ProcEnv (fuel + 3) s Miden.Core.U256.eq =
    some (s.withStack (
      (if ((b3 == a3) && (b2 == a2) && (b1 == a1) && (b0 == a0)) &&
          ((b7 == a7) && (b6 == a6) && (b5 == a5) && (b4 == a4))
       then (1 : Felt) else 0) :: rest)) := by
  miden_vcg
  all_goals tauto

/-- `u256::eq` tests equality of two 256-bit values.
    Input stack:  [b.a0, b.a1, ..., b.a7, a.a0, a.a1, ..., a.a7] ++ rest
    Output stack: [result] ++ rest
    where result = 1 if a = b, otherwise 0. -/
theorem u256_eq_correct (fuel : Nat) (a b : U256) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                    b.a4.val :: b.a5.val :: b.a6.val :: b.a7.val ::
                    a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val ::
                    a.a4.val :: a.a5.val :: a.a6.val :: a.a7.val :: rest) :
    execProcedure u256ProcEnv (fuel + 3) s Miden.Core.U256.eq =
    some (s.withStack (
      (if a == b then (1 : Felt) else 0) :: rest)) := by
  rw [u256_eq_exec fuel a.a0.val a.a1.val a.a2.val a.a3.val
    a.a4.val a.a5.val a.a6.val a.a7.val
    b.a0.val b.a1.val b.a2.val b.a3.val
    b.a4.val b.a5.val b.a6.val b.a7.val rest s hs]
  congr 1; congr 1; congr 1
  simp only [U256.beq_iff, Bool.beq_comm (a := a.a0.val), Bool.beq_comm (a := a.a1.val),
    Bool.beq_comm (a := a.a2.val), Bool.beq_comm (a := a.a3.val),
    Bool.beq_comm (a := a.a4.val), Bool.beq_comm (a := a.a5.val),
    Bool.beq_comm (a := a.a6.val), Bool.beq_comm (a := a.a7.val)]
  simp only [Bool.and_assoc]
  ac_rfl

end MidenLean.Proofs
