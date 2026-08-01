import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `u128::shr_k3` shifts the highest u32 limb right by the given bit count and
    leaves any lower-word padding in `rest`.
    Input stack:  [shift, a0, a1, a2, a3] ++ rest
    Output stack: [a3 >> shift] ++ rest
    Requires `shift` and `a3` to be u32 values, with `shift ≤ 31`.
    Parametric in `env` and `fuel` so this lemma serves both as a callee
    summary for reflective callers and as the basis for `u128_shr_k3_correct`. -/
@[miden_exec_summary]
theorem u128_shr_k3_exec
    (env : ProcEnv) (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = shift :: a0 :: a1 :: a2 :: a3 :: rest)
    (hshift_u32 : shift.isU32 = true)
    (ha3_u32 : a3.isU32 = true)
    (hshift : shift.val ≤ 31) :
    execProcedure env (fuel + 1) s Miden.Core.U128.shr_k3 =
    some (s.withStack (Felt.ofNat (a3.val / 2 ^ shift.val) :: rest)) := by
  miden_vcg

set_option maxHeartbeats 4000000 in
/-- `u128::shr_k3` returns the low limb of a u128 value shifted right by `96 + shift` bits.
    Input stack:  [shift, a.a0, a.a1, a.a2, a.a3] ++ rest
    Output stack: [(a.shr (96 + shift)).a0] ++ rest -/
theorem u128_shr_k3_correct
    (a : U128) (shift : U32) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest)
    (hshift_lt32 : shift.toNat < 32) :
    execProcedure emptyEnv 12 s Miden.Core.U128.shr_k3 =
    some (s.withStack ((a.shr (96 + shift.toNat)).a0.val :: rest)) := by
  have hshift_le31 : shift.toNat ≤ 31 := Nat.le_pred_of_lt hshift_lt32
  have hraw := u128_shr_k3_exec emptyEnv 11 shift.val a.a0.val a.a1.val a.a2.val a.a3.val rest s hs
    shift.isU32 a.a3.isU32 (by simpa [U32.toNat] using hshift_le31)
  obtain ⟨h0, h1, h2, h3⟩ := U128.shr_96_add_limbs a shift.toNat
  clear h1 h2 h3
  simpa [U32.toNat, h0] using hraw

end MidenLean.Proofs
