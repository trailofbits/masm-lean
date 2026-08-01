import MidenLean.Proofs.U256.Common
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U256

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `mulstep` computes one step of schoolbook long multiplication: given multiplier `a`,
    limb `b`, carry `c`, and accumulator `d` (all u32), produces `[new_carry, new_lo]`
    where `new_lo = (c * b + a + d) % 2^32` and `new_carry` is the high part.
    Input stack:  [a, b, c, d] ++ rest
    Output stack: [Felt.ofNat ((c*b+a) / 2^32) + Felt.ofNat (((c*b+a) % 2^32 + d) / 2^32),
                   Felt.ofNat (((c*b+a) % 2^32 + d) % 2^32)] ++ rest
    Parametric in `env` and `fuel` so this lemma serves both as a callee
    summary for reflective callers and as the basis for `u256_mulstep_correct`. -/
@[miden_exec_summary]
theorem u256_mulstep_exec
    (env : ProcEnv) (fuel : Nat)
    (a b c d : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a :: b :: c :: d :: rest)
    (ha_u32 : a.isU32 = true)
    (hb_u32 : b.isU32 = true)
    (hc_u32 : c.isU32 = true)
    (hd_u32 : d.isU32 = true) :
    execProcedure env (fuel + 1) s Miden.Core.U256.mulstep =
    some (s.withStack (
      (Felt.ofNat ((c.val * b.val + a.val) / 2 ^ 32) +
        Felt.ofNat (((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32)) ::
      Felt.ofNat (((c.val * b.val + a.val) % 2 ^ 32 + d.val) % 2 ^ 32) :: rest)) := by
  miden_vcg
  · miden_finish_reflection
  · simp only [MidenLean.u32Max, u32_mod_val, Nat.mod_add_mod]
    exact ⟨add_comm _ _, rfl⟩

set_option maxHeartbeats 4000000 in
/-- `mulstep` computes one step of schoolbook long multiplication: given multiplier `a`,
    limb `b`, carry `c`, and accumulator `d` (all u32), produces `[new_carry, new_lo]`
    where `new_lo = (c * b + a + d) % 2^32` and `new_carry` is the high part.
    Input stack:  [a, b, c, d] ++ rest
    Output stack: [Felt.ofNat ((c*b+a) / 2^32) + Felt.ofNat (((c*b+a) % 2^32 + d) / 2^32),
                   Felt.ofNat (((c*b+a) % 2^32 + d) % 2^32)] ++ rest -/
theorem u256_mulstep_correct
    (a b c d : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = a :: b :: c :: d :: rest)
    (ha_u32 : a.isU32 = true)
    (hb_u32 : b.isU32 = true)
    (hc_u32 : c.isU32 = true)
    (hd_u32 : d.isU32 = true) :
    execProcedure emptyEnv 11 s Miden.Core.U256.mulstep =
    some (s.withStack (
      (Felt.ofNat ((c.val * b.val + a.val) / 2 ^ 32) +
        Felt.ofNat (((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32)) ::
      Felt.ofNat (((c.val * b.val + a.val) % 2 ^ 32 + d.val) % 2 ^ 32) :: rest)) :=
  u256_mulstep_exec emptyEnv 10 a b c d rest s hs ha_u32 hb_u32 hc_u32 hd_u32

end MidenLean.Proofs
