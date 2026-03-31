import MidenLean.Proofs.U256.Common
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U256

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `mulstep` computes one step of schoolbook long multiplication: given multiplier `a`,
    limb `b`, carry `c`, and accumulator `d` (all u32), produces `[new_carry, new_lo]`
    where `new_lo = (c * b + a + d) % 2^32` and `new_carry` is the high part.
    Input stack:  [a, b, c, d] ++ rest
    Output stack: [Felt.ofNat ((c*b+a) / 2^32) + Felt.ofNat (((c*b+a) % 2^32 + d) / 2^32),
                   Felt.ofNat (((c*b+a) % 2^32 + d) % 2^32)] ++ rest -/
theorem u256_mulstep_correct
    (a b c d : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: b :: c :: d :: rest)
    (ha_u32 : a.isU32 = true)
    (hb_u32 : b.isU32 = true)
    (hc_u32 : c.isU32 = true)
    (hd_u32 : d.isU32 = true) :
    exec 11 s Miden.Core.U256.mulstep =
    some (s.withStack (
      (Felt.ofNat ((c.val * b.val + a.val) / 2 ^ 32) +
        Felt.ofNat (((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32)) ::
      Felt.ofNat (((c.val * b.val + a.val) % 2 ^ 32 + d.val) % 2 ^ 32) :: rest)) := by
  -- Manual setup (equivalent to miden_setup)
  obtain ⟨stk, mem, frames, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U256.mulstep execWithEnv
  simp only [List.foldlM]
  -- Instruction 1: movdn 2
  -- Stack: [a, b, c, d | rest] → [b, c, a, d | rest]
  miden_movdn
  -- Instruction 2: u32WidenMadd
  -- Stack: [b, c, a, d | rest]
  -- stepU32WidenMadd: ⟨b :: a :: c :: rest⟩ computes a.val * b.val + c.val
  -- Here: b=b, a=c, c=a → computes c.val * b.val + a.val
  rw [stepU32WidenMadd (ha := hc_u32) (hb := hb_u32) (hc := ha_u32)]
  miden_bind
  -- Recover value: (Felt.ofNat (x % 2^32)).val = x % 2^32
  have hval_recover : (Felt.ofNat ((c.val * b.val + a.val) % 2 ^ 32)).val =
      (c.val * b.val + a.val) % 2 ^ 32 :=
    felt_ofNat_val_lt _ (u32_mod_lt_prime _)
  -- Stack: [lo, hi, d | rest] where lo = (c*b+a) % 2^32, hi = (c*b+a) / 2^32
  -- Instruction 3: movup 2
  -- Stack: [lo, hi, d | rest] → [d, lo, hi | rest]
  miden_movup
  -- Instruction 4: u32OverflowAdd
  -- Stack: [d, lo, hi | rest]
  -- stepU32OverflowAdd: ⟨b :: a :: rest⟩ computes a.val + b.val
  -- Here: b=d, a=lo → computes lo.val + d.val
  have hlo_u32 : (Felt.ofNat ((c.val * b.val + a.val) % 2 ^ 32)).isU32 = true :=
    u32_mod_isU32 (c.val * b.val + a.val)
  rw [stepU32OverflowAdd (ha := hlo_u32) (hb := hd_u32)]
  miden_bind
  -- Simplify the nested Felt.ofNat val
  rw [hval_recover]
  -- Stack: [carry_add, lo_new, hi | rest]
  -- Instruction 5: movup 2
  -- Stack: [carry_add, lo_new, hi | rest] → [hi, carry_add, lo_new | rest]
  miden_movup
  -- Instruction 6: add
  -- Stack: [hi, carry_add, lo_new | rest]
  -- stepAdd: ⟨b :: a :: rest⟩ → (a + b) :: rest
  -- Here: b=hi, a=carry_add → carry_add + hi
  rw [stepAdd]; miden_bind
  simp only [pure, Pure.pure]
  -- Fix addition order: carry_add + hi = hi + carry_add
  congr 1; congr 1; congr 1
  exact add_comm
    (Felt.ofNat (((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32))
    (Felt.ofNat ((c.val * b.val + a.val) / 2 ^ 32))

end MidenLean.Proofs
