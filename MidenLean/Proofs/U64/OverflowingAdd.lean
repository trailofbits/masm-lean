import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

theorem u64_overflowing_add_run
    (env : ProcEnv) (fuel : Nat)
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) (evts : List Felt)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    execWithEnv env (fuel + 1) ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, mem, locs, adv, evts⟩
      Miden.Core.U64.overflowing_add =
    some ⟨
      Felt.ofNat ((a_hi.val + b_hi.val + (b_lo.val + a_lo.val) / 2 ^ 32) / 2 ^ 32) ::
      Felt.ofNat ((b_lo.val + a_lo.val) % 2 ^ 32) ::
      Felt.ofNat ((a_hi.val + b_hi.val + (b_lo.val + a_lo.val) / 2 ^ 32) % 2 ^ 32) ::
      rest,
      mem, locs, adv, evts⟩ := by
  unfold Miden.Core.U64.overflowing_add execWithEnv
  simp only [List.foldlM]
  miden_movup
  rw [stepU32WidenAdd (ha := by assumption) (hb := by assumption)]
  miden_bind
  miden_movdn
  have h_mod_isU32 : (Felt.ofNat ((b_lo.val + a_lo.val) % 2 ^ 32)).isU32 = true :=
    u32_mod_isU32 _
  have h_carry_isU32 : (Felt.ofNat ((b_lo.val + a_lo.val) / 2 ^ 32)).isU32 = true :=
    u32_div_2_32_isU32 b_lo a_lo hb_lo ha_lo
  rw [stepU32WidenAdd3 (ha := by assumption) (hb := by assumption) (hc := by assumption)]
  miden_bind
  miden_movdn
  dsimp only [pure, Pure.pure]
  have hcarry : (Felt.ofNat ((b_lo.val + a_lo.val) / 2 ^ 32)).val =
      (b_lo.val + a_lo.val) / 2 ^ 32 :=
    felt_ofNat_val_lt _ (sum_div_2_32_lt_prime b_lo a_lo)
  rw [hcarry]

/-- `u64::overflowing_add` correctly computes addition of two u64 values with carry.
    Input stack:  [b_lo, b_hi, a_lo, a_hi] ++ rest
    Output stack: [overflow, c_lo, c_hi] ++ rest
    where `(c_hi, c_lo)` is the 64-bit sum and `overflow` is the carry bit. -/
theorem u64_overflowing_add_correct
    (a_lo a_hi b_lo b_hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true) (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true) (hb_hi : b_hi.isU32 = true) :
    exec 10 s Miden.Core.U64.overflowing_add =
    some (s.withStack (
      let lo_sum := b_lo.val + a_lo.val
      let carry := lo_sum / 2 ^ 32
      let hi_sum := a_hi.val + b_hi.val + carry
      Felt.ofNat (hi_sum / 2 ^ 32) ::
      Felt.ofNat (lo_sum % 2 ^ 32) ::
      Felt.ofNat (hi_sum % 2 ^ 32) :: rest)) := by
  obtain ⟨stk, mem, locs, adv, evts⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  simpa [exec] using
    u64_overflowing_add_run (fun _ => none) 9 a_lo a_hi b_lo b_hi rest mem locs adv
      ha_lo ha_hi hb_lo hb_hi

end MidenLean.Proofs
