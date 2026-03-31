import MidenLean.Proofs.U256.Common
import MidenLean.Proofs.U256.Mulstep
import MidenLean.Proofs.Tactics

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Helper definitions for mulstep output
-- ============================================================================

/-- The carry output of a single mulstep call (raw computation order).
    Given carry-in `a`, value `b`, multiplier `c`, and accumulator `d`,
    mulstep computes `c * b + a` (widening multiply-add), then overflow-adds
    the low 32 bits with `d`. The carry is the sum of the two high parts. -/
noncomputable def mulstepCarry (a b c d : Felt) : Felt :=
  Felt.ofNat (((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32) +
  Felt.ofNat ((c.val * b.val + a.val) / 2 ^ 32)

/-- The low output of a single mulstep call:
    lo = ((c*b+a) % 2^32 + d) % 2^32. -/
noncomputable def mulstepLo (a b c d : Felt) : Felt :=
  Felt.ofNat (((c.val * b.val + a.val) % 2 ^ 32 + d.val) % 2 ^ 32)

-- ============================================================================
-- Helper lemmas for carry isU32
-- ============================================================================

private theorem mulstep_carry_nat_lt (a b c d : Nat)
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (hc : c < 2 ^ 32) (hd : d < 2 ^ 32) :
    (c * b + a) / 2 ^ 32 + ((c * b + a) % 2 ^ 32 + d) / 2 ^ 32 < 2 ^ 32 := by
  have hcba : c * b + a ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1) := by
    have : c * b ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have h1 : (c * b + a) / 2 ^ 32 ≤ 2 ^ 32 - 1 := by
    calc (c * b + a) / 2 ^ 32
        ≤ ((2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := Nat.div_le_div_right hcba
      _ ≤ 2 ^ 32 - 1 := by native_decide
  have h2 : ((c * b + a) % 2 ^ 32 + d) / 2 ^ 32 ≤ 1 := by
    calc ((c * b + a) % 2 ^ 32 + d) / 2 ^ 32
        ≤ ((2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := by
          apply Nat.div_le_div_right
          have : (c * b + a) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by positivity)
          omega
      _ ≤ 1 := by native_decide
  omega

/-- The Felt-level carry from mulstep is isU32. -/
theorem mulstep_carry_isU32 (a b c d : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true)
    (hc : c.isU32 = true) (hd : d.isU32 = true) :
    (mulstepCarry a b c d).isU32 = true := by
  unfold mulstepCarry
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb hc hd ⊢
  have hcba : c.val * b.val + a.val ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1) := by
    have : c.val * b.val ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have h1_lt : (c.val * b.val + a.val) / 2 ^ 32 < GOLDILOCKS_PRIME := by
    calc (c.val * b.val + a.val) / 2 ^ 32
        ≤ ((2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := Nat.div_le_div_right hcba
      _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide
  have h2_lt : ((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32 < GOLDILOCKS_PRIME := by
    calc ((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32
        ≤ ((2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := by
          apply Nat.div_le_div_right
          have : (c.val * b.val + a.val) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by positivity)
          omega
      _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide
  have hsum_lt : ((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32 +
      (c.val * b.val + a.val) / 2 ^ 32 < GOLDILOCKS_PRIME := by
    have h1 : (c.val * b.val + a.val) / 2 ^ 32 ≤ 2 ^ 32 - 1 := by
      calc (c.val * b.val + a.val) / 2 ^ 32
          ≤ ((2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := Nat.div_le_div_right hcba
        _ ≤ 2 ^ 32 - 1 := by native_decide
    have h2 : ((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32 ≤ 1 := by
      calc ((c.val * b.val + a.val) % 2 ^ 32 + d.val) / 2 ^ 32
          ≤ ((2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := by
            apply Nat.div_le_div_right
            have : (c.val * b.val + a.val) % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by positivity)
            omega
        _ ≤ 1 := by native_decide
    unfold GOLDILOCKS_PRIME; omega
  rw [felt_add_val_no_wrap _ _
    (by rw [felt_ofNat_val_lt _ h2_lt, felt_ofNat_val_lt _ h1_lt]; exact hsum_lt)]
  rw [felt_ofNat_val_lt _ h2_lt, felt_ofNat_val_lt _ h1_lt]
  have := mulstep_carry_nat_lt a.val b.val c.val d.val ha hb hc hd
  omega

-- ============================================================================
-- execWithEnv-compatible mulstep lemma
-- ============================================================================

set_option maxHeartbeats 4000000 in
/-- mulstep correctness for execWithEnv: given any env and sufficient fuel,
    mulstep produces [mulstepCarry a b c d, mulstepLo a b c d] ++ rest. -/
theorem mulstep_execWithEnv
    (env : ProcEnv) (fuel : Nat) (a b c d : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: b :: c :: d :: rest)
    (ha : a.isU32 = true) (hb : b.isU32 = true)
    (hc : c.isU32 = true) (hd : d.isU32 = true) :
    execWithEnv env (fuel + 1) s Miden.Core.U256.mulstep =
    some (s.withStack (mulstepCarry a b c d :: mulstepLo a b c d :: rest)) := by
  obtain ⟨stk, mem, frames, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold mulstepCarry mulstepLo
  unfold Miden.Core.U256.mulstep execWithEnv
  simp only [List.foldlM]
  -- movdn 2
  miden_movdn
  -- u32WidenMadd
  rw [stepU32WidenMadd (ha := hc) (hb := hb) (hc := ha)]
  miden_bind
  -- movup 2
  miden_movup
  -- u32OverflowAdd
  rw [stepU32OverflowAdd (ha := u32_mod_isU32 _) (hb := hd)]
  miden_bind
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  -- movup 2
  miden_movup
  -- add
  rw [stepAdd]; miden_bind
  simp only [pure, Pure.pure]

-- ============================================================================
-- Main theorem
-- ============================================================================

set_option maxHeartbeats 64000000 in
/-- `mulstep4` performs four sequential `mulstep` calls, threading carry through.
    Input stack:  [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12] ++ rest
    Output stack: [carry4, x0, x1, x2, x3, x4, lo4, lo3, lo2, lo1] ++ rest
    where carry_i and lo_i are the carry and low outputs of each sequential mulstep call:
      carry1 = mulstepCarry(0, x8, x0, x12),  lo1 = mulstepLo(0, x8, x0, x12)
      carry2 = mulstepCarry(carry1, x7, x0, x11), lo2 = mulstepLo(carry1, x7, x0, x11)
      carry3 = mulstepCarry(carry2, x6, x0, x10), lo3 = mulstepLo(carry2, x6, x0, x10)
      carry4 = mulstepCarry(carry3, x5, x0, x9),  lo4 = mulstepLo(carry3, x5, x0, x9) -/
theorem u256_mulstep4_correct
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: rest)
    (hx0 : x0.isU32 = true) (hx5 : x5.isU32 = true)
    (hx6 : x6.isU32 = true) (hx7 : x7.isU32 = true)
    (hx8 : x8.isU32 = true) (hx9 : x9.isU32 = true)
    (hx10 : x10.isU32 = true) (hx11 : x11.isU32 = true)
    (hx12 : x12.isU32 = true) :
    let carry1 := mulstepCarry 0 x8 x0 x12
    let lo1    := mulstepLo    0 x8 x0 x12
    let carry2 := mulstepCarry carry1 x7 x0 x11
    let lo2    := mulstepLo    carry1 x7 x0 x11
    let carry3 := mulstepCarry carry2 x6 x0 x10
    let lo3    := mulstepLo    carry2 x6 x0 x10
    let carry4 := mulstepCarry carry3 x5 x0 x9
    let lo4    := mulstepLo    carry3 x5 x0 x9
    execWithEnv u256ProcEnv 109 s Miden.Core.U256.mulstep4 =
    some (s.withStack (carry4 :: x0 :: x1 :: x2 :: x3 :: x4 ::
                       lo4 :: lo3 :: lo2 :: lo1 :: rest)) := by
  -- Setup
  obtain ⟨stk, mem, frames, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold Miden.Core.U256.mulstep4 execWithEnv
  simp only [List.foldlM]
  -- ==================================================================
  -- Pre-call-1: movup 12, dup 1, movup 10, push 0
  -- ==================================================================
  miden_movup; miden_dup; miden_movup; miden_step
  -- ==================================================================
  -- Resolve all procedure lookups
  -- ==================================================================
  simp only [u256ProcEnv]
  have h0u : (0 : Felt).isU32 = true := by simp [Felt.isU32]
  -- ==================================================================
  -- Call 1: rewrite execWithEnv call using mulstep_execWithEnv
  -- Use `have` to create a rewrite equation, then `simp only` with it
  -- ==================================================================
  have hcall1 := mulstep_execWithEnv u256ProcEnv 107 0 x8 x0 x12
    (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x9 :: x10 :: x11 :: rest)
    ⟨0 :: x8 :: x0 :: x12 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x9 :: x10 :: x11 :: rest, mem, frames, adv⟩
    rfl h0u hx8 hx0 hx12
  simp only [MidenState.withStack] at hcall1
  simp only [hcall1]
  -- Pre-call-2
  miden_swap; miden_movdn; miden_dup; miden_movup; miden_movup; miden_swap
  -- ==================================================================
  -- Call 2
  -- ==================================================================
  have hc1u : (mulstepCarry 0 x8 x0 x12).isU32 = true :=
    mulstep_carry_isU32 0 x8 x0 x12 h0u hx8 hx0 hx12
  have hcall2 := mulstep_execWithEnv u256ProcEnv 107 (mulstepCarry 0 x8 x0 x12) x7 x0 x11
    (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 ::
     mulstepLo 0 x8 x0 x12 :: x9 :: x10 :: rest)
    ⟨mulstepCarry 0 x8 x0 x12 :: x7 :: x0 :: x11 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 ::
     mulstepLo 0 x8 x0 x12 :: x9 :: x10 :: rest, mem, frames, adv⟩
    rfl hc1u hx7 hx0 hx11
  simp only [MidenState.withStack] at hcall2
  simp only [hcall2]
  -- Pre-call-3
  miden_swap; miden_movdn; miden_dup; miden_movup; miden_movup; miden_swap
  -- ==================================================================
  -- Call 3
  -- ==================================================================
  have hc2u : (mulstepCarry (mulstepCarry 0 x8 x0 x12) x7 x0 x11).isU32 = true :=
    mulstep_carry_isU32 _ x7 x0 x11 hc1u hx7 hx0 hx11
  have hcall3 := mulstep_execWithEnv u256ProcEnv 107
    (mulstepCarry (mulstepCarry 0 x8 x0 x12) x7 x0 x11) x6 x0 x10
    (x0 :: x1 :: x2 :: x3 :: x4 :: x5 ::
     mulstepLo (mulstepCarry 0 x8 x0 x12) x7 x0 x11 ::
     mulstepLo 0 x8 x0 x12 :: x9 :: rest)
    ⟨mulstepCarry (mulstepCarry 0 x8 x0 x12) x7 x0 x11 :: x6 :: x0 :: x10 :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 ::
     mulstepLo (mulstepCarry 0 x8 x0 x12) x7 x0 x11 ::
     mulstepLo 0 x8 x0 x12 :: x9 :: rest, mem, frames, adv⟩
    rfl hc2u hx6 hx0 hx10
  simp only [MidenState.withStack] at hcall3
  simp only [hcall3]
  -- Pre-call-4
  miden_swap; miden_movdn; miden_dup; miden_movup; miden_movup; miden_swap
  -- ==================================================================
  -- Call 4
  -- ==================================================================
  have hc3u : (mulstepCarry (mulstepCarry (mulstepCarry 0 x8 x0 x12) x7 x0 x11) x6 x0 x10).isU32 = true :=
    mulstep_carry_isU32 _ x6 x0 x10 hc2u hx6 hx0 hx10
  have hcall4 := mulstep_execWithEnv u256ProcEnv 107
    (mulstepCarry (mulstepCarry (mulstepCarry 0 x8 x0 x12) x7 x0 x11) x6 x0 x10) x5 x0 x9
    (x0 :: x1 :: x2 :: x3 :: x4 ::
     mulstepLo (mulstepCarry (mulstepCarry 0 x8 x0 x12) x7 x0 x11) x6 x0 x10 ::
     mulstepLo (mulstepCarry 0 x8 x0 x12) x7 x0 x11 ::
     mulstepLo 0 x8 x0 x12 :: rest)
    ⟨mulstepCarry (mulstepCarry (mulstepCarry 0 x8 x0 x12) x7 x0 x11) x6 x0 x10 :: x5 :: x0 :: x9 :: x0 :: x1 :: x2 :: x3 :: x4 ::
     mulstepLo (mulstepCarry (mulstepCarry 0 x8 x0 x12) x7 x0 x11) x6 x0 x10 ::
     mulstepLo (mulstepCarry 0 x8 x0 x12) x7 x0 x11 ::
     mulstepLo 0 x8 x0 x12 :: rest, mem, frames, adv⟩
    rfl hc3u hx5 hx0 hx9
  simp only [MidenState.withStack] at hcall4
  simp only [hcall4]
  -- ==================================================================
  -- Final: swap 1, movdn 6
  -- ==================================================================
  miden_swap; miden_movdn
  -- Close
  simp only [pure, Pure.pure]

end MidenLean.Proofs
