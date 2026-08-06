import MidenLean.Proofs.U128.WrappingMul
import MidenLean.Proofs.Helpers
import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Helper lemmas
-- ============================================================================

private theorem felt128_val : (128 : Felt).val = 128 :=
  felt_ofNat_val_lt 128 (by unfold GOLDILOCKS_PRIME; omega)

private theorem felt64_val : (64 : Felt).val = 64 :=
  felt_ofNat_val_lt 64 (by unfold GOLDILOCKS_PRIME; omega)

private theorem pow2_lt_prime (n : Nat) (h : n < 64) :
    2 ^ n < GOLDILOCKS_PRIME := by
  have h1 : 2 ^ n ≤ 2 ^ 63 := by
    apply Nat.pow_le_pow_right <;> omega
  have h2 : (2 : Nat) ^ 63 < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; norm_num
  omega

private theorem pow2_val (n : Nat) (h : n < 64) :
    (Felt.ofNat (2 ^ n)).val = 2 ^ n :=
  felt_ofNat_val_lt _ (pow2_lt_prime n h)

private theorem pow2_val_lt_2_64 (n : Nat) (h : n < 64) :
    (Felt.ofNat (2 ^ n)).val < 2 ^ 64 := by
  rw [pow2_val n h]; exact Nat.pow_lt_pow_right (by omega) h

private theorem u32OverflowingSub_snd_of_ge (a b : Nat) (h : a ≥ b) :
    (u32OverflowingSub a b).2 = a - b := by
  unfold u32OverflowingSub; simp [h]

private theorem sub64_val (shift : Felt)
    (hshift_u32 : shift.isU32 = true)
    (hshift_ge64 : ¬(shift.val < 64)) :
    (Felt.ofNat (u32OverflowingSub shift.val 64).2).val =
    shift.val - 64 := by
  rw [u32OverflowingSub_snd_of_ge _ _ (by omega)]
  apply felt_ofNat_val_lt
  simp [Felt.isU32, decide_eq_true_eq] at hshift_u32
  unfold GOLDILOCKS_PRIME; omega

private theorem sub64_le63 (shift : Felt)
    (hshift_u32 : shift.isU32 = true)
    (hshift_ge64 : ¬(shift.val < 64))
    (hshift_lt128 : shift.val < 128) :
    (Felt.ofNat (u32OverflowingSub shift.val 64).2).val ≤ 63 := by
  rw [sub64_val shift hshift_u32 hshift_ge64]
  omega

private theorem sub64_lt64 (shift : Felt)
    (hshift_u32 : shift.isU32 = true)
    (hshift_ge64 : ¬(shift.val < 64))
    (hshift_lt128 : shift.val < 128) :
    (Felt.ofNat (u32OverflowingSub shift.val 64).2).val < 64 := by
  rw [sub64_val shift hshift_u32 hshift_ge64]
  omega

-- ============================================================================
-- Chunk definitions
-- ============================================================================

/-- Validation and condition: dup, push 128, u32Lt, assert, dup, push 64, u32Lt -/
private def shl_prefix : List Op := [
  .inst (.dup 0), .inst (.push 128), .inst (.u32Lt),
  .inst (.assertWithError "shift amount must be in the range [0, 128)"),
  .inst (.dup 0), .inst (.push 64), .inst (.u32Lt)]

/-- True branch setup (shift < 64): pow2, u32Split, push 0, push 0, movup 3, movup 3 -/
private def shl_true_setup : List Op := [
  .inst (.pow2), .inst (.u32Split),
  .inst (.push 0), .inst (.push 0),
  .inst (.movup 3), .inst (.movup 3)]

/-- False branch setup (shift >= 64): push 64, u32WrappingSub, pow2, u32Split, push 0, push 0 -/
private def shl_false_setup : List Op := [
  .inst (.push 64), .inst (.u32WrappingSub),
  .inst (.pow2), .inst (.u32Split),
  .inst (.push 0), .inst (.push 0)]

private def shl_true_branch : List Op :=
  shl_true_setup ++ [.inst (.exec "wrapping_mul")]

private def shl_false_branch : List Op :=
  shl_false_setup ++ [.inst (.exec "wrapping_mul")]

-- ============================================================================
-- Decomposition
-- ============================================================================

private theorem shl_decomp :
    Miden.Core.U128.shl.body = shl_prefix ++ [.ifElse shl_true_branch shl_false_branch] := by
  simp [Miden.Core.U128.shl, shl_prefix, shl_true_branch, shl_true_setup,
        shl_false_branch, shl_false_setup]

-- ============================================================================
-- Prefix correctness
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem shl_prefix_correct (env : ProcEnv) (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true)
    (hshift_lt128 : shift.val < 128) :
    execProcedure env (fuel + 1)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩
      shl_prefix =
    some ⟨(if shift.val < 64 then (1 : Felt) else 0) ::
          shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩ := by
  unfold shl_prefix execProcedure
  simp only [List.foldlM]
  dsimp only [bind, Bind.bind, Option.bind]
  miden_dup
  miden_step -- push 128
  rw [stepU32Lt (ha := hshift_u32) (hb := U32.felt128_isU32)]
  miden_bind
  simp only [felt128_val]
  rw [stepAssertWithError (h := by simp [hshift_lt128, Felt.val_one'])]
  miden_bind
  miden_dup
  miden_step -- push 64
  rw [stepU32Lt (ha := hshift_u32) (hb := U32.felt64_isU32)]
  miden_bind
  simp only [felt64_val]
  simp [pure, Pure.pure]

-- ============================================================================
-- True branch setup correctness (shift < 64)
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem shl_true_setup_correct (env : ProcEnv) (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hshift_lt64 : shift.val < 64) :
    let p := Felt.ofNat (2 ^ shift.val)
    execProcedure env (fuel + 1)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩
      shl_true_setup =
    some ⟨p.lo32 :: p.hi32 :: 0 :: 0 :: a0 :: a1 :: a2 :: a3 :: rest,
          mem, frames, adv⟩ := by
  unfold shl_true_setup execProcedure
  simp only [List.foldlM]
  dsimp only [bind, Bind.bind, Option.bind]
  rw [stepPow2 (ha := by omega)]
  miden_bind
  rw [stepU32Split]
  miden_bind
  miden_step  -- push 0
  miden_step  -- push 0
  miden_movup  -- movup 3
  miden_movup  -- movup 3
  simp [pure, Pure.pure]

-- ============================================================================
-- False branch setup correctness (shift >= 64)
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem shl_false_setup_correct (env : ProcEnv) (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true)
    (hshift_ge64 : ¬(shift.val < 64))
    (hshift_lt128 : shift.val < 128) :
    let s64 := Felt.ofNat (u32OverflowingSub shift.val 64).2
    let q := Felt.ofNat (2 ^ s64.val)
    execProcedure env (fuel + 1)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩
      shl_false_setup =
    some ⟨0 :: 0 :: q.lo32 :: q.hi32 :: a0 :: a1 :: a2 :: a3 :: rest,
          mem, frames, adv⟩ := by
  unfold shl_false_setup execProcedure
  simp only [List.foldlM]
  dsimp only [bind, Bind.bind, Option.bind]
  miden_step  -- push 64
  rw [stepU32WrappingSubLocal (ha := hshift_u32) (hb := U32.felt64_isU32)]
  miden_bind
  simp only [felt64_val]
  rw [stepPow2 (ha := sub64_le63 shift hshift_u32 hshift_ge64 hshift_lt128)]
  miden_bind
  rw [stepU32Split]
  miden_bind
  miden_step  -- push 0
  miden_step  -- push 0
  simp [pure, Pure.pure]

-- ============================================================================
-- True branch full correctness
-- ============================================================================

set_option maxHeartbeats 8000000 in
private theorem shl_true_branch_correct (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
  (hshift_lt64 : shift.val < 64)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true) :
    let p := Felt.ofNat (2 ^ shift.val)
    execProcedure u128ProcEnv (fuel + 2)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩
      shl_true_branch =
    some ⟨u128MulC0 a0 p.lo32 ::
          u128MulC1 a0 a1 p.lo32 p.hi32 ::
          u128MulC2 a0 a1 a2 p.lo32 p.hi32 0 ::
          u128MulC3 a0 a1 a2 a3 p.lo32 p.hi32 0 0 ::
          rest, mem, frames, adv⟩ := by
  let p := Felt.ofNat (2 ^ shift.val)
  show execProcedure u128ProcEnv (fuel + 2)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩
      (shl_true_setup ++ ([.inst (.exec "wrapping_mul")] : List Op)) =
    some ⟨u128MulC0 a0 p.lo32 ::
          u128MulC1 a0 a1 p.lo32 p.hi32 ::
          u128MulC2 a0 a1 a2 p.lo32 p.hi32 0 ::
          u128MulC3 a0 a1 a2 a3 p.lo32 p.hi32 0 0 ::
          rest, mem, frames, adv⟩
  rw [execProcedure_append]
  rw [shl_true_setup_correct u128ProcEnv (fuel + 1) shift a0 a1 a2 a3 rest mem frames adv
    hshift_lt64]
  simp only [bind, Bind.bind, Option.bind]
  unfold execProcedure
  simp only [List.foldlM, u128ProcEnv, bind, Bind.bind, Option.bind, pure, Pure.pure]
  rw [u128_wrapping_mul_exec (env := u128ProcEnv) (fuel := fuel)
    a0 a1 a2 a3
    (Felt.ofNat (2 ^ shift.val)).lo32
    (Felt.ofNat (2 ^ shift.val)).hi32
    0 0
    rest
    ⟨(Felt.ofNat (2 ^ shift.val)).lo32 ::
      (Felt.ofNat (2 ^ shift.val)).hi32 :: 0 :: 0 :: a0 :: a1 :: a2 :: a3 :: rest,
      mem, frames, adv⟩
    rfl
    ha0 ha1 ha2 ha3
    (U32.lo32_isU32 _)
    (U32.hi32_isU32_of_val_lt_2_64 _ (pow2_val_lt_2_64 shift.val hshift_lt64))
    (by apply felt_ofNat_isU32_of_lt; norm_num)
    (by apply felt_ofNat_isU32_of_lt; norm_num)]
  rfl

-- ============================================================================
-- False branch full correctness
-- ============================================================================

set_option maxHeartbeats 8000000 in
private theorem shl_false_branch_correct (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true)
    (hshift_ge64 : ¬(shift.val < 64))
    (hshift_lt128 : shift.val < 128)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true) :
    let s64 := Felt.ofNat (u32OverflowingSub shift.val 64).2
    let q := Felt.ofNat (2 ^ s64.val)
    execProcedure u128ProcEnv (fuel + 2)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩
      shl_false_branch =
    some ⟨u128MulC0 a0 0 ::
          u128MulC1 a0 a1 0 0 ::
          u128MulC2 a0 a1 a2 0 0 q.lo32 ::
          u128MulC3 a0 a1 a2 a3 0 0 q.lo32 q.hi32 ::
          rest, mem, frames, adv⟩ := by
  let s64 := Felt.ofNat (u32OverflowingSub shift.val 64).2
  let q := Felt.ofNat (2 ^ s64.val)
  show execProcedure u128ProcEnv (fuel + 2)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩
      (shl_false_setup ++ ([.inst (.exec "wrapping_mul")] : List Op)) =
    some ⟨u128MulC0 a0 0 ::
          u128MulC1 a0 a1 0 0 ::
          u128MulC2 a0 a1 a2 0 0 q.lo32 ::
          u128MulC3 a0 a1 a2 a3 0 0 q.lo32 q.hi32 ::
          rest, mem, frames, adv⟩
  rw [execProcedure_append]
  rw [shl_false_setup_correct u128ProcEnv (fuel + 1) shift a0 a1 a2 a3 rest mem frames adv
    hshift_u32 hshift_ge64 hshift_lt128]
  simp only [bind, Bind.bind, Option.bind]
  unfold execProcedure
  simp only [List.foldlM, u128ProcEnv, bind, Bind.bind, Option.bind, pure, Pure.pure]
  rw [u128_wrapping_mul_exec (env := u128ProcEnv) (fuel := fuel)
    a0 a1 a2 a3
    0 0
    (Felt.ofNat (2 ^ (Felt.ofNat (u32OverflowingSub shift.val 64).2).val)).lo32
    (Felt.ofNat (2 ^ (Felt.ofNat (u32OverflowingSub shift.val 64).2).val)).hi32
    rest
    ⟨0 :: 0 ::
      (Felt.ofNat (2 ^ (Felt.ofNat (u32OverflowingSub shift.val 64).2).val)).lo32 ::
      (Felt.ofNat (2 ^ (Felt.ofNat (u32OverflowingSub shift.val 64).2).val)).hi32 ::
      a0 :: a1 :: a2 :: a3 :: rest,
      mem, frames, adv⟩
    rfl
    ha0 ha1 ha2 ha3
    (by apply felt_ofNat_isU32_of_lt; norm_num)
    (by apply felt_ofNat_isU32_of_lt; norm_num)
    (U32.lo32_isU32 _)
    (by
      have hq_lt2_64 : q.val < 2 ^ 64 := by
        rw [show q = Felt.ofNat (2 ^ s64.val) by rfl]
        exact pow2_val_lt_2_64 s64.val
          (sub64_lt64 shift hshift_u32 hshift_ge64 hshift_lt128)
      exact U32.hi32_isU32_of_val_lt_2_64 q hq_lt2_64)]
  rfl

-- ============================================================================
-- Low-level exec theorem
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- `u128::shl` computes the left shift of a 128-bit value by a given amount (raw limb version).
    Input stack:  [shift, a0, a1, a2, a3] ++ rest  (shift < 128, a0..a3 are u32 limbs)
    Output stack: [r0, r1, r2, r3] ++ rest
    where `r0..r3` are the u32 limbs of `(a << shift) mod 2^128`, computed via
    multiplication by `2^shift` using `wrapping_mul`.
    Parametric in `fuel` so this lemma serves both as a callee summary for
    reflective callers and as the basis for `u128_shl_correct`. -/
@[miden_exec_summary]
theorem u128_shl_exec
    (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = shift :: a0 :: a1 :: a2 :: a3 :: rest)
    (hshift_u32 : shift.isU32 = true)
    (hshift_lt128 : shift.val < 128)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true) :
    execProcedure u128ProcEnv (fuel + 3) s Miden.Core.U128.shl =
    some (if shift.val < 64 then
      let p := Felt.ofNat (2 ^ shift.val)
      s.withStack (
        u128MulC0 a0 p.lo32 ::
        u128MulC1 a0 a1 p.lo32 p.hi32 ::
        u128MulC2 a0 a1 a2 p.lo32 p.hi32 0 ::
        u128MulC3 a0 a1 a2 a3 p.lo32 p.hi32 0 0 ::
        rest)
    else
      let s64 := Felt.ofNat (u32OverflowingSub shift.val 64).2
      let q := Felt.ofNat (2 ^ s64.val)
      s.withStack (
        u128MulC0 a0 0 ::
        u128MulC1 a0 a1 0 0 ::
        u128MulC2 a0 a1 a2 0 0 q.lo32 ::
        u128MulC3 a0 a1 a2 a3 0 0 q.lo32 q.hi32 ::
        rest)) := by
  rcases s with ⟨stack, mem, frames, adv⟩
  simp only [Concrete.State.withStack] at hs ⊢
  subst hs
  rw [execProcedure_body_eq _ _ _ _ _ shl_decomp rfl, execProcedure_append]
  rw [shl_prefix_correct u128ProcEnv (fuel + 2) shift a0 a1 a2 a3 rest mem frames adv
    hshift_u32 hshift_lt128]
  simp only [bind, Bind.bind, Option.bind]
  miden_vcg_step
  · exact shl_true_branch_correct fuel shift a0 a1 a2 a3 rest mem frames adv
      h ha0 ha1 ha2 ha3
  · have hshift_ge64 : ¬ shift.val < 64 := by omega
    exact shl_false_branch_correct fuel shift a0 a1 a2 a3 rest mem frames adv
      hshift_u32 hshift_ge64 hshift_lt128 ha0 ha1 ha2 ha3

-- ============================================================================
-- High-level correctness theorem
-- ============================================================================

-- Helper: for shift < 64, U128.ofNat(2^shift) limbs match p.lo32/p.hi32/0/0
private theorem pow2_ofNat_a0 (n : Nat) :
    (U128.ofNat (2^n)).a0.val = Felt.ofNat (2^n % 2^32) := by
  simp [U128.ofNat_a0]

private theorem pow2_ofNat_a1_lt64 (n : Nat) (h : n < 64) :
    (U128.ofNat (2^n)).a1.val = Felt.ofNat (2^n / 2^32) := by
  simp only [U128.ofNat_a1]
  congr 1
  rw [Nat.mod_eq_of_lt]
  calc 2^n / 2^32 ≤ 2^63 / 2^32 :=
    Nat.div_le_div_right (Nat.pow_le_pow_right (by omega) (by omega))
    _ < 2^32 := by decide

private theorem pow2_ofNat_a2_lt64 (n : Nat) (h : n < 64) :
    (U128.ofNat (2^n)).a2.val = 0 := by
  simp only [U128.ofNat_a2]
  rw [Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by omega) h)]
  decide

private theorem pow2_ofNat_a3_lt64 (n : Nat) (h : n < 64) :
    (U128.ofNat (2^n)).a3.val = 0 := by
  simp only [U128.ofNat_a3]
  rw [Nat.div_eq_of_lt (show 2^n < 2^96 from Nat.pow_lt_pow_right (by omega) (by omega))]
  decide

private theorem pow2_ofNat_a0_ge64 (n : Nat) (h : 64 ≤ n) :
    (U128.ofNat (2^n)).a0.val = 0 := by
  simp only [U128.ofNat_a0]
  rw [(Nat.dvd_iff_mod_eq_zero.mp (Nat.pow_dvd_pow 2 (by omega : 32 ≤ n)))]
  decide

private theorem pow2_ofNat_a1_ge64 (n : Nat) (h : 64 ≤ n) :
    (U128.ofNat (2^n)).a1.val = 0 := by
  simp only [U128.ofNat_a1]
  rw [Nat.pow_div (by omega : 32 ≤ n) (by omega)]
  rw [(Nat.dvd_iff_mod_eq_zero.mp (Nat.pow_dvd_pow 2 (by omega : 32 ≤ n - 32)))]
  decide

private theorem pow2_ofNat_a2_ge64 (n : Nat) (h : 64 ≤ n) (_ : n < 128) :
    (U128.ofNat (2^n)).a2.val = Felt.ofNat (2^(n-64) % 2^32) := by
  simp only [U128.ofNat_a2]
  congr 1; rw [Nat.pow_div (by omega : 64 ≤ n) (by omega)]

private theorem pow2_ofNat_a3_ge64 (n : Nat) (h : 64 ≤ n) (_ : n < 128) :
    (U128.ofNat (2^n)).a3.val = Felt.ofNat (2^(n-64) / 2^32) := by
  simp only [U128.ofNat_a3]
  congr 1
  rw [show (2:Nat)^n / 2^96 = 2^(n-64) / 2^32 from by
    have : 2^n / 2^96 = 2^n / 2^64 / 2^32 := by
      rw [Nat.div_div_eq_div_mul]; ring_nf
    rw [this, Nat.pow_div (by omega : 64 ≤ n) (by omega)]]
  rw [Nat.mod_eq_of_lt]
  calc 2^(n-64) / 2^32 ≤ 2^63 / 2^32 :=
    Nat.div_le_div_right (Nat.pow_le_pow_right (by omega) (by omega))
    _ < 2^32 := by decide

-- Helper to recover Felt.ofNat(2^n).val = 2^n for shift values
private theorem felt_pow2_val (n : Nat) (h : n < 64) :
    (Felt.ofNat (2^n)).val = 2^n :=
  felt_ofNat_val_lt _ (pow2_lt_prime n h)

-- lo32 of Felt.ofNat(2^n) = Felt.ofNat (2^n % 2^32)
private theorem felt_pow2_lo32 (n : Nat) (h : n < 64) :
    (Felt.ofNat (2^n)).lo32 = Felt.ofNat (2^n % 2^32) := by
  simp only [Felt.lo32, felt_pow2_val n h]

-- hi32 of Felt.ofNat(2^n) = Felt.ofNat (2^n / 2^32)
private theorem felt_pow2_hi32 (n : Nat) (h : n < 64) :
    (Felt.ofNat (2^n)).hi32 = Felt.ofNat (2^n / 2^32) := by
  simp only [Felt.hi32, felt_pow2_val n h]

set_option maxHeartbeats 12000000 in
/-- `u128::shl` left-shifts a u128 value by `shift` bits (mod 2^128).
    Input stack:  [shift, a.a0, a.a1, a.a2, a.a3] ++ rest
    Output stack: [(a.shl shift).a0, (a.shl shift).a1, (a.shl shift).a2, (a.shl shift).a3] ++ rest -/
theorem u128_shl_correct (a : U128) (shift : U32) (rest : List Felt) (s : Concrete.State)
    (hs : s.stack = shift.val :: a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest)
    (hshift_lt128 : shift.toNat < 128) :
    execProcedure u128ProcEnv 70 s Miden.Core.U128.shl =
    some (s.withStack (
      (a.shl shift.toNat).a0.val :: (a.shl shift.toNat).a1.val ::
      (a.shl shift.toNat).a2.val :: (a.shl shift.toNat).a3.val :: rest)) := by
  have h := u128_shl_exec 67 shift.val a.a0.val a.a1.val a.a2.val a.a3.val rest s hs
    shift.isU32 hshift_lt128 a.a0.isU32 a.a1.isU32 a.a2.isU32 a.a3.isU32
  rw [h]
  rw [U128.shl_eq_mul_ofNat_pow2 a shift.toNat]
  -- Convert RHS from (a * pow2).aI.val to u128MulC0..C3 form
  rw [← u128MulResult_eq a (U128.ofNat (2 ^ shift.toNat))]
  by_cases hlt : shift.toNat < 64
  · -- shift < 64: raw uses (p.lo32, p.hi32, 0, 0) = ofNat(2^shift) limbs
    simp only [U32.toNat, hlt, ↓reduceIte]
    congr 1; congr 1
    rw [felt_pow2_lo32 shift.toNat hlt, pow2_ofNat_a0 shift.toNat,
        felt_pow2_hi32 shift.toNat hlt, pow2_ofNat_a1_lt64 shift.toNat hlt,
        pow2_ofNat_a2_lt64 shift.toNat hlt, pow2_ofNat_a3_lt64 shift.toNat hlt]
  · -- shift >= 64: raw uses (0, 0, q.lo32, q.hi32) = ofNat(2^shift) limbs
    push_neg at hlt
    simp only [U32.toNat, show ¬(shift.toNat < 64) from by omega, ↓reduceIte]
    have hs64_val : (Felt.ofNat (u32OverflowingSub shift.toNat 64).2).val = shift.toNat - 64 := by
      unfold u32OverflowingSub
      simp only [ge_iff_le, show shift.toNat ≥ 64 from hlt, ↓reduceIte]
      exact felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)
    have hs64_lt : shift.toNat - 64 < 64 := by omega
    -- Rewrite all raw pow2 limbs to match ofNat(2^shift) limbs
    have hlo : (Felt.ofNat (2 ^ (Felt.ofNat (u32OverflowingSub shift.toNat 64).2).val)).lo32 =
        Felt.ofNat (2 ^ (shift.toNat - 64) % 2 ^ 32) := by
      rw [hs64_val, felt_pow2_lo32 (shift.toNat - 64) hs64_lt]
    have hhi : (Felt.ofNat (2 ^ (Felt.ofNat (u32OverflowingSub shift.toNat 64).2).val)).hi32 =
        Felt.ofNat (2 ^ (shift.toNat - 64) / 2 ^ 32) := by
      rw [hs64_val, felt_pow2_hi32 (shift.toNat - 64) hs64_lt]
    rw [hlo, hhi]
    congr 1; congr 1
    rw [pow2_ofNat_a0_ge64 shift.toNat hlt, pow2_ofNat_a1_ge64 shift.toNat hlt,
        pow2_ofNat_a2_ge64 shift.toNat hlt hshift_lt128,
        pow2_ofNat_a3_ge64 shift.toNat hlt hshift_lt128]

end MidenLean.Proofs
