import MidenLean.Proofs.Tactics
import MidenLean.Proofs.Sha256.Common
import MidenLean.Proofs.Sha256.SmallSigma0
import MidenLean.Proofs.Sha256.SmallSigma1
import MidenLean.Spec.Sha256Spec

/-!
# compute_message_schedule_word Correctness

Proves that the MASM procedure `compute_message_schedule_word` computes
the SHA-256 message schedule expansion:

  W[t] = σ₁(W[t-2]) + σ₀(W[t-15]) + W[t-16] + W[t-7]

per FIPS 180-4 §6.2.2.

## Input stack

  [W[t-2], W[t-7], W[t-15], W[t-16], ...rest]

(Confirmed from MASM source comments: a=msg[i-2], b=msg[i-7], c=msg[i-15], d=msg[i-16])

## Proof architecture (per DESIGN-end-to-end-verification.md §3)

- Layer 1: `_layer1_total` — biconditional: exec succeeds ↔ domain ∧ local semantics
- Layer 2: `_layer2_spec_equiv` — local semantics → SHA-256 spec
- Combined: `_layer12_state_spec_total` — exec succeeds ↔ state_spec
-/

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Layer-1 definitions: code-level semantics
-- ============================================================================

/-- Layer-1 local output for `compute_message_schedule_word`.
    This is the intermediate representation before bridging to the SHA-256 spec.
    Computes: u32_wrapping_add(u32_wrapping_add3(σ₁(w2), σ₀(w15), w7), w16) -/
def compute_msw_local_out (w2 w7 w15 w16 : Felt) : Felt :=
  let s1 := sha256_small_sigma_1_local_out w2
  let s0 := sha256_small_sigma_0_local_out w15
  let sum3 := Felt.ofNat ((s1.val + s0.val + w7.val) % u32Max)
  Felt.ofNat ((sum3.val + w16.val) % u32Max)

/-- Layer-1 local semantic relation. -/
def compute_msw_sem (s s' : MidenState) : Prop :=
  ∃ w2 w7 w15 w16 rest,
    s.stack = w2 :: w7 :: w15 :: w16 :: rest ∧
    s' = s.withStack (compute_msw_local_out w2 w7 w15 w16 :: rest)

-- ============================================================================
-- Layer-2 definitions: bridge to SHA-256 spec
-- ============================================================================

/-- Layer-2 mathematical output: the SHA-256 message schedule word. -/
def compute_msw_spec_out (w2 w7 w15 w16 : Felt) : Felt :=
  Felt.ofNat (Sha256Spec.messageScheduleWord
    (BitVec.ofNat 32 w2.val) (BitVec.ofNat 32 w15.val)
    (BitVec.ofNat 32 w16.val) (BitVec.ofNat 32 w7.val)).toNat

/-- Code-level partial IO spec. The u32 domain is part of the spec itself,
    not carried as a separate side condition (per DESIGN §1.1). -/
def compute_msw_io_spec (w2 w7 w15 w16 out : Felt) : Prop :=
  w2.isU32 = true ∧ w7.isU32 = true ∧ w15.isU32 = true ∧ w16.isU32 = true ∧
  out = compute_msw_spec_out w2 w7 w15 w16

/-- Code-level state spec, lifting the IO spec to machine states. -/
def compute_msw_state_spec (s s' : MidenState) : Prop :=
  ∃ w2 w7 w15 w16 rest out,
    s.stack = w2 :: w7 :: w15 :: w16 :: rest ∧
    compute_msw_io_spec w2 w7 w15 w16 out ∧
    s' = s.withStack (out :: rest)

/-- Domain derived from state spec (per DESIGN §3.0). -/
def compute_msw_dom (s : MidenState) : Prop :=
  ∃ s', compute_msw_state_spec s s'

private theorem compute_msw_dom_iff
    (s : MidenState) :
    compute_msw_dom s ↔
      ∃ w2 w7 w15 w16 rest,
        s.stack = w2 :: w7 :: w15 :: w16 :: rest ∧
        w2.isU32 = true ∧ w7.isU32 = true ∧ w15.isU32 = true ∧ w16.isU32 = true := by
  constructor
  · rintro ⟨s', w2, w7, w15, w16, rest, out, hs, h_io, hs'⟩
    exact ⟨w2, w7, w15, w16, rest, hs, h_io.1, h_io.2.1, h_io.2.2.1, h_io.2.2.2.1⟩
  · rintro ⟨w2, w7, w15, w16, rest, hs, h2, h7, h15, h16⟩
    refine ⟨s.withStack (compute_msw_spec_out w2 w7 w15 w16 :: rest),
      w2, w7, w15, w16, rest, compute_msw_spec_out w2 w7 w15 w16, hs, ?_, rfl⟩
    exact ⟨h2, h7, h15, h16, rfl⟩

-- ============================================================================
-- Layer-1 theorems (DESIGN §3.1, §3.2, §3.3)
-- ============================================================================

-- Helper lemmas for intermediate isU32 / bound conditions in composition proof
private theorem u32RotateRight_val_lt_msw (a : Nat) (n : Nat) (ha : a < 2 ^ 32) :
    u32RotateRight a n < 2 ^ 32 := by
  unfold u32RotateRight u32Max
  apply Nat_or_lt_of_lt
  · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha
  · exact Nat.mod_lt _ (by positivity)

private theorem u32RotateRight_lt_prime_msw (a : Nat) (n : Nat) (ha : a < 2 ^ 32) :
    u32RotateRight a n < GOLDILOCKS_PRIME := by
  calc u32RotateRight a n < 2 ^ 32 := u32RotateRight_val_lt_msw a n ha
    _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; omega

private theorem u32_div_lt_prime_msw (a : Nat) (n : Nat) (ha : a < 2 ^ 32) :
    a / 2 ^ n < GOLDILOCKS_PRIME := by
  calc a / 2 ^ n ≤ a := Nat.div_le_self _ _
    _ < 2 ^ 32 := ha
    _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; omega

private theorem u32_xor_lt_prime_msw (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    a ^^^ b < GOLDILOCKS_PRIME := by
  calc a ^^^ b < 2 ^ 32 := Nat_xor_lt_of_lt ha hb
    _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; omega

private theorem messageScheduleWord_nat_eq_spec
    (w2 w15 w16 w7 : Nat) :
    (Sha256Spec.messageScheduleWord
      (BitVec.ofNat 32 w2) (BitVec.ofNat 32 w15)
      (BitVec.ofNat 32 w16) (BitVec.ofNat 32 w7)).toNat =
    ((Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2)).toNat +
      (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15)).toNat + w16 + w7) % u32Max := by
  unfold Sha256Spec.messageScheduleWord BitVec.toNat u32Max
  rw [BitVec.toFin_add]
  simp [Fin.val_add, Nat.add_assoc]

-- Fuel equivalence for flat instruction lists (sigma_0 and sigma_1 have no exec calls)
private theorem sigma1_fuel_19_eq_20 (env : ProcEnv) (s : MidenState) :
    execWithEnv env 19 s Miden.Crypto.Sha256.small_sigma_1 =
    execWithEnv env 20 s Miden.Crypto.Sha256.small_sigma_1 := by
  unfold Miden.Crypto.Sha256.small_sigma_1
  simp only [execWithEnv, List.foldlM]

private theorem sigma0_fuel_19_eq_20 (env : ProcEnv) (s : MidenState) :
    execWithEnv env 19 s Miden.Crypto.Sha256.small_sigma_0 =
    execWithEnv env 20 s Miden.Crypto.Sha256.small_sigma_0 := by
  unfold Miden.Crypto.Sha256.small_sigma_0
  simp only [execWithEnv, List.foldlM]

private theorem sigma0_fuel_18_eq_20 (env : ProcEnv) (s : MidenState) :
    execWithEnv env 18 s Miden.Crypto.Sha256.small_sigma_0 =
    execWithEnv env 20 s Miden.Crypto.Sha256.small_sigma_0 := by
  unfold Miden.Crypto.Sha256.small_sigma_0
  simp only [execWithEnv, List.foldlM]

-- Sigma output isU32 helpers (xor-based outputs are always < 2^32)
private theorem sigma1_out_isU32 (x : Felt) (hx : x.isU32 = true) :
    (sha256_small_sigma_1_local_out x).isU32 = true := by
  unfold sha256_small_sigma_1_local_out
  apply felt_ofNat_isU32_of_lt
  have hx_u32 : x.val < 2 ^ 32 := by
    simp only [Felt.isU32, decide_eq_true_eq] at hx; exact hx
  apply Nat_xor_lt_of_lt
  · exact u32RotateRight_val_lt_msw x.val 17 hx_u32
  · apply Nat_xor_lt_of_lt
    · exact u32RotateRight_val_lt_msw x.val 19 hx_u32
    · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx_u32

private theorem sigma0_out_isU32 (x : Felt) (hx : x.isU32 = true) :
    (sha256_small_sigma_0_local_out x).isU32 = true := by
  unfold sha256_small_sigma_0_local_out
  apply felt_ofNat_isU32_of_lt
  have hx_u32 : x.val < 2 ^ 32 := by
    simp only [Felt.isU32, decide_eq_true_eq] at hx; exact hx
  apply Nat_xor_lt_of_lt
  · exact u32RotateRight_val_lt_msw x.val 7 hx_u32
  · apply Nat_xor_lt_of_lt
    · exact u32RotateRight_val_lt_msw x.val 18 hx_u32
    · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx_u32

-- Helper: Option.bind propagation
private theorem bind_none_is_none {α β : Type} (f : α → Option β) :
    (none : Option α) >>= f = none := rfl

private theorem bind_some_eq {α β : Type} (a : α) (f : α → Option β) :
    (some a : Option α) >>= f = f a := rfl

private theorem compute_msw_reject_empty
    (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv sha256ProcEnv 20 ⟨[], mem, locs, adv⟩
      Miden.Crypto.Sha256.compute_message_schedule_word = none := by
  unfold Miden.Crypto.Sha256.compute_message_schedule_word execWithEnv
  simp only [List.foldlM, sha256ProcEnv]
  have h_s1_rej : execWithEnv sha256ProcEnv 19 ⟨[], mem, locs, adv⟩
      Miden.Crypto.Sha256.small_sigma_1 = none := by
    rw [sigma1_fuel_19_eq_20]
    apply sha256_small_sigma_1_layer1_reject
    intro h_dom
    rcases h_dom with ⟨s', x, rest, y, hs, h_io, hs'⟩
    simp at hs
  rw [h_s1_rej, bind_none_is_none]

private theorem compute_msw_reject_one
    (w2 : Felt) (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv sha256ProcEnv 20 ⟨[w2], mem, locs, adv⟩
      Miden.Crypto.Sha256.compute_message_schedule_word = none := by
  unfold Miden.Crypto.Sha256.compute_message_schedule_word execWithEnv
  simp only [List.foldlM, sha256ProcEnv]
  by_cases hw2 : w2.isU32 = true
  · rw [sigma1_fuel_19_eq_20]
    rw [sha256_small_sigma_1_correct w2 [] ⟨[w2], mem, locs, adv⟩ rfl hw2]
    simp [bind_some_eq, MidenState.withStack, execInstruction, execMovup, removeNth]
  · have h_s1_rej : execWithEnv sha256ProcEnv 19 ⟨[w2], mem, locs, adv⟩
        Miden.Crypto.Sha256.small_sigma_1 = none := by
      rw [sigma1_fuel_19_eq_20]
      apply sha256_small_sigma_1_rejects_invalid_input
      rintro ⟨x, rest', hstk, hx_u32⟩
      simp at hstk
      rw [← hstk.1] at hx_u32
      exact hw2 hx_u32
    rw [h_s1_rej, bind_none_is_none]

private theorem compute_msw_reject_two
    (w2 w7 : Felt) (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv sha256ProcEnv 20 ⟨[w2, w7], mem, locs, adv⟩
      Miden.Crypto.Sha256.compute_message_schedule_word = none := by
  unfold Miden.Crypto.Sha256.compute_message_schedule_word execWithEnv
  simp only [List.foldlM, sha256ProcEnv]
  by_cases hw2 : w2.isU32 = true
  · rw [sigma1_fuel_19_eq_20]
    rw [sha256_small_sigma_1_correct w2 [w7] ⟨[w2, w7], mem, locs, adv⟩ rfl hw2]
    simp [bind_some_eq, MidenState.withStack, execInstruction, execMovup, removeNth]
  · have h_s1_rej : execWithEnv sha256ProcEnv 19 ⟨[w2, w7], mem, locs, adv⟩
        Miden.Crypto.Sha256.small_sigma_1 = none := by
      rw [sigma1_fuel_19_eq_20]
      apply sha256_small_sigma_1_rejects_invalid_input
      rintro ⟨x, rest', hstk, hx_u32⟩
      simp at hstk
      rw [← hstk.1] at hx_u32
      exact hw2 hx_u32
    rw [h_s1_rej, bind_none_is_none]

private theorem compute_msw_reject_three
    (w2 w7 w15 : Felt) (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv sha256ProcEnv 20 ⟨[w2, w7, w15], mem, locs, adv⟩
      Miden.Crypto.Sha256.compute_message_schedule_word = none := by
  unfold Miden.Crypto.Sha256.compute_message_schedule_word execWithEnv
  simp only [List.foldlM, sha256ProcEnv]
  by_cases hw2 : w2.isU32 = true
  · rw [sigma1_fuel_19_eq_20]
    rw [sha256_small_sigma_1_correct w2 [w7, w15] ⟨[w2, w7, w15], mem, locs, adv⟩ rfl hw2]
    simp only [bind_some_eq, MidenState.withStack]
    rw [stepMovup (hn := by decide) (hv := by rfl)]
    simp only [List.eraseIdx, bind_some_eq]
    by_cases hw15 : w15.isU32 = true
    · rw [sigma0_fuel_19_eq_20]
      rw [sha256_small_sigma_0_correct w15
        [Felt.ofNat (Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat, w7]
        ⟨[w15, Felt.ofNat (Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat, w7], mem, locs, adv⟩
        rfl hw15]
      have hs1_u32 : (Felt.ofNat (Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat).isU32 = true :=
        felt_ofNat_isU32_of_lt _ (Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).isLt
      have hs0_u32 : (Felt.ofNat (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15.val)).toNat).isU32 = true :=
        felt_ofNat_isU32_of_lt _ (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15.val)).isLt
      by_cases hw7 : w7.isU32 = true
      · simp [bind_some_eq, MidenState.withStack, execInstruction, execU32WrappingAdd3, execU32WrappingAdd,
          hs1_u32, hs0_u32, hw7]
      · simp [bind_some_eq, MidenState.withStack, execInstruction, execU32WrappingAdd3, execU32WrappingAdd,
          hs1_u32, hs0_u32, hw7]
    · have h_s0_rej : execWithEnv sha256ProcEnv 19
          ⟨[w15, Felt.ofNat (Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat, w7], mem, locs, adv⟩
          Miden.Crypto.Sha256.small_sigma_0 = none := by
        rw [sigma0_fuel_19_eq_20]
        apply sha256_small_sigma_0_rejects_invalid_input
        rintro ⟨x, rest', hstk, hx_u32⟩
        simp at hstk
        rw [← hstk.1] at hx_u32
        exact hw15 hx_u32
      rw [h_s0_rej, bind_none_is_none]
  · have h_s1_rej : execWithEnv sha256ProcEnv 19 ⟨[w2, w7, w15], mem, locs, adv⟩
        Miden.Crypto.Sha256.small_sigma_1 = none := by
      rw [sigma1_fuel_19_eq_20]
      apply sha256_small_sigma_1_rejects_invalid_input
      rintro ⟨x, rest', hstk, hx_u32⟩
      simp at hstk
      rw [← hstk.1] at hx_u32
      exact hw2 hx_u32
    rw [h_s1_rej, bind_none_is_none]

set_option maxHeartbeats 64000000 in
/-- Layer-1 execution: on valid inputs, the procedure executes and
    produces the local output. (DESIGN §3.1) -/
theorem compute_msw_layer1_executes_local
    (w2 w7 w15 w16 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = w2 :: w7 :: w15 :: w16 :: rest)
    (h2 : w2.isU32 = true) (h7 : w7.isU32 = true)
    (h15 : w15.isU32 = true) (h16 : w16.isU32 = true) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.compute_message_schedule_word =
    some (s.withStack (compute_msw_local_out w2 w7 w15 w16 :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold Miden.Crypto.Sha256.compute_message_schedule_word execWithEnv
  simp only [List.foldlM, sha256ProcEnv]
  -- == exec "small_sigma_1": fuel 19→20 equivalence + existing sigma_1 lemma ==
  rw [sigma1_fuel_19_eq_20]
  rw [sha256_small_sigma_1_layer1_executes_local w2 (w7 :: w15 :: w16 :: rest)
    ⟨w2 :: w7 :: w15 :: w16 :: rest, mem, locs, adv⟩ rfl h2]
  simp only [MidenState.withStack, bind, Bind.bind, Option.bind]
  -- == movup 2: brings w15 to top of [σ₁(w2), w7, w15, w16, ...rest] ==
  miden_step
  -- == exec "small_sigma_0": fuel 19→20 equivalence + existing sigma_0 lemma ==
  rw [sigma0_fuel_19_eq_20]
  rw [sha256_small_sigma_0_layer1_executes_local w15
    (sha256_small_sigma_1_local_out w2 :: w7 :: w16 :: rest)
    ⟨w15 :: sha256_small_sigma_1_local_out w2 :: w7 :: w16 :: rest, mem, locs, adv⟩ rfl h15]
  simp only [MidenState.withStack]
  -- == u32WrappingAdd3: (w7 + σ₁(w2) + σ₀(w15)) % 2^32 ==
  unfold execInstruction execU32WrappingAdd3
  simp only [sigma0_out_isU32 w15 h15, sigma1_out_isU32 w2 h2, h7, Bool.not_true, Bool.false_or,
    u32Max, ite_false, Bool.false_eq_true, MidenState.withStack]
  -- == u32WrappingAdd: (sum3 + w16) % 2^32 ==
  unfold execU32WrappingAdd u32WAdd u32Max
  have h_sum3_isU32 : (Felt.ofNat ((w7.val + (sha256_small_sigma_1_local_out w2).val +
    (sha256_small_sigma_0_local_out w15).val) % 2 ^ 32)).isU32 = true := by
    apply felt_ofNat_isU32_of_lt; exact Nat.mod_lt _ (by positivity)
  simp only [h_sum3_isU32, h16, Bool.not_true, Bool.false_or, ite_false, Bool.false_eq_true,
    MidenState.withStack]
  -- == Final: match Nat addition order (commutativity) ==
  unfold compute_msw_local_out u32Max
  -- The inner sum differs only in Nat.add order:
  -- LHS: w7.val + σ₁.val + σ₀.val    RHS: σ₁.val + σ₀.val + w7.val
  -- Rewrite the inner sum to match
  have h_inner : w7.val + (sha256_small_sigma_1_local_out w2).val +
    (sha256_small_sigma_0_local_out w15).val =
    (sha256_small_sigma_1_local_out w2).val + (sha256_small_sigma_0_local_out w15).val +
    w7.val := by omega
  rw [h_inner]
  -- Now the outer sum order: LHS: w16.val + sum3.val    RHS: sum3.val + w16.val
  have h_outer : w16.val +
    (Felt.ofNat (((sha256_small_sigma_1_local_out w2).val +
      (sha256_small_sigma_0_local_out w15).val + w7.val) % 2 ^ 32)).val =
    (Felt.ofNat (((sha256_small_sigma_1_local_out w2).val +
      (sha256_small_sigma_0_local_out w15).val + w7.val) % 2 ^ 32)).val +
    w16.val := by omega
  rw [h_outer]
  rfl

set_option maxHeartbeats 32000000 in
/-- Layer-1 rejection: non-u32 inputs cause failure. (DESIGN §3.2) -/
theorem compute_msw_layer1_reject
    (w2 w7 w15 w16 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = w2 :: w7 :: w15 :: w16 :: rest)
    (h_bad : w2.isU32 = false ∨ w7.isU32 = false ∨ w15.isU32 = false ∨ w16.isU32 = false) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.compute_message_schedule_word = none := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [] at hs
  subst hs
  -- Unfold the outer call: 20 = 19 + 1, so foldlM over the 5 ops
  unfold Miden.Crypto.Sha256.compute_message_schedule_word execWithEnv
  simp only [List.foldlM, sha256ProcEnv]
  -- Convert fuel 19 to fuel 20 for sigma_1 (flat ops, fuel-independent)
  rw [sigma1_fuel_19_eq_20]
  -- Case-split on w2.isU32 to determine if sigma_1 succeeds
  by_cases hw2_u32 : w2.isU32 = true
  · -- sigma_1 succeeds (w2 is u32)
    -- Narrow h_bad: since w2 is u32, one of w7/w15/w16 must be bad
    have h_bad_rest : w7.isU32 = false ∨ w15.isU32 = false ∨ w16.isU32 = false := by
      rcases h_bad with h | h
      · simp [hw2_u32] at h
      · exact h
    -- Rewrite sigma_1 call with its correctness theorem
    rw [sha256_small_sigma_1_correct w2 (w7 :: w15 :: w16 :: rest)
      ⟨w2 :: w7 :: w15 :: w16 :: rest, mem, locs, adv⟩ rfl hw2_u32]
    -- Simplify: some state >>= f = f state
    simp only [bind_some_eq, MidenState.withStack]
    -- movup 2: rewrite using step lemma
    rw [stepMovup (hn := by decide) (hv := by rfl)]
    -- Normalize: eraseIdx and bind
    simp only [List.eraseIdx, bind_some_eq]
    -- Now state has stack [w15, s1out, w7, w16, ...rest]
    -- Convert sigma_0 fuel
    rw [sigma0_fuel_19_eq_20]
    -- Case-split on w15.isU32 to determine if sigma_0 succeeds
    by_cases hw15_u32 : w15.isU32 = true
    · -- sigma_0 succeeds (w15 is u32). w7 or w16 must be bad.
      have h_bad_w7_w16 : w7.isU32 = false ∨ w16.isU32 = false := by
        rcases h_bad_rest with h | h | h
        · exact Or.inl h
        · simp [hw15_u32] at h
        · exact Or.inr h
      -- Rewrite sigma_0 with its correctness theorem
      rw [sha256_small_sigma_0_correct w15
        (Felt.ofNat (Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat :: w7 :: w16 :: rest)
        ⟨w15 :: Felt.ofNat (Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat
          :: w7 :: w16 :: rest, mem, locs, adv⟩ rfl hw15_u32]
      simp only [bind_some_eq, MidenState.withStack]
      -- Now stack is [s0out(w15), s1out(w2), w7, w16, ...rest]
      -- Case split on w7.isU32
      by_cases hw7_u32 : w7.isU32 = true
      · -- w7 u32, so w16 must be bad
        have hw16_false : w16.isU32 = false := by
          rcases h_bad_w7_w16 with h | h
          · simp [hw7_u32] at h
          · exact h
        -- s0out and s1out are u32 (BitVec 32 toNat < 2^32)
        have hs0_u32 : (Felt.ofNat (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15.val)).toNat).isU32 = true :=
          felt_ofNat_isU32_of_lt _ (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15.val)).isLt
        have hs1_u32 : (Felt.ofNat (Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat).isU32 = true :=
          felt_ofNat_isU32_of_lt _ (Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).isLt
        -- u32WrappingAdd3 succeeds (s0, s1, w7 all u32)
        unfold execInstruction execU32WrappingAdd3
        simp only [MidenState.withStack, hw7_u32, hs1_u32, hs0_u32,
          Bool.not_true, Bool.false_or]
        -- u32WrappingAdd on [sum3_result, w16, ...rest]: w16 is not u32, so it fails
        unfold execU32WrappingAdd
        simp only [MidenState.withStack]
        have hsum3_u32 : (Felt.ofNat ((w7.val + (Felt.ofNat (Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat).val +
          (Felt.ofNat (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15.val)).toNat).val) % u32Max)).isU32 = true :=
          u32_mod_isU32 _
        simp only [Bool.false_eq_true, ite_false, bind_some_eq]
        simp only [hw16_false, hsum3_u32, Bool.not_false, Bool.not_true,
          Bool.true_or, ite_true, bind_none_is_none]
      · -- w7 not u32, u32WrappingAdd3 fails
        have hw7_false : w7.isU32 = false := by
          cases hb : w7.isU32 <;> simp_all
        unfold execInstruction execU32WrappingAdd3
        simp only [MidenState.withStack, hw7_false, Bool.not_false, Bool.true_or,
          ite_true, bind_none_is_none]
    · -- sigma_0 rejects (w15 is not u32)
      have h_s0_rej : execWithEnv sha256ProcEnv 20
          ⟨w15 :: Felt.ofNat (Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat
            :: w7 :: w16 :: rest, mem, locs, adv⟩
          Miden.Crypto.Sha256.small_sigma_0 = none := by
        apply sha256_small_sigma_0_rejects_invalid_input
        rintro ⟨x, rest', hstk, hx_u32⟩
        simp at hstk; rw [← hstk.1] at hx_u32; exact hw15_u32 hx_u32
      rw [h_s0_rej, bind_none_is_none]
  · -- sigma_1 rejects (w2 is not u32)
    have h_s1_rej : execWithEnv sha256ProcEnv 20
        ⟨w2 :: w7 :: w15 :: w16 :: rest, mem, locs, adv⟩
        Miden.Crypto.Sha256.small_sigma_1 = none := by
      apply sha256_small_sigma_1_rejects_invalid_input
      rintro ⟨x, rest', hstk, hx_u32⟩
      simp at hstk; rw [← hstk.1] at hx_u32; exact hw2_u32 hx_u32
    rw [h_s1_rej, bind_none_is_none]

/-- Layer-1 total correctness: biconditional. (DESIGN §3.3) -/
theorem compute_msw_layer1_total
    (s s' : MidenState) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.compute_message_schedule_word = some s' ↔
    compute_msw_sem s s' ∧ compute_msw_dom s := by
  constructor
  · intro h_exec
    unfold compute_msw_sem
    obtain ⟨stk, mem, locs, adv⟩ := s
    simp only [MidenState.withStack] at h_exec ⊢
    match stk with
    | [] =>
      exfalso
      rw [compute_msw_reject_empty mem locs adv] at h_exec
      cases h_exec
    | [w2] =>
      exfalso
      rw [compute_msw_reject_one w2 mem locs adv] at h_exec
      cases h_exec
    | [w2, w7] =>
      exfalso
      rw [compute_msw_reject_two w2 w7 mem locs adv] at h_exec
      cases h_exec
    | [w2, w7, w15] =>
      exfalso
      rw [compute_msw_reject_three w2 w7 w15 mem locs adv] at h_exec
      cases h_exec
    | w2 :: w7 :: w15 :: w16 :: rest =>
      by_cases h2 : w2.isU32 = true
      · by_cases h7 : w7.isU32 = true
        · by_cases h15 : w15.isU32 = true
          · by_cases h16 : w16.isU32 = true
            · refine ⟨⟨w2, w7, w15, w16, rest, rfl, ?_⟩,
                (compute_msw_dom_iff ⟨w2 :: w7 :: w15 :: w16 :: rest, mem, locs, adv⟩).2
                  ⟨w2, w7, w15, w16, rest, rfl, h2, h7, h15, h16⟩⟩
              have h_local := compute_msw_layer1_executes_local w2 w7 w15 w16 rest
                ⟨w2 :: w7 :: w15 :: w16 :: rest, mem, locs, adv⟩ rfl h2 h7 h15 h16
              rw [h_local] at h_exec
              exact (Option.some.inj h_exec).symm
            · have h16_false : w16.isU32 = false := by
                cases hb : w16.isU32 <;> simp_all
              have h_none := compute_msw_layer1_reject w2 w7 w15 w16 rest
                ⟨w2 :: w7 :: w15 :: w16 :: rest, mem, locs, adv⟩ rfl
                (Or.inr <| Or.inr <| Or.inr h16_false)
              exfalso
              rw [h_none] at h_exec
              cases h_exec
          · have h15_false : w15.isU32 = false := by
              cases hb : w15.isU32 <;> simp_all
            have h_none := compute_msw_layer1_reject w2 w7 w15 w16 rest
              ⟨w2 :: w7 :: w15 :: w16 :: rest, mem, locs, adv⟩ rfl
              (Or.inr <| Or.inr <| Or.inl h15_false)
            exfalso
            rw [h_none] at h_exec
            cases h_exec
        · have h7_false : w7.isU32 = false := by
            cases hb : w7.isU32 <;> simp_all
          have h_none := compute_msw_layer1_reject w2 w7 w15 w16 rest
            ⟨w2 :: w7 :: w15 :: w16 :: rest, mem, locs, adv⟩ rfl
            (Or.inr <| Or.inl h7_false)
          exfalso
          rw [h_none] at h_exec
          cases h_exec
      · have h2_false : w2.isU32 = false := by
          cases hb : w2.isU32 <;> simp_all
        have h_none := compute_msw_layer1_reject w2 w7 w15 w16 rest
          ⟨w2 :: w7 :: w15 :: w16 :: rest, mem, locs, adv⟩ rfl
          (Or.inl h2_false)
        exfalso
        rw [h_none] at h_exec
        cases h_exec
  · rintro ⟨h_sem, h_dom⟩
    rw [compute_msw_dom_iff] at h_dom
    rcases h_dom with ⟨w2, w7, w15, w16, rest, hs, h2, h7, h15, h16⟩
    rcases h_sem with ⟨w2', w7', w15', w16', rest', hs', hs_out⟩
    rw [hs] at hs'
    cases hs'
    rw [hs_out]
    exact compute_msw_layer1_executes_local w2 w7 w15 w16 rest s hs h2 h7 h15 h16

/-- Layer-1 success: execution succeeds iff domain holds. -/
theorem compute_msw_layer1_success
    (s : MidenState) :
    (∃ s', execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.compute_message_schedule_word = some s') ↔
    compute_msw_dom s := by
  constructor
  · rintro ⟨s', h_exec⟩
    exact (compute_msw_layer1_total s s').1 h_exec |>.2
  · intro h_dom
    rcases (compute_msw_dom_iff s).1 h_dom with ⟨w2, w7, w15, w16, rest, hs, h2, h7, h15, h16⟩
    refine ⟨s.withStack (compute_msw_local_out w2 w7 w15 w16 :: rest), ?_⟩
    exact compute_msw_layer1_executes_local w2 w7 w15 w16 rest s hs h2 h7 h15 h16

-- ============================================================================
-- Layer-2 theorems: bridge to SHA-256 spec (DESIGN §3.4)
-- ============================================================================

/-- The local output equals the spec output on u32 inputs. -/
theorem compute_msw_layer2_spec_out_equiv
    (w2 w7 w15 w16 : Felt)
    (h2 : w2.isU32 = true) (_h7 : w7.isU32 = true)
    (h15 : w15.isU32 = true) (_h16 : w16.isU32 = true) :
    compute_msw_local_out w2 w7 w15 w16 = compute_msw_spec_out w2 w7 w15 w16 := by
  unfold compute_msw_local_out compute_msw_spec_out
  rw [sha256_small_sigma_1_layer2_spec_out_equiv w2 h2]
  rw [sha256_small_sigma_0_layer2_spec_out_equiv w15 h15]
  dsimp
  have h_s1_ltprime :
      (Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat < GOLDILOCKS_PRIME := by
    calc
      (Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat < 2 ^ 32 :=
        (Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).isLt
      _ < GOLDILOCKS_PRIME := by
            unfold GOLDILOCKS_PRIME
            omega
  have h_s0_ltprime :
      (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15.val)).toNat < GOLDILOCKS_PRIME := by
    calc
      (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15.val)).toNat < 2 ^ 32 :=
        (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15.val)).isLt
      _ < GOLDILOCKS_PRIME := by
            unfold GOLDILOCKS_PRIME
            omega
  have h_s1_val :
      (sha256_small_sigma_1_spec_out w2).val =
        (Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat := by
    unfold sha256_small_sigma_1_spec_out
    rw [felt_ofNat_val_lt _ h_s1_ltprime]
  have h_s0_val :
      (sha256_small_sigma_0_spec_out w15).val =
        (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15.val)).toNat := by
    unfold sha256_small_sigma_0_spec_out
    rw [felt_ofNat_val_lt _ h_s0_ltprime]
  rw [h_s1_val, h_s0_val]
  have h_inner_lt :
      ((Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat +
          (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15.val)).toNat + w7.val) % u32Max <
        GOLDILOCKS_PRIME := by
    calc
      ((Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat +
          (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15.val)).toNat + w7.val) % u32Max < u32Max := by
            exact Nat.mod_lt _ (by unfold u32Max; omega)
      _ < GOLDILOCKS_PRIME := by
            unfold u32Max GOLDILOCKS_PRIME
            omega
  rw [show
      (Felt.ofNat
        (((Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat +
            (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15.val)).toNat + w7.val) % u32Max)).val =
      ((Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat +
          (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15.val)).toNat + w7.val) % u32Max by
        exact felt_ofNat_val_lt _ h_inner_lt]
  rw [messageScheduleWord_nat_eq_spec w2.val w15.val w16.val w7.val]
  have h_mod :
      (((Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat +
          (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15.val)).toNat + w7.val) % u32Max +
        w16.val) % u32Max =
      ((Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat +
          (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15.val)).toNat + w16.val + w7.val) % u32Max := by
    calc
      (((Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat +
            (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15.val)).toNat + w7.val) % u32Max +
          w16.val) % u32Max =
          ((Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat +
            (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15.val)).toNat + w7.val +
            w16.val) % u32Max := by
              have h_add :=
                Nat.mod_add_mod
                  ((Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat +
                    (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15.val)).toNat + w7.val)
                  u32Max w16.val
              simpa [Nat.add_assoc] using h_add
      _ = ((Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat +
          (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15.val)).toNat + w16.val + w7.val) % u32Max := by
            have h_swap :
                (Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat +
                    (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15.val)).toNat + w7.val +
                    w16.val =
                  (Sha256Spec.smallSigma1 (BitVec.ofNat 32 w2.val)).toNat +
                    (Sha256Spec.smallSigma0 (BitVec.ofNat 32 w15.val)).toNat + w16.val +
                    w7.val := by
              omega
            simpa using congrArg (fun t => t % u32Max) h_swap
  rw [h_mod]

/-- Layer-2 IO spec: local semantics imply the IO spec. -/
theorem compute_msw_layer2_io_spec
    (w2 w7 w15 w16 : Felt)
    (h2 : w2.isU32 = true) (h7 : w7.isU32 = true)
    (h15 : w15.isU32 = true) (h16 : w16.isU32 = true) :
    compute_msw_io_spec w2 w7 w15 w16 (compute_msw_local_out w2 w7 w15 w16) := by
  refine ⟨h2, h7, h15, h16, ?_⟩
  exact compute_msw_layer2_spec_out_equiv w2 w7 w15 w16 h2 h7 h15 h16

-- ============================================================================
-- Combined Layer 1+2 (DESIGN §2.2)
-- ============================================================================

/-- Direct code-vs-spec biconditional: exec succeeds ↔ state spec holds. -/
theorem compute_msw_layer12_state_spec_total
    (s s' : MidenState) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.compute_message_schedule_word = some s' ↔
    compute_msw_state_spec s s' := by
  constructor
  · intro h_exec
    rcases (compute_msw_layer1_total s s').1 h_exec with ⟨h_sem, h_dom⟩
    rw [compute_msw_dom_iff] at h_dom
    rcases h_dom with ⟨w2, w7, w15, w16, rest, hs, h2, h7, h15, h16⟩
    rcases h_sem with ⟨w2', w7', w15', w16', rest', hs', hs_out⟩
    rw [hs] at hs'
    cases hs'
    refine ⟨w2, w7, w15, w16, rest, compute_msw_local_out w2 w7 w15 w16, hs, ?_, ?_⟩
    · exact compute_msw_layer2_io_spec w2 w7 w15 w16 h2 h7 h15 h16
    · simpa using hs_out
  · intro h_spec
    have h_dom : compute_msw_dom s := ⟨s', h_spec⟩
    have h_sem : compute_msw_sem s s' := by
      rcases h_spec with ⟨w2, w7, w15, w16, rest, out, hs, h_io, hs_out⟩
      refine ⟨w2, w7, w15, w16, rest, hs, ?_⟩
      have h_eq : compute_msw_local_out w2 w7 w15 w16 = out := by
        rw [h_io.2.2.2.2]
        exact compute_msw_layer2_spec_out_equiv w2 w7 w15 w16
          h_io.1 h_io.2.1 h_io.2.2.1 h_io.2.2.2.1
      rw [← h_eq] at hs_out
      exact hs_out
    exact (compute_msw_layer1_total s s').2 ⟨h_sem, h_dom⟩

-- ============================================================================
-- Output u32 guarantee (important for recursive application)
-- ============================================================================

/-- The output of compute_message_schedule_word is always u32,
    because u32WrappingAdd produces values mod 2^32.
    This ensures the recursive invariant: if W[0..15] are u32,
    then W[16..63] are also u32. -/
theorem compute_msw_output_isU32
    (w2 w7 w15 w16 : Felt)
    (_h2 : w2.isU32 = true) (_h7 : w7.isU32 = true)
    (_h15 : w15.isU32 = true) (_h16 : w16.isU32 = true) :
    (compute_msw_local_out w2 w7 w15 w16).isU32 = true := by
  unfold compute_msw_local_out
  exact u32_mod_isU32 _

end MidenLean.Proofs
