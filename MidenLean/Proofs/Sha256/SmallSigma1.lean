import MidenLean.Proofs.Tactics
import MidenLean.Proofs.Sha256.Common
import MidenLean.Spec.Sha256Spec

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Helper: bound lemmas for intermediate results
-- ============================================================================

private theorem u32RotateRight_val_lt (a : Nat) (n : Nat) (ha : a < 2 ^ 32) :
    u32RotateRight a n < 2 ^ 32 := by
  unfold u32RotateRight u32Max
  apply Nat_or_lt_of_lt
  · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha
  · exact Nat.mod_lt _ (by positivity)

private theorem u32RotateRight_lt_prime (a : Nat) (n : Nat) (ha : a < 2 ^ 32) :
    u32RotateRight a n < GOLDILOCKS_PRIME := by
  calc u32RotateRight a n < 2 ^ 32 := u32RotateRight_val_lt a n ha
    _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; omega

private theorem u32_div_lt_prime (a : Nat) (n : Nat) (ha : a < 2 ^ 32) :
    a / 2 ^ n < GOLDILOCKS_PRIME := by
  calc a / 2 ^ n ≤ a := Nat.div_le_self _ _
    _ < 2 ^ 32 := ha
    _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; omega

private theorem u32_xor_lt_prime (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    a ^^^ b < GOLDILOCKS_PRIME := by
  calc a ^^^ b < 2 ^ 32 := Nat_xor_lt_of_lt ha hb
    _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; omega

-- ============================================================================
-- Nat-to-BitVec bridge lemmas
-- ============================================================================

private theorem u32RotateRight_eq_bv_rotateRight (a : Nat) (n : Nat) (ha : a < 2 ^ 32) (hn : n < 32) :
    u32RotateRight a n = ((BitVec.ofNat 32 a).rotateRight n).toNat := by
  unfold u32RotateRight u32Max
  rw [BitVec.toNat_rotateRight]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have : n % 32 = n := Nat.mod_eq_of_lt hn
  rw [this]

private theorem smallSigma1_nat_eq_spec (a : Nat) (ha : a < 2 ^ 32) :
    u32RotateRight a 17 ^^^ (u32RotateRight a 19 ^^^ a / 2 ^ 10) =
      (Sha256Spec.smallSigma1 (BitVec.ofNat 32 a)).toNat := by
  calc
    u32RotateRight a 17 ^^^ (u32RotateRight a 19 ^^^ a / 2 ^ 10)
      = u32RotateRight a 17 ^^^ u32RotateRight a 19 ^^^ (a / 2 ^ 10) := by
          rw [Nat.xor_assoc]
    _ = (Sha256Spec.smallSigma1 (BitVec.ofNat 32 a)).toNat := by
          rw [u32RotateRight_eq_bv_rotateRight _ _ ha (by omega)]
          rw [u32RotateRight_eq_bv_rotateRight _ _ ha (by omega)]
          unfold Sha256Spec.smallSigma1 Sha256Spec.rotr Sha256Spec.shr
          simp only [Nat.reduceMod, Nat.reduceSub, BitVec.rotateRightAux, BitVec.toNat_xor,
            BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
            BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
            Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, BitVec.rotateRight]

-- ============================================================================
-- Canonical helper schema
-- ============================================================================

/-- Layer-1 local output relation for `small_sigma_1`, stated before any
    bridge to the SHA-256 mathematical spec. -/
def sha256_small_sigma_1_local_out (x : Felt) : Felt :=
  Felt.ofNat (u32RotateRight x.val 17 ^^^ (u32RotateRight x.val 19 ^^^ x.val / 2 ^ 10))

/-- Layer-1 local semantic relation for `small_sigma_1`. -/
def sha256_small_sigma_1_sem (s s' : MidenState) : Prop :=
  ∃ x rest,
    s.stack = x :: rest ∧
    s' = s.withStack (sha256_small_sigma_1_local_out x :: rest)

/-- Layer-2 mathematical output for `small_sigma_1`. -/
def sha256_small_sigma_1_spec_out (x : Felt) : Felt :=
  Felt.ofNat (Sha256Spec.smallSigma1 (BitVec.ofNat 32 x.val)).toNat

/-- Code-level partial IO spec for `small_sigma_1`. The `u32` domain is part of
    the spec itself, not carried as a separate side condition. -/
def sha256_small_sigma_1_io_spec (x y : Felt) : Prop :=
  x.isU32 = true ∧ y = sha256_small_sigma_1_spec_out x

/-- Code-level state spec for `small_sigma_1`, lifting the partial IO spec to
    machine states. -/
def sha256_small_sigma_1_state_spec (s s' : MidenState) : Prop :=
  ∃ x rest y,
    s.stack = x :: rest ∧
    sha256_small_sigma_1_io_spec x y ∧
    s' = s.withStack (y :: rest)

/-- Compatibility alias for the Layer-2 code-level state spec. -/
abbrev sha256_small_sigma_1_spec_sem (s s' : MidenState) : Prop :=
  sha256_small_sigma_1_state_spec s s'

/-- Layer-1 domain for `small_sigma_1`, derived from the code-level state
    spec rather than duplicated by hand. -/
def sha256_small_sigma_1_dom (s : MidenState) : Prop :=
  ∃ s', sha256_small_sigma_1_state_spec s s'

private theorem sha256_small_sigma_1_dom_iff
    (s : MidenState) :
    sha256_small_sigma_1_dom s ↔ ∃ x rest, s.stack = x :: rest ∧ x.isU32 = true := by
  constructor
  · rintro ⟨s', x, rest, y, hs, h_io, hs'⟩
    exact ⟨x, rest, hs, h_io.1⟩
  · rintro ⟨x, rest, hs, hx⟩
    refine ⟨s.withStack (sha256_small_sigma_1_spec_out x :: rest), x, rest,
      sha256_small_sigma_1_spec_out x, hs, ?_, rfl⟩
    exact ⟨hx, rfl⟩

-- ============================================================================
-- Layer 1: local helper correctness for small_sigma_1
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- Concrete layer-1 execution theorem: the generated MASM helper runs to the
    local `small_sigma_1` semantic summary on valid inputs. -/
theorem sha256_small_sigma_1_layer1_executes_local
    (x : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = x :: rest)
    (hx : x.isU32 = true) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.small_sigma_1 =
    some (s.withStack (sha256_small_sigma_1_local_out x :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold Miden.Crypto.Sha256.small_sigma_1 execWithEnv
  simp only [List.foldlM]
  miden_step
  miden_step
  miden_step
  miden_step
  miden_step
  miden_step
  miden_step
  have h_shr : (Felt.ofNat (x.val / 2 ^ 10)).isU32 = true :=
    u32_div_pow_isU32 x 10 hx
  have h_rotr19 : (Felt.ofNat (u32RotateRight x.val 19)).isU32 = true :=
    u32RotateRight_isU32 x 19 hx
  miden_step
  have hx_u32 : x.val < 2 ^ 32 := by
    simp only [Felt.isU32, decide_eq_true_eq] at hx
    exact hx
  rw [felt_ofNat_val_lt _ (u32RotateRight_lt_prime x.val 19 hx_u32)]
  rw [felt_ofNat_val_lt _ (u32_div_lt_prime x.val 10 hx_u32)]
  have h_rotr17 : (Felt.ofNat (u32RotateRight x.val 17)).isU32 = true :=
    u32RotateRight_isU32 x 17 hx
  have h_xor1 : (Felt.ofNat (u32RotateRight x.val 19 ^^^ x.val / 2 ^ 10)).isU32 = true := by
    apply felt_ofNat_isU32_of_lt
    apply Nat_xor_lt_of_lt
    · exact u32RotateRight_val_lt x.val 19 hx_u32
    · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx_u32
  miden_step
  rw [felt_ofNat_val_lt _ (u32RotateRight_lt_prime x.val 17 hx_u32)]
  rw [felt_ofNat_val_lt _ (u32_xor_lt_prime _ _ (u32RotateRight_val_lt _ _ hx_u32)
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx_u32))]
  unfold sha256_small_sigma_1_local_out
  rfl

set_option maxHeartbeats 16000000 in
private theorem sha256_small_sigma_1_layer1_success
    (s s' : MidenState)
    (h : execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.small_sigma_1 = some s') :
    sha256_small_sigma_1_dom s ∧ sha256_small_sigma_1_sem s s' := by
  unfold sha256_small_sigma_1_sem
  unfold Miden.Crypto.Sha256.small_sigma_1 execWithEnv at h
  simp only [List.foldlM] at h
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at h ⊢
  match hstk : stk with
  | [] =>
    simp [execInstruction, execDup] at h
  | x :: rest =>
    by_cases hx : x.isU32 = true
    · refine ⟨(sha256_small_sigma_1_dom_iff ⟨x :: rest, mem, locs, adv⟩).2 ⟨x, rest, rfl, hx⟩,
        ⟨x, rest, rfl, ?_⟩⟩
      have hc := sha256_small_sigma_1_layer1_executes_local x rest ⟨x :: rest, mem, locs, adv⟩ rfl hx
      unfold Miden.Crypto.Sha256.small_sigma_1 execWithEnv at hc
      simp only [List.foldlM, MidenState.withStack] at hc
      rw [hc] at h
      exact (Option.some.inj h).symm
    · exfalso
      simp only [execInstruction, execDup, bind, Bind.bind, Option.bind, MidenState.withStack] at h
      simp [execU32RotrImm, hx] at h

set_option maxHeartbeats 16000000 in
/-- Layer-1 functional correctness: on the declared helper domain, execution
    produces the local `small_sigma_1` semantic relation. -/
theorem sha256_small_sigma_1_layer1_correct
    (s s' : MidenState) :
    sha256_small_sigma_1_dom s →
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.small_sigma_1 = some s' →
    sha256_small_sigma_1_sem s s' := by
  intro h_dom h_exec
  rw [sha256_small_sigma_1_dom_iff] at h_dom
  rcases h_dom with ⟨x, rest, hs, hx⟩
  refine ⟨x, rest, hs, ?_⟩
  have h_local := sha256_small_sigma_1_layer1_executes_local x rest s hs hx
  rw [h_local] at h_exec
  exact (Option.some.inj h_exec).symm

/-- Layer-1 total correctness: execution succeeds exactly on the declared
    helper domain, and then the local semantic relation holds. -/
theorem sha256_small_sigma_1_layer1_total
    (s s' : MidenState) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.small_sigma_1 = some s' ↔
    sha256_small_sigma_1_dom s ∧ sha256_small_sigma_1_sem s s' := by
  constructor
  · intro h
    exact sha256_small_sigma_1_layer1_success s s' h
  · rintro ⟨h_dom, h_sem⟩
    rw [sha256_small_sigma_1_dom_iff] at h_dom
    rcases h_dom with ⟨x, rest, hs, hx⟩
    rcases h_sem with ⟨x', rest', hs', hs_out⟩
    rw [hs] at hs'
    cases hs'
    rw [hs_out]
    exact sha256_small_sigma_1_layer1_executes_local x rest s hs hx

/-- Layer-1 rejection theorem: any state outside the declared helper domain is
    rejected by honest execution. -/
theorem sha256_small_sigma_1_layer1_reject
    (s : MidenState)
    (h_invalid : ¬ sha256_small_sigma_1_dom s) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.small_sigma_1 = none := by
  cases h_exec : execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.small_sigma_1 with
  | none => rfl
  | some s' =>
    exfalso
    exact h_invalid (sha256_small_sigma_1_layer1_success s s' h_exec).1

-- ============================================================================
-- Layer 2: bridge from local helper semantics to the SHA-256 spec
-- ============================================================================

/-- Layer-2 IO-spec theorem: the local helper summary satisfies the code-level
    partial spec on valid inputs. -/
theorem sha256_small_sigma_1_layer2_io_spec
    (x : Felt) (hx : x.isU32 = true) :
    sha256_small_sigma_1_io_spec x (sha256_small_sigma_1_local_out x) := by
  refine ⟨hx, ?_⟩
  unfold sha256_small_sigma_1_local_out sha256_small_sigma_1_spec_out
  have hx_u32 : x.val < 2 ^ 32 := by
    simp only [Felt.isU32, decide_eq_true_eq] at hx
    exact hx
  rw [smallSigma1_nat_eq_spec x.val hx_u32]

/-- Layer-2 output equivalence: the local helper summary matches the SHA-256
    mathematical `σ₁` output on valid inputs. -/
theorem sha256_small_sigma_1_layer2_spec_out_equiv
    (x : Felt) (hx : x.isU32 = true) :
    sha256_small_sigma_1_local_out x = sha256_small_sigma_1_spec_out x := by
  unfold sha256_small_sigma_1_local_out sha256_small_sigma_1_spec_out
  have hx_u32 : x.val < 2 ^ 32 := by
    simp only [Felt.isU32, decide_eq_true_eq] at hx
    exact hx
  rw [smallSigma1_nat_eq_spec x.val hx_u32]

/-- Layer-2 semantic equivalence: the local helper semantics matches the
    code-level SHA-256 state spec whose domain is internalized in the spec
    relation itself. -/
theorem sha256_small_sigma_1_layer2_spec_equiv
    (s s' : MidenState)
    (h_dom : sha256_small_sigma_1_dom s)
    (h_sem : sha256_small_sigma_1_sem s s') :
    sha256_small_sigma_1_spec_sem s s' := by
  rw [sha256_small_sigma_1_dom_iff] at h_dom
  rcases h_dom with ⟨x, rest, hs, hx⟩
  rcases h_sem with ⟨x', rest', hs', hs_out⟩
  rw [hs] at hs'
  cases hs'
  refine ⟨x, rest, sha256_small_sigma_1_local_out x, hs, ?_, ?_⟩
  · exact sha256_small_sigma_1_layer2_io_spec x hx
  · simpa using hs_out

/-- Direct code-vs-spec theorem: honest execution succeeds exactly when the
    code-level state spec holds. This is the main point where MASM is compared
    directly against the lifted SHA-256 helper spec. -/
theorem sha256_small_sigma_1_layer12_state_spec_total
    (s s' : MidenState) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.small_sigma_1 = some s' ↔
    sha256_small_sigma_1_state_spec s s' := by
  constructor
  · intro h_exec
    rcases (sha256_small_sigma_1_layer1_total s s').1 h_exec with ⟨h_dom, h_sem⟩
    exact sha256_small_sigma_1_layer2_spec_equiv s s' h_dom h_sem
  · intro h_spec
    have h_dom : sha256_small_sigma_1_dom s := ⟨s', h_spec⟩
    have h_sem : sha256_small_sigma_1_sem s s' := by
      rcases h_spec with ⟨x, rest, y, hs, h_io, hs_out⟩
      refine ⟨x, rest, hs, ?_⟩
      have h_eq : sha256_small_sigma_1_local_out x = y := by
        rw [h_io.2]
        exact sha256_small_sigma_1_layer2_spec_out_equiv x h_io.1
      rw [← h_eq] at hs_out
      exact hs_out
    exact (sha256_small_sigma_1_layer1_total s s').2 ⟨h_dom, h_sem⟩

-- ============================================================================
-- Compatibility theorems: legacy combined Layer-1 + Layer-2 shape
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- Legacy combined theorem: layer-1 execution plus the layer-2 SHA-256 spec
    bridge, stated in the original file shape for downstream compatibility. -/
theorem sha256_small_sigma_1_correct
    (x : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = x :: rest)
    (hx : x.isU32 = true) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.small_sigma_1 =
    some (s.withStack (
      Felt.ofNat (Sha256Spec.smallSigma1 (BitVec.ofNat 32 x.val)).toNat :: rest)) := by
  have h_local := sha256_small_sigma_1_layer1_executes_local x rest s hs hx
  rw [sha256_small_sigma_1_layer2_spec_out_equiv x hx] at h_local
  simpa [sha256_small_sigma_1_spec_out] using h_local

set_option maxHeartbeats 16000000 in
/-- Legacy combined soundness theorem in the original file shape. -/
theorem sha256_small_sigma_1_sound
    (s s' : MidenState)
    (h : execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.small_sigma_1 = some s') :
    ∃ x rest,
      s.stack = x :: rest
      ∧ x.isU32 = true
      ∧ s' = s.withStack (Felt.ofNat (Sha256Spec.smallSigma1 (BitVec.ofNat 32 x.val)).toNat :: rest) := by
  rcases (sha256_small_sigma_1_layer12_state_spec_total s s').1 h with
    ⟨x, rest, y, hs, h_io, hs_out⟩
  rcases h_io with ⟨hx, hy⟩
  exact ⟨x, rest, hs, hx, by rw [hy] at hs_out; simpa [sha256_small_sigma_1_spec_out] using hs_out⟩

/-- Legacy combined total correctness theorem in the original file shape. -/
theorem sha256_small_sigma_1_total
    (s s' : MidenState) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.small_sigma_1 = some s' ↔
    ∃ x rest,
      s.stack = x :: rest
      ∧ x.isU32 = true
      ∧ s' = s.withStack (Felt.ofNat (Sha256Spec.smallSigma1 (BitVec.ofNat 32 x.val)).toNat :: rest) := by
  constructor
  · intro h
    exact sha256_small_sigma_1_sound s s' h
  · rintro ⟨x, rest, hs, hx, rfl⟩
    exact sha256_small_sigma_1_correct x rest s hs hx

/-- Legacy combined rejection theorem in the original file shape. -/
theorem sha256_small_sigma_1_rejects_invalid_input
    (s : MidenState)
    (h_invalid : ¬ ∃ x rest, s.stack = x :: rest ∧ x.isU32 = true) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.small_sigma_1 = none := by
  apply sha256_small_sigma_1_layer1_reject s
  intro h_dom
  exact h_invalid ((sha256_small_sigma_1_dom_iff s).1 h_dom)

end MidenLean.Proofs
