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

private theorem u32_and_lt_prime (a b : Nat) (hb : b < 2 ^ 32) :
    a &&& b < GOLDILOCKS_PRIME := by
  calc
    a &&& b < 2 ^ 32 := Nat.and_lt_two_pow _ hb
    _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; omega

private theorem u32_not_lt_prime (a : Nat) (ha : a < 2 ^ 32) :
    u32Max - 1 - a < GOLDILOCKS_PRIME := by
  unfold u32Max GOLDILOCKS_PRIME
  omega

private theorem u32_xor_lt_prime (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    a ^^^ b < GOLDILOCKS_PRIME := by
  calc
    a ^^^ b < 2 ^ 32 := Nat_xor_lt_of_lt ha hb
    _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; omega

-- ============================================================================
-- Nat-to-BitVec bridge lemma
-- ============================================================================

private theorem ch_nat_eq_spec (x y z : Nat)
    (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) (hz : z < 2 ^ 32) :
    (x &&& y) ^^^ ((u32Max - 1 - x) &&& z) =
      (Sha256Spec.ch (BitVec.ofNat 32 x) (BitVec.ofNat 32 y) (BitVec.ofNat 32 z)).toNat := by
  unfold Sha256Spec.ch u32Max
  simp only [BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hz]

-- ============================================================================
-- Canonical helper schema
-- ============================================================================

/-- Layer-1 local output relation for `ch`, stated before any bridge to the
    SHA-256 mathematical spec. -/
def sha256_ch_local_out (x y z : Felt) : Felt :=
  Felt.ofNat ((x.val &&& y.val) ^^^ ((u32Max - 1 - x.val) &&& z.val))

/-- Layer-1 local semantic relation for `ch`. -/
def sha256_ch_sem (s s' : MidenState) : Prop :=
  ∃ x y z rest,
    s.stack = x :: y :: z :: rest ∧
    s' = s.withStack (sha256_ch_local_out x y z :: rest)

/-- Layer-2 mathematical output for `ch`. -/
def sha256_ch_spec_out (x y z : Felt) : Felt :=
  Felt.ofNat (Sha256Spec.ch (BitVec.ofNat 32 x.val) (BitVec.ofNat 32 y.val)
    (BitVec.ofNat 32 z.val)).toNat

/-- Code-level partial IO spec for `ch`. The `u32` domain is part of the spec
    itself, not carried as a separate side condition. -/
def sha256_ch_io_spec (x y z out : Felt) : Prop :=
  x.isU32 = true ∧ y.isU32 = true ∧ z.isU32 = true ∧ out = sha256_ch_spec_out x y z

/-- Code-level state spec for `ch`, lifting the partial IO spec to machine
    states. -/
def sha256_ch_state_spec (s s' : MidenState) : Prop :=
  ∃ x y z rest out,
    s.stack = x :: y :: z :: rest ∧
    sha256_ch_io_spec x y z out ∧
    s' = s.withStack (out :: rest)

/-- Compatibility alias for the Layer-2 code-level state spec. -/
abbrev sha256_ch_spec_sem (s s' : MidenState) : Prop :=
  sha256_ch_state_spec s s'

/-- Layer-1 domain for `ch`, derived from the code-level state spec rather than
    duplicated by hand. -/
def sha256_ch_dom (s : MidenState) : Prop :=
  ∃ s', sha256_ch_state_spec s s'

private theorem sha256_ch_dom_iff (s : MidenState) :
    sha256_ch_dom s ↔
      ∃ x y z rest, s.stack = x :: y :: z :: rest ∧
        x.isU32 = true ∧ y.isU32 = true ∧ z.isU32 = true := by
  constructor
  · rintro ⟨s', x, y, z, rest, out, hs, h_io, hs'⟩
    exact ⟨x, y, z, rest, hs, h_io.1, h_io.2.1, h_io.2.2.1⟩
  · rintro ⟨x, y, z, rest, hs, hx, hy, hz⟩
    refine ⟨s.withStack (sha256_ch_spec_out x y z :: rest), x, y, z, rest,
      sha256_ch_spec_out x y z, hs, ?_, rfl⟩
    exact ⟨hx, hy, hz, rfl⟩

-- ============================================================================
-- Layer 1: local helper correctness for ch
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- Concrete layer-1 execution theorem: the generated MASM helper runs to the
    local `ch` semantic summary on valid inputs. -/
theorem sha256_ch_layer1_executes_local
    (x y z : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = x :: y :: z :: rest)
    (hx : x.isU32 = true) (hy : y.isU32 = true) (hz : z.isU32 = true) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.ch =
      some (s.withStack (sha256_ch_local_out x y z :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold Miden.Crypto.Sha256.ch execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨x :: y :: z :: rest, mem, locs, adv⟩ (.swap 1)
    let s' ← execInstruction s' (.dup 1)
    let s' ← execInstruction s' (.u32And)
    let s' ← execInstruction s' (.swap 1)
    let s' ← execInstruction s' (.u32Not)
    let s' ← execInstruction s' (.movup 2)
    let s' ← execInstruction s' (.u32And)
    let s' ← execInstruction s' (.u32Xor)
    pure s') = _
  miden_swap
  miden_dup
  rw [stepU32And (ha := hy) (hb := hx)]
  miden_bind
  miden_swap
  rw [stepU32Not (ha := hx)]
  miden_bind
  miden_movup
  have hx_u32 : x.val < 2 ^ 32 := by
    simp only [Felt.isU32, decide_eq_true_eq] at hx
    exact hx
  have hy_u32 : y.val < 2 ^ 32 := by
    simp only [Felt.isU32, decide_eq_true_eq] at hy
    exact hy
  have hz_u32 : z.val < 2 ^ 32 := by
    simp only [Felt.isU32, decide_eq_true_eq] at hz
    exact hz
  have h_notx : (Felt.ofNat (u32Max - 1 - x.val)).isU32 = true := by
    apply felt_ofNat_isU32_of_lt
    unfold u32Max
    omega
  rw [stepU32And (ha := h_notx) (hb := hz)]
  miden_bind
  rw [felt_ofNat_val_lt _ (u32_not_lt_prime x.val hx_u32)]
  have h_and2_u32 : (Felt.ofNat ((u32Max - 1 - x.val) &&& z.val)).isU32 = true := by
    apply felt_ofNat_isU32_of_lt
    exact Nat.and_lt_two_pow _ hz_u32
  have h_and1_u32 : (Felt.ofNat (y.val &&& x.val)).isU32 = true := by
    simpa [Nat.and_comm] using
      felt_ofNat_isU32_of_lt (x.val &&& y.val) (Nat.and_lt_two_pow x.val hy_u32)
  have h_and1_lt : y.val &&& x.val < GOLDILOCKS_PRIME := u32_and_lt_prime y.val x.val hx_u32
  have h_and2_lt : (u32Max - 1 - x.val) &&& z.val < GOLDILOCKS_PRIME := by
    exact u32_and_lt_prime (u32Max - 1 - x.val) z.val hz_u32
  rw [stepU32Xor (ha := h_and1_u32) (hb := h_and2_u32)]
  rw [felt_ofNat_val_lt _ h_and2_lt]
  rw [felt_ofNat_val_lt _ h_and1_lt]
  unfold sha256_ch_local_out
  rw [Nat.and_comm x.val y.val]
  rfl

set_option maxHeartbeats 16000000 in
private theorem sha256_ch_layer1_success
    (s s' : MidenState)
    (h : execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.ch = some s') :
    sha256_ch_dom s ∧ sha256_ch_sem s s' := by
  unfold sha256_ch_sem
  unfold Miden.Crypto.Sha256.ch execWithEnv at h
  simp only [List.foldlM] at h
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at h ⊢
  match stk with
  | [] =>
    simp [execInstruction, execSwap] at h
  | [x] =>
    simp [execInstruction, execSwap] at h
  | x :: y :: rest2 =>
    match rest2 with
    | [] =>
      simp only [execInstruction, execSwap, execDup, bind, Bind.bind, Option.bind,
        MidenState.withStack] at h
      by_cases hx : x.isU32 = true
      · by_cases hy : y.isU32 = true
        · simp [execU32And, execU32Not, execMovup, execU32Xor, hx, hy, removeNth] at h
        · have hy_false : y.isU32 = false := by
            cases hyu : y.isU32 <;> simp_all
          simp [execU32And, execU32Not, execMovup, execU32Xor, hx, hy_false, removeNth] at h
      · have hx_false : x.isU32 = false := by
          cases hxu : x.isU32 <;> simp_all
        simp [execU32And, execU32Not, execMovup, execU32Xor, hx_false, removeNth] at h
    | z :: rest =>
      by_cases hx : x.isU32 = true
      · by_cases hy : y.isU32 = true
        · by_cases hz : z.isU32 = true
          · refine ⟨(sha256_ch_dom_iff ⟨x :: y :: z :: rest, mem, locs, adv⟩).2
              ⟨x, y, z, rest, rfl, hx, hy, hz⟩, ⟨x, y, z, rest, rfl, ?_⟩⟩
            have hc := sha256_ch_layer1_executes_local x y z rest ⟨x :: y :: z :: rest, mem, locs, adv⟩
              rfl hx hy hz
            unfold Miden.Crypto.Sha256.ch execWithEnv at hc
            simp only [List.foldlM, MidenState.withStack] at hc
            rw [hc] at h
            exact (Option.some.inj h).symm
          · exfalso
            have hz_false : z.isU32 = false := by
              cases hzu : z.isU32 <;> simp_all
            simp only [execInstruction, execSwap, execDup, bind, Bind.bind, Option.bind,
              MidenState.withStack] at h
            simp [execU32And, execU32Not, execMovup, execU32Xor, hx, hy, hz_false, removeNth] at h
        · exfalso
          have hy_false : y.isU32 = false := by
            cases hyu : y.isU32 <;> simp_all
          simp only [execInstruction, execSwap, execDup, bind, Bind.bind, Option.bind,
            MidenState.withStack] at h
          simp [execU32And, execU32Not, execMovup, execU32Xor, hx, hy_false, removeNth] at h
      · exfalso
        have hx_false : x.isU32 = false := by
          cases hxu : x.isU32 <;> simp_all
        simp only [execInstruction, execSwap, execDup, bind, Bind.bind, Option.bind,
          MidenState.withStack] at h
        simp [execU32And, execU32Not, execMovup, execU32Xor, hx_false, removeNth] at h

/-- Layer-1 functional correctness: on the declared helper domain, execution
    produces the local `ch` semantic relation. -/
theorem sha256_ch_layer1_correct
    (s s' : MidenState) :
    sha256_ch_dom s →
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.ch = some s' →
    sha256_ch_sem s s' := by
  intro h_dom h_exec
  rw [sha256_ch_dom_iff] at h_dom
  rcases h_dom with ⟨x, y, z, rest, hs, hx, hy, hz⟩
  refine ⟨x, y, z, rest, hs, ?_⟩
  have h_local := sha256_ch_layer1_executes_local x y z rest s hs hx hy hz
  rw [h_local] at h_exec
  exact (Option.some.inj h_exec).symm

/-- Layer-1 total correctness: execution succeeds exactly on the declared
    helper domain, and then the local semantic relation holds. -/
theorem sha256_ch_layer1_total
    (s s' : MidenState) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.ch = some s' ↔
    sha256_ch_dom s ∧ sha256_ch_sem s s' := by
  constructor
  · intro h
    exact sha256_ch_layer1_success s s' h
  · rintro ⟨h_dom, h_sem⟩
    rw [sha256_ch_dom_iff] at h_dom
    rcases h_dom with ⟨x, y, z, rest, hs, hx, hy, hz⟩
    rcases h_sem with ⟨x', y', z', rest', hs', hs_out⟩
    rw [hs] at hs'
    cases hs'
    rw [hs_out]
    exact sha256_ch_layer1_executes_local x y z rest s hs hx hy hz

/-- Layer-1 rejection theorem: any state outside the declared helper domain is
    rejected by honest execution. -/
theorem sha256_ch_layer1_reject
    (s : MidenState)
    (h_invalid : ¬ sha256_ch_dom s) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.ch = none := by
  cases h_exec : execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.ch with
  | none => rfl
  | some s' =>
    exfalso
    exact h_invalid (sha256_ch_layer1_success s s' h_exec).1

-- ============================================================================
-- Layer 2: bridge from local helper semantics to the SHA-256 spec
-- ============================================================================

/-- Layer-2 IO-spec theorem: the local helper summary satisfies the code-level
    partial spec on valid inputs. -/
theorem sha256_ch_layer2_io_spec
    (x y z : Felt) (hx : x.isU32 = true) (hy : y.isU32 = true) (hz : z.isU32 = true) :
    sha256_ch_io_spec x y z (sha256_ch_local_out x y z) := by
  refine ⟨hx, hy, hz, ?_⟩
  unfold sha256_ch_local_out sha256_ch_spec_out
  have hx_u32 : x.val < 2 ^ 32 := by
    simp only [Felt.isU32, decide_eq_true_eq] at hx
    exact hx
  have hy_u32 : y.val < 2 ^ 32 := by
    simp only [Felt.isU32, decide_eq_true_eq] at hy
    exact hy
  have hz_u32 : z.val < 2 ^ 32 := by
    simp only [Felt.isU32, decide_eq_true_eq] at hz
    exact hz
  rw [ch_nat_eq_spec x.val y.val z.val hx_u32 hy_u32 hz_u32]

/-- Layer-2 output equivalence: the local helper summary matches the SHA-256
    mathematical `ch` output on valid inputs. -/
theorem sha256_ch_layer2_spec_out_equiv
    (x y z : Felt) (hx : x.isU32 = true) (hy : y.isU32 = true) (hz : z.isU32 = true) :
    sha256_ch_local_out x y z = sha256_ch_spec_out x y z := by
  unfold sha256_ch_local_out sha256_ch_spec_out
  have hx_u32 : x.val < 2 ^ 32 := by
    simp only [Felt.isU32, decide_eq_true_eq] at hx
    exact hx
  have hy_u32 : y.val < 2 ^ 32 := by
    simp only [Felt.isU32, decide_eq_true_eq] at hy
    exact hy
  have hz_u32 : z.val < 2 ^ 32 := by
    simp only [Felt.isU32, decide_eq_true_eq] at hz
    exact hz
  rw [ch_nat_eq_spec x.val y.val z.val hx_u32 hy_u32 hz_u32]

/-- Layer-2 semantic equivalence: the local helper semantics matches the
    code-level SHA-256 state spec whose domain is internalized in the spec
    relation itself. -/
theorem sha256_ch_layer2_spec_equiv
    (s s' : MidenState)
    (h_dom : sha256_ch_dom s)
    (h_sem : sha256_ch_sem s s') :
    sha256_ch_spec_sem s s' := by
  rw [sha256_ch_dom_iff] at h_dom
  rcases h_dom with ⟨x, y, z, rest, hs, hx, hy, hz⟩
  rcases h_sem with ⟨x', y', z', rest', hs', hs_out⟩
  rw [hs] at hs'
  cases hs'
  refine ⟨x, y, z, rest, sha256_ch_local_out x y z, hs, ?_, ?_⟩
  · exact sha256_ch_layer2_io_spec x y z hx hy hz
  · simpa using hs_out

/-- Direct code-vs-spec theorem: honest execution succeeds exactly when the
    code-level state spec holds. This is the main point where MASM is compared
    directly against the lifted SHA-256 helper spec. -/
theorem sha256_ch_layer12_state_spec_total
    (s s' : MidenState) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.ch = some s' ↔
    sha256_ch_state_spec s s' := by
  constructor
  · intro h_exec
    rcases (sha256_ch_layer1_total s s').1 h_exec with ⟨h_dom, h_sem⟩
    exact sha256_ch_layer2_spec_equiv s s' h_dom h_sem
  · intro h_spec
    have h_dom : sha256_ch_dom s := ⟨s', h_spec⟩
    have h_sem : sha256_ch_sem s s' := by
      rcases h_spec with ⟨x, y, z, rest, out, hs, h_io, hs_out⟩
      refine ⟨x, y, z, rest, hs, ?_⟩
      have h_eq : sha256_ch_local_out x y z = out := by
        rw [h_io.2.2.2]
        exact sha256_ch_layer2_spec_out_equiv x y z h_io.1 h_io.2.1 h_io.2.2.1
      rw [← h_eq] at hs_out
      exact hs_out
    exact (sha256_ch_layer1_total s s').2 ⟨h_dom, h_sem⟩

-- ============================================================================
-- Compatibility theorems: legacy combined Layer-1 + Layer-2 shape
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- Legacy combined theorem: layer-1 execution plus the layer-2 SHA-256 spec
    bridge, stated in the original file shape for downstream compatibility. -/
theorem sha256_ch_correct
    (x y z : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = x :: y :: z :: rest)
    (hx : x.isU32 = true) (hy : y.isU32 = true) (hz : z.isU32 = true) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.ch =
      some (s.withStack (
        Felt.ofNat (Sha256Spec.ch (BitVec.ofNat 32 x.val) (BitVec.ofNat 32 y.val)
          (BitVec.ofNat 32 z.val)).toNat :: rest)) := by
  have h_local := sha256_ch_layer1_executes_local x y z rest s hs hx hy hz
  rw [sha256_ch_layer2_spec_out_equiv x y z hx hy hz] at h_local
  simpa [sha256_ch_spec_out] using h_local

set_option maxHeartbeats 16000000 in
/-- Legacy combined soundness theorem in the original file shape. -/
theorem sha256_ch_sound
    (s s' : MidenState)
    (h : execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.ch = some s') :
    ∃ x y z rest,
      s.stack = x :: y :: z :: rest ∧
      x.isU32 = true ∧ y.isU32 = true ∧ z.isU32 = true ∧
      s' = s.withStack (
        Felt.ofNat (Sha256Spec.ch (BitVec.ofNat 32 x.val) (BitVec.ofNat 32 y.val)
          (BitVec.ofNat 32 z.val)).toNat :: rest) := by
  rcases (sha256_ch_layer12_state_spec_total s s').1 h with
    ⟨x, y, z, rest, out, hs, h_io, hs_out⟩
  rcases h_io with ⟨hx, hy, hz, hout⟩
  exact ⟨x, y, z, rest, hs, hx, hy, hz,
    by rw [hout] at hs_out; simpa [sha256_ch_spec_out] using hs_out⟩

/-- Legacy combined total correctness theorem in the original file shape. -/
theorem sha256_ch_total
    (s s' : MidenState) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.ch = some s' ↔
    ∃ x y z rest,
      s.stack = x :: y :: z :: rest ∧
      x.isU32 = true ∧ y.isU32 = true ∧ z.isU32 = true ∧
      s' = s.withStack (
        Felt.ofNat (Sha256Spec.ch (BitVec.ofNat 32 x.val) (BitVec.ofNat 32 y.val)
          (BitVec.ofNat 32 z.val)).toNat :: rest) := by
  constructor
  · intro h
    exact sha256_ch_sound s s' h
  · rintro ⟨x, y, z, rest, hs, hx, hy, hz, rfl⟩
    exact sha256_ch_correct x y z rest s hs hx hy hz

/-- Legacy combined rejection theorem in the original file shape. -/
theorem sha256_ch_rejects_invalid_input
    (s : MidenState)
    (h_invalid : ¬ ∃ x y z rest, s.stack = x :: y :: z :: rest ∧
      x.isU32 = true ∧ y.isU32 = true ∧ z.isU32 = true) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.ch = none := by
  apply sha256_ch_layer1_reject s
  intro h_dom
  exact h_invalid ((sha256_ch_dom_iff s).1 h_dom)

end MidenLean.Proofs
