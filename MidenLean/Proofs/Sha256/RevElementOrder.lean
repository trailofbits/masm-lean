import MidenLean.Proofs.Tactics
import MidenLean.Proofs.Sha256.Common

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- Layer-1 local semantic relation for `rev_element_order`. -/
def sha256_rev_element_order_sem (s s' : MidenState) : Prop :=
  ∃ a b c d rest,
    s.stack = a :: b :: c :: d :: rest ∧
    s' = s.withStack (d :: c :: b :: a :: rest)

/-- Code-level state spec for `rev_element_order`.
This helper is a pure stack permutation, so the Layer-2 state spec is exactly
the local Layer-1 semantic summary. -/
abbrev sha256_rev_element_order_state_spec (s s' : MidenState) : Prop :=
  sha256_rev_element_order_sem s s'

/-- Compatibility alias for the Layer-2 code-level state spec. -/
abbrev sha256_rev_element_order_spec_sem (s s' : MidenState) : Prop :=
  sha256_rev_element_order_state_spec s s'

/-- Layer-1 domain for `rev_element_order`: at least four visible stack
elements. -/
def sha256_rev_element_order_dom (s : MidenState) : Prop :=
  ∃ a b c d rest, s.stack = a :: b :: c :: d :: rest

private theorem sha256_rev_element_order_dom_iff (s : MidenState) :
    sha256_rev_element_order_dom s ↔
      ∃ a b c d rest, s.stack = a :: b :: c :: d :: rest := by
  rfl

-- ============================================================================
-- Layer 1: local helper correctness for rev_element_order
-- ============================================================================

/-- Concrete layer-1 execution theorem: the generated MASM helper runs to the
local stack-reversal summary on valid inputs. -/
theorem sha256_rev_element_order_layer1_executes_local
    (a b c d : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: b :: c :: d :: rest) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.rev_element_order =
      some (s.withStack (d :: c :: b :: a :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold Miden.Crypto.Sha256.rev_element_order execWithEnv
  simp only [List.foldlM]
  change (do
    let s' ← execInstruction ⟨a :: b :: c :: d :: rest, mem, locs, adv⟩ (.swap 1)
    let s' ← execInstruction s' (.movup 2)
    let s' ← execInstruction s' (.movup 3)
    pure s') = _
  miden_swap
  miden_movup
  miden_movup
  rfl

private theorem sha256_rev_element_order_layer1_success
    (s s' : MidenState)
    (h : execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.rev_element_order = some s') :
    sha256_rev_element_order_dom s ∧ sha256_rev_element_order_sem s s' := by
  unfold sha256_rev_element_order_sem
  unfold Miden.Crypto.Sha256.rev_element_order execWithEnv at h
  simp only [List.foldlM] at h
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at h ⊢
  match stk with
  | [] =>
    simp [execInstruction, execSwap] at h
  | [a] =>
    simp [execInstruction, execSwap] at h
  | [a, b] =>
    simp [execInstruction, execSwap, execMovup, removeNth] at h
  | [a, b, c] =>
    simp [execInstruction, execSwap, execMovup, removeNth] at h
  | a :: b :: c :: d :: rest =>
    refine ⟨(sha256_rev_element_order_dom_iff ⟨a :: b :: c :: d :: rest, mem, locs, adv⟩).2
      ⟨a, b, c, d, rest, rfl⟩, ⟨a, b, c, d, rest, rfl, ?_⟩⟩
    have hc := sha256_rev_element_order_layer1_executes_local a b c d rest
      ⟨a :: b :: c :: d :: rest, mem, locs, adv⟩ rfl
    unfold Miden.Crypto.Sha256.rev_element_order execWithEnv at hc
    simp only [List.foldlM, MidenState.withStack] at hc
    rw [hc] at h
    exact (Option.some.inj h).symm

/-- Layer-1 functional correctness: on the declared helper domain, execution
produces the local stack-reversal summary. -/
theorem sha256_rev_element_order_layer1_correct
    (s s' : MidenState) :
    sha256_rev_element_order_dom s →
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.rev_element_order = some s' →
    sha256_rev_element_order_sem s s' := by
  intro h_dom h_exec
  rw [sha256_rev_element_order_dom_iff] at h_dom
  rcases h_dom with ⟨a, b, c, d, rest, hs⟩
  refine ⟨a, b, c, d, rest, hs, ?_⟩
  have h_local := sha256_rev_element_order_layer1_executes_local a b c d rest s hs
  rw [h_local] at h_exec
  exact (Option.some.inj h_exec).symm

/-- Layer-1 total correctness: execution succeeds exactly on the declared
helper domain, and then the local semantic relation holds. -/
theorem sha256_rev_element_order_layer1_total
    (s s' : MidenState) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.rev_element_order = some s' ↔
    sha256_rev_element_order_dom s ∧ sha256_rev_element_order_sem s s' := by
  constructor
  · intro h
    exact sha256_rev_element_order_layer1_success s s' h
  · rintro ⟨h_dom, h_sem⟩
    rw [sha256_rev_element_order_dom_iff] at h_dom
    rcases h_dom with ⟨a, b, c, d, rest, hs⟩
    rcases h_sem with ⟨a', b', c', d', rest', hs', hs_out⟩
    rw [hs] at hs'
    cases hs'
    rw [hs_out]
    exact sha256_rev_element_order_layer1_executes_local a b c d rest s hs

/-- Layer-1 rejection theorem: any state outside the declared helper domain is
rejected by honest execution. -/
theorem sha256_rev_element_order_layer1_reject
    (s : MidenState)
    (h_invalid : ¬ sha256_rev_element_order_dom s) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.rev_element_order = none := by
  cases h_exec : execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.rev_element_order with
  | none => rfl
  | some s' =>
    exfalso
    exact h_invalid (sha256_rev_element_order_layer1_success s s' h_exec).1

-- ============================================================================
-- Layer 2: code-level spec equivalence
-- ============================================================================

/-- Layer-2 semantic equivalence: `rev_element_order` has no separate arithmetic
spec boundary, so the code-level state spec is definitionally the local
semantic summary. -/
theorem sha256_rev_element_order_layer2_spec_equiv
    (s s' : MidenState)
    (h_sem : sha256_rev_element_order_sem s s') :
    sha256_rev_element_order_spec_sem s s' := by
  exact h_sem

/-- Direct code-vs-spec theorem: honest execution succeeds exactly when the
code-level state spec holds. -/
theorem sha256_rev_element_order_layer12_state_spec_total
    (s s' : MidenState) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.rev_element_order = some s' ↔
    sha256_rev_element_order_state_spec s s' := by
  constructor
  · intro h_exec
    exact (sha256_rev_element_order_layer1_total s s').1 h_exec |>.2
  · intro h_spec
    have h_dom : sha256_rev_element_order_dom s := by
      rcases h_spec with ⟨a, b, c, d, rest, hs, hs_out⟩
      exact ⟨a, b, c, d, rest, hs⟩
    exact (sha256_rev_element_order_layer1_total s s').2 ⟨h_dom, h_spec⟩

-- ============================================================================
-- Compatibility theorems: legacy combined Layer-1 + Layer-2 shape
-- ============================================================================

/-- Legacy combined theorem in the original file shape. -/
theorem sha256_rev_element_order_correct
    (a b c d : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: b :: c :: d :: rest) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.rev_element_order =
      some (s.withStack (d :: c :: b :: a :: rest)) := by
  exact sha256_rev_element_order_layer1_executes_local a b c d rest s hs

/-- Legacy combined soundness theorem in the original file shape. -/
theorem sha256_rev_element_order_sound
    (s s' : MidenState)
    (h : execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.rev_element_order = some s') :
    ∃ a b c d rest,
      s.stack = a :: b :: c :: d :: rest ∧
      s' = s.withStack (d :: c :: b :: a :: rest) := by
  exact (sha256_rev_element_order_layer1_total s s').1 h |>.2

/-- Legacy combined total correctness theorem in the original file shape. -/
theorem sha256_rev_element_order_total
    (s s' : MidenState) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.rev_element_order = some s' ↔
    ∃ a b c d rest,
      s.stack = a :: b :: c :: d :: rest ∧
      s' = s.withStack (d :: c :: b :: a :: rest) := by
  exact sha256_rev_element_order_layer12_state_spec_total s s'

/-- Legacy combined rejection theorem in the original file shape. -/
theorem sha256_rev_element_order_rejects_invalid_input
    (s : MidenState)
    (h_invalid : ¬ ∃ a b c d rest, s.stack = a :: b :: c :: d :: rest) :
    execWithEnv sha256ProcEnv 20 s Miden.Crypto.Sha256.rev_element_order = none := by
  apply sha256_rev_element_order_layer1_reject s
  intro h_dom
  exact h_invalid ((sha256_rev_element_order_dom_iff s).1 h_dom)

end MidenLean.Proofs
