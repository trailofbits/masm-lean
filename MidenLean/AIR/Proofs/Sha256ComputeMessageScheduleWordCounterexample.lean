import MidenLean.AIR.Constraints.StackArith
import MidenLean.AIR.Frame
import MidenLean.AIR.Proofs.U32ImmediateLoweringCounterexamples
import MidenLean.AIR.Proofs.Sha256SmallSigma0Counterexample
import MidenLean.AIR.Proofs.Sha256SmallSigma1Counterexample
import MidenLean.Proofs.Helpers
import MidenLean.Proofs.Sha256.ComputeMessageScheduleWord
/-!
# SHA-256 `compute_message_schedule_word` Layer-3 Counterexample

This file records a malicious-prover / verifier-acceptance counterexample for
the full lowered `compute_message_schedule_word` helper.

The helper lowers to:

- `exec.small_sigma_1`
- `movup.2`
- `exec.small_sigma_0`
- `u32WrappingAdd3`
- `u32WrappingAdd`

The local Layer-3 failure is inherited from the two sigma helpers. For the
non-`u32` witnesses `w[t-2] = 2^32` and `w[t-15] = 2^32`, with `w[t-7] = 0`
and `w[t-16] = 0`, the visible low 32-bit words are all zero, so the intended
SHA-256 schedule word is also zero. But the lowered AIR accepts nonzero outputs
from both sigma helpers, and the two stack-arithmetic cycles then accept their
nonzero sum. Hence the full helper boundary is locally unsound.
-/

namespace MidenLean.AIR.Proofs.Sha256ComputeMessageScheduleWordCounterexample

open MidenLean MidenLean.AIR MidenLean.AIR.Constraints
open MidenLean.AIR.Proofs.U32ImmediateLoweringCounterexamples
open MidenLean.AIR.Proofs.Sha256SmallSigma0Counterexample
open MidenLean.AIR.Proofs.Sha256SmallSigma1Counterexample

/-- Malicious `W[t-2]`: the canonical hidden-high-limb witness. -/
abbrev maliciousW2 : Felt := hiddenHighLimbInput

/-- Malicious `W[t-7]`: zero, so only the sigma helper failures matter. -/
abbrev maliciousW7 : Felt := 0

/-- Malicious `W[t-15]`: the canonical hidden-high-limb witness. -/
abbrev maliciousW15 : Felt := hiddenHighLimbInput

/-- Malicious `W[t-16]`: zero, so only the sigma helper failures matter. -/
abbrev maliciousW16 : Felt := 0

/-- AIR-visible low 32-bit sum produced by the lowered `u32WrappingAdd3`. -/
def computeMswSum3Nat : Nat :=
  (sigma0AirOutput.val + sigma1AirOutput.val + maliciousW7.val) % u32Max

/-- AIR-visible output of the lowered `u32WrappingAdd3`. -/
def computeMswSum3Output : Felt := Felt.ofNat computeMswSum3Nat

/-- AIR-visible low 32-bit output produced by the final lowered `u32WrappingAdd`. -/
def computeMswAirNat : Nat :=
  (computeMswSum3Nat + maliciousW16.val) % u32Max

/-- AIR-visible output of the full lowered `compute_message_schedule_word`
helper on the malicious witness. -/
def computeMswAirOutput : Felt := Felt.ofNat computeMswAirNat

/-- Concrete `u32add3` frame that combines the two malicious sigma outputs with
`W[t-7] = 0`. -/
def computeMswAdd3Frame : Frame :=
  Frame.ofLists
    [sigma0AirOutput.val, sigma1AirOutput.val, maliciousW7.val]
    [computeMswSum3Nat, 0]
    [computeMswSum3Nat % 2 ^ 16, computeMswSum3Nat / 2 ^ 16, 0, 0]

/-- Concrete `u32add` frame that adds `W[t-16] = 0` to the malicious `sum3`
result. -/
def computeMswAddFrame : Frame :=
  Frame.ofLists
    [computeMswSum3Nat, maliciousW16.val]
    [computeMswAirNat, 0]
    [computeMswAirNat % 2 ^ 16, computeMswAirNat / 2 ^ 16, 0]

/-- Layer-3 acceptance relation for the full lowered helper on the malicious
witness family. -/
def computeMswAirAccepts (w2 w7 w15 w16 y : Felt) : Prop :=
  w2 = maliciousW2 ∧
  w7 = maliciousW7 ∧
  w15 = maliciousW15 ∧
  w16 = maliciousW16 ∧
  smallSigma1AirAccepts w2 sigma1AirOutput ∧
  smallSigma0AirAccepts w15 sigma0AirOutput ∧
  computeMswAdd3Frame.check Constraints.u32add3 = true ∧
  computeMswAddFrame.check Constraints.u32add = true ∧
  y = computeMswAirOutput

theorem computeMswAdd3Frame_check_all :
    computeMswAdd3Frame.check Constraints.u32add3 = true := by
  native_decide

theorem computeMswAddFrame_check_all :
    computeMswAddFrame.check Constraints.u32add = true := by
  native_decide

/-- Final composed Layer-3 witness: the full lowered helper accepts a non-`u32`
input pair and produces a wrong schedule word. -/
theorem computeMswAirAccepts_malicious :
    computeMswAirAccepts maliciousW2 maliciousW7 maliciousW15 maliciousW16 computeMswAirOutput := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, computeMswAdd3Frame_check_all,
    computeMswAddFrame_check_all, rfl⟩
  · exact smallSigma1AirAccepts_malicious
  · exact smallSigma0AirAccepts_malicious

/-- Intended SHA-256 schedule word on the visible low 32-bit words of the
malicious witness. -/
def computeMswVisibleSpec (w2 w7 w15 w16 : Felt) : Felt :=
  MidenLean.Proofs.compute_msw_spec_out w2 w7 w15 w16

theorem computeMswVisibleSpec_malicious :
    computeMswVisibleSpec maliciousW2 maliciousW7 maliciousW15 maliciousW16 = 0 := by
  native_decide

theorem computeMswAirOutput_ne_visibleSpec :
    computeMswAirOutput ≠
      computeMswVisibleSpec maliciousW2 maliciousW7 maliciousW15 maliciousW16 := by
  rw [computeMswVisibleSpec_malicious]
  native_decide

/-- The helper-level AIR witness fails the same code-level partial spec used by
the honest-execution `compute_message_schedule_word` proofs. -/
theorem computeMsw_malicious_not_io_spec :
    ¬ MidenLean.Proofs.compute_msw_io_spec
      maliciousW2 maliciousW7 maliciousW15 maliciousW16 computeMswAirOutput := by
  intro h
  have hw2 : maliciousW2.IsU32 := by
    simpa [maliciousW2, Felt.IsU32, Felt.isU32, decide_eq_true_eq] using h.1
  exact hiddenHighLimbInput_not_u32 hw2

/-- Full-helper Layer-3 soundness is false against the code-level helper spec:
AIR acceptance does not imply the helper's own partial IO spec. -/
theorem computeMsw_false_io_spec_soundness_claim :
    ¬ (∀ w2 w7 w15 w16 y,
      computeMswAirAccepts w2 w7 w15 w16 y →
        MidenLean.Proofs.compute_msw_io_spec w2 w7 w15 w16 y) := by
  intro h
  exact computeMsw_malicious_not_io_spec
    (h maliciousW2 maliciousW7 maliciousW15 maliciousW16
      computeMswAirOutput computeMswAirAccepts_malicious)

/-- Full-helper Layer-3 input soundness is false already at `W[t-2]`. -/
theorem computeMsw_false_w2_input_soundness_claim :
    ¬ (∀ w2 w7 w15 w16 y,
      computeMswAirAccepts w2 w7 w15 w16 y → w2.IsU32) := by
  intro h
  exact hiddenHighLimbInput_not_u32
    (h maliciousW2 maliciousW7 maliciousW15 maliciousW16
      computeMswAirOutput computeMswAirAccepts_malicious)

/-- Full-helper Layer-3 input soundness is also false at `W[t-15]`. -/
theorem computeMsw_false_w15_input_soundness_claim :
    ¬ (∀ w2 w7 w15 w16 y,
      computeMswAirAccepts w2 w7 w15 w16 y → w15.IsU32) := by
  intro h
  exact hiddenHighLimbInput_not_u32
    (h maliciousW2 maliciousW7 maliciousW15 maliciousW16
      computeMswAirOutput computeMswAirAccepts_malicious)

/-- Full-helper Layer-3 output refinement is false for
`compute_message_schedule_word`. -/
theorem computeMsw_false_output_refinement_claim :
    ¬ (∀ w2 w7 w15 w16 y,
      computeMswAirAccepts w2 w7 w15 w16 y →
        y = computeMswVisibleSpec w2 w7 w15 w16) := by
  intro h
  exact computeMswAirOutput_ne_visibleSpec
    (h maliciousW2 maliciousW7 maliciousW15 maliciousW16
      computeMswAirOutput computeMswAirAccepts_malicious)

end MidenLean.AIR.Proofs.Sha256ComputeMessageScheduleWordCounterexample
