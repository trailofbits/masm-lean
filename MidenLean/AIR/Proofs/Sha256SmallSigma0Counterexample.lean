import MidenLean.AIR.Constraints.StackArith
import MidenLean.AIR.Constraints.BitwiseChiplet
import MidenLean.AIR.Frame
import MidenLean.AIR.Proofs.U32ImmediateLoweringCounterexamples
import MidenLean.Proofs.Helpers
import MidenLean.Proofs.Sha256.SmallSigma0
import MidenLean.Spec.Sha256Spec
/-!
# SHA-256 `small_sigma_0` Layer-3 Counterexample

This file records a malicious-prover / verifier-acceptance counterexample at
the lowered AIR boundary.

It now contains two artifacts:

1. a one-off counterexample for the first `u32rotr.7` slice inside
   `small_sigma_0`
2. a composed helper-level counterexample for the full lowered
   `small_sigma_0` path

The immediate `u32rotr.7` lowers to:

- `push.2^25`
- `u32mul`
- `add`

For the non-`u32` input `2^32 + 128`, the stack arithmetic AIR accepts the
following trace fragment:

- `u32mul` on `[2^25, 2^32 + 128]` with output `[0, 2^25 + 1]`
- `add` on `[0, 2^25 + 1]` with output `[2^25 + 1]`

But the visible 32-bit word is `128`, and `rotr(128, 7) = 1`. Hence the
lowered AIR slice is not locally sound without a caller-side `u32`
precondition.
-/

namespace MidenLean.AIR.Proofs.Sha256SmallSigma0Counterexample

open MidenLean MidenLean.AIR MidenLean.AIR.Constraints
open MidenLean.AIR.Constraints.BitwiseChiplet
open MidenLean.AIR.Proofs.U32ImmediateLoweringCounterexamples

abbrev rotr7Const : Felt := Felt.ofNat (2 ^ 25)

/-- Non-`u32` field element whose low 32-bit word is `128`. -/
def maliciousInput : Felt := Felt.ofNat 4294967424

/-- AIR-visible result of the lowered `u32rotr.7` slice on `maliciousInput`. -/
def airOutput : Felt := Felt.ofNat 33554433

/-- Concrete `u32mul` frame for `2^25 * (2^32 + 128) = 2^57 + 2^32`. -/
def mulFrame : Frame :=
  Frame.ofLists [2 ^ 25, 4294967424] [0, 33554433] [0, 0, 1, 512, 0, 0]

/-- Concrete `add` frame that folds the split limbs back together. -/
def addFrame : Frame :=
  Frame.ofLists [0, 33554433] [33554433] []

/-- Local Layer-3 relation for the first lowered `u32rotr.7` slice used by
`small_sigma_0`: `push.2^25; u32mul; add`. -/
def loweredRotr7AirAccepts (x y : Felt) : Prop :=
  ∃ fMul fAdd : Frame,
    fMul.satisfies Constraints.u32mul ∧
    fAdd.satisfies Constraints.add ∧
    fMul.s 0 = rotr7Const ∧
    fMul.s 1 = x ∧
    fMul.s' 0 = fAdd.s 0 ∧
    fMul.s' 1 = fAdd.s 1 ∧
    fAdd.s' 0 = y

theorem mulFrame_valid : mulFrame.satisfies Constraints.u32mul := by
  apply Frame.check_sound
  native_decide

theorem addFrame_valid : addFrame.satisfies Constraints.add := by
  apply Frame.check_sound
  native_decide

theorem loweredRotr7AirAccepts_malicious :
    loweredRotr7AirAccepts maliciousInput airOutput := by
  refine ⟨mulFrame, addFrame, mulFrame_valid, addFrame_valid, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem maliciousInput_not_u32 : ¬ maliciousInput.IsU32 := by
  unfold maliciousInput Felt.IsU32
  rw [felt_ofNat_val_lt 4294967424]
  · native_decide
  · unfold GOLDILOCKS_PRIME
    native_decide

theorem visibleWord_rotr7_eq_one :
    Felt.ofNat (Sha256Spec.rotr (BitVec.ofNat 32 maliciousInput.val) 7).toNat =
      Felt.ofNat 1 := by
  unfold maliciousInput
  rw [felt_ofNat_val_lt 4294967424]
  · native_decide
  · unfold GOLDILOCKS_PRIME
    native_decide

theorem airOutput_ne_visibleWord_rotr7 :
    airOutput ≠
      Felt.ofNat (Sha256Spec.rotr (BitVec.ofNat 32 maliciousInput.val) 7).toNat := by
  rw [visibleWord_rotr7_eq_one]
  unfold airOutput
  native_decide

/-- AIR-valid lowered `u32rotr.7` slices do not force the input to be a `u32`. -/
theorem loweredRotr7_false_input_soundness_claim :
    ¬ (∀ x y, loweredRotr7AirAccepts x y → x.IsU32) := by
  intro h
  exact maliciousInput_not_u32 (h maliciousInput airOutput loweredRotr7AirAccepts_malicious)

/-- AIR-valid lowered `u32rotr.7` slices do not force the output to agree with
the 32-bit rotate of the visible low word. -/
theorem loweredRotr7_false_output_refinement_claim :
    ¬ (∀ x y, loweredRotr7AirAccepts x y →
      y = Felt.ofNat (Sha256Spec.rotr (BitVec.ofNat 32 x.val) 7).toNat) := by
  intro h
  exact airOutput_ne_visibleWord_rotr7
    (h maliciousInput airOutput loweredRotr7AirAccepts_malicious)

-- ============================================================================
-- Full `small_sigma_0` composition theorem
-- ============================================================================

/-- Immediate selector for the lowered `u32rotr.7` in `small_sigma_0`. -/
abbrev sigma0Rotr7Imm : ImmShift := ⟨6, by decide⟩

/-- Immediate selector for the lowered `u32rotr.18` in `small_sigma_0`. -/
abbrev sigma0Rotr18Imm : ImmShift := ⟨17, by decide⟩

/-- Immediate selector for the lowered `u32shr.3` in `small_sigma_0`. -/
abbrev sigma0Shr3Imm : ImmShift := ⟨2, by decide⟩

/-- AIR-visible output of lowered `u32rotr.7` on the hidden-high-limb witness. -/
def sigma0Rotr7Output : Felt := rotrImmAirOutput sigma0Rotr7Imm

/-- AIR-visible output of lowered `u32rotr.18` on the hidden-high-limb witness. -/
def sigma0Rotr18Output : Felt := rotrImmAirOutput sigma0Rotr18Imm

/-- AIR-visible output of lowered `u32shr.3` on the hidden-high-limb witness. -/
def sigma0Shr3Output : Felt := shrImmAirOutput sigma0Shr3Imm

/-- AIR-visible output of the first `u32xor`, combining `rotr.18` and `shr.3`. -/
def sigma0Xor1Output : Felt :=
  Felt.ofNat (sigma0Rotr18Output.val ^^^ sigma0Shr3Output.val)

/-- AIR-visible output of the full lowered `small_sigma_0` helper. -/
def sigma0AirOutput : Felt :=
  Felt.ofNat (sigma0Rotr7Output.val ^^^ sigma0Xor1Output.val)

/-- Intended SHA-256 `small_sigma_0` value on the visible low 32-bit word. -/
def smallSigma0VisibleSpec (x : Felt) : Felt :=
  Felt.ofNat (Sha256Spec.smallSigma0 (BitVec.ofNat 32 x.val)).toNat

private def nibbleAt (x : Nat) (i : Fin 8) : Nat :=
  (x / 16 ^ (7 - i.val)) % 16

private def prefixAt (x : Nat) (i : Fin 8) : Nat :=
  x / 16 ^ (7 - i.val)

private def bitAt (n j : Nat) : Nat :=
  (n / 2 ^ j) % 2

private def nibbleBits (n : Nat) : List Nat :=
  [bitAt n 0, bitAt n 1, bitAt n 2, bitAt n 3]

private def prevOut (x : Nat) (i : Fin 8) : Nat :=
  if i.val = 0 then 0 else x / 16 ^ (8 - i.val)

private def xorCurrRow (a b : Nat) (i : Fin 8) : List Nat :=
  let z := a ^^^ b
  [1, prefixAt a i, prefixAt b i] ++ nibbleBits (nibbleAt a i) ++
    nibbleBits (nibbleAt b i) ++ [prevOut z i, prefixAt z i]

private def xorNextRow (a b : Nat) (i : Fin 8) : List Nat :=
  if h : i.val < 7 then
    let j : Fin 8 := ⟨i.val + 1, by omega⟩
    let z := a ^^^ b
    [1, prefixAt a j, prefixAt b j] ++ nibbleBits (nibbleAt a j) ++
      nibbleBits (nibbleAt b j) ++ [prevOut z j, prefixAt z j]
  else
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def xorPeriodic (i : Fin 8) : List Nat :=
  [if i.val = 0 then 1 else 0, if i.val < 7 then 1 else 0]

private def xorFrame (a b : Nat) (i : Fin 8) : BitwiseFrame :=
  BitwiseFrame.ofLists (xorCurrRow a b i) (xorNextRow a b i) (xorPeriodic i)

/-- AIR acceptance relation for a concrete `u32xor` cycle. -/
def xorCycleAccepts (a b y : Felt) : Prop :=
  (∀ i : Fin 8, (xorFrame a.val b.val i).check allConstraints = true) ∧
  y = Felt.ofNat (a.val ^^^ b.val)

/-- Layer-3 acceptance relation for the full lowered `small_sigma_0` helper on
the hidden-high-limb witness. This composes:
- lowered `u32rotr.7`
- lowered `u32rotr.18`
- lowered `u32shr.3`
- `u32xor`
- `u32xor` -/
def smallSigma0AirAccepts (x y : Felt) : Prop :=
  x = hiddenHighLimbInput ∧
  (rotrMulFrame sigma0Rotr7Imm).check Constraints.u32mul = true ∧
  (rotrAddFrame sigma0Rotr7Imm).check Constraints.add = true ∧
  (rotrMulFrame sigma0Rotr18Imm).check Constraints.u32mul = true ∧
  (rotrAddFrame sigma0Rotr18Imm).check Constraints.add = true ∧
  (shrDivFrame sigma0Shr3Imm).check Constraints.u32div = true ∧
  xorCycleAccepts sigma0Rotr18Output sigma0Shr3Output sigma0Xor1Output ∧
  xorCycleAccepts sigma0Rotr7Output sigma0Xor1Output y

theorem sigma0_xor1_cycle_accepted :
    xorCycleAccepts sigma0Rotr18Output sigma0Shr3Output sigma0Xor1Output := by
  refine ⟨?_, rfl⟩
  native_decide

theorem sigma0_xor2_cycle_accepted :
    xorCycleAccepts sigma0Rotr7Output sigma0Xor1Output sigma0AirOutput := by
  refine ⟨?_, rfl⟩
  native_decide

/-- Final composed Layer-3 witness: the full lowered `small_sigma_0` helper
accepts a non-`u32` input and produces a wrong output. -/
theorem smallSigma0AirAccepts_malicious :
    smallSigma0AirAccepts hiddenHighLimbInput sigma0AirOutput := by
  refine ⟨rfl, rotrMulFrame_check_all _, rotrAddFrame_check_all _,
    rotrMulFrame_check_all _, rotrAddFrame_check_all _,
    shrDivFrame_check_all _, sigma0_xor1_cycle_accepted, sigma0_xor2_cycle_accepted⟩

theorem smallSigma0VisibleSpec_hiddenHighLimb :
    smallSigma0VisibleSpec hiddenHighLimbInput = 0 := by
  native_decide

theorem sigma0AirOutput_ne_smallSigma0VisibleSpec :
    sigma0AirOutput ≠ smallSigma0VisibleSpec hiddenHighLimbInput := by
  rw [smallSigma0VisibleSpec_hiddenHighLimb]
  native_decide

/-- The helper-level AIR witness fails the same code-level partial spec used by
the honest-execution `small_sigma_0` proofs. -/
theorem smallSigma0_malicious_not_io_spec :
    ¬ MidenLean.Proofs.sha256_small_sigma_0_io_spec hiddenHighLimbInput sigma0AirOutput := by
  intro h
  have hx : hiddenHighLimbInput.IsU32 := by
    simpa [Felt.IsU32, Felt.isU32, decide_eq_true_eq] using h.1
  exact hiddenHighLimbInput_not_u32 hx

/-- Full-helper Layer-3 soundness is false against the code-level helper spec:
AIR acceptance does not imply the helper's own partial IO spec. -/
theorem smallSigma0_false_io_spec_soundness_claim :
    ¬ (∀ x y, smallSigma0AirAccepts x y → MidenLean.Proofs.sha256_small_sigma_0_io_spec x y) := by
  intro h
  exact smallSigma0_malicious_not_io_spec
    (h hiddenHighLimbInput sigma0AirOutput smallSigma0AirAccepts_malicious)

/-- Full-helper Layer-3 input soundness is false for `small_sigma_0`. -/
theorem smallSigma0_false_input_soundness_claim :
    ¬ (∀ x y, smallSigma0AirAccepts x y → x.IsU32) := by
  intro h
  exact hiddenHighLimbInput_not_u32
    (h hiddenHighLimbInput sigma0AirOutput smallSigma0AirAccepts_malicious)

/-- Full-helper Layer-3 output refinement is false for `small_sigma_0`. -/
theorem smallSigma0_false_output_refinement_claim :
    ¬ (∀ x y, smallSigma0AirAccepts x y → y = smallSigma0VisibleSpec x) := by
  intro h
  exact sigma0AirOutput_ne_smallSigma0VisibleSpec
    (h hiddenHighLimbInput sigma0AirOutput smallSigma0AirAccepts_malicious)

end MidenLean.AIR.Proofs.Sha256SmallSigma0Counterexample
