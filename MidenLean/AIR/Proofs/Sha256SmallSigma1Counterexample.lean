import MidenLean.AIR.Constraints.StackArith
import MidenLean.AIR.Constraints.BitwiseChiplet
import MidenLean.AIR.Frame
import MidenLean.AIR.Proofs.U32ImmediateLoweringCounterexamples
import MidenLean.Proofs.Helpers
import MidenLean.Proofs.Sha256.SmallSigma1
import MidenLean.Spec.Sha256Spec
/-!
# SHA-256 `small_sigma_1` Layer-3 Counterexample

This file records a malicious-prover / verifier-acceptance counterexample for
the full lowered `small_sigma_1` helper.

The helper lowers to:

- `u32rotr.17`
- `u32rotr.19`
- `u32shr.10`
- `u32xor`
- `u32xor`

For the non-`u32` witness `2^32`, the visible low 32-bit word is `0`, so the
honest SHA-256 `small_sigma_1` output should also be `0`. But the lowered AIR
fragments admit nonzero intermediate values for both rotates and the shift, and
the two `u32xor` cycles accept the resulting nonzero final output. Hence the
verifier-side helper boundary is locally unsound without an enforced `u32`
precondition.
-/

namespace MidenLean.AIR.Proofs.Sha256SmallSigma1Counterexample

open MidenLean MidenLean.AIR MidenLean.AIR.Constraints
open MidenLean.AIR.Constraints.BitwiseChiplet
open MidenLean.AIR.Proofs.U32ImmediateLoweringCounterexamples

/-- Immediate selector for the lowered `u32rotr.17` in `small_sigma_1`. -/
abbrev sigma1Rotr17Imm : ImmShift := ⟨16, by decide⟩

/-- Immediate selector for the lowered `u32rotr.19` in `small_sigma_1`. -/
abbrev sigma1Rotr19Imm : ImmShift := ⟨18, by decide⟩

/-- Immediate selector for the lowered `u32shr.10` in `small_sigma_1`. -/
abbrev sigma1Shr10Imm : ImmShift := ⟨9, by decide⟩

/-- AIR-visible output of lowered `u32rotr.17` on the hidden-high-limb witness. -/
def sigma1Rotr17Output : Felt := rotrImmAirOutput sigma1Rotr17Imm

/-- AIR-visible output of lowered `u32rotr.19` on the hidden-high-limb witness. -/
def sigma1Rotr19Output : Felt := rotrImmAirOutput sigma1Rotr19Imm

/-- AIR-visible output of lowered `u32shr.10` on the hidden-high-limb witness. -/
def sigma1Shr10Output : Felt := shrImmAirOutput sigma1Shr10Imm

/-- AIR-visible output of the first `u32xor`, combining `rotr.19` and `shr.10`. -/
def sigma1Xor1Output : Felt :=
  Felt.ofNat (sigma1Rotr19Output.val ^^^ sigma1Shr10Output.val)

/-- AIR-visible output of the full lowered `small_sigma_1` helper. -/
def sigma1AirOutput : Felt :=
  Felt.ofNat (sigma1Rotr17Output.val ^^^ sigma1Xor1Output.val)

/-- Intended SHA-256 `small_sigma_1` value on the visible low 32-bit word. -/
def smallSigma1VisibleSpec (x : Felt) : Felt :=
  Felt.ofNat (Sha256Spec.smallSigma1 (BitVec.ofNat 32 x.val)).toNat

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

/-- Layer-3 acceptance relation for the full lowered `small_sigma_1` helper on
the hidden-high-limb witness. This composes:
- lowered `u32rotr.17`
- lowered `u32rotr.19`
- lowered `u32shr.10`
- `u32xor`
- `u32xor` -/
def smallSigma1AirAccepts (x y : Felt) : Prop :=
  x = hiddenHighLimbInput ∧
  (rotrMulFrame sigma1Rotr17Imm).check Constraints.u32mul = true ∧
  (rotrAddFrame sigma1Rotr17Imm).check Constraints.add = true ∧
  (rotrMulFrame sigma1Rotr19Imm).check Constraints.u32mul = true ∧
  (rotrAddFrame sigma1Rotr19Imm).check Constraints.add = true ∧
  (shrDivFrame sigma1Shr10Imm).check Constraints.u32div = true ∧
  xorCycleAccepts sigma1Rotr19Output sigma1Shr10Output sigma1Xor1Output ∧
  xorCycleAccepts sigma1Rotr17Output sigma1Xor1Output y

theorem sigma1_xor1_cycle_accepted :
    xorCycleAccepts sigma1Rotr19Output sigma1Shr10Output sigma1Xor1Output := by
  refine ⟨?_, rfl⟩
  native_decide

theorem sigma1_xor2_cycle_accepted :
    xorCycleAccepts sigma1Rotr17Output sigma1Xor1Output sigma1AirOutput := by
  refine ⟨?_, rfl⟩
  native_decide

/-- Final composed Layer-3 witness: the full lowered `small_sigma_1` helper
accepts a non-`u32` input and produces a wrong output. -/
theorem smallSigma1AirAccepts_malicious :
    smallSigma1AirAccepts hiddenHighLimbInput sigma1AirOutput := by
  refine ⟨rfl, rotrMulFrame_check_all _, rotrAddFrame_check_all _,
    rotrMulFrame_check_all _, rotrAddFrame_check_all _,
    shrDivFrame_check_all _, sigma1_xor1_cycle_accepted, sigma1_xor2_cycle_accepted⟩

theorem smallSigma1VisibleSpec_hiddenHighLimb :
    smallSigma1VisibleSpec hiddenHighLimbInput = 0 := by
  native_decide

theorem sigma1AirOutput_ne_smallSigma1VisibleSpec :
    sigma1AirOutput ≠ smallSigma1VisibleSpec hiddenHighLimbInput := by
  rw [smallSigma1VisibleSpec_hiddenHighLimb]
  native_decide

/-- The helper-level AIR witness fails the same code-level partial spec used by
the honest-execution `small_sigma_1` proofs. -/
theorem smallSigma1_malicious_not_io_spec :
    ¬ MidenLean.Proofs.sha256_small_sigma_1_io_spec hiddenHighLimbInput sigma1AirOutput := by
  intro h
  have hx : hiddenHighLimbInput.IsU32 := by
    simpa [Felt.IsU32, Felt.isU32, decide_eq_true_eq] using h.1
  exact hiddenHighLimbInput_not_u32 hx

/-- Full-helper Layer-3 soundness is false against the code-level helper spec:
AIR acceptance does not imply the helper's own partial IO spec. -/
theorem smallSigma1_false_io_spec_soundness_claim :
    ¬ (∀ x y, smallSigma1AirAccepts x y → MidenLean.Proofs.sha256_small_sigma_1_io_spec x y) := by
  intro h
  exact smallSigma1_malicious_not_io_spec
    (h hiddenHighLimbInput sigma1AirOutput smallSigma1AirAccepts_malicious)

/-- Full-helper Layer-3 input soundness is false for `small_sigma_1`. -/
theorem smallSigma1_false_input_soundness_claim :
    ¬ (∀ x y, smallSigma1AirAccepts x y → x.IsU32) := by
  intro h
  exact hiddenHighLimbInput_not_u32
    (h hiddenHighLimbInput sigma1AirOutput smallSigma1AirAccepts_malicious)

/-- Full-helper Layer-3 output refinement is false for `small_sigma_1`. -/
theorem smallSigma1_false_output_refinement_claim :
    ¬ (∀ x y, smallSigma1AirAccepts x y → y = smallSigma1VisibleSpec x) := by
  intro h
  exact sigma1AirOutput_ne_smallSigma1VisibleSpec
    (h hiddenHighLimbInput sigma1AirOutput smallSigma1AirAccepts_malicious)

end MidenLean.AIR.Proofs.Sha256SmallSigma1Counterexample
