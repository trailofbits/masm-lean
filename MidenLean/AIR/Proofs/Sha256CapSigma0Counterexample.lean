import MidenLean.AIR.Constraints.StackArith
import MidenLean.AIR.Constraints.BitwiseChiplet
import MidenLean.AIR.Frame
import MidenLean.AIR.Proofs.U32ImmediateLoweringCounterexamples
import MidenLean.Proofs.Helpers
import MidenLean.Proofs.Sha256.CapSigma0
import MidenLean.Spec.Sha256Spec
/-!
# SHA-256 `cap_sigma_0` Layer-3 Counterexample

This file records a malicious-prover / verifier-acceptance counterexample for
the full lowered `cap_sigma_0` helper.

The helper lowers to:

- `u32rotr.2`
- `u32rotr.13`
- `u32rotr.22`
- `u32xor`
- `u32xor`

For the non-`u32` witness `2^32`, the visible low 32-bit word is `0`, so the
honest SHA-256 `cap_sigma_0` output should also be `0`. But the lowered AIR
fragments admit nonzero intermediate values for all three rotates, and the two
`u32xor` cycles accept the resulting nonzero final output. Hence the
verifier-side helper boundary is locally unsound without an enforced `u32`
precondition.
-/

namespace MidenLean.AIR.Proofs.Sha256CapSigma0Counterexample

open MidenLean MidenLean.AIR MidenLean.AIR.Constraints
open MidenLean.AIR.Constraints.BitwiseChiplet
open MidenLean.AIR.Proofs.U32ImmediateLoweringCounterexamples

/-- Immediate selector for the lowered `u32rotr.2` in `cap_sigma_0`. -/
abbrev capSigma0Rotr2Imm : ImmShift := ⟨1, by decide⟩

/-- Immediate selector for the lowered `u32rotr.13` in `cap_sigma_0`. -/
abbrev capSigma0Rotr13Imm : ImmShift := ⟨12, by decide⟩

/-- Immediate selector for the lowered `u32rotr.22` in `cap_sigma_0`. -/
abbrev capSigma0Rotr22Imm : ImmShift := ⟨21, by decide⟩

/-- AIR-visible output of lowered `u32rotr.2` on the hidden-high-limb witness. -/
def capSigma0Rotr2Output : Felt := rotrImmAirOutput capSigma0Rotr2Imm

/-- AIR-visible output of lowered `u32rotr.13` on the hidden-high-limb witness. -/
def capSigma0Rotr13Output : Felt := rotrImmAirOutput capSigma0Rotr13Imm

/-- AIR-visible output of lowered `u32rotr.22` on the hidden-high-limb witness. -/
def capSigma0Rotr22Output : Felt := rotrImmAirOutput capSigma0Rotr22Imm

/-- AIR-visible output of the first `u32xor`, combining `rotr.22` and
`rotr.13`. -/
def capSigma0Xor1Output : Felt :=
  Felt.ofNat (capSigma0Rotr22Output.val ^^^ capSigma0Rotr13Output.val)

/-- AIR-visible output of the full lowered `cap_sigma_0` helper. -/
def capSigma0AirOutput : Felt :=
  Felt.ofNat (capSigma0Rotr2Output.val ^^^ capSigma0Xor1Output.val)

/-- Intended SHA-256 `cap_sigma_0` value on the visible low 32-bit word. -/
def capSigma0VisibleSpec (x : Felt) : Felt :=
  Felt.ofNat (Sha256Spec.bigSigma0 (BitVec.ofNat 32 x.val)).toNat

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

/-- Layer-3 acceptance relation for the full lowered `cap_sigma_0` helper on
the hidden-high-limb witness. This composes:
- lowered `u32rotr.2`
- lowered `u32rotr.13`
- lowered `u32rotr.22`
- `u32xor`
- `u32xor` -/
def capSigma0AirAccepts (x y : Felt) : Prop :=
  x = hiddenHighLimbInput ∧
  (rotrMulFrame capSigma0Rotr2Imm).check Constraints.u32mul = true ∧
  (rotrAddFrame capSigma0Rotr2Imm).check Constraints.add = true ∧
  (rotrMulFrame capSigma0Rotr13Imm).check Constraints.u32mul = true ∧
  (rotrAddFrame capSigma0Rotr13Imm).check Constraints.add = true ∧
  (rotrMulFrame capSigma0Rotr22Imm).check Constraints.u32mul = true ∧
  (rotrAddFrame capSigma0Rotr22Imm).check Constraints.add = true ∧
  xorCycleAccepts capSigma0Rotr22Output capSigma0Rotr13Output capSigma0Xor1Output ∧
  xorCycleAccepts capSigma0Rotr2Output capSigma0Xor1Output y

theorem capSigma0_xor1_cycle_accepted :
    xorCycleAccepts capSigma0Rotr22Output capSigma0Rotr13Output capSigma0Xor1Output := by
  refine ⟨?_, rfl⟩
  native_decide

theorem capSigma0_xor2_cycle_accepted :
    xorCycleAccepts capSigma0Rotr2Output capSigma0Xor1Output capSigma0AirOutput := by
  refine ⟨?_, rfl⟩
  native_decide

/-- Final composed Layer-3 witness: the full lowered `cap_sigma_0` helper
accepts a non-`u32` input and produces a wrong output. -/
theorem capSigma0AirAccepts_malicious :
    capSigma0AirAccepts hiddenHighLimbInput capSigma0AirOutput := by
  refine ⟨rfl, rotrMulFrame_check_all _, rotrAddFrame_check_all _,
    rotrMulFrame_check_all _, rotrAddFrame_check_all _,
    rotrMulFrame_check_all _, rotrAddFrame_check_all _,
    capSigma0_xor1_cycle_accepted, capSigma0_xor2_cycle_accepted⟩

theorem capSigma0VisibleSpec_hiddenHighLimb :
    capSigma0VisibleSpec hiddenHighLimbInput = 0 := by
  native_decide

theorem capSigma0AirOutput_ne_capSigma0VisibleSpec :
    capSigma0AirOutput ≠ capSigma0VisibleSpec hiddenHighLimbInput := by
  rw [capSigma0VisibleSpec_hiddenHighLimb]
  native_decide

/-- The helper-level AIR witness fails the same code-level partial spec used by
the honest-execution `cap_sigma_0` proofs. -/
theorem capSigma0_malicious_not_io_spec :
    ¬ MidenLean.Proofs.sha256_cap_sigma_0_io_spec hiddenHighLimbInput capSigma0AirOutput := by
  intro h
  have hx : hiddenHighLimbInput.IsU32 := by
    simpa [Felt.IsU32, Felt.isU32, decide_eq_true_eq] using h.1
  exact hiddenHighLimbInput_not_u32 hx

/-- Full-helper Layer-3 soundness is false against the code-level helper spec:
AIR acceptance does not imply the helper's own partial IO spec. -/
theorem capSigma0_false_io_spec_soundness_claim :
    ¬ (∀ x y, capSigma0AirAccepts x y → MidenLean.Proofs.sha256_cap_sigma_0_io_spec x y) := by
  intro h
  exact capSigma0_malicious_not_io_spec
    (h hiddenHighLimbInput capSigma0AirOutput capSigma0AirAccepts_malicious)

/-- Full-helper Layer-3 input soundness is false for `cap_sigma_0`. -/
theorem capSigma0_false_input_soundness_claim :
    ¬ (∀ x y, capSigma0AirAccepts x y → x.IsU32) := by
  intro h
  exact hiddenHighLimbInput_not_u32
    (h hiddenHighLimbInput capSigma0AirOutput capSigma0AirAccepts_malicious)

/-- Full-helper Layer-3 output refinement is false for `cap_sigma_0`. -/
theorem capSigma0_false_output_refinement_claim :
    ¬ (∀ x y, capSigma0AirAccepts x y → y = capSigma0VisibleSpec x) := by
  intro h
  exact capSigma0AirOutput_ne_capSigma0VisibleSpec
    (h hiddenHighLimbInput capSigma0AirOutput capSigma0AirAccepts_malicious)

end MidenLean.AIR.Proofs.Sha256CapSigma0Counterexample
