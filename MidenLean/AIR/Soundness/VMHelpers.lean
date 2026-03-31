import MidenLean.AIR.Soundness.VM
import Mathlib.Tactic

namespace MidenLean.AIR.Soundness

open MidenLean

private theorem SymbolicFrame.satisfiesBase_getElem
    {f : SymbolicFrame} {cs : List SymbolicConstraint}
    (hsat : f.satisfiesBase cs) {i : Nat} (hi : i < cs.length) :
    cs[i] f = 0 := by
  exact hsat _ (List.getElem_mem hi)

/-- The processor main-trace obligations split naturally by extracted AIR subsystem. -/
abbrev VmBaseConstraintPieces (f : SymbolicFrame) : Prop :=
  f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.System.base ∧
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.Range.base ∧
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.Decoder.base ∧
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackGeneral.base ∧
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackOverflow.base ∧
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackOps.base ∧
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackArith.base ∧
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackCrypto.base ∧
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletSelectors.base ∧
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletBitwise.base ∧
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletHasher.base ∧
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletKernelRom.base ∧
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletMemory.base ∧
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletAce.base ∧
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.PublicInputs.base

/-- Named subsystem packaging for one symbolic VM row. -/
structure VmBaseSubsystemSatisfied (f : SymbolicFrame) : Prop where
  system :
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.System.base
  range :
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.Range.base
  decoder :
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.Decoder.base
  stackGeneral :
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackGeneral.base
  stackOverflow :
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackOverflow.base
  stackOps :
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackOps.base
  stackArith :
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackArith.base
  stackCrypto :
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackCrypto.base
  chipletSelectors :
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletSelectors.base
  chipletBitwise :
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletBitwise.base
  chipletHasher :
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletHasher.base
  chipletKernelRom :
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletKernelRom.base
  chipletMemory :
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletMemory.base
  chipletAce :
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletAce.base
  publicInputs :
    f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.PublicInputs.base

theorem VmBaseSubsystemSatisfied.toPieces {f : SymbolicFrame}
    (h : VmBaseSubsystemSatisfied f) :
    VmBaseConstraintPieces f :=
  ⟨h.system, h.range, h.decoder, h.stackGeneral, h.stackOverflow, h.stackOps,
    h.stackArith, h.stackCrypto, h.chipletSelectors, h.chipletBitwise,
    h.chipletHasher, h.chipletKernelRom, h.chipletMemory, h.chipletAce,
    h.publicInputs⟩

theorem VmBaseSubsystemSatisfied.ofPieces {f : SymbolicFrame}
    (h : VmBaseConstraintPieces f) :
    VmBaseSubsystemSatisfied f := by
  rcases h with
    ⟨hsystem, hrange, hdecoder, hstackGeneral, hstackOverflow, hstackOps,
      hstackArith, hstackCrypto, hchipletSelectors, hchipletBitwise,
      hchipletHasher, hchipletKernelRom, hchipletMemory, hchipletAce,
      hpublicInputs⟩
  exact
    { system := hsystem
      range := hrange
      decoder := hdecoder
      stackGeneral := hstackGeneral
      stackOverflow := hstackOverflow
      stackOps := hstackOps
      stackArith := hstackArith
      stackCrypto := hstackCrypto
      chipletSelectors := hchipletSelectors
      chipletBitwise := hchipletBitwise
      chipletHasher := hchipletHasher
      chipletKernelRom := hchipletKernelRom
      chipletMemory := hchipletMemory
      chipletAce := hchipletAce
      publicInputs := hpublicInputs }

/-- The aggregate processor base constraints are exactly the conjunction of the
named subsystem constraint lists. -/
theorem SymbolicFrame.satisfiesVmBaseConstraints_iff (f : SymbolicFrame) :
    f.satisfiesBase vmBaseConstraints ↔ VmBaseConstraintPieces f := by
  simp [VmBaseConstraintPieces, vmBaseConstraints,
    MidenLean.AIR.SymbolicFrame.satisfiesBase_append]

theorem VmBaseSubsystemSatisfied.ofSatisfiesVmBaseConstraints {f : SymbolicFrame}
    (hsat : f.satisfiesBase vmBaseConstraints) :
    VmBaseSubsystemSatisfied f :=
  VmBaseSubsystemSatisfied.ofPieces
    ((MidenLean.AIR.SymbolicFrame.satisfiesVmBaseConstraints_iff f).mp hsat)

theorem VmBaseSubsystemSatisfied.satisfiesVmBaseConstraints {f : SymbolicFrame}
    (h : VmBaseSubsystemSatisfied f) :
    f.satisfiesBase vmBaseConstraints :=
  (MidenLean.AIR.SymbolicFrame.satisfiesVmBaseConstraints_iff f).mpr h.toPieces

theorem VmAirSatisfied.rowBaseSubsystems {n : Nat} {w : VmWitness n}
    (hair : VmAirSatisfied w) (i : Fin n) :
    VmBaseSubsystemSatisfied (w.rowView i) :=
  VmBaseSubsystemSatisfied.ofSatisfiesVmBaseConstraints (hair.base i)

theorem VmAirSatisfied.rowSatisfiesSystem {n : Nat} {w : VmWitness n}
    (hair : VmAirSatisfied w) (i : Fin n) :
    (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.System.base :=
  (hair.rowBaseSubsystems i).system

theorem VmAirSatisfied.rowSatisfiesRange {n : Nat} {w : VmWitness n}
    (hair : VmAirSatisfied w) (i : Fin n) :
    (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.Range.base :=
  (hair.rowBaseSubsystems i).range

theorem VmAirSatisfied.rowSatisfiesDecoder {n : Nat} {w : VmWitness n}
    (hair : VmAirSatisfied w) (i : Fin n) :
    (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.Decoder.base :=
  (hair.rowBaseSubsystems i).decoder

theorem VmAirSatisfied.rowSatisfiesStackGeneral {n : Nat} {w : VmWitness n}
    (hair : VmAirSatisfied w) (i : Fin n) :
    (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackGeneral.base :=
  (hair.rowBaseSubsystems i).stackGeneral

theorem VmAirSatisfied.rowSatisfiesStackOverflow {n : Nat} {w : VmWitness n}
    (hair : VmAirSatisfied w) (i : Fin n) :
    (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackOverflow.base :=
  (hair.rowBaseSubsystems i).stackOverflow

theorem VmAirSatisfied.rowSatisfiesStackOps {n : Nat} {w : VmWitness n}
    (hair : VmAirSatisfied w) (i : Fin n) :
    (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackOps.base :=
  (hair.rowBaseSubsystems i).stackOps

theorem VmAirSatisfied.rowSatisfiesStackArith {n : Nat} {w : VmWitness n}
    (hair : VmAirSatisfied w) (i : Fin n) :
    (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackArith.base :=
  (hair.rowBaseSubsystems i).stackArith

theorem VmAirSatisfied.rowSatisfiesStackCrypto {n : Nat} {w : VmWitness n}
    (hair : VmAirSatisfied w) (i : Fin n) :
    (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackCrypto.base :=
  (hair.rowBaseSubsystems i).stackCrypto

theorem VmAirSatisfied.rowSatisfiesChipletSelectors {n : Nat} {w : VmWitness n}
    (hair : VmAirSatisfied w) (i : Fin n) :
    (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletSelectors.base :=
  (hair.rowBaseSubsystems i).chipletSelectors

theorem VmAirSatisfied.rowSatisfiesChipletBitwise {n : Nat} {w : VmWitness n}
    (hair : VmAirSatisfied w) (i : Fin n) :
    (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletBitwise.base :=
  (hair.rowBaseSubsystems i).chipletBitwise

theorem VmAirSatisfied.rowSatisfiesChipletHasher {n : Nat} {w : VmWitness n}
    (hair : VmAirSatisfied w) (i : Fin n) :
    (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletHasher.base :=
  (hair.rowBaseSubsystems i).chipletHasher

theorem VmAirSatisfied.rowSatisfiesChipletKernelRom {n : Nat} {w : VmWitness n}
    (hair : VmAirSatisfied w) (i : Fin n) :
    (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletKernelRom.base :=
  (hair.rowBaseSubsystems i).chipletKernelRom

theorem VmAirSatisfied.rowSatisfiesChipletMemory {n : Nat} {w : VmWitness n}
    (hair : VmAirSatisfied w) (i : Fin n) :
    (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletMemory.base :=
  (hair.rowBaseSubsystems i).chipletMemory

theorem VmAirSatisfied.rowSatisfiesChipletAce {n : Nat} {w : VmWitness n}
    (hair : VmAirSatisfied w) (i : Fin n) :
    (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletAce.base :=
  (hair.rowBaseSubsystems i).chipletAce

theorem VmAirSatisfied.rowSatisfiesPublicInputs {n : Nat} {w : VmWitness n}
    (hair : VmAirSatisfied w) (i : Fin n) :
    (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.PublicInputs.base :=
  (hair.rowBaseSubsystems i).publicInputs

theorem VmLayer3CompletenessAssumptions.rowBaseSubsystems
    {n : Nat} {spec : VmExecutionSpec n}
    (hcomplete : VmLayer3CompletenessAssumptions spec)
    {w : VmWitness n} (hvalid : VmValidExecution spec w) (i : Fin n) :
    VmBaseSubsystemSatisfied (w.rowView i) :=
  VmBaseSubsystemSatisfied.ofSatisfiesVmBaseConstraints (hcomplete.base hvalid i)

def VmLayer3CompletenessAssumptions.ofRowBaseSubsystems
    {n : Nat} {spec : VmExecutionSpec n}
    (wellFormed :
      ∀ {w : VmWitness n}, VmValidExecution spec w → w.WellFormed)
    (baseSubsystems :
      ∀ {w : VmWitness n}, VmValidExecution spec w →
        ∀ i : Fin n, VmBaseSubsystemSatisfied (w.rowView i))
    (bus :
      ∀ {w : VmWitness n}, VmValidExecution spec w →
        ∀ i : Fin n, (w.rowView i).satisfiesBus vmBusConstraints)
    (reducedAux :
      ∀ {w : VmWitness n}, VmValidExecution spec w →
        MidenLean.AIR.ReducedAux.verifierAccepts
          w.auxFinals w.reducedChallenges w.publicInputs) :
    VmLayer3CompletenessAssumptions spec where
  wellFormed := wellFormed
  base := by
    intro w hvalid i
    exact (baseSubsystems hvalid i).satisfiesVmBaseConstraints
  bus := bus
  reducedAux := reducedAux

@[simp] theorem VmWitness.rowView_isFirstRow {n : Nat}
    (w : VmWitness n) (i : Fin n) :
    (w.rowView i).is_first_row = if i.val = 0 then 1 else 0 := rfl

@[simp] theorem VmWitness.rowView_isLastRow {n : Nat}
    (w : VmWitness n) (i : Fin n) :
    (w.rowView i).is_last_row = if i.val + 1 = n then 1 else 0 := rfl

@[simp] theorem VmWitness.rowView_isTransition {n : Nat}
    (w : VmWitness n) (i : Fin n) :
    (w.rowView i).is_transition = if i.val + 1 < n then 1 else 0 := rfl

@[simp] theorem VmWitness.firstRowView_isFirstRow {n : Nat}
    (w : VmWitness n) :
    (w.rowView ⟨0, w.pos⟩).is_first_row = 1 := by
  simp [VmWitness.rowView]

@[simp] theorem VmWitness.lastRowView_isLastRow {n : Nat}
    (w : VmWitness n) :
    (w.rowView ⟨n - 1, Nat.sub_lt w.pos (by decide)⟩).is_last_row = 1 := by
  simp [VmWitness.rowView]

theorem system_clk_zero_of_sat (f : SymbolicFrame)
    (hsat : f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.System.base)
    (hfirst : f.is_first_row = 1) :
    f.clk = 0 := by
  have h0 := MidenLean.AIR.SymbolicFrame.satisfiesBase_getElem
    (f := f) (cs := MidenLean.AIR.Constraints.Symbolic.System.base) hsat
    (i := 0) (by simp [MidenLean.AIR.Constraints.Symbolic.System.base])
  simpa [MidenLean.AIR.Constraints.Symbolic.System.base, hfirst] using h0

theorem system_clk_step_of_sat (f : SymbolicFrame)
    (hsat : f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.System.base)
    (htrans : f.is_transition = 1) :
    f.clk' = f.clk + 1 := by
  have h1 := MidenLean.AIR.SymbolicFrame.satisfiesBase_getElem
    (f := f) (cs := MidenLean.AIR.Constraints.Symbolic.System.base) hsat
    (i := 1) (by simp [MidenLean.AIR.Constraints.Symbolic.System.base])
  simpa [MidenLean.AIR.Constraints.Symbolic.System.base, htrans] using h1

theorem range_first_row_zero_of_sat (f : SymbolicFrame)
    (hsat : f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.Range.base)
    (hfirst : f.is_first_row = 1) :
    f.colCurr 50 = 0 := by
  have h0 := MidenLean.AIR.SymbolicFrame.satisfiesBase_getElem
    (f := f) (cs := MidenLean.AIR.Constraints.Symbolic.Range.base) hsat
    (i := 0) (by simp [MidenLean.AIR.Constraints.Symbolic.Range.base])
  simpa [MidenLean.AIR.Constraints.Symbolic.Range.base, hfirst] using h0

theorem range_last_row_max_of_sat (f : SymbolicFrame)
    (hsat : f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.Range.base)
    (hlast : f.is_last_row = 1) :
    f.colCurr 50 = Felt.ofNat 65535 := by
  have h1 := MidenLean.AIR.SymbolicFrame.satisfiesBase_getElem
    (f := f) (cs := MidenLean.AIR.Constraints.Symbolic.Range.base) hsat
    (i := 1) (by simp [MidenLean.AIR.Constraints.Symbolic.Range.base])
  simpa [MidenLean.AIR.Constraints.Symbolic.Range.base, hlast] using h1

theorem range_step_polynomial_of_sat (f : SymbolicFrame)
    (hsat : f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.Range.base)
    (htrans : f.is_transition = 1) :
    (((((((((f.colNext 50 - f.colCurr 50) * ((f.colNext 50 - f.colCurr 50) - 1)) *
      ((f.colNext 50 - f.colCurr 50) - Felt.ofNat 3)) *
      ((f.colNext 50 - f.colCurr 50) - Felt.ofNat 9)) *
      ((f.colNext 50 - f.colCurr 50) - Felt.ofNat 27)) *
      ((f.colNext 50 - f.colCurr 50) - Felt.ofNat 81)) *
      ((f.colNext 50 - f.colCurr 50) - Felt.ofNat 243)) *
      ((f.colNext 50 - f.colCurr 50) - Felt.ofNat 729)) *
      ((f.colNext 50 - f.colCurr 50) - Felt.ofNat 2187)) = 0 := by
  have h2 := MidenLean.AIR.SymbolicFrame.satisfiesBase_getElem
    (f := f) (cs := MidenLean.AIR.Constraints.Symbolic.Range.base) hsat
    (i := 2) (by simp [MidenLean.AIR.Constraints.Symbolic.Range.base])
  simpa [MidenLean.AIR.Constraints.Symbolic.Range.base, htrans] using h2

theorem decoder_col22_binary_of_sat (f : SymbolicFrame)
    (hsat : f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.Decoder.base) :
    f.colCurr 22 * (f.colCurr 22 - 1) = 0 := by
  have h1 := MidenLean.AIR.SymbolicFrame.satisfiesBase_getElem
    (f := f) (cs := MidenLean.AIR.Constraints.Symbolic.Decoder.base) hsat
    (i := 1) (by simp [MidenLean.AIR.Constraints.Symbolic.Decoder.base])
  simpa [MidenLean.AIR.Constraints.Symbolic.Decoder.base] using h1

theorem decoder_opBit_binary_of_sat (f : SymbolicFrame)
    (hsat : f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.Decoder.base)
    (i : Fin 7) :
    f.colCurr (7 + i.val) * (f.colCurr (7 + i.val) - 1) = 0 := by
  fin_cases i <;>
    simpa [MidenLean.AIR.Constraints.Symbolic.Decoder.base] using
      (MidenLean.AIR.SymbolicFrame.satisfiesBase_getElem
        (f := f) (cs := MidenLean.AIR.Constraints.Symbolic.Decoder.base) hsat
        (i := by first | exact 4 | exact 5 | exact 6 | exact 7 | exact 8 | exact 9 | exact 10)
        (by simp [MidenLean.AIR.Constraints.Symbolic.Decoder.base]))

theorem decoder_col25to27_binary_of_sat (f : SymbolicFrame)
    (hsat : f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.Decoder.base)
    (i : Fin 3) :
    f.colCurr (25 + i.val) * (f.colCurr (25 + i.val) - 1) = 0 := by
  fin_cases i <;>
    simpa [MidenLean.AIR.Constraints.Symbolic.Decoder.base] using
      (MidenLean.AIR.SymbolicFrame.satisfiesBase_getElem
        (f := f) (cs := MidenLean.AIR.Constraints.Symbolic.Decoder.base) hsat
        (i := by first | exact 16 | exact 17 | exact 18)
        (by simp [MidenLean.AIR.Constraints.Symbolic.Decoder.base]))

theorem publicInputs_firstRowStackIn_of_sat (f : SymbolicFrame)
    (hsat : f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.PublicInputs.base)
    (hfirst : f.is_first_row = 1) (i : Fin 16) :
    f.s i = f.publicValue (4 + i.val) := by
  fin_cases i <;>
    have h := MidenLean.AIR.SymbolicFrame.satisfiesBase_getElem
      (f := f) (cs := MidenLean.AIR.Constraints.Symbolic.PublicInputs.base) hsat
      (i := by
        first
        | exact 0 | exact 1 | exact 2 | exact 3 | exact 4 | exact 5 | exact 6 | exact 7
        | exact 8 | exact 9 | exact 10 | exact 11 | exact 12 | exact 13 | exact 14 | exact 15)
      (by simp [MidenLean.AIR.Constraints.Symbolic.PublicInputs.base])
    all_goals
      have hEq : f.s _ - f.publicValue _ = 0 := by
        simpa [MidenLean.AIR.Constraints.Symbolic.PublicInputs.base, hfirst] using h
      exact sub_eq_zero.mp hEq

theorem publicInputs_lastRowStackOut_of_sat (f : SymbolicFrame)
    (hsat : f.satisfiesBase MidenLean.AIR.Constraints.Symbolic.PublicInputs.base)
    (hlast : f.is_last_row = 1) (i : Fin 16) :
    f.s i = f.publicValue (20 + i.val) := by
  fin_cases i <;>
    have h := MidenLean.AIR.SymbolicFrame.satisfiesBase_getElem
      (f := f) (cs := MidenLean.AIR.Constraints.Symbolic.PublicInputs.base) hsat
      (i := by
        first
        | exact 16 | exact 17 | exact 18 | exact 19 | exact 20 | exact 21 | exact 22 | exact 23
        | exact 24 | exact 25 | exact 26 | exact 27 | exact 28 | exact 29 | exact 30 | exact 31)
      (by simp [MidenLean.AIR.Constraints.Symbolic.PublicInputs.base])
    all_goals
      have hEq : f.s _ - f.publicValue _ = 0 := by
        simpa [MidenLean.AIR.Constraints.Symbolic.PublicInputs.base, hlast] using h
      exact sub_eq_zero.mp hEq

end MidenLean.AIR.Soundness
