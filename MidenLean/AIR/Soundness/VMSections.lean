import MidenLean.AIR.Soundness.VM

set_option maxRecDepth 8192

/-!
# Whole-VM Layer-3 Closure by Subsystem Sections

This file instantiates the generic whole-VM Layer-3 scaffold with the concrete
subsystem decomposition already present in the trusted Lean AIR:

- processor/system + range + decoder
- stack constraints
- chiplet constraints
- public-input constraints
- bus constraints
- reduced auxiliary final check

The result is a closed theorem over the current trusted Lean AIR boundary,
without claiming a stronger source-semantic execution theorem.
-/

namespace MidenLean.AIR.Soundness

open MidenLean

/-- Processor-side base constraints: system, range, and decoder. -/
def vmProcessorBaseConstraints : List SymbolicConstraint :=
  MidenLean.AIR.Constraints.Symbolic.System.base ++
    MidenLean.AIR.Constraints.Symbolic.Range.base ++
    MidenLean.AIR.Constraints.Symbolic.Decoder.base

/-- Stack-side base constraints. -/
def vmStackBaseConstraints : List SymbolicConstraint :=
  MidenLean.AIR.Constraints.Symbolic.StackGeneral.base ++
    MidenLean.AIR.Constraints.Symbolic.StackOverflow.base ++
    MidenLean.AIR.Constraints.Symbolic.StackOps.base ++
    MidenLean.AIR.Constraints.Symbolic.StackArith.base ++
    MidenLean.AIR.Constraints.Symbolic.StackCrypto.base

/-- Chiplet-side base constraints. -/
def vmChipletBaseConstraints : List SymbolicConstraint :=
  MidenLean.AIR.Constraints.Symbolic.ChipletSelectors.base ++
    MidenLean.AIR.Constraints.Symbolic.ChipletBitwise.base ++
    MidenLean.AIR.Constraints.Symbolic.ChipletHasher.base ++
    MidenLean.AIR.Constraints.Symbolic.ChipletKernelRom.base ++
    MidenLean.AIR.Constraints.Symbolic.ChipletMemory.base ++
    MidenLean.AIR.Constraints.Symbolic.ChipletAce.base

/-- Public-input boundary constraints. -/
def vmPublicIOBaseConstraints : List SymbolicConstraint :=
  MidenLean.AIR.Constraints.Symbolic.PublicInputs.base

private theorem processor_subset_vmBase :
    vmProcessorBaseConstraints ⊆ vmBaseConstraints := by
  intro c hc
  change c ∈ (((vmProcessorBaseConstraints ++ vmStackBaseConstraints) ++
      vmChipletBaseConstraints) ++ vmPublicIOBaseConstraints)
  exact List.mem_append.mpr <| Or.inl <|
    List.mem_append.mpr <| Or.inl <|
      List.mem_append.mpr <| Or.inl hc

private theorem system_subset_processor :
    MidenLean.AIR.Constraints.Symbolic.System.base ⊆ vmProcessorBaseConstraints := by
  intro c hc
  change c ∈ ((MidenLean.AIR.Constraints.Symbolic.System.base ++
      MidenLean.AIR.Constraints.Symbolic.Range.base) ++
        MidenLean.AIR.Constraints.Symbolic.Decoder.base)
  exact List.mem_append.mpr <| Or.inl <|
    List.mem_append.mpr <| Or.inl hc

private theorem range_subset_processor :
    MidenLean.AIR.Constraints.Symbolic.Range.base ⊆ vmProcessorBaseConstraints := by
  intro c hc
  change c ∈ ((MidenLean.AIR.Constraints.Symbolic.System.base ++
      MidenLean.AIR.Constraints.Symbolic.Range.base) ++
        MidenLean.AIR.Constraints.Symbolic.Decoder.base)
  exact List.mem_append.mpr <| Or.inl <|
    List.mem_append.mpr <| Or.inr hc

private theorem decoder_subset_processor :
    MidenLean.AIR.Constraints.Symbolic.Decoder.base ⊆ vmProcessorBaseConstraints := by
  intro c hc
  change c ∈ ((MidenLean.AIR.Constraints.Symbolic.System.base ++
      MidenLean.AIR.Constraints.Symbolic.Range.base) ++
        MidenLean.AIR.Constraints.Symbolic.Decoder.base)
  exact List.mem_append.mpr <| Or.inr hc

private theorem system_subset_vmBase :
    MidenLean.AIR.Constraints.Symbolic.System.base ⊆ vmBaseConstraints := by
  intro c hc
  exact processor_subset_vmBase (system_subset_processor hc)

private theorem decoder_subset_vmBase :
    MidenLean.AIR.Constraints.Symbolic.Decoder.base ⊆ vmBaseConstraints := by
  intro c hc
  exact processor_subset_vmBase (decoder_subset_processor hc)

private theorem range_subset_vmBase :
    MidenLean.AIR.Constraints.Symbolic.Range.base ⊆ vmBaseConstraints := by
  intro c hc
  exact processor_subset_vmBase (range_subset_processor hc)

private theorem stack_subset_vmBase :
    vmStackBaseConstraints ⊆ vmBaseConstraints := by
  intro c hc
  change c ∈ (((vmProcessorBaseConstraints ++ vmStackBaseConstraints) ++
      vmChipletBaseConstraints) ++ vmPublicIOBaseConstraints)
  exact List.mem_append.mpr <| Or.inl <|
    List.mem_append.mpr <| Or.inl <|
      List.mem_append.mpr <| Or.inr hc

private theorem chiplets_subset_vmBase :
    vmChipletBaseConstraints ⊆ vmBaseConstraints := by
  intro c hc
  change c ∈ (((vmProcessorBaseConstraints ++ vmStackBaseConstraints) ++
      vmChipletBaseConstraints) ++ vmPublicIOBaseConstraints)
  exact List.mem_append.mpr <| Or.inl <|
    List.mem_append.mpr <| Or.inr hc

private theorem publicIO_subset_vmBase :
    vmPublicIOBaseConstraints ⊆ vmBaseConstraints := by
  intro c hc
  change c ∈ (((vmProcessorBaseConstraints ++ vmStackBaseConstraints) ++
      vmChipletBaseConstraints) ++ vmPublicIOBaseConstraints)
  exact List.mem_append.mpr <| Or.inr hc

/-- Concrete whole-VM Layer-3 validity predicate induced directly by the
trusted Lean subsystem decomposition. -/
def vmSectionSpec (n : Nat) : VmExecutionSpec n where
  systemValid := fun w =>
    w.WellFormed ∧
      ∀ i : Fin n,
        (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.System.base
  decoderValid := fun w =>
    ∀ i : Fin n,
      (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.Decoder.base
  stackValid := fun w =>
    ∀ i : Fin n, (w.rowView i).satisfiesBase vmStackBaseConstraints
  rangeValid := fun w =>
    ∀ i : Fin n,
      (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.Range.base
  chipletsValid := fun w =>
    ∀ i : Fin n, (w.rowView i).satisfiesBase vmChipletBaseConstraints
  busesValid := fun w =>
    ∀ i : Fin n, (w.rowView i).satisfiesBus vmBusConstraints
  publicIOValid := fun w =>
    (∀ i : Fin n, (w.rowView i).satisfiesBase vmPublicIOBaseConstraints) ∧
      MidenLean.AIR.ReducedAux.verifierAccepts
        w.auxFinals w.reducedChallenges w.publicInputs

/-- Closed whole-VM validity predicate obtained by decomposing the aggregate AIR
into its trusted Lean subsystems. -/
abbrev VmSectionValidExecution {n : Nat} (w : VmWitness n) : Prop :=
  VmValidExecution (vmSectionSpec n) w

/-- The generic Layer-3 soundness kit specialized to the trusted Lean
subsystem decomposition. -/
def vmSectionSoundnessAssumptions (n : Nat) :
    VmLayer3SoundnessAssumptions (vmSectionSpec n) where
  system := by
    intro w hair
    refine ⟨hair.wellFormed, ?_⟩
    intro i
    exact hair.rowSatisfiesBaseOfSubset i system_subset_vmBase
  decoder := by
    intro w hair i
    exact hair.rowSatisfiesBaseOfSubset i decoder_subset_vmBase
  stack := by
    intro w hair i
    exact hair.rowSatisfiesBaseOfSubset i stack_subset_vmBase
  range := by
    intro w hair i
    exact hair.rowSatisfiesBaseOfSubset i range_subset_vmBase
  chiplets := by
    intro w hair i
    exact hair.rowSatisfiesBaseOfSubset i chiplets_subset_vmBase
  buses := by
    intro w hair i
    simpa [vmBusConstraints] using hair.bus i
  publicIO := by
    intro w hair
    refine ⟨?_, hair.reducedAux⟩
    intro i
    exact hair.rowSatisfiesBaseOfSubset i publicIO_subset_vmBase

/-- The generic Layer-3 completeness kit specialized to the trusted Lean
subsystem decomposition. -/
def vmSectionCompletenessAssumptions (n : Nat) :
    VmLayer3CompletenessAssumptions (vmSectionSpec n) where
  wellFormed := by
    intro w hvalid
    exact hvalid.1.1
  base := by
    intro w hvalid i
    rcases hvalid with ⟨hsystem, hdecoder, hstack, hrange, hchiplets, _hbuses, hpublicIO⟩
    have hprocessor : (w.rowView i).satisfiesBase vmProcessorBaseConstraints := by
      change (w.rowView i).satisfiesBase
        ((MidenLean.AIR.Constraints.Symbolic.System.base ++
            MidenLean.AIR.Constraints.Symbolic.Range.base) ++
          MidenLean.AIR.Constraints.Symbolic.Decoder.base)
      apply MidenLean.AIR.SymbolicFrame.satisfiesBase_append.mpr
      refine ⟨?_ , hdecoder i⟩
      apply MidenLean.AIR.SymbolicFrame.satisfiesBase_append.mpr
      exact ⟨hsystem.2 i, hrange i⟩
    have hprocStack : (w.rowView i).satisfiesBase
        (vmProcessorBaseConstraints ++ vmStackBaseConstraints) := by
      exact MidenLean.AIR.SymbolicFrame.satisfiesBase_append.mpr ⟨hprocessor, hstack i⟩
    have hprocStackChiplets : (w.rowView i).satisfiesBase
        ((vmProcessorBaseConstraints ++ vmStackBaseConstraints) ++
          vmChipletBaseConstraints) := by
      exact MidenLean.AIR.SymbolicFrame.satisfiesBase_append.mpr
        ⟨hprocStack, hchiplets i⟩
    change (w.rowView i).satisfiesBase
      (((vmProcessorBaseConstraints ++ vmStackBaseConstraints) ++
        vmChipletBaseConstraints) ++ vmPublicIOBaseConstraints)
    exact MidenLean.AIR.SymbolicFrame.satisfiesBase_append.mpr
      ⟨hprocStackChiplets, hpublicIO.1 i⟩
  bus := by
    intro w hvalid i
    exact hvalid.2.2.2.2.2.1 i
  reducedAux := by
    intro w hvalid
    exact hvalid.2.2.2.2.2.2.2

/-- Closed whole-VM Layer-3 exactness theorem over the current trusted Lean AIR,
decomposed by concrete subsystem sections. -/
theorem vm_layer3_exact_by_sections {n : Nat} {w : VmWitness n} :
    VmAirSatisfied w ↔ VmSectionValidExecution w := by
  simpa [VmSectionValidExecution] using
    (vm_layer3_exact_of_assumptions
      (hsound := vmSectionSoundnessAssumptions n)
      (hcomplete := vmSectionCompletenessAssumptions n)
      (w := w))

end MidenLean.AIR.Soundness
