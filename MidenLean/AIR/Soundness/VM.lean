import MidenLean.AIR.TraceFrame
import MidenLean.AIR.SymbolicFrame
import MidenLean.AIR.ReducedAux
import MidenLean.AIR.Constraints.Symbolic.System
import MidenLean.AIR.Constraints.Symbolic.Range
import MidenLean.AIR.Constraints.Symbolic.Decoder
import MidenLean.AIR.Constraints.Symbolic.StackGeneral
import MidenLean.AIR.Constraints.Symbolic.StackOverflow
import MidenLean.AIR.Constraints.Symbolic.StackOps
import MidenLean.AIR.Constraints.Symbolic.StackArith
import MidenLean.AIR.Constraints.Symbolic.StackCrypto
import MidenLean.AIR.Constraints.Symbolic.ChipletSelectors
import MidenLean.AIR.Constraints.Symbolic.ChipletBitwise
import MidenLean.AIR.Constraints.Symbolic.ChipletHasher
import MidenLean.AIR.Constraints.Symbolic.ChipletKernelRom
import MidenLean.AIR.Constraints.Symbolic.ChipletMemory
import MidenLean.AIR.Constraints.Symbolic.ChipletAce
import MidenLean.AIR.Constraints.Symbolic.PublicInputs
import MidenLean.AIR.Constraints.Symbolic.Bus
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Whole-VM Layer-3 Scaffold

This file packages the current trusted Lean AIR boundary for the full VM:

- a whole-trace witness built from `TraceFrame`s
- a row-wise view into the extracted symbolic AIR
- generic running-product / LogUp composition helpers
- an assumption-based Layer-3 exactness theorem shape

It intentionally stops at Layer 3:
`VmAirSatisfied ↔ VmValidExecution spec`
under explicit subsystem soundness/completeness assumptions.
-/

namespace MidenLean.AIR

open MidenLean
open scoped BigOperators

/-- Restricting the constraint list preserves base-constraint satisfaction. -/
theorem TraceFrame.satisfiesBase_of_subset {f : TraceFrame}
    {cs ds : List TraceConstraint} (hsub : cs ⊆ ds) :
    f.satisfiesBase ds → f.satisfiesBase cs := by
  intro hsat c hc
  exact hsat c (hsub hc)

/-- Restricting the constraint list preserves extension-constraint satisfaction. -/
theorem TraceFrame.satisfiesExt_of_subset {f : TraceFrame}
    {cs ds : List ExtTraceConstraint} (hsub : cs ⊆ ds) :
    f.satisfiesExt ds → f.satisfiesExt cs := by
  intro hsat c hc
  exact hsat c (hsub hc)

/-- Satisfaction of appended base constraints splits componentwise. -/
theorem TraceFrame.satisfiesBase_append {f : TraceFrame}
    {cs ds : List TraceConstraint} :
    f.satisfiesBase (cs ++ ds) ↔ f.satisfiesBase cs ∧ f.satisfiesBase ds := by
  constructor
  · intro hsat
    constructor
    · intro c hc
      exact hsat c (List.mem_append.mpr (Or.inl hc))
    · intro c hc
      exact hsat c (List.mem_append.mpr (Or.inr hc))
  · intro hsat c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hsat.1 c hc
    · exact hsat.2 c hc

/-- Satisfaction of appended extension constraints splits componentwise. -/
theorem TraceFrame.satisfiesExt_append {f : TraceFrame}
    {cs ds : List ExtTraceConstraint} :
    f.satisfiesExt (cs ++ ds) ↔ f.satisfiesExt cs ∧ f.satisfiesExt ds := by
  constructor
  · intro hsat
    constructor
    · intro c hc
      exact hsat c (List.mem_append.mpr (Or.inl hc))
    · intro c hc
      exact hsat c (List.mem_append.mpr (Or.inr hc))
  · intro hsat c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hsat.1 c hc
    · exact hsat.2 c hc

/-- Restricting the constraint list preserves symbolic base satisfaction. -/
theorem SymbolicFrame.satisfiesBase_of_subset {f : SymbolicFrame}
    {cs ds : List SymbolicConstraint} (hsub : cs ⊆ ds) :
    f.satisfiesBase ds → f.satisfiesBase cs := by
  intro hsat c hc
  exact hsat c (hsub hc)

/-- Restricting the constraint list preserves symbolic bus satisfaction. -/
theorem SymbolicFrame.satisfiesBus_of_subset {f : SymbolicFrame}
    {cs ds : List SymbolicBusConstraint} (hsub : cs ⊆ ds) :
    f.satisfiesBus ds → f.satisfiesBus cs := by
  intro hsat c hc
  exact hsat c (hsub hc)

/-- Satisfaction of appended symbolic base constraints splits componentwise. -/
theorem SymbolicFrame.satisfiesBase_append {f : SymbolicFrame}
    {cs ds : List SymbolicConstraint} :
    f.satisfiesBase (cs ++ ds) ↔ f.satisfiesBase cs ∧ f.satisfiesBase ds := by
  constructor
  · intro hsat
    constructor
    · intro c hc
      exact hsat c (List.mem_append.mpr (Or.inl hc))
    · intro c hc
      exact hsat c (List.mem_append.mpr (Or.inr hc))
  · intro hsat c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hsat.1 c hc
    · exact hsat.2 c hc

/-- Satisfaction of appended symbolic bus constraints splits componentwise. -/
theorem SymbolicFrame.satisfiesBus_append {f : SymbolicFrame}
    {cs ds : List SymbolicBusConstraint} :
    f.satisfiesBus (cs ++ ds) ↔ f.satisfiesBus cs ∧ f.satisfiesBus ds := by
  constructor
  · intro hsat
    constructor
    · intro c hc
      exact hsat c (List.mem_append.mpr (Or.inl hc))
    · intro c hc
      exact hsat c (List.mem_append.mpr (Or.inr hc))
  · intro hsat c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hsat.1 c hc
    · exact hsat.2 c hc

end MidenLean.AIR

namespace MidenLean.AIR.Soundness

open MidenLean
open scoped BigOperators

private def liftFelt {n : Nat} (f : Fin n → Felt) : Nat → Felt :=
  fun i => if h : i < n then f ⟨i, h⟩ else 0

private def liftQuad {n : Nat} (f : Fin n → QuadFelt) : Nat → QuadFelt :=
  fun i => if h : i < n then f ⟨i, h⟩ else 0

private def rowIdx {n : Nat} (i : Fin (n - 1)) : Fin n := ⟨i.val, by omega⟩

private def nextRowIdx {n : Nat} (i : Fin (n - 1)) : Fin n := ⟨i.val + 1, by omega⟩

/-- Whole-VM witness at the trusted Lean AIR boundary.

`rows` carries the typed current/next trace data. Shared verifier data and
public inputs live once at the witness level, while `WellFormed` states that
the per-row `TraceFrame`s agree with those shared values and with one another.
-/
structure VmWitness (n : Nat) where
  pos : 0 < n
  rows : Fin n → TraceFrame
  challenges : Fin 2 → QuadFelt
  permValues : Fin 8 → QuadFelt
  publicInputs : MidenLean.AIR.ReducedAux.PublicInputs
  periodic : Nat → Felt := fun _ => 0
  preprocessed : Nat → Felt := fun _ => 0

abbrev VmWitness.firstRow {n : Nat} (w : VmWitness n) : TraceFrame :=
  w.rows ⟨0, w.pos⟩

abbrev VmWitness.lastRow {n : Nat} (w : VmWitness n) : TraceFrame :=
  w.rows ⟨n - 1, Nat.sub_lt w.pos (by decide)⟩

/-- Shared reduced-aux challenges induced by the witness. -/
def VmWitness.reducedChallenges {n : Nat} (w : VmWitness n) :
    MidenLean.AIR.ReducedAux.Challenges :=
  MidenLean.AIR.ReducedAux.Challenges.new
    (w.challenges ⟨0, by decide⟩)
    (w.challenges ⟨1, by decide⟩)

/-- Shared final auxiliary values induced by the witness. -/
def VmWitness.auxFinals {n : Nat} (w : VmWitness n) :
    MidenLean.AIR.ReducedAux.AuxFinals where
  p1 := w.permValues ⟨0, by decide⟩
  p2 := w.permValues ⟨1, by decide⟩
  p3 := w.permValues ⟨2, by decide⟩
  s_aux := w.permValues ⟨3, by decide⟩
  b_range := w.permValues ⟨4, by decide⟩
  b_hash_kernel := w.permValues ⟨5, by decide⟩
  b_chiplets := w.permValues ⟨6, by decide⟩
  v_wiring := w.permValues ⟨7, by decide⟩

/-- Well-formedness of the row sequence and the shared verifier data. -/
structure VmWitness.WellFormed {n : Nat} (w : VmWitness n) : Prop where
  main_link :
    ∀ i : Fin (n - 1), ∀ j : Fin 71,
      (w.rows (rowIdx i)).next j = (w.rows (nextRowIdx i)).curr j
  aux_link :
    ∀ i : Fin (n - 1), ∀ j : Fin 8,
      (w.rows (rowIdx i)).aux_next j = (w.rows (nextRowIdx i)).aux_curr j
  row_challenges :
    ∀ i : Fin n, ∀ j : Fin 2, (w.rows i).challenge j = w.challenges j
  row_permValues :
    ∀ i : Fin n, ∀ j : Fin 8, (w.rows i).perm_value j = w.permValues j

/-- Symbolic row view consumed by the extracted whole-VM AIR. -/
def VmWitness.rowView {n : Nat} (w : VmWitness n) (i : Fin n) : SymbolicFrame where
  curr := liftFelt (w.rows i).curr
  next := liftFelt (w.rows i).next
  auxCurr := liftQuad (w.rows i).aux_curr
  auxNext := liftQuad (w.rows i).aux_next
  challenge := liftQuad w.challenges
  permValue := liftQuad w.permValues
  publicValue := liftFelt w.publicInputs.values
  periodic := w.periodic
  preprocessed := w.preprocessed
  is_first_row := if i.val = 0 then 1 else 0
  is_last_row := if i.val + 1 = n then 1 else 0
  is_transition := if i.val + 1 < n then 1 else 0

/-- Aggregate trusted Lean base constraints for the processor main trace. -/
def vmBaseConstraints : List SymbolicConstraint :=
  MidenLean.AIR.Constraints.Symbolic.System.base ++
    MidenLean.AIR.Constraints.Symbolic.Range.base ++
    MidenLean.AIR.Constraints.Symbolic.Decoder.base ++
    MidenLean.AIR.Constraints.Symbolic.StackGeneral.base ++
    MidenLean.AIR.Constraints.Symbolic.StackOverflow.base ++
    MidenLean.AIR.Constraints.Symbolic.StackOps.base ++
    MidenLean.AIR.Constraints.Symbolic.StackArith.base ++
    MidenLean.AIR.Constraints.Symbolic.StackCrypto.base ++
    MidenLean.AIR.Constraints.Symbolic.ChipletSelectors.base ++
    MidenLean.AIR.Constraints.Symbolic.ChipletBitwise.base ++
    MidenLean.AIR.Constraints.Symbolic.ChipletHasher.base ++
    MidenLean.AIR.Constraints.Symbolic.ChipletKernelRom.base ++
    MidenLean.AIR.Constraints.Symbolic.ChipletMemory.base ++
    MidenLean.AIR.Constraints.Symbolic.ChipletAce.base ++
    MidenLean.AIR.Constraints.Symbolic.PublicInputs.base

/-- Aggregate trusted Lean extension-field bus constraints. -/
def vmBusConstraints : List SymbolicBusConstraint :=
  MidenLean.AIR.Constraints.Symbolic.Bus.bus

/-- Whole-VM AIR satisfaction at Layer 3. -/
structure VmAirSatisfied {n : Nat} (w : VmWitness n) : Prop where
  wellFormed : w.WellFormed
  base :
    ∀ i : Fin n, (w.rowView i).satisfiesBase vmBaseConstraints
  bus :
    ∀ i : Fin n, (w.rowView i).satisfiesBus vmBusConstraints
  reducedAux :
    MidenLean.AIR.ReducedAux.verifierAccepts
      w.auxFinals w.reducedChallenges w.publicInputs

/-- Extract any base-constraint subsystem from the aggregate Layer-3 hypothesis. -/
theorem VmAirSatisfied.rowSatisfiesBaseOfSubset {n : Nat} {w : VmWitness n}
    (hair : VmAirSatisfied w) (i : Fin n) {cs : List SymbolicConstraint}
    (hsub : cs ⊆ vmBaseConstraints) :
    (w.rowView i).satisfiesBase cs :=
  MidenLean.AIR.SymbolicFrame.satisfiesBase_of_subset hsub (hair.base i)

/-- Extract any bus-constraint subsystem from the aggregate Layer-3 hypothesis. -/
theorem VmAirSatisfied.rowSatisfiesBusOfSubset {n : Nat} {w : VmWitness n}
    (hair : VmAirSatisfied w) (i : Fin n) {cs : List SymbolicBusConstraint}
    (hsub : cs ⊆ vmBusConstraints) :
    (w.rowView i).satisfiesBus cs :=
  MidenLean.AIR.SymbolicFrame.satisfiesBus_of_subset hsub (hair.bus i)

/-- A local running-product witness for one auxiliary bus column. -/
structure RunningProductWitness {n : Nat} (w : VmWitness n) (col : Fin 8) where
  response : Fin (n - 1) → QuadFelt
  request : Fin (n - 1) → QuadFelt
  boundary_one : w.firstRow.aux_curr col = QuadFelt.one
  transition :
    ∀ i : Fin (n - 1),
      (w.rows (rowIdx i)).aux_next col * request i =
        (w.rows (rowIdx i)).aux_curr col * response i
  final_one : w.lastRow.aux_curr col = QuadFelt.one

/-- A local additive LogUp witness for one auxiliary column. -/
structure LogUpWitness {n : Nat} (w : VmWitness n) (col : Fin 8) where
  term : Fin (n - 1) → QuadFelt
  boundary_zero : w.firstRow.aux_curr col = QuadFelt.zero
  transition :
    ∀ i : Fin (n - 1),
      (w.rows (rowIdx i)).aux_next col =
        (w.rows (rowIdx i)).aux_curr col + term i
  final_zero : w.lastRow.aux_curr col = QuadFelt.zero

/-- Normalize a local running-product witness into `ReducedAux.RunningProduct`. -/
def RunningProductWitness.toRunningProduct {n : Nat} {w : VmWitness n}
    {col : Fin 8} (_hwf : w.WellFormed) (h : RunningProductWitness w col) :
    MidenLean.AIR.ReducedAux.RunningProduct n where
  val := fun i => (w.rows i).aux_curr col
  response := h.response
  request := h.request

theorem RunningProductWitness.transitionOk {n : Nat} {w : VmWitness n}
    {col : Fin 8} (hwf : w.WellFormed) (h : RunningProductWitness w col) :
    (h.toRunningProduct hwf).transitionOk := by
  intro i
  have hlink := hwf.aux_link i col
  calc
    (h.toRunningProduct hwf).val ⟨i.val + 1, by omega⟩ * h.request i
        = (w.rows (nextRowIdx i)).aux_curr col * h.request i := by
            rfl
    _ = (w.rows (rowIdx i)).aux_next col * h.request i := by
          rw [← hlink]
    _ = (w.rows (rowIdx i)).aux_curr col * h.response i := h.transition i
    _ = (h.toRunningProduct hwf).val ⟨i.val, by omega⟩ * h.response i := by
          rfl

/-- Generic encoded-product identity for a normalized VM bus witness. -/
theorem RunningProductWitness.encoded_product_eq {n : Nat} {w : VmWitness n}
    {col : Fin 8} (hwf : w.WellFormed) (h : RunningProductWitness w col) :
    (∏ i : Fin (n - 1), h.response i) =
      ∏ i : Fin (n - 1), h.request i := by
  let rp := h.toRunningProduct hwf
  let last : Fin n := ⟨n - 1, Nat.sub_lt w.pos (by decide)⟩
  have hboundary : rp.boundaryOk w.pos := by
    simpa [rp, RunningProductWitness.toRunningProduct, VmWitness.firstRow]
      using h.boundary_one
  have htransition : rp.transitionOk := h.transitionOk hwf
  have hfinal : rp.val last = QuadFelt.one := by
    simpa [rp, last, RunningProductWitness.toRunningProduct, VmWitness.lastRow]
      using h.final_one
  simpa [rp, RunningProductWitness.toRunningProduct] using
    MidenLean.AIR.ReducedAux.RunningProduct.encoded_product_eq_of_final_one
      (rp := rp) (hn := w.pos) hboundary htransition hfinal

/-- Normalize a local LogUp witness into the additive `ReducedAux` form. -/
theorem LogUpWitness.sum_zero {n : Nat} {w : VmWitness n}
    {col : Fin 8} (hwf : w.WellFormed) (h : LogUpWitness w col) :
    (∑ i : Fin (n - 1), h.term i) = QuadFelt.zero := by
  let val : Fin n → QuadFelt := fun i => (w.rows i).aux_curr col
  have htransition :
      ∀ i : Fin (n - 1),
        val ⟨i.val + 1, by omega⟩ = val ⟨i.val, by omega⟩ + h.term i := by
    intro i
    have hlink := hwf.aux_link i col
    calc
      val ⟨i.val + 1, by omega⟩ = (w.rows (nextRowIdx i)).aux_curr col := by
        rfl
      _ = (w.rows (rowIdx i)).aux_next col := by
            rw [← hlink]
      _ = (w.rows (rowIdx i)).aux_curr col + h.term i := h.transition i
      _ = val ⟨i.val, by omega⟩ + h.term i := by
            rfl
  simpa [val, VmWitness.firstRow, VmWitness.lastRow] using
    MidenLean.AIR.ReducedAux.logup_sum_zero
      (val := val) (term := h.term) (hn := w.pos)
      (hb := by simpa [val, VmWitness.firstRow] using h.boundary_zero)
      htransition
      (hfinal := by simpa [val, VmWitness.lastRow] using h.final_zero)

/-- Expose the generic encoded-product identity from `VmAirSatisfied`. -/
theorem VmAirSatisfied.encodedProductEq {n : Nat} {w : VmWitness n}
    (hair : VmAirSatisfied w) {col : Fin 8} (h : RunningProductWitness w col) :
    (∏ i : Fin (n - 1), h.response i) =
      ∏ i : Fin (n - 1), h.request i :=
  h.encoded_product_eq hair.wellFormed

/-- Expose the generic LogUp zero-sum identity from `VmAirSatisfied`. -/
theorem VmAirSatisfied.logupSumZero {n : Nat} {w : VmWitness n}
    (hair : VmAirSatisfied w) {col : Fin 8} (h : LogUpWitness w col) :
    (∑ i : Fin (n - 1), h.term i) = QuadFelt.zero :=
  h.sum_zero hair.wellFormed

/-- Concrete whole-VM validity at the current trusted Lean AIR boundary.

This is the strongest closed whole-VM notion justified by the current
repository state. It records exactly the split symbolic AIR obligations already
modeled in Lean, plus trace well-formedness and reduced-aux verifier
acceptance.

It is intentionally not a source-semantics statement: the repository still
lacks a relation from a `VmWitness` to a concrete `(procedures, ops, fuel,
initialState, finalState)` execution of `MidenLean.execWithProcs`. In
particular, `VmWitness` does not yet carry a program/procedure environment or a
proof that decoder, memory, clock/context, and chiplet rows arise from that
execution. -/
structure VmCurrentAirValid {n : Nat} (w : VmWitness n) : Prop where
  wellFormed : w.WellFormed
  system :
    ∀ i : Fin n, (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.System.base
  range :
    ∀ i : Fin n, (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.Range.base
  decoder :
    ∀ i : Fin n, (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.Decoder.base
  stackGeneral :
    ∀ i : Fin n, (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackGeneral.base
  stackOverflow :
    ∀ i : Fin n, (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackOverflow.base
  stackOps :
    ∀ i : Fin n, (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackOps.base
  stackArith :
    ∀ i : Fin n, (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackArith.base
  stackCrypto :
    ∀ i : Fin n, (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackCrypto.base
  chipletSelectors :
    ∀ i : Fin n, (w.rowView i).satisfiesBase
      MidenLean.AIR.Constraints.Symbolic.ChipletSelectors.base
  chipletBitwise :
    ∀ i : Fin n, (w.rowView i).satisfiesBase
      MidenLean.AIR.Constraints.Symbolic.ChipletBitwise.base
  chipletHasher :
    ∀ i : Fin n, (w.rowView i).satisfiesBase
      MidenLean.AIR.Constraints.Symbolic.ChipletHasher.base
  chipletKernelRom :
    ∀ i : Fin n, (w.rowView i).satisfiesBase
      MidenLean.AIR.Constraints.Symbolic.ChipletKernelRom.base
  chipletMemory :
    ∀ i : Fin n, (w.rowView i).satisfiesBase
      MidenLean.AIR.Constraints.Symbolic.ChipletMemory.base
  chipletAce :
    ∀ i : Fin n, (w.rowView i).satisfiesBase
      MidenLean.AIR.Constraints.Symbolic.ChipletAce.base
  publicInputs :
    ∀ i : Fin n, (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.PublicInputs.base
  bus :
    ∀ i : Fin n, (w.rowView i).satisfiesBus MidenLean.AIR.Constraints.Symbolic.Bus.bus
  reducedAux :
    MidenLean.AIR.ReducedAux.verifierAccepts
      w.auxFinals w.reducedChallenges w.publicInputs

private theorem rowSatisfiesVmBaseConstraints_ofCurrentAirValid
    {n : Nat} {w : VmWitness n} (i : Fin n)
    (hsystem :
      (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.System.base)
    (hrange :
      (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.Range.base)
    (hdecoder :
      (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.Decoder.base)
    (hstackGeneral :
      (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackGeneral.base)
    (hstackOverflow :
      (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackOverflow.base)
    (hstackOps :
      (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackOps.base)
    (hstackArith :
      (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackArith.base)
    (hstackCrypto :
      (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackCrypto.base)
    (hchipletSelectors :
      (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletSelectors.base)
    (hchipletBitwise :
      (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletBitwise.base)
    (hchipletHasher :
      (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletHasher.base)
    (hchipletKernelRom :
      (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletKernelRom.base)
    (hchipletMemory :
      (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletMemory.base)
    (hchipletAce :
      (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletAce.base)
    (hpublicInputs :
      (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.PublicInputs.base) :
    (w.rowView i).satisfiesBase vmBaseConstraints := by
  simpa [vmBaseConstraints] using
    (MidenLean.AIR.SymbolicFrame.satisfiesBase_append).2
      ⟨hsystem,
        (MidenLean.AIR.SymbolicFrame.satisfiesBase_append).2
          ⟨hrange,
            (MidenLean.AIR.SymbolicFrame.satisfiesBase_append).2
              ⟨hdecoder,
                (MidenLean.AIR.SymbolicFrame.satisfiesBase_append).2
                  ⟨hstackGeneral,
                    (MidenLean.AIR.SymbolicFrame.satisfiesBase_append).2
                      ⟨hstackOverflow,
                        (MidenLean.AIR.SymbolicFrame.satisfiesBase_append).2
                          ⟨hstackOps,
                            (MidenLean.AIR.SymbolicFrame.satisfiesBase_append).2
                              ⟨hstackArith,
                                (MidenLean.AIR.SymbolicFrame.satisfiesBase_append).2
                                  ⟨hstackCrypto,
                                    (MidenLean.AIR.SymbolicFrame.satisfiesBase_append).2
                                      ⟨hchipletSelectors,
                                        (MidenLean.AIR.SymbolicFrame.satisfiesBase_append).2
                                          ⟨hchipletBitwise,
                                            (MidenLean.AIR.SymbolicFrame.satisfiesBase_append).2
                                              ⟨hchipletHasher,
                                                (MidenLean.AIR.SymbolicFrame.satisfiesBase_append).2
                                                  ⟨hchipletKernelRom,
                                                    (MidenLean.AIR.SymbolicFrame.satisfiesBase_append).2
                                                      ⟨hchipletMemory,
                                                        (MidenLean.AIR.SymbolicFrame.satisfiesBase_append).2
                                                          ⟨hchipletAce, hpublicInputs⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

/-- Closed Layer-3 exactness for the current trusted Lean AIR boundary.

This theorem is stronger than `vm_layer3_exact_of_assumptions`: it has no
soundness/completeness hypotheses, but it only reaches the concrete AIR
boundary currently modeled in Lean, not source-program semantics. -/
theorem vm_layer3_exact_current_air_valid {n : Nat} {w : VmWitness n} :
    VmAirSatisfied w ↔ VmCurrentAirValid w := by
  constructor
  · intro hair
    refine
      { wellFormed := hair.wellFormed
        system := ?_
        range := ?_
        decoder := ?_
        stackGeneral := ?_
        stackOverflow := ?_
        stackOps := ?_
        stackArith := ?_
        stackCrypto := ?_
        chipletSelectors := ?_
        chipletBitwise := ?_
        chipletHasher := ?_
        chipletKernelRom := ?_
        chipletMemory := ?_
        chipletAce := ?_
        publicInputs := ?_
        bus := ?_
        reducedAux := hair.reducedAux }
    · intro i
      exact hair.rowSatisfiesBaseOfSubset i
        (cs := MidenLean.AIR.Constraints.Symbolic.System.base)
        (hsub := by
          intro c hc
          simp [vmBaseConstraints, hc])
    · intro i
      exact hair.rowSatisfiesBaseOfSubset i
        (cs := MidenLean.AIR.Constraints.Symbolic.Range.base)
        (hsub := by
          intro c hc
          simp [vmBaseConstraints, hc])
    · intro i
      exact hair.rowSatisfiesBaseOfSubset i
        (cs := MidenLean.AIR.Constraints.Symbolic.Decoder.base)
        (hsub := by
          intro c hc
          simp [vmBaseConstraints, hc])
    · intro i
      exact hair.rowSatisfiesBaseOfSubset i
        (cs := MidenLean.AIR.Constraints.Symbolic.StackGeneral.base)
        (hsub := by
          intro c hc
          simp [vmBaseConstraints, hc])
    · intro i
      exact hair.rowSatisfiesBaseOfSubset i
        (cs := MidenLean.AIR.Constraints.Symbolic.StackOverflow.base)
        (hsub := by
          intro c hc
          simp [vmBaseConstraints, hc])
    · intro i
      exact hair.rowSatisfiesBaseOfSubset i
        (cs := MidenLean.AIR.Constraints.Symbolic.StackOps.base)
        (hsub := by
          intro c hc
          simp [vmBaseConstraints, hc])
    · intro i
      exact hair.rowSatisfiesBaseOfSubset i
        (cs := MidenLean.AIR.Constraints.Symbolic.StackArith.base)
        (hsub := by
          intro c hc
          simp [vmBaseConstraints, hc])
    · intro i
      exact hair.rowSatisfiesBaseOfSubset i
        (cs := MidenLean.AIR.Constraints.Symbolic.StackCrypto.base)
        (hsub := by
          intro c hc
          simp [vmBaseConstraints, hc])
    · intro i
      exact hair.rowSatisfiesBaseOfSubset i
        (cs := MidenLean.AIR.Constraints.Symbolic.ChipletSelectors.base)
        (hsub := by
          intro c hc
          simp [vmBaseConstraints, hc])
    · intro i
      exact hair.rowSatisfiesBaseOfSubset i
        (cs := MidenLean.AIR.Constraints.Symbolic.ChipletBitwise.base)
        (hsub := by
          intro c hc
          simp [vmBaseConstraints, hc])
    · intro i
      exact hair.rowSatisfiesBaseOfSubset i
        (cs := MidenLean.AIR.Constraints.Symbolic.ChipletHasher.base)
        (hsub := by
          intro c hc
          simp [vmBaseConstraints, hc])
    · intro i
      exact hair.rowSatisfiesBaseOfSubset i
        (cs := MidenLean.AIR.Constraints.Symbolic.ChipletKernelRom.base)
        (hsub := by
          intro c hc
          simp [vmBaseConstraints, hc])
    · intro i
      exact hair.rowSatisfiesBaseOfSubset i
        (cs := MidenLean.AIR.Constraints.Symbolic.ChipletMemory.base)
        (hsub := by
          intro c hc
          simp [vmBaseConstraints, hc])
    · intro i
      exact hair.rowSatisfiesBaseOfSubset i
        (cs := MidenLean.AIR.Constraints.Symbolic.ChipletAce.base)
        (hsub := by
          intro c hc
          simp [vmBaseConstraints, hc])
    · intro i
      exact hair.rowSatisfiesBaseOfSubset i
        (cs := MidenLean.AIR.Constraints.Symbolic.PublicInputs.base)
        (hsub := by
          intro c hc
          simp [vmBaseConstraints, hc])
    · simpa [vmBusConstraints] using hair.bus
  · intro hvalid
    refine
      { wellFormed := hvalid.wellFormed
        base := ?_
        bus := ?_
        reducedAux := hvalid.reducedAux }
    · intro i
      exact rowSatisfiesVmBaseConstraints_ofCurrentAirValid i
        (hsystem := hvalid.system i)
        (hrange := hvalid.range i)
        (hdecoder := hvalid.decoder i)
        (hstackGeneral := hvalid.stackGeneral i)
        (hstackOverflow := hvalid.stackOverflow i)
        (hstackOps := hvalid.stackOps i)
        (hstackArith := hvalid.stackArith i)
        (hstackCrypto := hvalid.stackCrypto i)
        (hchipletSelectors := hvalid.chipletSelectors i)
        (hchipletBitwise := hvalid.chipletBitwise i)
        (hchipletHasher := hvalid.chipletHasher i)
        (hchipletKernelRom := hvalid.chipletKernelRom i)
        (hchipletMemory := hvalid.chipletMemory i)
        (hchipletAce := hvalid.chipletAce i)
        (hpublicInputs := hvalid.publicInputs i)
    · intro i
      simpa [vmBusConstraints] using hvalid.bus i

/-- Whole-VM semantic validity factored by subsystem.

This is intentionally abstract: the repository does not yet contain a single
fully elaborated whole-VM execution semantics object with clock/context,
decoder state, memory trace, and chiplet trace all bundled together.
-/
structure VmExecutionSpec (n : Nat) where
  systemValid : VmWitness n → Prop
  decoderValid : VmWitness n → Prop
  stackValid : VmWitness n → Prop
  rangeValid : VmWitness n → Prop
  chipletsValid : VmWitness n → Prop
  busesValid : VmWitness n → Prop
  publicIOValid : VmWitness n → Prop

/-- Whole-VM semantic validity assembled from subsystem obligations. -/
def VmValidExecution {n : Nat} (spec : VmExecutionSpec n) (w : VmWitness n) : Prop :=
  spec.systemValid w ∧ spec.decoderValid w ∧ spec.stackValid w ∧
    spec.rangeValid w ∧ spec.chipletsValid w ∧ spec.busesValid w ∧
    spec.publicIOValid w

/-- Layer-3 soundness assumptions, factored by subsystem semantics. -/
structure VmLayer3SoundnessAssumptions {n : Nat} (spec : VmExecutionSpec n) : Prop where
  system :
    ∀ {w : VmWitness n}, VmAirSatisfied w → spec.systemValid w
  decoder :
    ∀ {w : VmWitness n}, VmAirSatisfied w → spec.decoderValid w
  stack :
    ∀ {w : VmWitness n}, VmAirSatisfied w → spec.stackValid w
  range :
    ∀ {w : VmWitness n}, VmAirSatisfied w → spec.rangeValid w
  chiplets :
    ∀ {w : VmWitness n}, VmAirSatisfied w → spec.chipletsValid w
  buses :
    ∀ {w : VmWitness n}, VmAirSatisfied w → spec.busesValid w
  publicIO :
    ∀ {w : VmWitness n}, VmAirSatisfied w → spec.publicIOValid w

/-- Layer-3 completeness assumptions for the trusted Lean AIR boundary. -/
structure VmLayer3CompletenessAssumptions {n : Nat} (spec : VmExecutionSpec n) : Prop where
  wellFormed :
    ∀ {w : VmWitness n}, VmValidExecution spec w → w.WellFormed
  base :
    ∀ {w : VmWitness n}, VmValidExecution spec w →
      ∀ i : Fin n, (w.rowView i).satisfiesBase vmBaseConstraints
  bus :
    ∀ {w : VmWitness n}, VmValidExecution spec w →
      ∀ i : Fin n, (w.rowView i).satisfiesBus vmBusConstraints
  reducedAux :
    ∀ {w : VmWitness n}, VmValidExecution spec w →
      MidenLean.AIR.ReducedAux.verifierAccepts
        w.auxFinals w.reducedChallenges w.publicInputs

/-- Whole-VM Layer-3 soundness, assuming each subsystem bridge is available. -/
theorem vm_layer3_sound_of_assumptions {n : Nat} {spec : VmExecutionSpec n}
    (hsound : VmLayer3SoundnessAssumptions spec) {w : VmWitness n} :
    VmAirSatisfied w → VmValidExecution spec w := by
  intro hair
  exact ⟨hsound.system hair, hsound.decoder hair, hsound.stack hair,
    hsound.range hair, hsound.chiplets hair, hsound.buses hair,
    hsound.publicIO hair⟩

/-- Whole-VM Layer-3 completeness, assuming the semantic witness constructs the
trusted Lean AIR directly. -/
theorem vm_layer3_complete_of_assumptions {n : Nat} {spec : VmExecutionSpec n}
    (hcomplete : VmLayer3CompletenessAssumptions spec) {w : VmWitness n} :
    VmValidExecution spec w → VmAirSatisfied w := by
  intro hvalid
  exact
    { wellFormed := hcomplete.wellFormed hvalid
      base := hcomplete.base hvalid
      bus := hcomplete.bus hvalid
      reducedAux := hcomplete.reducedAux hvalid }

/-- Whole-VM Layer-3 exactness theorem shape under explicit subsystem bridges. -/
theorem vm_layer3_exact_of_assumptions {n : Nat} {spec : VmExecutionSpec n}
    (hsound : VmLayer3SoundnessAssumptions spec)
    (hcomplete : VmLayer3CompletenessAssumptions spec)
    {w : VmWitness n} :
    VmAirSatisfied w ↔ VmValidExecution spec w := by
  constructor
  · exact vm_layer3_sound_of_assumptions hsound
  · exact vm_layer3_complete_of_assumptions hcomplete

/-- Concrete `VmExecutionSpec` matching exactly the current trusted AIR
boundary, grouped by subsystem family. -/
def vmCurrentAirSpec (n : Nat) : VmExecutionSpec n where
  systemValid w :=
    w.WellFormed ∧
      ∀ i : Fin n, (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.System.base
  decoderValid w :=
    ∀ i : Fin n, (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.Decoder.base
  stackValid w :=
    ∀ i : Fin n,
      (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackGeneral.base ∧
        (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackOverflow.base ∧
        (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackOps.base ∧
        (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackArith.base ∧
        (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.StackCrypto.base
  rangeValid w :=
    ∀ i : Fin n, (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.Range.base
  chipletsValid w :=
    ∀ i : Fin n,
      (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletSelectors.base ∧
        (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletBitwise.base ∧
        (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletHasher.base ∧
        (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletKernelRom.base ∧
        (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletMemory.base ∧
        (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.ChipletAce.base
  busesValid w :=
    (∀ i : Fin n, (w.rowView i).satisfiesBus MidenLean.AIR.Constraints.Symbolic.Bus.bus) ∧
      MidenLean.AIR.ReducedAux.verifierAccepts
        w.auxFinals w.reducedChallenges w.publicInputs
  publicIOValid w :=
    ∀ i : Fin n, (w.rowView i).satisfiesBase MidenLean.AIR.Constraints.Symbolic.PublicInputs.base

/-- The concrete current-AIR `VmExecutionSpec` is equivalent to the more
readable `VmCurrentAirValid` predicate. -/
theorem vm_validExecution_current_air_spec_iff {n : Nat} {w : VmWitness n} :
    VmValidExecution (vmCurrentAirSpec n) w ↔ VmCurrentAirValid w := by
  constructor
  · intro hvalid
    rcases hvalid with ⟨hsystem, hdecoder, hstack, hrange, hchiplets, hbuses, hpublicInputs⟩
    refine
      { wellFormed := hsystem.1
        system := hsystem.2
        range := hrange
        decoder := hdecoder
        stackGeneral := ?_
        stackOverflow := ?_
        stackOps := ?_
        stackArith := ?_
        stackCrypto := ?_
        chipletSelectors := ?_
        chipletBitwise := ?_
        chipletHasher := ?_
        chipletKernelRom := ?_
        chipletMemory := ?_
        chipletAce := ?_
        publicInputs := hpublicInputs
        bus := hbuses.1
        reducedAux := hbuses.2 }
    · intro i
      exact (hstack i).1
    · intro i
      exact (hstack i).2.1
    · intro i
      exact (hstack i).2.2.1
    · intro i
      exact (hstack i).2.2.2.1
    · intro i
      exact (hstack i).2.2.2.2
    · intro i
      exact (hchiplets i).1
    · intro i
      exact (hchiplets i).2.1
    · intro i
      exact (hchiplets i).2.2.1
    · intro i
      exact (hchiplets i).2.2.2.1
    · intro i
      exact (hchiplets i).2.2.2.2.1
    · intro i
      exact (hchiplets i).2.2.2.2.2
  · intro hvalid
    exact
      ⟨⟨hvalid.wellFormed, hvalid.system⟩,
        hvalid.decoder,
        (fun i =>
          ⟨hvalid.stackGeneral i,
            ⟨hvalid.stackOverflow i,
              ⟨hvalid.stackOps i,
                ⟨hvalid.stackArith i, hvalid.stackCrypto i⟩⟩⟩⟩),
        hvalid.range,
        (fun i =>
          ⟨hvalid.chipletSelectors i,
            ⟨hvalid.chipletBitwise i,
              ⟨hvalid.chipletHasher i,
                ⟨hvalid.chipletKernelRom i,
                  ⟨hvalid.chipletMemory i, hvalid.chipletAce i⟩⟩⟩⟩⟩),
        ⟨hvalid.bus, hvalid.reducedAux⟩,
        hvalid.publicInputs⟩

/-- Closed specialization of `vm_layer3_exact_of_assumptions` to the exact
whole-VM AIR boundary currently modeled in Lean. -/
theorem vm_layer3_exact_current_air_spec {n : Nat} {w : VmWitness n} :
    VmAirSatisfied w ↔ VmValidExecution (vmCurrentAirSpec n) w := by
  exact vm_layer3_exact_current_air_valid.trans
    (vm_validExecution_current_air_spec_iff (n := n) (w := w)).symm

end MidenLean.AIR.Soundness
