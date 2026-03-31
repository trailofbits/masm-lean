import MidenLean.AIR.Soundness.VMSections
import MidenLean.Semantics

/-!
# Source-Level Bridge to Whole-VM Layer 3

This file states the strongest honest source-level theorem currently supported
by the repository.

The missing ingredient for an unconditional theorem is a concrete refinement
from big-step source semantics (`execWithEnv`) to a whole-trace `VmWitness`.
Until a trace-producing source semantics exists, that refinement remains an
explicit bridge assumption.
-/

namespace MidenLean.AIR.Soundness

open MidenLean

/-- Visible stack endpoint relation between a source state and one AIR row.

This is the only direct source-level endpoint relation we can state today
without a fuller trace-extraction model. The repository does not yet provide a
generic construction relating source memory, locals, advice, public I/O,
clock/context, decoder state, and chiplet/bus rows to `VmWitness`.
-/
structure StackColumnsMatch (st : MidenState) (row : TraceFrame) : Prop where
  stack :
    ∀ i : Fin 16, row.s i = st.stack.getD i.val 0

theorem StackColumnsMatch.stack_eq {st : MidenState} {row : TraceFrame}
    (h : StackColumnsMatch st row) (i : Fin 16) :
    row.s i = st.stack.getD i.val 0 :=
  h.stack i

/-- A source-level refinement witness connecting a big-step source execution to a
whole-VM Layer-3 witness. This is the precise interface needed until the
repository grows a concrete trace-producing source semantics. -/
structure SourceVmBridge {n : Nat} (spec : VmExecutionSpec n)
    (env : ProcEnv) (fuel : Nat)
    (init final : MidenState) (ops : List Op) where
  witness : VmWitness n
  inputStack : StackColumnsMatch init witness.firstRow
  outputStack : StackColumnsMatch final witness.lastRow
  source_to_vm :
    execWithEnv env fuel init ops = some final ->
      VmValidExecution spec witness
  vm_to_source :
    VmValidExecution spec witness ->
      execWithEnv env fuel init ops = some final

theorem SourceVmBridge.firstRow_stack
    {n : Nat} {spec : VmExecutionSpec n}
    {env : ProcEnv} {fuel : Nat}
    {init final : MidenState} {ops : List Op}
    (bridge : SourceVmBridge spec env fuel init final ops) (i : Fin 16) :
    bridge.witness.firstRow.s i = init.stack.getD i.val 0 :=
  bridge.inputStack.stack_eq i

theorem SourceVmBridge.lastRow_stack
    {n : Nat} {spec : VmExecutionSpec n}
    {env : ProcEnv} {fuel : Nat}
    {init final : MidenState} {ops : List Op}
    (bridge : SourceVmBridge spec env fuel init final ops) (i : Fin 16) :
    bridge.witness.lastRow.s i = final.stack.getD i.val 0 :=
  bridge.outputStack.stack_eq i

/-- Source execution is equivalent to semantic whole-VM validity once a source
refinement witness is supplied. -/
theorem source_exec_iff_vm_valid_of_bridge
    {n : Nat} {spec : VmExecutionSpec n}
    {env : ProcEnv} {fuel : Nat}
    {init final : MidenState} {ops : List Op}
    (bridge : SourceVmBridge spec env fuel init final ops) :
    execWithEnv env fuel init ops = some final ↔
      VmValidExecution spec bridge.witness := by
  constructor
  · exact bridge.source_to_vm
  · exact bridge.vm_to_source

/-- One-way source-to-AIR theorem under an explicit source refinement and
whole-VM Layer-3 exactness assumptions. -/
theorem source_exec_implies_vm_air_of_bridge
    {n : Nat} {spec : VmExecutionSpec n}
    {env : ProcEnv} {fuel : Nat}
    {init final : MidenState} {ops : List Op}
    (hcomplete : VmLayer3CompletenessAssumptions spec)
    (bridge : SourceVmBridge spec env fuel init final ops) :
    execWithEnv env fuel init ops = some final →
      VmAirSatisfied bridge.witness := by
  intro hexec
  exact vm_layer3_complete_of_assumptions hcomplete (bridge.source_to_vm hexec)

/-- One-way AIR-to-source theorem under an explicit source refinement and
whole-VM Layer-3 exactness assumptions. -/
theorem vm_air_implies_source_exec_of_bridge
    {n : Nat} {spec : VmExecutionSpec n}
    {env : ProcEnv} {fuel : Nat}
    {init final : MidenState} {ops : List Op}
    (hsound : VmLayer3SoundnessAssumptions spec)
    (bridge : SourceVmBridge spec env fuel init final ops) :
    VmAirSatisfied bridge.witness →
      execWithEnv env fuel init ops = some final := by
  intro hair
  exact bridge.vm_to_source (vm_layer3_sound_of_assumptions hsound hair)

/-- Strongest honest source-level theorem currently available:
source execution is equivalent to whole-VM AIR satisfaction once an explicit
refinement bridge from `execWithEnv` to `VmWitness` is provided. -/
theorem source_exec_iff_vm_air_of_bridge
    {n : Nat} {spec : VmExecutionSpec n}
    {env : ProcEnv} {fuel : Nat}
    {init final : MidenState} {ops : List Op}
    (hsound : VmLayer3SoundnessAssumptions spec)
    (hcomplete : VmLayer3CompletenessAssumptions spec)
    (bridge : SourceVmBridge spec env fuel init final ops) :
    execWithEnv env fuel init ops = some final ↔
      VmAirSatisfied bridge.witness := by
  constructor
  · exact source_exec_implies_vm_air_of_bridge hcomplete bridge
  · exact vm_air_implies_source_exec_of_bridge hsound bridge

/-- Source execution is equivalent to having the bridged whole-VM AIR witness
plus the currently expressible source-level stack endpoint relations. -/
theorem source_exec_iff_vm_air_with_stack_endpoints_of_bridge
    {n : Nat} {spec : VmExecutionSpec n}
    {env : ProcEnv} {fuel : Nat}
    {init final : MidenState} {ops : List Op}
    (hsound : VmLayer3SoundnessAssumptions spec)
    (hcomplete : VmLayer3CompletenessAssumptions spec)
    (bridge : SourceVmBridge spec env fuel init final ops) :
    execWithEnv env fuel init ops = some final ↔
      VmAirSatisfied bridge.witness ∧
        StackColumnsMatch init bridge.witness.firstRow ∧
        StackColumnsMatch final bridge.witness.lastRow := by
  constructor
  · intro hexec
    exact
      ⟨source_exec_implies_vm_air_of_bridge hcomplete bridge hexec,
        bridge.inputStack, bridge.outputStack⟩
  · intro h
    exact vm_air_implies_source_exec_of_bridge hsound bridge h.1

/-- Specialization of the source bridge to the closed whole-VM section validity
predicate. -/
theorem source_exec_iff_vm_sections_of_bridge
    {n : Nat}
    {env : ProcEnv} {fuel : Nat}
    {init final : MidenState} {ops : List Op}
    (bridge : SourceVmBridge (vmSectionSpec n) env fuel init final ops) :
    execWithEnv env fuel init ops = some final ↔
      VmSectionValidExecution bridge.witness := by
  simpa [VmSectionValidExecution] using source_exec_iff_vm_valid_of_bridge bridge

/-- Closed source-to-AIR equivalence under the current trusted Lean AIR
boundary, assuming an explicit refinement bridge from source big-step execution
to a whole-VM witness. -/
theorem source_exec_iff_vm_air_by_sections_of_bridge
    {n : Nat}
    {env : ProcEnv} {fuel : Nat}
    {init final : MidenState} {ops : List Op}
    (bridge : SourceVmBridge (vmSectionSpec n) env fuel init final ops) :
    execWithEnv env fuel init ops = some final ↔
      VmAirSatisfied bridge.witness := by
  exact source_exec_iff_vm_air_of_bridge
    (hsound := vmSectionSoundnessAssumptions n)
    (hcomplete := vmSectionCompletenessAssumptions n)
    bridge

/-- Closed source-to-AIR equivalence under the current trusted Lean AIR
boundary, together with the source-level stack endpoints that the repository
can express today. -/
theorem source_exec_iff_vm_air_with_stack_endpoints_by_sections_of_bridge
    {n : Nat}
    {env : ProcEnv} {fuel : Nat}
    {init final : MidenState} {ops : List Op}
    (bridge : SourceVmBridge (vmSectionSpec n) env fuel init final ops) :
    execWithEnv env fuel init ops = some final ↔
      VmAirSatisfied bridge.witness ∧
        StackColumnsMatch init bridge.witness.firstRow ∧
        StackColumnsMatch final bridge.witness.lastRow := by
  exact source_exec_iff_vm_air_with_stack_endpoints_of_bridge
    (hsound := vmSectionSoundnessAssumptions n)
    (hcomplete := vmSectionCompletenessAssumptions n)
    bridge

end MidenLean.AIR.Soundness
