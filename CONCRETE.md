# Concrete ↔ Symbolic Alignment Plan

Tracking naming and structural changes to make the concrete and symbolic implementations mirror each other.

## Completed

- **`execInst` → `execInstruction`** (symbolic): Rename the symbolic per-instruction dispatch to match the concrete `execInstruction`. Touches ~200 occurrences across `Exec.lean`, `SoundnessHelpers.lean`, `Soundness.lean`, `Reflect.lean`.
- **`SoundnessHelpers.lean` → `Helpers.lean`**: Rename the symbolic helpers file. Update import in `MidenLean.lean` and any internal references.
- **Argument order alignment**: Symbolic `execInstruction` changed from `(i : Instruction) (s : State)` to `(s : State) (i : Instruction)`, matching the concrete `execInstruction (s : MidenState) (i : Instruction)`.
- **Move concrete execution into `MidenLean/Concrete/`**: Created `Concrete/State.lean` (from `State.lean`) and `Concrete/Exec.lean` (from `Semantics.lean`). Old files deleted.
- **`MidenState` → `Concrete.State`**: Renamed across the entire codebase (~1090 occurrences in ~211 files). The struct is now `MidenLean.Concrete.State` inside `namespace MidenLean.Concrete`.
- **`concreteExecBlock` → `Concrete.execBlock`**: Moved from `Symbolic/Exec.lean` to `Concrete/Exec.lean`, mirroring `Symbolic.execBlock`.
- **`execWithEnv` → `execProcedure`**: Renamed the main concrete executor across the entire codebase (~831 occurrences in ~138 files). Related theorems (`execWithEnv_ofOps`, etc.) renamed to `execProcedure_ofOps`, etc.
- **`execOpsWithEnv` → `execOps`**: Renamed the block-level executor.
- **`exec` inlined as `execProcedure emptyEnv`**: The standalone `exec` function deleted. All call sites now use `execProcedure emptyEnv` directly. `emptyEnv : ProcEnv := fun _ => none` defined in `Concrete/Exec.lean`.
- **`execWithProcs` deleted**: Unused function removed entirely.
