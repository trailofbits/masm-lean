# Concrete ↔ Symbolic Alignment Plan

Tracking naming and structural changes to make the concrete and symbolic implementations mirror each other.

## Completed

- **`execInst` → `execInstruction`** (symbolic): Rename the symbolic per-instruction dispatch to match the concrete `execInstruction`. Touches ~200 occurrences across `Exec.lean`, `SoundnessHelpers.lean`, `Soundness.lean`, `Reflect.lean`.
- **`SoundnessHelpers.lean` → `Helpers.lean`**: Rename the symbolic helpers file. Update import in `MidenLean.lean` and any internal references.
- **Argument order alignment**: Symbolic `execInstruction` changed from `(i : Instruction) (s : State)` to `(s : State) (i : Instruction)`, matching the concrete `execInstruction (s : MidenState) (i : Instruction)`.

## Planned

- **Move concrete execution into `MidenLean/Concrete/`**: Create a `Concrete` directory mirroring the `Symbolic/` layout. Move `State.lean`, `Semantics.lean`, and `Instruction.lean` (or their relevant parts) into it.
- **`MidenState` → `State`** (concrete): Once inside `MidenLean.Concrete` namespace, rename `MidenState` to `State` so it becomes `Concrete.State`, paralleling `Symbolic.State`.
- **`concreteExecBlock` → move to `Concrete` namespace**: Currently lives in `Symbolic/Exec.lean` as a bridge helper. Once the `Concrete` namespace exists, move it there (e.g., `Concrete.execBlock`), mirroring `Symbolic.execBlock`.
