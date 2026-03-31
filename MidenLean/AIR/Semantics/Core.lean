import MidenLean.AIR.ExtField
/-!
# Canonical AIR Semantics Core

This file defines the foundational row model for the canonical AIR semantics
redesign. It intentionally stops at typed state and accessors:

- no constraint syntax,
- no expression AST,
- no satisfaction predicates,
- no subsystem semantics.

The widths match the current trusted Lean AIR boundary used by the symbolic AIR
extractor and by `VmWitness.rowView`.
-/

namespace MidenLean.AIR.Semantics

open MidenLean

/-- Width of the raw main Miden execution trace used by the AIR.
    This matches Rust `TRACE_WIDTH`; alignment padding columns are tracked
    separately in Rust via `PADDED_TRACE_WIDTH` and are intentionally not part
    of the canonical AIR row model here. -/
abbrev MainWidth : Nat := 71

/-- Width of the auxiliary trace used by permutation / LogUp arguments. -/
abbrev AuxWidth : Nat := 8

/-- Number of fixed public values exposed to the symbolic AIR boundary.
    Layout: program hash (4) + stack inputs (16) + stack outputs (16) +
    precompile transcript state (4). -/
abbrev PublicWidth : Nat := 40

/-- Number of periodic columns supplied to the symbolic AIR boundary.
    This is the current Rust total: Poseidon2 hasher periodic columns plus the
    two bitwise periodic selectors. -/
abbrev PeriodicWidth : Nat := 20

/-- Number of shared verifier challenges used by the bus constraints. -/
abbrev ChallengeWidth : Nat := 2

/-- Number of final permutation values committed by the prover. -/
abbrev PermFinalWidth : Nat := 8

/-- Width of the preprocessed trace.
    Miden currently does not use preprocessed columns, but we keep the slot
    explicit so the canonical AIR model can match the symbolic boundary. -/
abbrev PreprocessedWidth : Nat := 0

/-- Typed indices for the main trace. -/
abbrev MainCol := Fin MainWidth

/-- Typed indices for the aux trace. -/
abbrev AuxCol := Fin AuxWidth

/-- Typed indices for public values. -/
abbrev PublicCol := Fin PublicWidth

/-- Typed indices for periodic columns. -/
abbrev PeriodicCol := Fin PeriodicWidth

/-- Typed indices for shared verifier challenges. -/
abbrev ChallengeCol := Fin ChallengeWidth

/-- Typed indices for final permutation values. -/
abbrev PermFinalCol := Fin PermFinalWidth

/-- Typed indices for the preprocessed trace. -/
abbrev PreprocessedCol := Fin PreprocessedWidth

/-- Selector for whether an AIR expression looks at the current or next row. -/
inductive RowPhase
  | curr
  | next
  deriving Repr, DecidableEq

/-- Selector for the synthetic boundary flags supplied to the AIR. -/
inductive BoundaryFlag
  | first
  | last
  | transition
  deriving Repr, DecidableEq

/-- Shared AIR inputs that are constant across a whole witness. -/
structure AirGlobals where
  /-- Fixed public values seen by the AIR. -/
  publicValue : PublicCol → Felt := fun _ => 0
  /-- Current-row periodic column values. -/
  periodic : PeriodicCol → Felt := fun _ => 0
  /-- Shared verifier challenges used by lookup / bus constraints. -/
  challenge : ChallengeCol → QuadFelt := fun _ => 0
  /-- Final permutation values checked at the verifier boundary. -/
  permFinal : PermFinalCol → QuadFelt := fun _ => 0
  /-- Preprocessed columns. Currently empty, but kept explicit for fidelity. -/
  preprocessed : PreprocessedCol → Felt := fun i => Fin.elim0 i

namespace AirGlobals

/-- Read one public AIR value. -/
abbrev publicValueAt (g : AirGlobals) (i : PublicCol) : Felt := g.publicValue i

/-- Read one periodic AIR value. -/
abbrev periodicAt (g : AirGlobals) (i : PeriodicCol) : Felt := g.periodic i

/-- Read one shared challenge value. -/
abbrev challengeAt (g : AirGlobals) (i : ChallengeCol) : QuadFelt := g.challenge i

/-- Read one final permutation value. -/
abbrev permFinalAt (g : AirGlobals) (i : PermFinalCol) : QuadFelt := g.permFinal i

/-- Read one preprocessed-column value. -/
abbrev preprocessedAt (g : AirGlobals) (i : PreprocessedCol) : Felt := g.preprocessed i

end AirGlobals

/-- One canonical AIR row pair together with its shared globals. -/
structure AirRow where
  /-- Main-trace values in the current row. -/
  curr : MainCol → Felt := fun _ => 0
  /-- Main-trace values in the next row. -/
  next : MainCol → Felt := fun _ => 0
  /-- Aux-trace values in the current row. -/
  auxCurr : AuxCol → QuadFelt := fun _ => 0
  /-- Aux-trace values in the next row. -/
  auxNext : AuxCol → QuadFelt := fun _ => 0
  /-- Shared values supplied uniformly across the witness. -/
  globals : AirGlobals := {}
  /-- Boundary selector for the first row. -/
  isFirst : Felt := 0
  /-- Boundary selector for the last row. -/
  isLast : Felt := 0
  /-- Boundary selector for transition rows. -/
  isTransition : Felt := 0

namespace AirRow

/-- Read a main-trace value from either the current or next row. -/
def base (r : AirRow) (phase : RowPhase) : MainCol → Felt :=
  match phase with
  | .curr => r.curr
  | .next => r.next

/-- Read an aux-trace value from either the current or next row. -/
def aux (r : AirRow) (phase : RowPhase) : AuxCol → QuadFelt :=
  match phase with
  | .curr => r.auxCurr
  | .next => r.auxNext

/-- Read one main-trace value from the selected row. -/
abbrev baseAt (r : AirRow) (phase : RowPhase) (i : MainCol) : Felt := r.base phase i

/-- Read one aux-trace value from the selected row. -/
abbrev auxAt (r : AirRow) (phase : RowPhase) (i : AuxCol) : QuadFelt := r.aux phase i

/-- Read the shared public inputs. -/
abbrev publicValue (r : AirRow) : PublicCol → Felt := r.globals.publicValue

/-- Read the shared periodic column values. -/
abbrev periodic (r : AirRow) : PeriodicCol → Felt := r.globals.periodic

/-- Read the shared verifier challenges. -/
abbrev challenge (r : AirRow) : ChallengeCol → QuadFelt := r.globals.challenge

/-- Read the shared final permutation values. -/
abbrev permFinal (r : AirRow) : PermFinalCol → QuadFelt := r.globals.permFinal

/-- Read the shared preprocessed-column values. -/
abbrev preprocessed (r : AirRow) : PreprocessedCol → Felt := r.globals.preprocessed

/-- Read one public AIR value. -/
abbrev publicValueAt (r : AirRow) (i : PublicCol) : Felt := r.publicValue i

/-- Read one periodic AIR value. -/
abbrev periodicAt (r : AirRow) (i : PeriodicCol) : Felt := r.periodic i

/-- Read one verifier challenge. -/
abbrev challengeAt (r : AirRow) (i : ChallengeCol) : QuadFelt := r.challenge i

/-- Read one final permutation value. -/
abbrev permFinalAt (r : AirRow) (i : PermFinalCol) : QuadFelt := r.permFinal i

/-- Read one preprocessed-column value. -/
abbrev preprocessedAt (r : AirRow) (i : PreprocessedCol) : Felt := r.preprocessed i

/-- Read one synthetic boundary selector. -/
def boundary (r : AirRow) : BoundaryFlag → Felt
  | .first => r.isFirst
  | .last => r.isLast
  | .transition => r.isTransition

/-- Read one boundary selector by name. -/
abbrev boundaryAt (r : AirRow) (flag : BoundaryFlag) : Felt := r.boundary flag

end AirRow

end MidenLean.AIR.Semantics
