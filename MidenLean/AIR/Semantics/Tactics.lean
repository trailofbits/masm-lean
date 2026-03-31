import MidenLean.AIR.Semantics.Subsystems.StackArith
import MidenLean.AIR.Semantics.Check
import MidenLean.AIR.Constraints.Symbolic.StackArith

namespace MidenLean.AIR.Semantics.Tactics

open Lean Elab Tactic
open MidenLean
open MidenLean.AIR
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Builder

/-- Project one canonical AIR row into the raw symbolic-frame view used by the
symbolic Rust extractor. -/
def toSymbolicFrame (r : AirRow) : SymbolicFrame where
  curr i := if h : i < MainWidth then r.curr ⟨i, h⟩ else 0
  next i := if h : i < MainWidth then r.next ⟨i, h⟩ else 0
  auxCurr i := if h : i < AuxWidth then r.auxCurr ⟨i, h⟩ else 0
  auxNext i := if h : i < AuxWidth then r.auxNext ⟨i, h⟩ else 0
  challenge i := if h : i < ChallengeWidth then r.globals.challenge ⟨i, h⟩ else 0
  permValue i := if h : i < PermFinalWidth then r.globals.permFinal ⟨i, h⟩ else 0
  publicValue i := if h : i < PublicWidth then r.globals.publicValue ⟨i, h⟩ else 0
  periodic i := if h : i < PeriodicWidth then r.globals.periodic ⟨i, h⟩ else 0
  preprocessed i := if h : i < PreprocessedWidth then r.globals.preprocessed ⟨i, h⟩ else 0
  is_first_row := r.isFirst
  is_last_row := r.isLast
  is_transition := r.isTransition

@[simp] theorem toSymbolicFrame_isTransition (r : AirRow) :
    (toSymbolicFrame r).is_transition = r.isTransition := rfl

@[simp] theorem toSymbolicFrame_colCurr (r : AirRow) (i : Nat) :
    (toSymbolicFrame r).colCurr i = (if h : i < MainWidth then r.curr ⟨i, h⟩ else 0) := rfl

@[simp] theorem toSymbolicFrame_colNext (r : AirRow) (i : Nat) :
    (toSymbolicFrame r).colNext i = (if h : i < MainWidth then r.next ⟨i, h⟩ else 0) := rfl

@[simp] theorem curr_opBit0Col_eq (r : AirRow) :
    r.curr Subsystems.StackArith.opBit0Col = r.curr 7 := rfl

@[simp] theorem curr_opBit0Col_proof_eq (r : AirRow) :
    r.curr ⟨7, Subsystems.StackArith.opBit0Col._proof_1⟩ = r.curr 7 := rfl

@[simp] theorem curr_opBit1Col_eq (r : AirRow) :
    r.curr Subsystems.StackArith.opBit1Col = r.curr 8 := rfl

@[simp] theorem curr_opBit1Col_proof_eq (r : AirRow) :
    r.curr ⟨8, Subsystems.StackArith.opBit1Col._proof_1⟩ = r.curr 8 := rfl

@[simp] theorem curr_opBit2Col_eq (r : AirRow) :
    r.curr Subsystems.StackArith.opBit2Col = r.curr 9 := rfl

@[simp] theorem curr_opBit2Col_proof_eq (r : AirRow) :
    r.curr ⟨9, Subsystems.StackArith.opBit2Col._proof_1⟩ = r.curr 9 := rfl

@[simp] theorem curr_opBit3Col_eq (r : AirRow) :
    r.curr Subsystems.StackArith.opBit3Col = r.curr 10 := rfl

@[simp] theorem curr_opBit3Col_proof_eq (r : AirRow) :
    r.curr ⟨10, Subsystems.StackArith.opBit3Col._proof_1⟩ = r.curr 10 := rfl

@[simp] theorem curr_opBit4Col_eq (r : AirRow) :
    r.curr Subsystems.StackArith.opBit4Col = r.curr 11 := rfl

@[simp] theorem curr_opBit4Col_proof_eq (r : AirRow) :
    r.curr ⟨11, Subsystems.StackArith.opBit4Col._proof_1⟩ = r.curr 11 := rfl

@[simp] theorem curr_opBit5Col_eq (r : AirRow) :
    r.curr Subsystems.StackArith.opBit5Col = r.curr 12 := rfl

@[simp] theorem curr_opBit5Col_proof_eq (r : AirRow) :
    r.curr ⟨12, Subsystems.StackArith.opBit5Col._proof_1⟩ = r.curr 12 := rfl

@[simp] theorem curr_opBit6Col_eq (r : AirRow) :
    r.curr Subsystems.StackArith.opBit6Col = r.curr 13 := rfl

@[simp] theorem curr_opBit6Col_proof_eq (r : AirRow) :
    r.curr ⟨13, Subsystems.StackArith.opBit6Col._proof_1⟩ = r.curr 13 := rfl

@[simp] theorem curr_s0Col_eq (r : AirRow) :
    r.curr Subsystems.StackArith.s0Col = r.curr 30 := rfl

@[simp] theorem curr_s0Col_proof_eq (r : AirRow) :
    r.curr ⟨30, Subsystems.StackArith.s0Col._proof_1⟩ = r.curr 30 := rfl

@[simp] theorem next_s0Col_eq (r : AirRow) :
    r.next Subsystems.StackArith.s0Col = r.next 30 := rfl

@[simp] theorem next_s0Col_proof_eq (r : AirRow) :
    r.next ⟨30, Subsystems.StackArith.s0Col._proof_1⟩ = r.next 30 := rfl

@[simp] theorem curr_s1Col_eq (r : AirRow) :
    r.curr Subsystems.StackArith.s1Col = r.curr 31 := rfl

@[simp] theorem next_s1Col_eq (r : AirRow) :
    r.next Subsystems.StackArith.s1Col = r.next 31 := rfl

@[simp] theorem curr_s1Col_proof_eq (r : AirRow) :
    r.curr ⟨31, Subsystems.StackArith.s1Col._proof_1⟩ = r.curr 31 := rfl

@[simp] theorem next_s1Col_proof_eq (r : AirRow) :
    r.next ⟨31, Subsystems.StackArith.s1Col._proof_1⟩ = r.next 31 := rfl

@[simp] theorem curr_s2Col_eq (r : AirRow) :
    r.curr Subsystems.StackArith.s2Col = r.curr 32 := rfl

@[simp] theorem next_s2Col_eq (r : AirRow) :
    r.next Subsystems.StackArith.s2Col = r.next 32 := rfl

@[simp] theorem curr_s2Col_proof_eq (r : AirRow) :
    r.curr ⟨32, Subsystems.StackArith.s2Col._proof_1⟩ = r.curr 32 := rfl

@[simp] theorem next_s2Col_proof_eq (r : AirRow) :
    r.next ⟨32, Subsystems.StackArith.s2Col._proof_1⟩ = r.next 32 := rfl

@[simp] theorem curr_s3Col_eq (r : AirRow) :
    r.curr Subsystems.StackArith.s3Col = r.curr 33 := rfl

@[simp] theorem next_s3Col_eq (r : AirRow) :
    r.next Subsystems.StackArith.s3Col = r.next 33 := rfl

@[simp] theorem curr_s3Col_proof_eq (r : AirRow) :
    r.curr ⟨33, Subsystems.StackArith.s3Col._proof_1⟩ = r.curr 33 := rfl

@[simp] theorem next_s3Col_proof_eq (r : AirRow) :
    r.next ⟨33, Subsystems.StackArith.s3Col._proof_1⟩ = r.next 33 := rfl

@[simp] theorem curr_uopH0Col_eq (r : AirRow) :
    r.curr Subsystems.StackArith.uopH0Col = r.curr 16 := rfl

@[simp] theorem curr_uopH0Col_proof_eq (r : AirRow) :
    r.curr ⟨16, Subsystems.StackArith.uopH0Col._proof_1⟩ = r.curr 16 := rfl

@[simp] theorem curr_uopH1Col_eq (r : AirRow) :
    r.curr Subsystems.StackArith.uopH1Col = r.curr 17 := rfl

@[simp] theorem curr_uopH1Col_proof_eq (r : AirRow) :
    r.curr ⟨17, Subsystems.StackArith.uopH1Col._proof_1⟩ = r.curr 17 := rfl

@[simp] theorem curr_uopH2Col_eq (r : AirRow) :
    r.curr Subsystems.StackArith.uopH2Col = r.curr 18 := rfl

@[simp] theorem curr_uopH2Col_proof_eq (r : AirRow) :
    r.curr ⟨18, Subsystems.StackArith.uopH2Col._proof_1⟩ = r.curr 18 := rfl

@[simp] theorem curr_uopH3Col_eq (r : AirRow) :
    r.curr Subsystems.StackArith.uopH3Col = r.curr 19 := rfl

@[simp] theorem curr_uopH3Col_proof_eq (r : AirRow) :
    r.curr ⟨19, Subsystems.StackArith.uopH3Col._proof_1⟩ = r.curr 19 := rfl

@[simp] theorem curr_uopH4Col_eq (r : AirRow) :
    r.curr Subsystems.StackArith.uopH4Col = r.curr 20 := rfl

@[simp] theorem curr_uopH4Col_proof_eq (r : AirRow) :
    r.curr ⟨20, Subsystems.StackArith.uopH4Col._proof_1⟩ = r.curr 20 := rfl

/-- One-step projection normalization from `AirRow` to `SymbolicFrame`.
Use this only after choosing the specific extracted alias to unfold. -/
syntax (name := air_norm_projection) "air_norm_projection" : tactic

macro_rules
  | `(tactic| air_norm_projection) =>
      `(tactic|
        first
        | simp [
          toSymbolicFrame, toSymbolicFrame_isTransition, toSymbolicFrame_colCurr,
          toSymbolicFrame_colNext, SymbolicFrame.colCurr, SymbolicFrame.colNext,
          SymbolicFrame.s, SymbolicFrame.s', SymbolicFrame.h
        ]
        | skip)

-- Extracted alias unfolding is kept as explicit local `simp` in each
-- symbolic macro to keep rewrite evidence visible and parser-robust.

/-- One-step local algebra normalization for bridge goals that need
`sub_sub`-style reassociation only. -/
syntax (name := air_norm_sub_sub) "air_norm_sub_sub" : tactic

macro_rules
  | `(tactic| air_norm_sub_sub) =>
      `(tactic| simp [sub_sub, mul_assoc, mul_left_comm, mul_comm])

/-- Bridge finisher: no search, only AC normalization if it applies. -/
syntax (name := air_bridge_finish) "air_bridge_finish" : tactic

macro_rules
  | `(tactic| air_bridge_finish) =>
      `(tactic| first | ac_rfl | skip)

/-- Bridge finisher for gated symbolic equalities where simplification rewrites
to `mul_eq_zero` disjunctions. It closes either direct AC-equality goals or the
left-most AC branch of the disjunction. -/
syntax (name := air_bridge_finish_gated) "air_bridge_finish_gated" : tactic

macro_rules
  | `(tactic| air_bridge_finish_gated) =>
      `(tactic| first | ac_rfl | (left; left; ac_rfl))

/-- Bridge finisher for goals where simplification exposes selector-shape
equalities as the first branch of a disjunction. -/
syntax (name := air_bridge_pick_selector_eq) "air_bridge_pick_selector_eq" : tactic

macro_rules
  | `(tactic| air_bridge_pick_selector_eq) =>
      `(tactic| first | (left; left; ac_rfl) | (left; ac_rfl) | ac_rfl)

/-- Deterministic polynomial normalization for bridge goals whose remaining
work is pure ring algebra after explicit unfolding. -/
syntax (name := air_bridge_ring) "air_bridge_ring" : tactic

macro_rules
  | `(tactic| air_bridge_ring) =>
      `(tactic| ring_nf)

/-- Bridge helper: unfold one extracted symbolic side and one canonical side
for a symbolic-to-canonical equality goal. -/
syntax (name := air_bridge_unfold) "air_bridge_unfold " tacticSeq ", " tacticSeq : tactic

macro_rules
  | `(tactic| air_bridge_unfold $sym:tacticSeq, $can:tacticSeq) =>
      `(tactic|
        (conv_lhs => tactic => $sym); (conv_rhs => tactic => $can))

/-- Normalize generated `MainCol` proof terms for the named StackArith
columns used in bridge goals. Keep this list local and explicit. -/
syntax (name := air_simp_stackarith_named_cols) "air_simp_stackarith_named_cols" : tactic

macro_rules
  | `(tactic| air_simp_stackarith_named_cols) =>
      `(tactic|
        first
        | simp [
            curr_opBit0Col_eq,
            curr_opBit1Col_eq,
            curr_opBit2Col_eq,
            curr_opBit3Col_eq,
            curr_opBit4Col_eq,
            curr_opBit5Col_eq,
            curr_opBit6Col_eq,
            curr_uopH0Col_eq,
            curr_uopH1Col_eq,
            curr_uopH2Col_eq,
            curr_uopH3Col_eq,
            curr_uopH4Col_eq,
            curr_s0Col_eq,
            next_s0Col_eq,
            curr_s1Col_eq,
            next_s1Col_eq,
            curr_s2Col_eq,
            next_s2Col_eq,
            curr_s3Col_eq,
            next_s3Col_eq
          ]
        | skip)

/-- Extract the single constraint equation from `satisfiesBase r [constraint]`. -/
theorem singleton_constraint_eval_zero
    (r : AirRow)
    (constraint : BaseConstraint)
    (hsat : Check.satisfiesBase r [constraint]) :
    constraint.eval r = 0 := by
  exact hsat _ (by simp)

/-- Cancel the transition boundary factor from an explicit transition
hypothesis. -/
theorem cancel_transition_factor
    (r : AirRow)
    (body : Felt)
    (hprod : (FExpr.boundary .transition).eval r * body = 0)
    (htrans : r.isTransition = 1) :
    body = 0 := by
  simpa [FExpr.eval, AirRow.boundaryAt, AirRow.boundary, htrans] using hprod

/-- Cancel an active selector factor from an explicit selector hypothesis. -/
theorem cancel_active_selector_factor
    (selectorValue body : Felt)
    (hprod : selectorValue * body = 0)
    (hsel : selectorValue = 1) :
    body = 0 := by
  simpa [hsel] using hprod

@[simp] theorem felt_ofNat_two_eq : (Felt.ofNat 2 : Felt) = 2 := rfl

@[simp] theorem felt_ofNat_seven_eq : (Felt.ofNat 7 : Felt) = 7 := rfl

theorem felt_ofNat_65536_eq : (Felt.ofNat 65536 : Felt) = 65536 := rfl

theorem felt_ofNat_4294967295_eq : (Felt.ofNat 4294967295 : Felt) = 4294967295 := rfl

theorem felt_ofNat_4294967296_eq : (Felt.ofNat 4294967296 : Felt) = 4294967296 := rfl

theorem felt_ofNat_281474976710656_eq : (Felt.ofNat 281474976710656 : Felt) = 281474976710656 := rfl

/-- Normalize the extracted symbolic `StackArith.add` side of a refinement
goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_add) "air_simp_symbolic_add" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_add) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.add_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.neg` side of a refinement
goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_neg) "air_simp_symbolic_neg" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_neg) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.neg_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.mul` side of a refinement
goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_mul) "air_simp_symbolic_mul" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_mul) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.mul_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.inv` side of a refinement
goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_inv) "air_simp_symbolic_inv" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_inv) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.inv_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.incr` side of a refinement
goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_incr) "air_simp_symbolic_incr" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_incr) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.incr_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.notBinary` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_not_binary) "air_simp_symbolic_not_binary" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_not_binary) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.notBinary_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.notValue` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_not_value) "air_simp_symbolic_not_value" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_not_value) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.notValue_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.andS0Binary` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_and_s0_binary) "air_simp_symbolic_and_s0_binary" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_and_s0_binary) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.andS0Binary_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.andS1Binary` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_and_s1_binary) "air_simp_symbolic_and_s1_binary" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_and_s1_binary) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.andS1Binary_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.andValue` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_and_value) "air_simp_symbolic_and_value" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_and_value) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.andValue_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.orS0Binary` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_or_s0_binary) "air_simp_symbolic_or_s0_binary" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_or_s0_binary) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.orS0Binary_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.orS1Binary` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_or_s1_binary) "air_simp_symbolic_or_s1_binary" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_or_s1_binary) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.orS1Binary_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.orValue` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_or_value) "air_simp_symbolic_or_value" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_or_value) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.orValue_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.eqZeroProduct` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_eq_zero_product) "air_simp_symbolic_eq_zero_product" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_eq_zero_product) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.eqZeroProduct_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.eqValue` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_eq_value) "air_simp_symbolic_eq_value" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_eq_value) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.eqValue_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.eqzZeroProduct` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_eqz_zero_product) "air_simp_symbolic_eqz_zero_product" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_eqz_zero_product) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.eqzZeroProduct_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.eqzValue` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_eqz_value) "air_simp_symbolic_eqz_value" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_eqz_value) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.eqzValue_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.expaccExpSquare` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_expacc_exp_square) "air_simp_symbolic_expacc_exp_square" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_expacc_exp_square) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.expaccExpSquare_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.expaccExpVal` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_expacc_exp_val) "air_simp_symbolic_expacc_exp_val" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_expacc_exp_val) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.expaccExpVal_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.expaccAccUpdate` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_expacc_acc_update) "air_simp_symbolic_expacc_acc_update" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_expacc_acc_update) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.expaccAccUpdate_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.expaccExpShift` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_expacc_exp_shift) "air_simp_symbolic_expacc_exp_shift" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_expacc_exp_shift) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.expaccExpShift_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.expaccBitBinary` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_expacc_bit_binary) "air_simp_symbolic_expacc_bit_binary" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_expacc_bit_binary) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.expaccBitBinary_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.ext2mulD0` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_ext2mul_d0) "air_simp_symbolic_ext2mul_d0" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_ext2mul_d0) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.ext2mulD0_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.ext2mulD1` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_ext2mul_d1) "air_simp_symbolic_ext2mul_d1" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_ext2mul_d1) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.ext2mulD1_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.ext2mulC0` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_ext2mul_c0) "air_simp_symbolic_ext2mul_c0" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_ext2mul_c0) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.ext2mulC0_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.ext2mulC1` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_ext2mul_c1) "air_simp_symbolic_ext2mul_c1" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_ext2mul_c1) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.ext2mulC1_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.u32SplitMulMaddValidity` side
of a refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_u32_split_mul_madd_validity)
  "air_simp_symbolic_u32_split_mul_madd_validity" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_u32_split_mul_madd_validity) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.u32SplitMulMaddValidity_apply,
          felt_ofNat_65536_eq,
          felt_ofNat_4294967295_eq
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.u32TwoOutputsLo` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_u32_two_outputs_lo)
  "air_simp_symbolic_u32_two_outputs_lo" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_u32_two_outputs_lo) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.u32TwoOutputsLo_apply,
          felt_ofNat_65536_eq
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.u32TwoOutputsHi` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_u32_two_outputs_hi)
  "air_simp_symbolic_u32_two_outputs_hi" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_u32_two_outputs_hi) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.u32TwoOutputsHi_apply,
          felt_ofNat_65536_eq
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.u32SplitInput` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_u32_split_input)
  "air_simp_symbolic_u32_split_input" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_u32_split_input) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.u32SplitInput_apply,
          felt_ofNat_65536_eq,
          felt_ofNat_4294967296_eq,
          felt_ofNat_281474976710656_eq
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.u32AddInput` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_u32_add_input)
  "air_simp_symbolic_u32_add_input" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_u32_add_input) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.u32AddInput_apply,
          felt_ofNat_65536_eq,
          felt_ofNat_4294967296_eq
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.u32Add3Input` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_u32_add3_input)
  "air_simp_symbolic_u32_add3_input" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_u32_add3_input) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.u32Add3Input_apply,
          felt_ofNat_65536_eq,
          felt_ofNat_4294967296_eq
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.u32Assert2Hi` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_u32_assert2_hi)
  "air_simp_symbolic_u32_assert2_hi" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_u32_assert2_hi) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.u32Assert2Hi_apply,
          felt_ofNat_65536_eq
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.u32Assert2Lo` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_u32_assert2_lo)
  "air_simp_symbolic_u32_assert2_lo" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_u32_assert2_lo) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.u32Assert2Lo_apply,
          felt_ofNat_65536_eq
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.u32SubDiff` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_u32_sub_diff)
  "air_simp_symbolic_u32_sub_diff" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_u32_sub_diff) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.u32SubDiff_apply,
          felt_ofNat_4294967296_eq
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.u32SubBorrowBinary` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_u32_sub_borrow_binary)
  "air_simp_symbolic_u32_sub_borrow_binary" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_u32_sub_borrow_binary) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.u32SubBorrowBinary_apply
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.u32SubLow` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_u32_sub_low)
  "air_simp_symbolic_u32_sub_low" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_u32_sub_low) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.u32SubLow_apply,
          felt_ofNat_65536_eq
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.u32DivDividend` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_u32_div_dividend)
  "air_simp_symbolic_u32_div_dividend" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_u32_div_dividend) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.u32DivDividend_apply,
          felt_ofNat_4294967296_eq
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.u32DivLow` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_u32_div_low)
  "air_simp_symbolic_u32_div_low" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_u32_div_low) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.u32DivLow_apply,
          felt_ofNat_65536_eq
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.u32DivHigh` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_u32_div_high)
  "air_simp_symbolic_u32_div_high" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_u32_div_high) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.u32DivHigh_apply,
          felt_ofNat_65536_eq
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.u32Mul` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_u32_mul)
  "air_simp_symbolic_u32_mul" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_u32_mul) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.u32Mul_apply,
          felt_ofNat_4294967296_eq, felt_ofNat_281474976710656_eq,
          felt_ofNat_65536_eq
        ];
        air_norm_projection)

/-- Normalize the extracted symbolic `StackArith.u32Madd` side of a
refinement goal after projecting an `AirRow` through `toSymbolicFrame`. -/
syntax (name := air_simp_symbolic_u32_madd)
  "air_simp_symbolic_u32_madd" : tactic

macro_rules
  | `(tactic| air_simp_symbolic_u32_madd) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Constraints.Symbolic.StackArith.u32Madd_apply,
          felt_ofNat_4294967296_eq, felt_ofNat_281474976710656_eq,
          felt_ofNat_65536_eq
        ];
        air_norm_projection)
 
/-- Normalize the canonical `Subsystems.StackArith.add.eval` side of a
refinement goal. -/
syntax (name := air_simp_canonical_add) "air_simp_canonical_add" : tactic

macro_rules
  | `(tactic| air_simp_canonical_add) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.add,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isAdd,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.neg.eval` side of a
refinement goal. -/
syntax (name := air_simp_canonical_neg) "air_simp_canonical_neg" : tactic

macro_rules
  | `(tactic| air_simp_canonical_neg) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.neg,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isNeg,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.mul.eval` side of a
refinement goal. -/
syntax (name := air_simp_canonical_mul) "air_simp_canonical_mul" : tactic

macro_rules
  | `(tactic| air_simp_canonical_mul) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.mul,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isMul,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.inv.eval` side of a
refinement goal. -/
syntax (name := air_simp_canonical_inv) "air_simp_canonical_inv" : tactic

macro_rules
  | `(tactic| air_simp_canonical_inv) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.inv,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isInv,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.incr.eval` side of a
refinement goal. -/
syntax (name := air_simp_canonical_incr) "air_simp_canonical_incr" : tactic

macro_rules
  | `(tactic| air_simp_canonical_incr) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.incr,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isIncr,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.notBinary.eval` side of a
refinement goal. -/
syntax (name := air_simp_canonical_not_binary) "air_simp_canonical_not_binary" : tactic

macro_rules
  | `(tactic| air_simp_canonical_not_binary) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.notBinary,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isNot,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.notValue.eval` side of a
refinement goal. -/
syntax (name := air_simp_canonical_not_value) "air_simp_canonical_not_value" : tactic

macro_rules
  | `(tactic| air_simp_canonical_not_value) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.notValue,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isNot,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.andS0Binary.eval` side of a
refinement goal. -/
syntax (name := air_simp_canonical_and_s0_binary) "air_simp_canonical_and_s0_binary" : tactic

macro_rules
  | `(tactic| air_simp_canonical_and_s0_binary) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.andS0Binary,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isAnd,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.andS1Binary.eval` side of a
refinement goal. -/
syntax (name := air_simp_canonical_and_s1_binary) "air_simp_canonical_and_s1_binary" : tactic

macro_rules
  | `(tactic| air_simp_canonical_and_s1_binary) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.andS1Binary,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isAnd,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.andValue.eval` side of a
refinement goal. -/
syntax (name := air_simp_canonical_and_value) "air_simp_canonical_and_value" : tactic

macro_rules
  | `(tactic| air_simp_canonical_and_value) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.andValue,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isAnd,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.orS0Binary.eval` side of a
refinement goal. -/
syntax (name := air_simp_canonical_or_s0_binary) "air_simp_canonical_or_s0_binary" : tactic

macro_rules
  | `(tactic| air_simp_canonical_or_s0_binary) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.orS0Binary,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isOr,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.orS1Binary.eval` side of a
refinement goal. -/
syntax (name := air_simp_canonical_or_s1_binary) "air_simp_canonical_or_s1_binary" : tactic

macro_rules
  | `(tactic| air_simp_canonical_or_s1_binary) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.orS1Binary,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isOr,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.orValue.eval` side of a
refinement goal. -/
syntax (name := air_simp_canonical_or_value) "air_simp_canonical_or_value" : tactic

macro_rules
  | `(tactic| air_simp_canonical_or_value) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.orValue,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isOr,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.eqZeroProduct.eval` side of
a refinement goal. -/
syntax (name := air_simp_canonical_eq_zero_product) "air_simp_canonical_eq_zero_product" : tactic

macro_rules
  | `(tactic| air_simp_canonical_eq_zero_product) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.eqZeroProduct,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isEq,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.eqValue.eval` side of a
refinement goal. -/
syntax (name := air_simp_canonical_eq_value) "air_simp_canonical_eq_value" : tactic

macro_rules
  | `(tactic| air_simp_canonical_eq_value) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.eqValue,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isEq,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.eqzZeroProduct.eval` side
of a refinement goal. -/
syntax (name := air_simp_canonical_eqz_zero_product) "air_simp_canonical_eqz_zero_product" : tactic

macro_rules
  | `(tactic| air_simp_canonical_eqz_zero_product) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.eqzZeroProduct,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isEqz,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.eqzValue.eval` side of a
refinement goal. -/
syntax (name := air_simp_canonical_eqz_value) "air_simp_canonical_eqz_value" : tactic

macro_rules
  | `(tactic| air_simp_canonical_eqz_value) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.eqzValue,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isEqz,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.expaccExpSquare.eval` side
of a refinement goal. -/
syntax (name := air_simp_canonical_expacc_exp_square) "air_simp_canonical_expacc_exp_square" : tactic

macro_rules
  | `(tactic| air_simp_canonical_expacc_exp_square) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.expaccExpSquare,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isExpacc,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.expaccExpVal.eval` side of
a refinement goal. -/
syntax (name := air_simp_canonical_expacc_exp_val) "air_simp_canonical_expacc_exp_val" : tactic

macro_rules
  | `(tactic| air_simp_canonical_expacc_exp_val) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.expaccExpVal,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isExpacc,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.expaccAccUpdate.eval` side
of a refinement goal. -/
syntax (name := air_simp_canonical_expacc_acc_update) "air_simp_canonical_expacc_acc_update" : tactic

macro_rules
  | `(tactic| air_simp_canonical_expacc_acc_update) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.expaccAccUpdate,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isExpacc,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s2Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.expaccExpShift.eval` side
of a refinement goal. -/
syntax (name := air_simp_canonical_expacc_exp_shift) "air_simp_canonical_expacc_exp_shift" : tactic

macro_rules
  | `(tactic| air_simp_canonical_expacc_exp_shift) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.expaccExpShift,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isExpacc,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s3Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s3Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.expaccBitBinary.eval` side
of a refinement goal. -/
syntax (name := air_simp_canonical_expacc_bit_binary) "air_simp_canonical_expacc_bit_binary" : tactic

macro_rules
  | `(tactic| air_simp_canonical_expacc_bit_binary) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.expaccBitBinary,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isExpacc,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.ext2mulD0Unchanged.eval`
side of a refinement goal. -/
syntax (name := air_simp_canonical_ext2mul_d0) "air_simp_canonical_ext2mul_d0" : tactic

macro_rules
  | `(tactic| air_simp_canonical_ext2mul_d0) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.ext2mulD0Unchanged,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isExt2Mul,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.ext2mulD1Unchanged.eval`
side of a refinement goal. -/
syntax (name := air_simp_canonical_ext2mul_d1) "air_simp_canonical_ext2mul_d1" : tactic

macro_rules
  | `(tactic| air_simp_canonical_ext2mul_d1) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.ext2mulD1Unchanged,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isExt2Mul,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.ext2mulC0.eval` side
of a refinement goal. -/
syntax (name := air_simp_canonical_ext2mul_c0) "air_simp_canonical_ext2mul_c0" : tactic

macro_rules
  | `(tactic| air_simp_canonical_ext2mul_c0) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.ext2mulC0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isExt2Mul,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s2Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s3Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.ext2mulC1.eval` side
of a refinement goal. -/
syntax (name := air_simp_canonical_ext2mul_c1) "air_simp_canonical_ext2mul_c1" : tactic

macro_rules
  | `(tactic| air_simp_canonical_ext2mul_c1) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.ext2mulC1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isExt2Mul,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s3Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s3Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.u32SplitMulMaddValidity.eval`
side of a refinement goal. -/
syntax (name := air_simp_canonical_u32_split_mul_madd_validity)
  "air_simp_canonical_u32_split_mul_madd_validity" : tactic

macro_rules
  | `(tactic| air_simp_canonical_u32_split_mul_madd_validity) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32SplitMulMaddValidity,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32SplitMulMadd,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Split,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Mul,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Madd,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32VHiComp,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32VHi,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32VLo,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow16,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow32MinusOne,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH4Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.u32TwoOutputsLo.eval`
side of a refinement goal. -/
syntax (name := air_simp_canonical_u32_two_outputs_lo)
  "air_simp_canonical_u32_two_outputs_lo" : tactic

macro_rules
  | `(tactic| air_simp_canonical_u32_two_outputs_lo) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32TwoOutputsLo,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32TwoOutputs,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Split,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Add,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Add3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Mul,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Madd,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32VLo,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow16,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.u32TwoOutputsHi.eval`
side of a refinement goal. -/
syntax (name := air_simp_canonical_u32_two_outputs_hi)
  "air_simp_canonical_u32_two_outputs_hi" : tactic

macro_rules
  | `(tactic| air_simp_canonical_u32_two_outputs_hi) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32TwoOutputsHi,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32TwoOutputs,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Split,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Add,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Add3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Mul,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Madd,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32VHi,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow16,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.u32Mul.eval` side
of a refinement goal. -/
syntax (name := air_simp_canonical_u32_mul)
  "air_simp_canonical_u32_mul" : tactic

macro_rules
  | `(tactic| air_simp_canonical_u32_mul) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32Mul,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Mul,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32V64,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32V48,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32VLo,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow16,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow32,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow48,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH3Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.u32Madd.eval` side
of a refinement goal. -/
syntax (name := air_simp_canonical_u32_madd)
  "air_simp_canonical_u32_madd" : tactic

macro_rules
  | `(tactic| air_simp_canonical_u32_madd) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32Madd,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Madd,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32V64,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32V48,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32VLo,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow16,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow32,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow48,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH3Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.u32SplitInput.eval` side
of a refinement goal. -/
syntax (name := air_simp_canonical_u32_split_input)
  "air_simp_canonical_u32_split_input" : tactic

macro_rules
  | `(tactic| air_simp_canonical_u32_split_input) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32SplitInput,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Split,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32V64,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32V48,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32VLo,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow16,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow32,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow48,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.u32AddInput.eval` side
of a refinement goal. -/
syntax (name := air_simp_canonical_u32_add_input)
  "air_simp_canonical_u32_add_input" : tactic

macro_rules
  | `(tactic| air_simp_canonical_u32_add_input) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32AddInput,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Add,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32V48,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32VLo,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow16,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow32,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.u32Add3Input.eval` side
of a refinement goal. -/
syntax (name := air_simp_canonical_u32_add3_input)
  "air_simp_canonical_u32_add3_input" : tactic

macro_rules
  | `(tactic| air_simp_canonical_u32_add3_input) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32Add3Input,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Add3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32V48,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32VLo,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow16,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow32,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s2Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])


/-- Normalize the canonical `Subsystems.StackArith.u32SubDiff.eval` side of a
refinement goal. -/
syntax (name := air_simp_canonical_u32_sub_diff)
  "air_simp_canonical_u32_sub_diff" : tactic

macro_rules
  | `(tactic| air_simp_canonical_u32_sub_diff) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32SubDiff,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Sub,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow32,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.u32SubBorrowBinary.eval` side of a
refinement goal. -/
syntax (name := air_simp_canonical_u32_sub_borrow_binary)
  "air_simp_canonical_u32_sub_borrow_binary" : tactic

macro_rules
  | `(tactic| air_simp_canonical_u32_sub_borrow_binary) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32SubBorrowBinary,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Sub,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.u32SubLow.eval` side of a
refinement goal. -/
syntax (name := air_simp_canonical_u32_sub_low)
  "air_simp_canonical_u32_sub_low" : tactic

macro_rules
  | `(tactic| air_simp_canonical_u32_sub_low) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32SubLow,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Sub,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32VLo,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow16,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Next,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.u32DivDividend.eval` side of a
refinement goal. -/
syntax (name := air_simp_canonical_u32_div_dividend)
  "air_simp_canonical_u32_div_dividend" : tactic

macro_rules
  | `(tactic| air_simp_canonical_u32_div_dividend) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32DivDividend,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Div,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.u32DivLow.eval` side of a
refinement goal. -/
syntax (name := air_simp_canonical_u32_div_low)
  "air_simp_canonical_u32_div_low" : tactic

macro_rules
  | `(tactic| air_simp_canonical_u32_div_low) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32DivLow,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Div,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32VLo,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow16,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.u32DivHigh.eval` side of a
refinement goal. -/
syntax (name := air_simp_canonical_u32_div_high)
  "air_simp_canonical_u32_div_high" : tactic

macro_rules
  | `(tactic| air_simp_canonical_u32_div_high) =>
      `(tactic|
        simp [MainWidth,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32DivHigh,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Div,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32VHi,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow16,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])
/-- Normalize the canonical `Subsystems.StackArith.u32Assert2Hi.eval` side
of a refinement goal. -/
syntax (name := air_simp_canonical_u32_assert2_hi)
  "air_simp_canonical_u32_assert2_hi" : tactic

macro_rules
  | `(tactic| air_simp_canonical_u32_assert2_hi) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32Assert2Hi,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Assert2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32VHi,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow16,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s0Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

/-- Normalize the canonical `Subsystems.StackArith.u32Assert2Lo.eval` side
of a refinement goal. -/
syntax (name := air_simp_canonical_u32_assert2_lo)
  "air_simp_canonical_u32_assert2_lo" : tactic

macro_rules
  | `(tactic| air_simp_canonical_u32_assert2_lo) =>
      `(tactic|
        simp [
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32Assert2Lo,
          MidenLean.AIR.Semantics.Subsystems.StackArith.isU32Assert2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.u32VLo,
          MidenLean.AIR.Semantics.Subsystems.StackArith.twoPow16,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit2,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit4,
          MidenLean.AIR.Semantics.Subsystems.StackArith.notOpBit5,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH1,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Next,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit2Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit3Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit4Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit5Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.opBit6Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH0Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.uopH1Col,
          MidenLean.AIR.Semantics.Subsystems.StackArith.s1Col,
          whenTransition, gate, assertEq, assertZero, FExpr.eval,
          AirRow.boundaryAt, AirRow.boundary, AirRow.baseAt, AirRow.base
        ])

end MidenLean.AIR.Semantics.Tactics
