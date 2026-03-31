import MidenLean.AIR.Semantics.Core
/-!
# Canonical AIR Semantics Expressions

This file defines the expression layer for canonical AIR semantics:

- `FExpr`: base-field expressions.
- `QExpr`: extension-field expressions.
- executable evaluators for both expression types.

The file still intentionally stops before constraint builders, satisfaction
relations, or polynomial denotation.
-/

namespace MidenLean.AIR.Semantics

open MidenLean

/-- Base-field expression syntax for canonical AIR semantics. -/
inductive FExpr
  | const : Felt → FExpr
  | main : RowPhase → MainCol → FExpr
  | publicValue : PublicCol → FExpr
  | periodic : PeriodicCol → FExpr
  | boundary : BoundaryFlag → FExpr
  | preprocessed : PreprocessedCol → FExpr
  | add : FExpr → FExpr → FExpr
  | sub : FExpr → FExpr → FExpr
  | mul : FExpr → FExpr → FExpr
  deriving Repr, DecidableEq

namespace FExpr

/-- Current-row main-trace reference. -/
abbrev curr (i : MainCol) : FExpr := .main .curr i

/-- Next-row main-trace reference. -/
abbrev next (i : MainCol) : FExpr := .main .next i

/-- Shorthand constructor for addition in `FExpr`. -/
abbrev plus (a b : FExpr) : FExpr := .add a b

/-- Shorthand constructor for subtraction in `FExpr`. -/
abbrev minus (a b : FExpr) : FExpr := .sub a b

/-- Shorthand constructor for multiplication in `FExpr`. -/
abbrev times (a b : FExpr) : FExpr := .mul a b

/-- Evaluate a canonical base-field expression on one AIR row pair. -/
def eval : FExpr → AirRow → Felt
  | .const c, _ => c
  | .main phase i, r => r.baseAt phase i
  | .publicValue i, r => r.publicValueAt i
  | .periodic i, r => r.periodicAt i
  | .boundary flag, r => r.boundaryAt flag
  | .preprocessed i, r => r.preprocessedAt i
  | .add a b, r => a.eval r + b.eval r
  | .sub a b, r => a.eval r - b.eval r
  | .mul a b, r => a.eval r * b.eval r

@[simp]
theorem eval_add (a b : FExpr) (r : AirRow) :
    (FExpr.add a b).eval r = a.eval r + b.eval r := rfl

@[simp]
theorem eval_sub (a b : FExpr) (r : AirRow) :
    (FExpr.sub a b).eval r = a.eval r - b.eval r := rfl

@[simp]
theorem eval_mul (a b : FExpr) (r : AirRow) :
    (FExpr.mul a b).eval r = a.eval r * b.eval r := rfl

end FExpr

/-- Extension-field expression syntax for canonical AIR semantics. -/
inductive QExpr
  | const : QuadFelt → QExpr
  | aux : RowPhase → AuxCol → QExpr
  | challenge : ChallengeCol → QExpr
  | permFinal : PermFinalCol → QExpr
  | ofBase : FExpr → QExpr
  | add : QExpr → QExpr → QExpr
  | sub : QExpr → QExpr → QExpr
  | mul : QExpr → QExpr → QExpr
  deriving Repr, DecidableEq

namespace QExpr

/-- Current-row auxiliary-trace reference. -/
abbrev auxCurr (i : AuxCol) : QExpr := .aux .curr i

/-- Next-row auxiliary-trace reference. -/
abbrev auxNext (i : AuxCol) : QExpr := .aux .next i

/-- Embed a base-field expression into an extension-field expression. -/
abbrev liftBase (e : FExpr) : QExpr := .ofBase e

/-- Shorthand constructor for addition in `QExpr`. -/
abbrev plus (a b : QExpr) : QExpr := .add a b

/-- Shorthand constructor for subtraction in `QExpr`. -/
abbrev minus (a b : QExpr) : QExpr := .sub a b

/-- Shorthand constructor for multiplication in `QExpr`. -/
abbrev times (a b : QExpr) : QExpr := .mul a b

/-- Evaluate a canonical extension-field expression on one AIR row pair. -/
def eval : QExpr → AirRow → QuadFelt
  | .const c, _ => c
  | .aux phase i, r => r.auxAt phase i
  | .challenge i, r => r.challengeAt i
  | .permFinal i, r => r.permFinalAt i
  | .ofBase e, r => QuadFelt.ofFelt (e.eval r)
  | .add a b, r => a.eval r + b.eval r
  | .sub a b, r => a.eval r - b.eval r
  | .mul a b, r => a.eval r * b.eval r

@[simp]
theorem eval_add (a b : QExpr) (r : AirRow) :
    (QExpr.add a b).eval r = a.eval r + b.eval r := rfl

@[simp]
theorem eval_sub (a b : QExpr) (r : AirRow) :
    (QExpr.sub a b).eval r = a.eval r - b.eval r := rfl

@[simp]
theorem eval_mul (a b : QExpr) (r : AirRow) :
    (QExpr.mul a b).eval r = a.eval r * b.eval r := rfl

end QExpr

end MidenLean.AIR.Semantics
