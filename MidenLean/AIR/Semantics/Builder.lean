import MidenLean.AIR.Semantics.Expr
/-!
# Canonical AIR Constraint Builder DSL

Step 4 of the canonical semantics roadmap introduces a tiny
builder layer on top of the `FExpr` / `QExpr` language. The DSL
exposes the core combinators listed in the design note so that
subsystem modules can be written without anonymous lambdas.

No constraint satisfaction, subsystem logic, or polynomial
details are added here—those come in later steps.
-/

namespace MidenLean.AIR.Semantics.Builder

open MidenLean.AIR.Semantics

/-- A base-field AIR constraint is an expression intended to vanish. -/
inductive BaseConstraint
  | zeroAssert : FExpr → BaseConstraint
  deriving Repr, DecidableEq

abbrev BaseConstraintSet := List BaseConstraint

/-- An extension-field AIR constraint is an expression intended to vanish. -/
inductive ExtConstraint
  | zeroAssert : QExpr → ExtConstraint
  deriving Repr, DecidableEq

abbrev ExtConstraintSet := List ExtConstraint

namespace BaseConstraint

/-- Underlying expression of a base-field zero-constraint. -/
def expr : BaseConstraint → FExpr
  | .zeroAssert e => e

/-- Evaluate a base-field constraint on one AIR row pair. -/
def eval (c : BaseConstraint) (r : AirRow) : Felt := c.expr.eval r

@[simp]
theorem expr_zeroAssert (e : FExpr) : (BaseConstraint.zeroAssert e).expr = e := rfl

@[simp]
theorem eval_zeroAssert (e : FExpr) (r : AirRow) :
    (BaseConstraint.zeroAssert e).eval r = e.eval r := rfl

end BaseConstraint

namespace ExtConstraint

/-- Underlying expression of an extension-field zero-constraint. -/
def expr : ExtConstraint → QExpr
  | .zeroAssert e => e

/-- Evaluate an extension-field constraint on one AIR row pair. -/
def eval (c : ExtConstraint) (r : AirRow) : QuadFelt := c.expr.eval r

@[simp]
theorem expr_zeroAssert (e : QExpr) : (ExtConstraint.zeroAssert e).expr = e := rfl

@[simp]
theorem eval_zeroAssert (e : QExpr) (r : AirRow) :
    (ExtConstraint.zeroAssert e).eval r = e.eval r := rfl

end ExtConstraint

/- Base-field DSL ----------------------------------------------------------- -/

def assertZero (expr : FExpr) : BaseConstraint := .zeroAssert expr

def assertEq (lhs rhs : FExpr) : BaseConstraint := assertZero (FExpr.sub lhs rhs)

def gate (selector : FExpr) (body : BaseConstraint) : BaseConstraint :=
  assertZero (FExpr.mul selector body.expr)

def whenTransition (body : BaseConstraint) : BaseConstraint :=
  gate (FExpr.boundary .transition) body

def append (cs ds : BaseConstraintSet) : BaseConstraintSet := cs ++ ds

def allOf (cs : BaseConstraintSet) : BaseConstraintSet := cs

/- Extension-field DSL ------------------------------------------------------ -/

def assertZeroExt (expr : QExpr) : ExtConstraint := .zeroAssert expr

def assertEqExt (lhs rhs : QExpr) : ExtConstraint := assertZeroExt (QExpr.sub lhs rhs)

def gateExt (selector : FExpr) (body : ExtConstraint) : ExtConstraint :=
  assertZeroExt (QExpr.mul (QExpr.liftBase selector) body.expr)

def whenTransitionExt (body : ExtConstraint) : ExtConstraint :=
  gateExt (FExpr.boundary .transition) body

def appendExt (cs ds : ExtConstraintSet) : ExtConstraintSet := cs ++ ds

def allOfExt (cs : ExtConstraintSet) : ExtConstraintSet := cs

end MidenLean.AIR.Semantics.Builder
