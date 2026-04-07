import MidenLean.AIR.Semantics.Expr
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Canonical AIR Semantics Polynomial Denotation

This file gives a multivariate-polynomial denotation for canonical base-field
AIR expressions. The variable type intentionally covers all AIR row/global
slots so the same index type can be reused later for extension-field
denotations as well.
-/

noncomputable section

namespace MidenLean.AIR.Semantics

open MidenLean

/-- Variables for the polynomial denotation of AIR expressions. -/
inductive AirVar
  | mainCurr (i : MainCol)
  | mainNext (i : MainCol)
  | auxCurr (i : AuxCol)
  | auxNext (i : AuxCol)
  | publicValue (i : PublicCol)
  | periodic (i : PeriodicCol)
  | boundary (f : BoundaryFlag)
  | preprocessed (i : PreprocessedCol)
  | challenge (i : ChallengeCol)
  | permFinal (i : PermFinalCol)
  deriving Repr, DecidableEq

namespace FExpr

/-- Polynomial denotation of a base-field AIR expression. -/
def toPoly : FExpr → MvPolynomial AirVar Felt
  | .const c => MvPolynomial.C c
  | .main .curr i => MvPolynomial.X (.mainCurr i)
  | .main .next i => MvPolynomial.X (.mainNext i)
  | .publicValue i => MvPolynomial.X (.publicValue i)
  | .periodic i => MvPolynomial.X (.periodic i)
  | .boundary f => MvPolynomial.X (.boundary f)
  | .preprocessed i => MvPolynomial.X (.preprocessed i)
  | .add a b => a.toPoly + b.toPoly
  | .sub a b => a.toPoly - b.toPoly
  | .mul a b => a.toPoly * b.toPoly

end FExpr

/-- Base-field evaluation of AIR polynomial variables on one row pair.

Extension-valued slots are assigned `0` here because `FExpr` cannot mention
them. The eventual `QExpr` denotation should instead use an `ExtFelt`-valued
evaluation map on the same `AirVar` type. -/
def airVarEval (r : AirRow) : AirVar → Felt
  | .mainCurr i => r.baseAt .curr i
  | .mainNext i => r.baseAt .next i
  | .auxCurr _ => 0
  | .auxNext _ => 0
  | .publicValue i => r.publicValueAt i
  | .periodic i => r.periodicAt i
  | .boundary f => r.boundaryAt f
  | .preprocessed i => r.preprocessedAt i
  | .challenge _ => 0
  | .permFinal _ => 0

namespace FExpr

/-- Evaluating the polynomial denotation of `e` agrees with the executable
semantics of `e`. -/
theorem eval_toPoly (e : FExpr) (r : AirRow) :
    MvPolynomial.eval (airVarEval r) e.toPoly = e.eval r := by
  induction e with
  | const c =>
      simp [FExpr.toPoly, FExpr.eval]
  | main phase i =>
      cases phase <;> simp [FExpr.toPoly, FExpr.eval, airVarEval]
  | publicValue i =>
      simp [FExpr.toPoly, FExpr.eval, airVarEval]
  | periodic i =>
      simp [FExpr.toPoly, FExpr.eval, airVarEval]
  | boundary flag =>
      simp [FExpr.toPoly, FExpr.eval, airVarEval]
  | preprocessed i =>
      simp [FExpr.toPoly, FExpr.eval, airVarEval]
  | add a b ihA ihB =>
      simp [FExpr.toPoly, FExpr.eval, ihA, ihB]
  | sub a b ihA ihB =>
      simp [FExpr.toPoly, FExpr.eval, ihA, ihB]
  | mul a b ihA ihB =>
      simp [FExpr.toPoly, FExpr.eval, ihA, ihB]

theorem eval_eq_eval_toPoly (e : FExpr) (r : AirRow) :
    e.eval r = MvPolynomial.eval (airVarEval r) e.toPoly :=
  (eval_toPoly e r).symm

end FExpr

end MidenLean.AIR.Semantics
