import MidenLean.AIR.Semantics.Tactics
/-!
# StackArith Implementation Proofs (Step 9 bounded slice)

Semantic consequences over the current Rust-facing implementation AIR layer for
the current bounded slice: `ADD`, `NEG`, `MUL`, `INV`, `INCR`, `NOT`, `AND`,
`OR`, `EQ`, `EQZ`,
`EXPACC`, `EXT2MUL`, and grouped `u32` constraints for `U32SPLIT`,
`U32ASSERT2`, `U32ADD`, `U32ADD3`, and `U32SUB`.

These theorems only cover the op-specific arithmetic bodies from `StackArith`.
They do not restate the shared visible-stack shift laws, which are handled by
`StackGeneral`. If the intended mathematical spec is stronger than the current
Rust AIR, the stronger statement belongs in a separate spec module, not here.
-/

namespace MidenLean.AIR.Semantics.Proofs.StackArith

open MidenLean
open MidenLean.AIR.Semantics
open MidenLean.AIR.Semantics.Builder
open MidenLean.AIR.Semantics.Check
open MidenLean.AIR.Semantics.Subsystems
open MidenLean.AIR.Semantics.Tactics

/-- Shared zero-product elimination for active canonical transition constraints
of the form `whenTransition (gate selector (assertEq lhs rhs))`. -/
private theorem active_transition_gate_assertEq_implies_eq
    (r : AirRow)
    (selector lhs rhs : FExpr)
    (hsat : satisfiesBase r [whenTransition (gate selector (assertEq lhs rhs))])
    (htrans : r.isTransition = 1)
    (hsel : selector.eval r = 1) :
    lhs.eval r = rhs.eval r := by
  have hzero :
      (whenTransition (gate selector (assertEq lhs rhs))).eval r = 0 := by
    exact singleton_constraint_eval_zero r _ hsat
  have hgated :
      (FExpr.boundary .transition).eval r *
          (selector.eval r * (lhs.eval r - rhs.eval r)) = 0 := by
    simpa [whenTransition, gate, assertEq, assertZero] using hzero
  have hbody :
      selector.eval r * (lhs.eval r - rhs.eval r) = 0 := by
    exact cancel_transition_factor r _ hgated htrans
  have hsub : lhs.eval r - rhs.eval r = 0 := by
    exact cancel_active_selector_factor _ _ hbody hsel
  exact sub_eq_zero.mp hsub

/-- Shared zero-product elimination for active canonical integrity constraints
of the form `gate selector (assertEq lhs rhs)`. -/
private theorem active_gate_assertEq_implies_eq
    (r : AirRow)
    (selector lhs rhs : FExpr)
    (hsat : satisfiesBase r [gate selector (assertEq lhs rhs)])
    (hsel : selector.eval r = 1) :
    lhs.eval r = rhs.eval r := by
  have hzero :
      (gate selector (assertEq lhs rhs)).eval r = 0 := by
    exact singleton_constraint_eval_zero r _ hsat
  have hgated : selector.eval r * (lhs.eval r - rhs.eval r) = 0 := by
    simpa [gate, assertEq, assertZero] using hzero
  have hsub : lhs.eval r - rhs.eval r = 0 := by
    exact cancel_active_selector_factor _ _ hgated hsel
  exact sub_eq_zero.mp hsub

/-- Shared zero-product elimination for active canonical integrity constraints
of the form `gate selector (assertZero body)`. -/
private theorem active_gate_assertZero_implies_zero
    (r : AirRow)
    (selector body : FExpr)
    (hsat : satisfiesBase r [gate selector (assertZero body)])
    (hsel : selector.eval r = 1) :
    body.eval r = 0 := by
  have hzero :
      (gate selector (assertZero body)).eval r = 0 := by
    exact singleton_constraint_eval_zero r _ hsat
  have hgated : selector.eval r * body.eval r = 0 := by
    simpa [gate, assertZero] using hzero
  exact cancel_active_selector_factor _ _ hgated hsel

/-- Shared zero-product elimination for active canonical transition
constraints of the form `whenTransition (gate selector (assertZero body))`. -/
private theorem active_transition_gate_assertZero_implies_zero
    (r : AirRow)
    (selector body : FExpr)
    (hsat : satisfiesBase r [whenTransition (gate selector (assertZero body))])
    (htrans : r.isTransition = 1)
    (hsel : selector.eval r = 1) :
    body.eval r = 0 := by
  have hzero :
      (whenTransition (gate selector (assertZero body))).eval r = 0 := by
    exact singleton_constraint_eval_zero r _ hsat
  have hgated :
      (FExpr.boundary .transition).eval r *
          (selector.eval r * body.eval r) = 0 := by
    simpa [whenTransition, gate, assertZero] using hzero
  have hbody :
      selector.eval r * body.eval r = 0 := by
    exact cancel_transition_factor r _ hgated htrans
  exact cancel_active_selector_factor _ _ hbody hsel

/-- Active canonical `ADD` enforces `s0' = s0 + s1`. -/
theorem add_active_implies_s0Next_eq_sum
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.add])
    (htrans : r.isTransition = 1)
    (hadd : StackArith.isAdd.eval r = 1) :
    StackArith.s0Next.eval r = StackArith.s0.eval r + StackArith.s1.eval r := by
  exact active_transition_gate_assertEq_implies_eq
    r StackArith.isAdd StackArith.s0Next (FExpr.plus StackArith.s0 StackArith.s1)
    hsat htrans hadd

/-- Active canonical `NEG` enforces `s0' = -s0`. -/
theorem neg_active_implies_s0Next_eq_neg_s0
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.neg])
    (htrans : r.isTransition = 1)
    (hneg : StackArith.isNeg.eval r = 1) :
    StackArith.s0Next.eval r = -StackArith.s0.eval r := by
  have heq :
      StackArith.s0Next.eval r = (FExpr.minus (FExpr.const 0) StackArith.s0).eval r := by
    exact active_transition_gate_assertEq_implies_eq
      r StackArith.isNeg StackArith.s0Next (FExpr.minus (FExpr.const 0) StackArith.s0)
      hsat htrans hneg
  simpa [FExpr.eval, zero_sub] using heq

/-- Active canonical `MUL` enforces `s0' = s0 * s1`. -/
theorem mul_active_implies_s0Next_eq_mul
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.mul])
    (htrans : r.isTransition = 1)
    (hmulSel : StackArith.isMul.eval r = 1) :
    StackArith.s0Next.eval r = StackArith.s0.eval r * StackArith.s1.eval r := by
  exact active_transition_gate_assertEq_implies_eq
    r StackArith.isMul StackArith.s0Next (FExpr.times StackArith.s0 StackArith.s1)
    hsat htrans hmulSel

/-- Active canonical `INV` enforces `s0' * s0 = 1`. -/
theorem inv_active_implies_s0Next_mul_s0_eq_one
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.inv])
    (htrans : r.isTransition = 1)
    (hinv : StackArith.isInv.eval r = 1) :
    StackArith.s0Next.eval r * StackArith.s0.eval r = 1 := by
  have heq :
      (FExpr.times StackArith.s0Next StackArith.s0).eval r = (FExpr.const 1).eval r := by
    exact active_transition_gate_assertEq_implies_eq
      r StackArith.isInv (FExpr.times StackArith.s0Next StackArith.s0) (FExpr.const 1)
      hsat htrans hinv
  simpa [FExpr.eval] using heq

/-- Active canonical `INCR` enforces `s0' = s0 + 1`. -/
theorem incr_active_implies_s0Next_eq_s0_plus_one
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.incr])
    (htrans : r.isTransition = 1)
    (hincr : StackArith.isIncr.eval r = 1) :
    StackArith.s0Next.eval r = StackArith.s0.eval r + 1 := by
  have heq :
      StackArith.s0Next.eval r = (FExpr.plus StackArith.s0 (FExpr.const 1)).eval r := by
    exact active_transition_gate_assertEq_implies_eq
      r StackArith.isIncr StackArith.s0Next (FExpr.plus StackArith.s0 (FExpr.const 1))
      hsat htrans hincr
  simpa [FExpr.eval] using heq

/-- Intermediate activation theorem for canonical `NOT` binaryity:
under active selector, `s0 * (s0 - 1) = 0`. -/
theorem not_active_implies_s0_binary
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.notBinary])
    (hnot : StackArith.isNot.eval r = 1) :
    StackArith.s0.eval r * (StackArith.s0.eval r - 1) = 0 := by
  exact active_gate_assertZero_implies_zero
    r StackArith.isNot (FExpr.times StackArith.s0 (FExpr.minus StackArith.s0 (FExpr.const 1)))
    hsat hnot

/-- Intermediate activation theorem for canonical `NOT` output relation:
under transition + active selector, `s0 + s0' = 1`. -/
theorem not_active_implies_s0_plus_s0Next_eq_one
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.notValue])
    (htrans : r.isTransition = 1)
    (hnot : StackArith.isNot.eval r = 1) :
    StackArith.s0.eval r + StackArith.s0Next.eval r = 1 := by
  have heq :
      (FExpr.plus StackArith.s0 StackArith.s0Next).eval r = (FExpr.const 1).eval r := by
    exact active_transition_gate_assertEq_implies_eq
      r StackArith.isNot (FExpr.plus StackArith.s0 StackArith.s0Next) (FExpr.const 1)
      hsat htrans hnot
  simpa [FExpr.eval] using heq

/-- Intermediate activation theorem for canonical `NOT`:
under transition + active selector, `s0' = 1 - s0`. -/
theorem not_active_implies_s0Next_eq_one_sub_s0
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.notValue])
    (htrans : r.isTransition = 1)
    (hnot : StackArith.isNot.eval r = 1) :
    StackArith.s0Next.eval r = 1 - StackArith.s0.eval r := by
  have hsum :
      StackArith.s0.eval r + StackArith.s0Next.eval r = 1 := by
    exact not_active_implies_s0_plus_s0Next_eq_one r hsat htrans hnot
  have hsum' : StackArith.s0Next.eval r + StackArith.s0.eval r = 1 := by
    simpa [add_comm] using hsum
  exact (eq_sub_iff_add_eq).2 hsum'

/-- Intermediate activation theorem for canonical `AND` binaryity on `s0`. -/
theorem and_active_implies_s0_binary
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.andS0Binary])
    (hand : StackArith.isAnd.eval r = 1) :
    StackArith.s0.eval r * (StackArith.s0.eval r - 1) = 0 := by
  exact active_gate_assertZero_implies_zero
    r StackArith.isAnd (FExpr.times StackArith.s0 (FExpr.minus StackArith.s0 (FExpr.const 1)))
    hsat hand

/-- Intermediate activation theorem for canonical `AND` binaryity on `s1`. -/
theorem and_active_implies_s1_binary
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.andS1Binary])
    (hand : StackArith.isAnd.eval r = 1) :
    StackArith.s1.eval r * (StackArith.s1.eval r - 1) = 0 := by
  exact active_gate_assertZero_implies_zero
    r StackArith.isAnd (FExpr.times StackArith.s1 (FExpr.minus StackArith.s1 (FExpr.const 1)))
    hsat hand

/-- Intermediate activation theorem for canonical `AND` output relation. -/
theorem and_active_implies_s0Next_eq_s0_mul_s1
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.andValue])
    (htrans : r.isTransition = 1)
    (hand : StackArith.isAnd.eval r = 1) :
    StackArith.s0Next.eval r = StackArith.s0.eval r * StackArith.s1.eval r := by
  exact active_transition_gate_assertEq_implies_eq
    r StackArith.isAnd StackArith.s0Next (FExpr.times StackArith.s0 StackArith.s1)
    hsat htrans hand

/-- Intermediate activation theorem for canonical `OR` binaryity on `s0`. -/
theorem or_active_implies_s0_binary
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.orS0Binary])
    (hor : StackArith.isOr.eval r = 1) :
    StackArith.s0.eval r * (StackArith.s0.eval r - 1) = 0 := by
  exact active_gate_assertZero_implies_zero
    r StackArith.isOr (FExpr.times StackArith.s0 (FExpr.minus StackArith.s0 (FExpr.const 1)))
    hsat hor

/-- Intermediate activation theorem for canonical `OR` binaryity on `s1`. -/
theorem or_active_implies_s1_binary
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.orS1Binary])
    (hor : StackArith.isOr.eval r = 1) :
    StackArith.s1.eval r * (StackArith.s1.eval r - 1) = 0 := by
  exact active_gate_assertZero_implies_zero
    r StackArith.isOr (FExpr.times StackArith.s1 (FExpr.minus StackArith.s1 (FExpr.const 1)))
    hsat hor

/-- Intermediate activation theorem for canonical `OR` output relation. -/
theorem or_active_implies_s0Next_eq_or
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.orValue])
    (htrans : r.isTransition = 1)
    (hor : StackArith.isOr.eval r = 1) :
    StackArith.s0Next.eval r =
      (StackArith.s0.eval r + StackArith.s1.eval r) - (StackArith.s0.eval r * StackArith.s1.eval r) := by
  exact active_transition_gate_assertEq_implies_eq
    r StackArith.isOr StackArith.s0Next
    (FExpr.minus (FExpr.plus StackArith.s0 StackArith.s1) (FExpr.times StackArith.s0 StackArith.s1))
    hsat htrans hor

/-- Intermediate activation theorem for canonical `EQ` zero-product relation:
`(s0 - s1) * s0' = 0`. -/
theorem eq_active_implies_diff_mul_s0Next_eq_zero
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.eqZeroProduct])
    (htrans : r.isTransition = 1)
    (heqSel : StackArith.isEq.eval r = 1) :
    (StackArith.s0.eval r - StackArith.s1.eval r) * StackArith.s0Next.eval r = 0 := by
  exact active_transition_gate_assertZero_implies_zero
    r StackArith.isEq (FExpr.times (FExpr.minus StackArith.s0 StackArith.s1) StackArith.s0Next)
    hsat htrans heqSel

/-- Intermediate activation theorem for canonical `EQ` value relation:
`s0' = 1 - (s0 - s1) * h0`. -/
theorem eq_active_implies_s0Next_eq_one_sub_diff_mul_h0
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.eqValue])
    (htrans : r.isTransition = 1)
    (heqSel : StackArith.isEq.eval r = 1) :
    StackArith.s0Next.eval r =
      1 - ((StackArith.s0.eval r - StackArith.s1.eval r) * StackArith.uopH0.eval r) := by
  have heq :
      StackArith.s0Next.eval r =
        (FExpr.minus (FExpr.const 1)
          (FExpr.times (FExpr.minus StackArith.s0 StackArith.s1) StackArith.uopH0)).eval r := by
    exact active_transition_gate_assertEq_implies_eq
      r StackArith.isEq StackArith.s0Next
      (FExpr.minus (FExpr.const 1)
        (FExpr.times (FExpr.minus StackArith.s0 StackArith.s1) StackArith.uopH0))
      hsat htrans heqSel
  simpa [FExpr.eval] using heq

/-- Intermediate activation theorem for canonical `EQZ` zero-product relation:
`s0 * s0' = 0`. -/
theorem eqz_active_implies_s0_mul_s0Next_eq_zero
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.eqzZeroProduct])
    (htrans : r.isTransition = 1)
    (heqzSel : StackArith.isEqz.eval r = 1) :
    StackArith.s0.eval r * StackArith.s0Next.eval r = 0 := by
  exact active_transition_gate_assertZero_implies_zero
    r StackArith.isEqz (FExpr.times StackArith.s0 StackArith.s0Next)
    hsat htrans heqzSel

/-- Intermediate activation theorem for canonical `EQZ` value relation:
`s0' = 1 - s0 * h0`. -/
theorem eqz_active_implies_s0Next_eq_one_sub_s0_mul_h0
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.eqzValue])
    (htrans : r.isTransition = 1)
    (heqzSel : StackArith.isEqz.eval r = 1) :
    StackArith.s0Next.eval r = 1 - (StackArith.s0.eval r * StackArith.uopH0.eval r) := by
  have heq :
      StackArith.s0Next.eval r =
        (FExpr.minus (FExpr.const 1) (FExpr.times StackArith.s0 StackArith.uopH0)).eval r := by
    exact active_transition_gate_assertEq_implies_eq
      r StackArith.isEqz StackArith.s0Next
      (FExpr.minus (FExpr.const 1) (FExpr.times StackArith.s0 StackArith.uopH0))
      hsat htrans heqzSel
  simpa [FExpr.eval] using heq

/-- Intermediate activation theorem for canonical `EXPACC` square relation:
`s1' = s1 * s1`. -/
theorem expacc_active_implies_s1Next_eq_s1_sq
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.expaccExpSquare])
    (htrans : r.isTransition = 1)
    (hexpacc : StackArith.isExpacc.eval r = 1) :
    StackArith.s1Next.eval r = StackArith.s1.eval r * StackArith.s1.eval r := by
  exact active_transition_gate_assertEq_implies_eq
    r StackArith.isExpacc StackArith.s1Next (FExpr.times StackArith.s1 StackArith.s1)
    hsat htrans hexpacc

/-- Intermediate activation theorem for canonical `EXPACC` helper relation:
`h0 - 1 - (s1 - 1) * s0' = 0`. -/
theorem expacc_active_implies_h0_relation
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.expaccExpVal])
    (htrans : r.isTransition = 1)
    (hexpacc : StackArith.isExpacc.eval r = 1) :
    StackArith.uopH0.eval r - 1 - ((StackArith.s1.eval r - 1) * StackArith.s0Next.eval r) = 0 := by
  exact active_transition_gate_assertZero_implies_zero
    r StackArith.isExpacc
    (FExpr.minus (FExpr.minus StackArith.uopH0 (FExpr.const 1))
      (FExpr.times (FExpr.minus StackArith.s1 (FExpr.const 1)) StackArith.s0Next))
    hsat htrans hexpacc

/-- Intermediate activation theorem for canonical `EXPACC` accumulator update:
`s2' = s2 * h0`. -/
theorem expacc_active_implies_s2Next_eq_s2_mul_h0
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.expaccAccUpdate])
    (htrans : r.isTransition = 1)
    (hexpacc : StackArith.isExpacc.eval r = 1) :
    StackArith.s2Next.eval r = StackArith.s2.eval r * StackArith.uopH0.eval r := by
  exact active_transition_gate_assertEq_implies_eq
    r StackArith.isExpacc StackArith.s2Next (FExpr.times StackArith.s2 StackArith.uopH0)
    hsat htrans hexpacc

/-- Intermediate activation theorem for canonical `EXPACC` exponent shift:
`s3 - 2 * s3' - s0' = 0`. -/
theorem expacc_active_implies_s3_relation
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.expaccExpShift])
    (htrans : r.isTransition = 1)
    (hexpacc : StackArith.isExpacc.eval r = 1) :
    StackArith.s3.eval r - (StackArith.s3Next.eval r * 2) - StackArith.s0Next.eval r = 0 := by
  have hzero :
      (FExpr.minus (FExpr.minus StackArith.s3
        (FExpr.times StackArith.s3Next (FExpr.const 2))) StackArith.s0Next).eval r = 0 := by
    exact active_transition_gate_assertZero_implies_zero
      r StackArith.isExpacc
      (FExpr.minus (FExpr.minus StackArith.s3
        (FExpr.times StackArith.s3Next (FExpr.const 2))) StackArith.s0Next)
      hsat htrans hexpacc
  simpa [FExpr.eval] using hzero

/-- Intermediate activation theorem for canonical `EXPACC` bit binaryity:
`s0' * (s0' - 1) = 0`. -/
theorem expacc_active_implies_s0Next_binary
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.expaccBitBinary])
    (htrans : r.isTransition = 1)
    (hexpacc : StackArith.isExpacc.eval r = 1) :
    StackArith.s0Next.eval r * (StackArith.s0Next.eval r - 1) = 0 := by
  exact active_transition_gate_assertZero_implies_zero
    r StackArith.isExpacc (FExpr.times StackArith.s0Next (FExpr.minus StackArith.s0Next (FExpr.const 1)))
    hsat htrans hexpacc

/-- Active canonical `EXT2MUL` enforces `s0' = s0`. -/
theorem ext2mul_active_implies_s0Next_eq_s0
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.ext2mulD0Unchanged])
    (htrans : r.isTransition = 1)
    (hext2mul : StackArith.isExt2Mul.eval r = 1) :
    StackArith.s0Next.eval r = StackArith.s0.eval r := by
  exact active_transition_gate_assertEq_implies_eq
    r StackArith.isExt2Mul StackArith.s0Next StackArith.s0
    hsat htrans hext2mul

/-- Active canonical `EXT2MUL` enforces `s1' = s1`. -/
theorem ext2mul_active_implies_s1Next_eq_s1
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.ext2mulD1Unchanged])
    (htrans : r.isTransition = 1)
    (hext2mul : StackArith.isExt2Mul.eval r = 1) :
    StackArith.s1Next.eval r = StackArith.s1.eval r := by
  exact active_transition_gate_assertEq_implies_eq
    r StackArith.isExt2Mul StackArith.s1Next StackArith.s1
    hsat htrans hext2mul

/-- Active canonical `EXT2MUL` enforces
`s2' = s2*s0 + 7*s3*s1`. -/
theorem ext2mul_active_implies_s2Next_eq_c0
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.ext2mulC0])
    (htrans : r.isTransition = 1)
    (hext2mul : StackArith.isExt2Mul.eval r = 1) :
    StackArith.s2Next.eval r =
      (StackArith.s2.eval r * StackArith.s0.eval r) +
      (7 * (StackArith.s3.eval r * StackArith.s1.eval r)) := by
  exact active_transition_gate_assertEq_implies_eq
    r StackArith.isExt2Mul StackArith.s2Next
    (FExpr.plus (FExpr.times StackArith.s2 StackArith.s0)
      (FExpr.times (FExpr.const 7) (FExpr.times StackArith.s3 StackArith.s1)))
    hsat htrans hext2mul

/-- Active canonical `EXT2MUL` enforces
`s3' = (s2 + s3)*(s0 + s1) - s2*s0 - s3*s1`. -/
theorem ext2mul_active_implies_s3Next_eq_c1
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.ext2mulC1])
    (htrans : r.isTransition = 1)
    (hext2mul : StackArith.isExt2Mul.eval r = 1) :
    StackArith.s3Next.eval r =
      ((StackArith.s2.eval r + StackArith.s3.eval r) * (StackArith.s0.eval r + StackArith.s1.eval r) -
        (StackArith.s2.eval r * StackArith.s0.eval r)) -
      (StackArith.s3.eval r * StackArith.s1.eval r) := by
  exact active_transition_gate_assertEq_implies_eq
    r StackArith.isExt2Mul StackArith.s3Next
    (FExpr.minus
      (FExpr.minus (FExpr.times (FExpr.plus StackArith.s2 StackArith.s3) (FExpr.plus StackArith.s0 StackArith.s1))
        (FExpr.times StackArith.s2 StackArith.s0))
      (FExpr.times StackArith.s3 StackArith.s1))
    hsat htrans hext2mul

/-- Active grouped `u32` validity gate enforces
`u32_v_hi_comp * u32_v_lo = 0`. -/
theorem u32_split_mul_madd_active_implies_validity
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.u32SplitMulMaddValidity])
    (hu32grp : StackArith.u32SplitMulMadd.eval r = 1) :
    StackArith.u32VHiComp.eval r * StackArith.u32VLo.eval r = 0 := by
  exact active_gate_assertZero_implies_zero
    r StackArith.u32SplitMulMadd (FExpr.times StackArith.u32VHiComp StackArith.u32VLo)
    hsat hu32grp

/-- Active grouped `u32` two-outputs gate enforces `s0' = u32_v_lo`. -/
theorem u32_two_outputs_active_implies_s0Next_eq_u32VLo
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.u32TwoOutputsLo])
    (htrans : r.isTransition = 1)
    (hu32two : StackArith.u32TwoOutputs.eval r = 1) :
    StackArith.s0Next.eval r = StackArith.u32VLo.eval r := by
  exact active_transition_gate_assertEq_implies_eq
    r StackArith.u32TwoOutputs StackArith.s0Next StackArith.u32VLo
    hsat htrans hu32two

/-- Active grouped `u32` two-outputs gate enforces `s1' = u32_v_hi`. -/
theorem u32_two_outputs_active_implies_s1Next_eq_u32VHi
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.u32TwoOutputsHi])
    (htrans : r.isTransition = 1)
    (hu32two : StackArith.u32TwoOutputs.eval r = 1) :
    StackArith.s1Next.eval r = StackArith.u32VHi.eval r := by
  exact active_transition_gate_assertEq_implies_eq
    r StackArith.u32TwoOutputs StackArith.s1Next StackArith.u32VHi
    hsat htrans hu32two

/-- If `U32SPLIT` is active and other `u32TwoOutputs` contributors are inactive,
the shared two-output selector is active. -/
theorem u32split_selector_implies_u32_two_outputs_selector
    (r : AirRow)
    (hsplit : StackArith.isU32Split.eval r = 1)
    (hadd : StackArith.isU32Add.eval r = 0)
    (hadd3 : StackArith.isU32Add3.eval r = 0)
    (hmul : StackArith.isU32Mul.eval r = 0)
    (hmadd : StackArith.isU32Madd.eval r = 0) :
    StackArith.u32TwoOutputs.eval r = 1 := by
  simp [StackArith.u32TwoOutputs, hsplit, hadd, hadd3, hmul, hmadd]

/-- If `U32SPLIT` is active and other grouped-validity contributors are inactive,
the shared validity selector is active. -/
theorem u32split_selector_implies_u32_split_mul_madd_selector
    (r : AirRow)
    (hsplit : StackArith.isU32Split.eval r = 1)
    (hmul : StackArith.isU32Mul.eval r = 0)
    (hmadd : StackArith.isU32Madd.eval r = 0) :
    StackArith.u32SplitMulMadd.eval r = 1 := by
  simp [StackArith.u32SplitMulMadd, hsplit, hmul, hmadd]

/-- Active `U32SPLIT` implies `s0' = u32_v_lo` via the shared two-output gate. -/
theorem u32split_active_implies_s0Next_eq_u32VLo
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.u32TwoOutputsLo])
    (htrans : r.isTransition = 1)
    (hsplit : StackArith.isU32Split.eval r = 1)
    (hadd : StackArith.isU32Add.eval r = 0)
    (hadd3 : StackArith.isU32Add3.eval r = 0)
    (hmul : StackArith.isU32Mul.eval r = 0)
    (hmadd : StackArith.isU32Madd.eval r = 0) :
    StackArith.s0Next.eval r = StackArith.u32VLo.eval r := by
  have hu32two : StackArith.u32TwoOutputs.eval r = 1 :=
    u32split_selector_implies_u32_two_outputs_selector r hsplit hadd hadd3 hmul hmadd
  exact u32_two_outputs_active_implies_s0Next_eq_u32VLo r hsat htrans hu32two

/-- Active `U32SPLIT` implies `s1' = u32_v_hi` via the shared two-output gate. -/
theorem u32split_active_implies_s1Next_eq_u32VHi
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.u32TwoOutputsHi])
    (htrans : r.isTransition = 1)
    (hsplit : StackArith.isU32Split.eval r = 1)
    (hadd : StackArith.isU32Add.eval r = 0)
    (hadd3 : StackArith.isU32Add3.eval r = 0)
    (hmul : StackArith.isU32Mul.eval r = 0)
    (hmadd : StackArith.isU32Madd.eval r = 0) :
    StackArith.s1Next.eval r = StackArith.u32VHi.eval r := by
  have hu32two : StackArith.u32TwoOutputs.eval r = 1 :=
    u32split_selector_implies_u32_two_outputs_selector r hsplit hadd hadd3 hmul hmadd
  exact u32_two_outputs_active_implies_s1Next_eq_u32VHi r hsat htrans hu32two

/-- Active `U32SPLIT` implies grouped validity under the shared validity gate. -/
theorem u32split_active_implies_u32_validity
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.u32SplitMulMaddValidity])
    (hsplit : StackArith.isU32Split.eval r = 1)
    (hmul : StackArith.isU32Mul.eval r = 0)
    (hmadd : StackArith.isU32Madd.eval r = 0) :
    StackArith.u32VHiComp.eval r * StackArith.u32VLo.eval r = 0 := by
  have hu32grp : StackArith.u32SplitMulMadd.eval r = 1 :=
    u32split_selector_implies_u32_split_mul_madd_selector r hsplit hmul hmadd
  exact u32_split_mul_madd_active_implies_validity r hsat hu32grp

/-- Active `U32SPLIT` enforces the 64-bit limb reconstruction relation
`s0 = u32_v64`. -/
theorem u32split_active_implies_s0_eq_u32V64
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.u32SplitInput])
    (hsplit : StackArith.isU32Split.eval r = 1) :
    StackArith.s0.eval r = StackArith.u32V64.eval r := by
  exact active_gate_assertEq_implies_eq
    r StackArith.isU32Split StackArith.s0 StackArith.u32V64
    hsat hsplit

/-- If `U32ADD` is active and other `u32TwoOutputs` contributors are inactive,
the shared two-output selector is active. -/
theorem u32add_selector_implies_u32_two_outputs_selector
    (r : AirRow)
    (hadd : StackArith.isU32Add.eval r = 1)
    (hsplit : StackArith.isU32Split.eval r = 0)
    (hadd3 : StackArith.isU32Add3.eval r = 0)
    (hmul : StackArith.isU32Mul.eval r = 0)
    (hmadd : StackArith.isU32Madd.eval r = 0) :
    StackArith.u32TwoOutputs.eval r = 1 := by
  simp [StackArith.u32TwoOutputs, hsplit, hadd, hadd3, hmul, hmadd]

/-- Active `U32ADD` implies `s0' = u32_v_lo` via the shared two-output gate. -/
theorem u32add_active_implies_s0Next_eq_u32VLo
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.u32TwoOutputsLo])
    (htrans : r.isTransition = 1)
    (hadd : StackArith.isU32Add.eval r = 1)
    (hsplit : StackArith.isU32Split.eval r = 0)
    (hadd3 : StackArith.isU32Add3.eval r = 0)
    (hmul : StackArith.isU32Mul.eval r = 0)
    (hmadd : StackArith.isU32Madd.eval r = 0) :
    StackArith.s0Next.eval r = StackArith.u32VLo.eval r := by
  have hu32two : StackArith.u32TwoOutputs.eval r = 1 :=
    u32add_selector_implies_u32_two_outputs_selector r hadd hsplit hadd3 hmul hmadd
  exact u32_two_outputs_active_implies_s0Next_eq_u32VLo r hsat htrans hu32two

/-- Active `U32ADD` implies `s1' = u32_v_hi` via the shared two-output gate. -/
theorem u32add_active_implies_s1Next_eq_u32VHi
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.u32TwoOutputsHi])
    (htrans : r.isTransition = 1)
    (hadd : StackArith.isU32Add.eval r = 1)
    (hsplit : StackArith.isU32Split.eval r = 0)
    (hadd3 : StackArith.isU32Add3.eval r = 0)
    (hmul : StackArith.isU32Mul.eval r = 0)
    (hmadd : StackArith.isU32Madd.eval r = 0) :
    StackArith.s1Next.eval r = StackArith.u32VHi.eval r := by
  have hu32two : StackArith.u32TwoOutputs.eval r = 1 :=
    u32add_selector_implies_u32_two_outputs_selector r hadd hsplit hadd3 hmul hmadd
  exact u32_two_outputs_active_implies_s1Next_eq_u32VHi r hsat htrans hu32two

/-- Active `U32ADD` enforces the 48-bit input decomposition relation
`s0 + s1 = u32_v48`. -/
theorem u32add_active_implies_s0_plus_s1_eq_u32V48
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.u32AddInput])
    (hadd : StackArith.isU32Add.eval r = 1) :
    StackArith.s0.eval r + StackArith.s1.eval r = StackArith.u32V48.eval r := by
  exact active_gate_assertEq_implies_eq
    r StackArith.isU32Add (FExpr.plus StackArith.s0 StackArith.s1) StackArith.u32V48
    hsat hadd

/-- If `U32ADD3` is active and other `u32TwoOutputs` contributors are inactive,
the shared two-output selector is active. -/
theorem u32add3_selector_implies_u32_two_outputs_selector
    (r : AirRow)
    (hadd3 : StackArith.isU32Add3.eval r = 1)
    (hsplit : StackArith.isU32Split.eval r = 0)
    (hadd : StackArith.isU32Add.eval r = 0)
    (hmul : StackArith.isU32Mul.eval r = 0)
    (hmadd : StackArith.isU32Madd.eval r = 0) :
    StackArith.u32TwoOutputs.eval r = 1 := by
  simp [StackArith.u32TwoOutputs, hsplit, hadd, hadd3, hmul, hmadd]

/-- Active `U32ADD3` implies `s0' = u32_v_lo` via the shared two-output gate. -/
theorem u32add3_active_implies_s0Next_eq_u32VLo
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.u32TwoOutputsLo])
    (htrans : r.isTransition = 1)
    (hadd3 : StackArith.isU32Add3.eval r = 1)
    (hsplit : StackArith.isU32Split.eval r = 0)
    (hadd : StackArith.isU32Add.eval r = 0)
    (hmul : StackArith.isU32Mul.eval r = 0)
    (hmadd : StackArith.isU32Madd.eval r = 0) :
    StackArith.s0Next.eval r = StackArith.u32VLo.eval r := by
  have hu32two : StackArith.u32TwoOutputs.eval r = 1 :=
    u32add3_selector_implies_u32_two_outputs_selector r hadd3 hsplit hadd hmul hmadd
  exact u32_two_outputs_active_implies_s0Next_eq_u32VLo r hsat htrans hu32two

/-- Active `U32ADD3` implies `s1' = u32_v_hi` via the shared two-output gate. -/
theorem u32add3_active_implies_s1Next_eq_u32VHi
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.u32TwoOutputsHi])
    (htrans : r.isTransition = 1)
    (hadd3 : StackArith.isU32Add3.eval r = 1)
    (hsplit : StackArith.isU32Split.eval r = 0)
    (hadd : StackArith.isU32Add.eval r = 0)
    (hmul : StackArith.isU32Mul.eval r = 0)
    (hmadd : StackArith.isU32Madd.eval r = 0) :
    StackArith.s1Next.eval r = StackArith.u32VHi.eval r := by
  have hu32two : StackArith.u32TwoOutputs.eval r = 1 :=
    u32add3_selector_implies_u32_two_outputs_selector r hadd3 hsplit hadd hmul hmadd
  exact u32_two_outputs_active_implies_s1Next_eq_u32VHi r hsat htrans hu32two

/-- Active `U32ADD3` enforces the 48-bit input decomposition relation
`s0 + s1 + s2 = u32_v48`. -/
theorem u32add3_active_implies_s0_plus_s1_plus_s2_eq_u32V48
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.u32Add3Input])
    (hadd3 : StackArith.isU32Add3.eval r = 1) :
    StackArith.s0.eval r + StackArith.s1.eval r + StackArith.s2.eval r =
      StackArith.u32V48.eval r := by
  exact active_gate_assertEq_implies_eq
    r StackArith.isU32Add3 (FExpr.plus (FExpr.plus StackArith.s0 StackArith.s1) StackArith.s2)
    StackArith.u32V48 hsat hadd3

/-- Active `U32MUL` enforces `s0 * s1 = u32_v64`. -/
theorem u32mul_active_implies_s0_times_s1_eq_u32V64
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.u32Mul])
    (hmul : StackArith.isU32Mul.eval r = 1) :
    StackArith.s0.eval r * StackArith.s1.eval r = StackArith.u32V64.eval r := by
  exact active_gate_assertEq_implies_eq
    r StackArith.isU32Mul (FExpr.times StackArith.s0 StackArith.s1)
    StackArith.u32V64 hsat hmul

/-- Active `U32MADD` enforces `s0 * s1 + s2 = u32_v64`. -/
theorem u32madd_active_implies_s0_times_s1_plus_s2_eq_u32V64
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.u32Madd])
    (hmadd : StackArith.isU32Madd.eval r = 1) :
    StackArith.s0.eval r * StackArith.s1.eval r + StackArith.s2.eval r =
      StackArith.u32V64.eval r := by
  exact active_gate_assertEq_implies_eq
    r StackArith.isU32Madd (FExpr.plus (FExpr.times StackArith.s0 StackArith.s1) StackArith.s2)
    StackArith.u32V64 hsat hmadd

/-- Active `U32SUB` transition constraint enforces the difference relation. -/
theorem u32sub_active_implies_diff_relation
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.u32SubDiff])
    (htrans : r.isTransition = 1)
    (hsub : StackArith.isU32Sub.eval r = 1) :
    StackArith.s1.eval r =
      StackArith.s0.eval r + StackArith.s1Next.eval r -
        StackArith.s0Next.eval r * StackArith.twoPow32.eval r := by
  have hzero :=
    active_transition_gate_assertZero_implies_zero
      r StackArith.isU32Sub
      (FExpr.plus
        (FExpr.minus (FExpr.minus StackArith.s1 StackArith.s0) StackArith.s1Next)
        (FExpr.times StackArith.s0Next StackArith.twoPow32))
      hsat htrans hsub
  have hdiff :
      StackArith.s1.eval r -
          (StackArith.s0.eval r + StackArith.s1Next.eval r -
            StackArith.s0Next.eval r * StackArith.twoPow32.eval r) = 0 := by
    simpa [FExpr.eval, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hzero
  exact sub_eq_zero.mp hdiff

/-- Active `U32SUB` transition constraint enforces the borrow binaryity. -/
theorem u32sub_active_implies_borrow_binary
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.u32SubBorrowBinary])
    (htrans : r.isTransition = 1)
    (hsub : StackArith.isU32Sub.eval r = 1) :
    StackArith.s0Next.eval r * (StackArith.s0Next.eval r - 1) = 0 := by
  exact active_transition_gate_assertZero_implies_zero
    r StackArith.isU32Sub
      (FExpr.times StackArith.s0Next (FExpr.minus StackArith.s0Next (FExpr.const 1)))
      hsat htrans hsub

/-- Active `U32SUB` transition constraint sets `s1' = u32_v_lo`. -/
theorem u32sub_active_implies_s1Next_eq_u32VLo
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.u32SubLow])
    (htrans : r.isTransition = 1)
    (hsub : StackArith.isU32Sub.eval r = 1) :
    StackArith.s1Next.eval r = StackArith.u32VLo.eval r := by
  exact active_transition_gate_assertEq_implies_eq
    r StackArith.isU32Sub StackArith.s1Next StackArith.u32VLo
    hsat htrans hsub

/-- Active `U32ASSERT2` enforces `s0' = u32_v_hi`. -/
theorem u32assert2_active_implies_s0Next_eq_u32VHi
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.u32Assert2Hi])
    (htrans : r.isTransition = 1)
    (hassert2 : StackArith.isU32Assert2.eval r = 1) :
    StackArith.s0Next.eval r = StackArith.u32VHi.eval r := by
  exact active_transition_gate_assertEq_implies_eq
    r StackArith.isU32Assert2 StackArith.s0Next StackArith.u32VHi
    hsat htrans hassert2

/-- Active `U32ASSERT2` enforces `s1' = u32_v_lo`. -/
theorem u32assert2_active_implies_s1Next_eq_u32VLo
    (r : AirRow)
    (hsat : satisfiesBase r [StackArith.u32Assert2Lo])
    (htrans : r.isTransition = 1)
    (hassert2 : StackArith.isU32Assert2.eval r = 1) :
    StackArith.s1Next.eval r = StackArith.u32VLo.eval r := by
  exact active_transition_gate_assertEq_implies_eq
    r StackArith.isU32Assert2 StackArith.s1Next StackArith.u32VLo
    hsat htrans hassert2

end MidenLean.AIR.Semantics.Proofs.StackArith
