import MidenLean.Felt
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Monic

/-!
# Quadratic Extension of the Goldilocks Field

Miden uses a quadratic extension GF(p²) of the Goldilocks field GF(p) where
p = 2^64 - 2^32 + 1. The extension is defined by the irreducible polynomial
`x² - 7` over GF(p), so elements are pairs `(a, b)` representing `a + b·x`
where `x² = 7`.

## Architecture

Two representations coexist:
- **`QuadFelt`** (concrete): `(re, im)` pairs with explicit arithmetic.
  Used for `#eval`, differential testing, and extracted AIR evaluation.
- **`ExtFelt`** (abstract): `AdjoinRoot (X² - 7)` from Mathlib.
  This is the proof-facing algebraic model.
- **`QuadFelt.toExtFelt`**: a small bridge from the executable representation
  into the abstract quotient ring. The `CommRing` structure on `QuadFelt` is
  transported through this bridge rather than proved ad hoc componentwise.
-/

namespace MidenLean

/-- A quadratic extension field element over the Goldilocks field.
    Represents `a + b·x` where `x² = 7`. -/
structure QuadFelt where
  /-- Real part: coefficient of `1`. -/
  re : Felt
  /-- Imaginary part: coefficient of `x`. -/
  im : Felt
  deriving Repr, BEq, DecidableEq

namespace QuadFelt

/-- The residue used in the extension: `x² = RESIDUE`. For Miden, `RESIDUE = 7`. -/
def RESIDUE : Felt := 7

/-- Zero element of `GF(p²)`. -/
def zero : QuadFelt := ⟨0, 0⟩

/-- One element of `GF(p²)`. -/
def one : QuadFelt := ⟨1, 0⟩

/-- Addition in `GF(p²)`: component-wise addition. -/
def add (f g : QuadFelt) : QuadFelt :=
  ⟨f.re + g.re, f.im + g.im⟩

/-- Negation in `GF(p²)`: negate each component. -/
def neg (f : QuadFelt) : QuadFelt :=
  ⟨-f.re, -f.im⟩

/-- Subtraction in `GF(p²)`: component-wise subtraction. -/
def sub (f g : QuadFelt) : QuadFelt :=
  ⟨f.re - g.re, f.im - g.im⟩

/-- Multiplication in `GF(p²)`, using `x² = 7`. -/
def mul (f g : QuadFelt) : QuadFelt :=
  ⟨f.re * g.re + RESIDUE * f.im * g.im,
   f.re * g.im + f.im * g.re⟩

/-- Recursive natural-number scalar multiplication. -/
def nsmul (n : Nat) (f : QuadFelt) : QuadFelt :=
  ⟨n • f.re, n • f.im⟩

/-- Recursive integer scalar multiplication. -/
def zsmul (n : Int) (f : QuadFelt) : QuadFelt :=
  ⟨n • f.re, n • f.im⟩

/-- Recursive powering. -/
def pow (f : QuadFelt) : Nat → QuadFelt
  | 0 => QuadFelt.one
  | n + 1 => QuadFelt.mul (pow f n) f

/-- Check whether a `QuadFelt` element is zero (both components are zero). -/
def check_zero (f : QuadFelt) : Bool :=
  f.re == 0 && f.im == 0

/-- Scalar multiplication by a base-field element. -/
def smul (c : Felt) (f : QuadFelt) : QuadFelt :=
  ⟨c * f.re, c * f.im⟩

/-- Embed a base-field element into `GF(p²)` as `(a, 0)`. -/
def ofFelt (a : Felt) : QuadFelt :=
  ⟨a, 0⟩

instance : Add QuadFelt := ⟨QuadFelt.add⟩
instance : Sub QuadFelt := ⟨QuadFelt.sub⟩
instance : Mul QuadFelt := ⟨QuadFelt.mul⟩
instance : Neg QuadFelt := ⟨QuadFelt.neg⟩
instance : Zero QuadFelt := ⟨QuadFelt.zero⟩
instance : One QuadFelt := ⟨QuadFelt.one⟩
instance : Inhabited QuadFelt := ⟨QuadFelt.zero⟩
instance : HSMul Felt QuadFelt QuadFelt := ⟨QuadFelt.smul⟩
instance : Coe Felt QuadFelt := ⟨QuadFelt.ofFelt⟩
instance : SMul Nat QuadFelt := ⟨QuadFelt.nsmul⟩
instance : SMul Int QuadFelt := ⟨QuadFelt.zsmul⟩
instance : Pow QuadFelt Nat := ⟨QuadFelt.pow⟩
instance : NatCast QuadFelt := ⟨fun n => QuadFelt.ofFelt n⟩
instance : IntCast QuadFelt := ⟨fun n => QuadFelt.ofFelt n⟩

@[ext] theorem ext {a b : QuadFelt} (hre : a.re = b.re) (him : a.im = b.im) : a = b := by
  cases a
  cases b
  cases hre
  cases him
  rfl

@[simp] theorem add_re (a b : QuadFelt) : (a + b).re = a.re + b.re := rfl
@[simp] theorem add_im (a b : QuadFelt) : (a + b).im = a.im + b.im := rfl
@[simp] theorem sub_re (a b : QuadFelt) : (a - b).re = a.re - b.re := rfl
@[simp] theorem sub_im (a b : QuadFelt) : (a - b).im = a.im - b.im := rfl
@[simp] theorem neg_re (a : QuadFelt) : (-a).re = -a.re := rfl
@[simp] theorem neg_im (a : QuadFelt) : (-a).im = -a.im := rfl
@[simp] theorem mul_re (a b : QuadFelt) :
    (a * b).re = a.re * b.re + RESIDUE * a.im * b.im := rfl
@[simp] theorem mul_im (a b : QuadFelt) :
    (a * b).im = a.re * b.im + a.im * b.re := rfl
@[simp] theorem zero_re : (0 : QuadFelt).re = 0 := rfl
@[simp] theorem zero_im : (0 : QuadFelt).im = 0 := rfl
@[simp] theorem one_re : (1 : QuadFelt).re = 1 := rfl
@[simp] theorem one_im : (1 : QuadFelt).im = 0 := rfl
@[simp] theorem ofFelt_re (a : Felt) : (QuadFelt.ofFelt a).re = a := rfl
@[simp] theorem ofFelt_im (a : Felt) : (QuadFelt.ofFelt a).im = 0 := rfl

end QuadFelt

-- ============================================================================
-- Mathlib-backed extension ring (for proofs)
-- ============================================================================

open Polynomial

/-- The polynomial `X² - 7` over the Goldilocks field. -/
noncomputable def extPoly : Polynomial Felt := X ^ 2 - C QuadFelt.RESIDUE

/-- The proof-facing quotient ring `GF(p)[X]/(X² - 7)`. -/
noncomputable def ExtFelt := AdjoinRoot extPoly

noncomputable instance : CommRing ExtFelt := AdjoinRoot.instCommRing _

namespace QuadFelt

/-- The linear polynomial corresponding to `a + b·x`: `b·X + a`. -/
noncomputable def toPoly (z : QuadFelt) : Polynomial Felt :=
  C z.im * X + C z.re

/-- Bridge from the executable pair representation into the abstract quotient ring. -/
noncomputable def toExtFelt (z : QuadFelt) : ExtFelt :=
  AdjoinRoot.of extPoly z.re + AdjoinRoot.of extPoly z.im * AdjoinRoot.root extPoly

theorem toExtFelt_eq_mk (z : QuadFelt) :
    z.toExtFelt = AdjoinRoot.mk extPoly z.toPoly := by
  simp [QuadFelt.toExtFelt, QuadFelt.toPoly, AdjoinRoot.mk_C, AdjoinRoot.mk_X, add_comm]

private theorem extPoly_monic : extPoly.Monic := by
  simpa [extPoly, QuadFelt.RESIDUE] using
    (Polynomial.monic_X_pow_sub_C (R := Felt) (a := QuadFelt.RESIDUE) (n := 2) (by decide : (2 : Nat) ≠ 0))

private theorem extPoly_natDegree : extPoly.natDegree = 2 := by
  simpa [extPoly, QuadFelt.RESIDUE] using
    (Polynomial.natDegree_X_pow_sub_C (R := Felt) (n := 2) (r := QuadFelt.RESIDUE))

private theorem root_mul_root :
    AdjoinRoot.root extPoly * AdjoinRoot.root extPoly = AdjoinRoot.of extPoly QuadFelt.RESIDUE := by
  have h := AdjoinRoot.eval₂_root extPoly
  have h' : AdjoinRoot.root extPoly * AdjoinRoot.root extPoly - AdjoinRoot.of extPoly QuadFelt.RESIDUE = 0 := by
    simpa [extPoly, QuadFelt.RESIDUE, pow_two] using h
  exact sub_eq_zero.mp h'

@[simp] theorem toExtFelt_zero : QuadFelt.toExtFelt 0 = 0 := by
  simp [QuadFelt.toExtFelt]

@[simp] theorem toExtFelt_one : QuadFelt.toExtFelt 1 = 1 := by
  simp [QuadFelt.toExtFelt]

@[simp] theorem toExtFelt_add (x y : QuadFelt) :
    QuadFelt.toExtFelt (x + y) = QuadFelt.toExtFelt x + QuadFelt.toExtFelt y := by
  simp [QuadFelt.toExtFelt, QuadFelt.add]
  ring_nf

@[simp] theorem toExtFelt_neg (x : QuadFelt) :
    QuadFelt.toExtFelt (-x) = -QuadFelt.toExtFelt x := by
  simp [QuadFelt.toExtFelt, QuadFelt.neg]
  ring_nf

@[simp] theorem toExtFelt_sub (x y : QuadFelt) :
    QuadFelt.toExtFelt (x - y) = QuadFelt.toExtFelt x - QuadFelt.toExtFelt y := by
  simp [QuadFelt.toExtFelt, QuadFelt.sub]
  ring_nf

@[simp] theorem toExtFelt_mul (x y : QuadFelt) :
    QuadFelt.toExtFelt (x * y) = QuadFelt.toExtFelt x * QuadFelt.toExtFelt y := by
  have hres :
      AdjoinRoot.of extPoly (QuadFelt.RESIDUE * x.im * y.im) =
        (AdjoinRoot.of extPoly x.im * AdjoinRoot.of extPoly y.im) *
          (AdjoinRoot.root extPoly * AdjoinRoot.root extPoly) := by
    calc
      AdjoinRoot.of extPoly (QuadFelt.RESIDUE * x.im * y.im)
          = AdjoinRoot.of extPoly QuadFelt.RESIDUE *
              (AdjoinRoot.of extPoly x.im * AdjoinRoot.of extPoly y.im) := by
                simp [QuadFelt.RESIDUE, mul_left_comm, mul_comm]
      _ = (AdjoinRoot.root extPoly * AdjoinRoot.root extPoly) *
            (AdjoinRoot.of extPoly x.im * AdjoinRoot.of extPoly y.im) := by
              rw [← root_mul_root]
      _ = (AdjoinRoot.of extPoly x.im * AdjoinRoot.of extPoly y.im) *
            (AdjoinRoot.root extPoly * AdjoinRoot.root extPoly) := by
              ring_nf
  calc
    QuadFelt.toExtFelt (x * y)
        = AdjoinRoot.of extPoly (x.re * y.re) +
            AdjoinRoot.of extPoly (QuadFelt.RESIDUE * x.im * y.im) +
            (AdjoinRoot.of extPoly (x.re * y.im) * AdjoinRoot.root extPoly +
              AdjoinRoot.of extPoly (x.im * y.re) * AdjoinRoot.root extPoly) := by
              simp [QuadFelt.toExtFelt, map_add, add_mul]
    _ = AdjoinRoot.of extPoly (x.re * y.re) +
          (AdjoinRoot.of extPoly x.im * AdjoinRoot.of extPoly y.im) *
            (AdjoinRoot.root extPoly * AdjoinRoot.root extPoly) +
          (AdjoinRoot.of extPoly (x.re * y.im) * AdjoinRoot.root extPoly +
            AdjoinRoot.of extPoly (x.im * y.re) * AdjoinRoot.root extPoly) := by
              rw [hres]
    _ = QuadFelt.toExtFelt x * QuadFelt.toExtFelt y := by
          simp [QuadFelt.toExtFelt]
          ring_nf

@[simp] theorem toExtFelt_natCast (n : Nat) :
    QuadFelt.toExtFelt (n : QuadFelt) = (n : ExtFelt) := by
  change AdjoinRoot.of extPoly n + AdjoinRoot.of extPoly 0 * AdjoinRoot.root extPoly = n
  simp

@[simp] theorem toExtFelt_intCast (n : Int) :
    QuadFelt.toExtFelt (n : QuadFelt) = (n : ExtFelt) := by
  change AdjoinRoot.of extPoly n + AdjoinRoot.of extPoly 0 * AdjoinRoot.root extPoly = n
  simp

@[simp] theorem toExtFelt_nsmul (n : Nat) (x : QuadFelt) :
    QuadFelt.toExtFelt (n • x) = n • QuadFelt.toExtFelt x := by
  change AdjoinRoot.of extPoly (n • x.re) + AdjoinRoot.of extPoly (n • x.im) * AdjoinRoot.root extPoly =
    n • (AdjoinRoot.of extPoly x.re + AdjoinRoot.of extPoly x.im * AdjoinRoot.root extPoly)
  simp [QuadFelt.nsmul, QuadFelt.toExtFelt, smul_eq_mul, mul_add, mul_assoc, mul_left_comm, mul_comm]

@[simp] theorem toExtFelt_zsmul (n : Int) (x : QuadFelt) :
    QuadFelt.toExtFelt (n • x) = n • QuadFelt.toExtFelt x := by
  change AdjoinRoot.of extPoly (n • x.re) + AdjoinRoot.of extPoly (n • x.im) * AdjoinRoot.root extPoly =
    n • (AdjoinRoot.of extPoly x.re + AdjoinRoot.of extPoly x.im * AdjoinRoot.root extPoly)
  simp [QuadFelt.zsmul, QuadFelt.toExtFelt, zsmul_eq_mul, mul_add, mul_assoc, mul_left_comm, mul_comm]

@[simp] theorem toExtFelt_pow (x : QuadFelt) (n : Nat) :
    QuadFelt.toExtFelt (x ^ n) = QuadFelt.toExtFelt x ^ n := by
  show QuadFelt.toExtFelt (QuadFelt.pow x n) = QuadFelt.toExtFelt x ^ n
  induction n with
  | zero =>
      exact QuadFelt.toExtFelt_one
  | succ n ih =>
      change QuadFelt.toExtFelt (QuadFelt.pow x n * x) = QuadFelt.toExtFelt x ^ (n + 1)
      rw [QuadFelt.toExtFelt_mul, ih, pow_succ]

@[simp] theorem toPoly_sub (x y : QuadFelt) :
    x.toPoly - y.toPoly = C (x.im - y.im) * X + C (x.re - y.re) := by
  simp [QuadFelt.toPoly, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, right_distrib]

private theorem linear_natDegree_lt_extPoly (a b : Felt) :
    (C a * X + C b : Polynomial Felt).natDegree < extPoly.natDegree := by
  have hlin : (C a * X + C b : Polynomial Felt).natDegree ≤ 1 := Polynomial.natDegree_linear_le
  rw [extPoly_natDegree]
  exact lt_of_le_of_lt hlin (by decide)

theorem toExtFelt_injective : Function.Injective QuadFelt.toExtFelt := by
  intro x y hxy
  have hmk : AdjoinRoot.mk extPoly x.toPoly = AdjoinRoot.mk extPoly y.toPoly := by
    calc
      AdjoinRoot.mk extPoly x.toPoly = QuadFelt.toExtFelt x := (QuadFelt.toExtFelt_eq_mk x).symm
      _ = QuadFelt.toExtFelt y := hxy
      _ = AdjoinRoot.mk extPoly y.toPoly := QuadFelt.toExtFelt_eq_mk y
  have hzero : AdjoinRoot.mk extPoly (x.toPoly - y.toPoly) = 0 := by
    calc
      AdjoinRoot.mk extPoly (x.toPoly - y.toPoly)
          = AdjoinRoot.mk extPoly x.toPoly - AdjoinRoot.mk extPoly y.toPoly := by
              simpa using (map_sub (AdjoinRoot.mk extPoly) x.toPoly y.toPoly)
      _ = 0 := by
            simpa [hmk]
  have hdvd : extPoly ∣ x.toPoly - y.toPoly :=
    (AdjoinRoot.mk_eq_zero (f := extPoly) (g := x.toPoly - y.toPoly)).mp hzero
  rw [QuadFelt.toPoly_sub] at hdvd
  have hlin0 : (C (x.im - y.im) * X + C (x.re - y.re) : Polynomial Felt) = 0 := by
    exact Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd (linear_natDegree_lt_extPoly _ _)
  have hre : x.re - y.re = 0 := by
    have hcoeff := congrArg (fun p : Polynomial Felt => p.coeff 0) hlin0
    simpa using hcoeff
  have him : x.im - y.im = 0 := by
    have hcoeff := congrArg (fun p : Polynomial Felt => p.coeff 1) hlin0
    simpa using hcoeff
  ext
  · exact sub_eq_zero.mp hre
  · exact sub_eq_zero.mp him

noncomputable instance : CommRing QuadFelt :=
  Function.Injective.commRing QuadFelt.toExtFelt QuadFelt.toExtFelt_injective
    QuadFelt.toExtFelt_zero
    QuadFelt.toExtFelt_one
    QuadFelt.toExtFelt_add
    QuadFelt.toExtFelt_mul
    QuadFelt.toExtFelt_neg
    QuadFelt.toExtFelt_sub
    QuadFelt.toExtFelt_nsmul
    QuadFelt.toExtFelt_zsmul
    QuadFelt.toExtFelt_pow
    QuadFelt.toExtFelt_natCast
    QuadFelt.toExtFelt_intCast

/-- Bundled ring hom for the bridge into the abstract quotient ring. -/
noncomputable def toExtFeltRingHom : QuadFelt →+* ExtFelt where
  toFun := QuadFelt.toExtFelt
  map_zero' := QuadFelt.toExtFelt_zero
  map_one' := QuadFelt.toExtFelt_one
  map_add' := QuadFelt.toExtFelt_add
  map_mul' := QuadFelt.toExtFelt_mul

-- ============================================================================
-- Smoke tests
-- ============================================================================

-- Test: `(1, 0) * (1, 0) = (1, 0)`
#eval do
  let a : QuadFelt := ⟨1, 0⟩
  let r := a * a
  assert! r == (⟨1, 0⟩ : QuadFelt)
  return s!"(1,0) * (1,0) = ({r.re.val}, {r.im.val}) -- OK"

-- Test: `(0, 1) * (0, 1) = (7, 0)` since `x² = 7`
#eval do
  let x : QuadFelt := ⟨0, 1⟩
  let r := x * x
  assert! r == (⟨7, 0⟩ : QuadFelt)
  return s!"(0,1) * (0,1) = ({r.re.val}, {r.im.val}) -- OK (x² = 7)"

-- Test: `(1, 1) + (2, 3) = (3, 4)`
#eval do
  let a : QuadFelt := ⟨1, 1⟩
  let b : QuadFelt := ⟨2, 3⟩
  let r := a + b
  assert! r == (⟨3, 4⟩ : QuadFelt)
  return s!"(1,1) + (2,3) = ({r.re.val}, {r.im.val}) -- OK"

-- Test: `check_zero` on zero element returns true
#eval do
  let z : QuadFelt := 0
  assert! z.check_zero == true
  return s!"check_zero(0,0) = {z.check_zero} -- OK"

-- Test: `check_zero` on non-zero element returns false
#eval do
  let a : QuadFelt := ⟨1, 0⟩
  assert! a.check_zero == false
  return s!"check_zero(1,0) = {a.check_zero} -- OK"

-- Test: subtraction `(3, 4) - (1, 1) = (2, 3)`
#eval do
  let a : QuadFelt := ⟨3, 4⟩
  let b : QuadFelt := ⟨1, 1⟩
  let r := a - b
  assert! r == (⟨2, 3⟩ : QuadFelt)
  return s!"(3,4) - (1,1) = ({r.re.val}, {r.im.val}) -- OK"

-- Test: negation `-(2, 3) + (2, 3) = (0, 0)`
#eval do
  let a : QuadFelt := ⟨2, 3⟩
  let r := -a + a
  assert! r.check_zero
  return s!"-(2,3) + (2,3) = ({r.re.val}, {r.im.val}) -- OK (zero)"

end QuadFelt

end MidenLean
