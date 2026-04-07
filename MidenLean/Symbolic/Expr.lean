import MidenLean.Semantics

/-!
# Symbolic Expressions

Minimal symbolic expression type. Each constructor's `eval` is definitionally
equal to what the corresponding concrete instruction computes.
-/

namespace MidenLean.Symbolic

/-- Variable assignment: maps variable indices to concrete Felt values. -/
abbrev Assignment := Nat → Felt

/-- Symbolic expression type. Each constructor's `eval` is definitionally equal
    to what the corresponding concrete instruction computes, making soundness
    cases provable by `rfl`. -/
inductive Expr where
  -- Variables and constants
  | var (idx : Nat)
  | lit (v : Felt)
  -- Field arithmetic
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  -- Field negation / inverse
  | neg (a : Expr)
  | inv (a : Expr)
  -- Field comparisons (produce 0 or 1 as Felt)
  | feltEq (a b : Expr)
  | feltNeq (a b : Expr)
  | feltLt (a b : Expr)
  | feltGt (a b : Expr)
  | feltLte (a b : Expr)
  | feltGte (a b : Expr)
  | feltIsOdd (a : Expr)
  -- Boolean Felt operations (operands assumed 0 or 1)
  | feltAnd (a b : Expr)
  | feltOr (a b : Expr)
  | feltXor (a b : Expr)
  | feltNot (a : Expr)
  -- U32 arithmetic (encapsulates the .val → Nat → Felt.ofNat round-trip)
  | u32AddLo (a b : Expr)
  | u32AddHi (a b : Expr)
  | u32SubDiff (a b : Expr)
  | u32SubBorrow (a b : Expr)
  -- U32 3-operand add
  | u32Add3Lo (a b c : Expr)
  | u32Add3Hi (a b c : Expr)
  -- U32 multiply
  | u32MulLo (a b : Expr)
  | u32MulHi (a b : Expr)
  -- U32 multiply-add
  | u32MaddLo (a b c : Expr)
  | u32MaddHi (a b c : Expr)
  -- U32 division
  | u32DivQuot (a b : Expr)
  | u32DivRem (a b : Expr)
  -- U32 bitwise
  | u32And (a b : Expr)
  | u32Or (a b : Expr)
  | u32Xor (a b : Expr)
  | u32Not (a : Expr)
  -- U32 shift/rotate
  | u32Shl (a b : Expr)
  | u32Shr (a b : Expr)
  | u32Rotl (a b : Expr)
  | u32Rotr (a b : Expr)
  -- U32 bit counting
  | u32Popcnt (a : Expr)
  | u32Clz (a : Expr)
  | u32Ctz (a : Expr)
  | u32Clo (a : Expr)
  | u32Cto (a : Expr)
  -- U32 comparison (produce 0 or 1)
  | u32Lt (a b : Expr)
  | u32Lte (a b : Expr)
  | u32Gt (a b : Expr)
  | u32Gte (a b : Expr)
  -- U32 min/max (select one value)
  | u32Min (a b : Expr)
  | u32Max (a b : Expr)
  -- Felt ↔ u32 boundary
  | lo32 (a : Expr)
  | hi32 (a : Expr)
  | pow2 (a : Expr)
  -- U32 wrapping ops (single result)
  | u32WAdd (a b : Expr)
  | u32WAdd3 (a b c : Expr)
  | u32WMul (a b : Expr)
  | u32WMadd (a b c : Expr)
  | u32WSub (a b : Expr)
  -- Word comparison (for eqw)
  | eqw4 (a0 a1 a2 a3 b0 b1 b2 b3 : Expr)
  -- Conditionals
  | ite (cond a b : Expr)
  deriving Repr, BEq, Inhabited

/-- Evaluate a symbolic expression under a concrete assignment. -/
def Expr.eval (σ : Assignment) : Expr → Felt
  | .var idx => σ idx
  | .lit v => v
  | .add a b => a.eval σ + b.eval σ
  | .sub a b => a.eval σ - b.eval σ
  | .mul a b => a.eval σ * b.eval σ
  | .neg a => -(a.eval σ)
  | .inv a => (a.eval σ)⁻¹
  | .feltEq a b =>
      if a.eval σ == b.eval σ then 1 else 0
  | .feltNeq a b =>
      if a.eval σ == b.eval σ then 0 else 1
  | .feltLt a b =>
      if (a.eval σ).val < (b.eval σ).val then 1 else 0
  | .feltGt a b =>
      if (a.eval σ).val > (b.eval σ).val then 1 else 0
  | .feltLte a b =>
      if (a.eval σ).val ≤ (b.eval σ).val then 1 else 0
  | .feltGte a b =>
      if (a.eval σ).val ≥ (b.eval σ).val then 1 else 0
  | .feltIsOdd a =>
      if (a.eval σ).val % 2 == 1 then 1 else 0
  | .feltAnd a b => a.eval σ * b.eval σ
  | .feltOr a b => a.eval σ + b.eval σ - a.eval σ * b.eval σ
  | .feltXor a b => a.eval σ + b.eval σ - 2 * a.eval σ * b.eval σ
  | .feltNot a => 1 - a.eval σ
  | .u32AddLo a b =>
      Felt.ofNat (((a.eval σ).val + (b.eval σ).val) % MidenLean.u32Max)
  | .u32AddHi a b =>
      Felt.ofNat (((a.eval σ).val + (b.eval σ).val) / MidenLean.u32Max)
  | .u32SubDiff a b =>
      Felt.ofNat (u32OverflowingSub (a.eval σ).val (b.eval σ).val).2
  | .u32SubBorrow a b =>
      Felt.ofNat (u32OverflowingSub (a.eval σ).val (b.eval σ).val).1
  | .u32Add3Lo a b c =>
      Felt.ofNat (((a.eval σ).val + (b.eval σ).val + (c.eval σ).val) % MidenLean.u32Max)
  | .u32Add3Hi a b c =>
      Felt.ofNat (((a.eval σ).val + (b.eval σ).val + (c.eval σ).val) / MidenLean.u32Max)
  | .u32MulLo a b =>
      Felt.ofNat (u32WideMul (a.eval σ).val (b.eval σ).val).1
  | .u32MulHi a b =>
      Felt.ofNat (u32WideMul (a.eval σ).val (b.eval σ).val).2
  | .u32MaddLo a b c =>
      Felt.ofNat (u32WideMadd (a.eval σ).val (b.eval σ).val (c.eval σ).val).1
  | .u32MaddHi a b c =>
      Felt.ofNat (u32WideMadd (a.eval σ).val (b.eval σ).val (c.eval σ).val).2
  | .u32DivQuot a b =>
      Felt.ofNat ((a.eval σ).val / (b.eval σ).val)
  | .u32DivRem a b =>
      Felt.ofNat ((a.eval σ).val % (b.eval σ).val)
  | .u32And a b =>
      Felt.ofNat (Nat.land (a.eval σ).val (b.eval σ).val)
  | .u32Or a b =>
      Felt.ofNat (Nat.lor (a.eval σ).val (b.eval σ).val)
  | .u32Xor a b =>
      Felt.ofNat (Nat.xor (a.eval σ).val (b.eval σ).val)
  | .u32Not a =>
      Felt.ofNat (MidenLean.u32Max - 1 - (a.eval σ).val)
  | .u32Shl a b =>
      Felt.ofNat (((a.eval σ).val * 2 ^ (b.eval σ).val) % MidenLean.u32Max)
  | .u32Shr a b =>
      Felt.ofNat ((a.eval σ).val / 2 ^ (b.eval σ).val)
  | .u32Rotl a b =>
      Felt.ofNat (u32RotateLeft (a.eval σ).val (b.eval σ).val)
  | .u32Rotr a b =>
      Felt.ofNat (u32RotateRight (a.eval σ).val (b.eval σ).val)
  | .u32Popcnt a =>
      Felt.ofNat (u32PopCount (a.eval σ).val)
  | .u32Clz a =>
      Felt.ofNat (u32CountLeadingZeros (a.eval σ).val)
  | .u32Ctz a =>
      Felt.ofNat (u32CountTrailingZeros (a.eval σ).val)
  | .u32Clo a =>
      Felt.ofNat (u32CountLeadingOnes (a.eval σ).val)
  | .u32Cto a =>
      Felt.ofNat (u32CountTrailingOnes (a.eval σ).val)
  | .u32Lt a b =>
      if (a.eval σ).val < (b.eval σ).val then 1 else 0
  | .u32Lte a b =>
      if (a.eval σ).val ≤ (b.eval σ).val then 1 else 0
  | .u32Gt a b =>
      if (a.eval σ).val > (b.eval σ).val then 1 else 0
  | .u32Gte a b =>
      if (a.eval σ).val ≥ (b.eval σ).val then 1 else 0
  | .u32Min a b =>
      if (a.eval σ).val ≤ (b.eval σ).val then a.eval σ else b.eval σ
  | .u32Max a b =>
      if (a.eval σ).val ≥ (b.eval σ).val then a.eval σ else b.eval σ
  | .lo32 a => (a.eval σ).lo32
  | .hi32 a => (a.eval σ).hi32
  | .pow2 a =>
      Felt.ofNat (2 ^ (a.eval σ).val)
  | .u32WAdd a b =>
      Felt.ofNat (((a.eval σ).val + (b.eval σ).val) % (2^32 : Nat))
  | .u32WAdd3 a b c =>
      Felt.ofNat (((a.eval σ).val + (b.eval σ).val + (c.eval σ).val) % (2^32 : Nat))
  | .u32WMul a b =>
      Felt.ofNat (((a.eval σ).val * (b.eval σ).val) % (2^32 : Nat))
  | .u32WMadd a b c =>
      Felt.ofNat (((a.eval σ).val * (b.eval σ).val + (c.eval σ).val) % (2^32 : Nat))
  | .u32WSub a b =>
      Felt.ofNat (u32OverflowingSub (a.eval σ).val (b.eval σ).val).2
  | .eqw4 a0 a1 a2 a3 b0 b1 b2 b3 =>
      if a0.eval σ == b0.eval σ && a1.eval σ == b1.eval σ &&
         a2.eval σ == b2.eval σ && a3.eval σ == b3.eval σ
      then (1 : Felt) else 0
  | .ite c a b =>
      if (c.eval σ).val == 1 then a.eval σ else b.eval σ

/-- Preconditions collected during symbolic execution. -/
inductive Precondition where
  | isU32 (e : Expr)
  | nonzero (e : Expr)
  | valLeq (e : Expr) (bound : Nat)
  | isBool (e : Expr)
  | eqZero (e : Expr)
  | eqOne (e : Expr)
  | feltEq (a b : Expr)
  deriving Repr, BEq

/-- Semantic interpretation of a precondition under a concrete assignment. -/
def Precondition.holds (p : Precondition) (σ : Assignment) : Prop :=
  match p with
  | .isU32 e => (e.eval σ).isU32 = true
  | .nonzero e => (e.eval σ == (0 : Felt)) = false
  | .valLeq e n => (e.eval σ).val ≤ n
  | .isBool e => (e.eval σ) = 0 ∨ (e.eval σ) = 1
  | .eqZero e => (e.eval σ) = 0
  | .eqOne e => (e.eval σ) = 1
  | .feltEq a b => (a.eval σ) = (b.eval σ)

end MidenLean.Symbolic
