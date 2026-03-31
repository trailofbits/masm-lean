/-!
# SHA-256 Block Compression Specification

Pure mathematical specification of SHA-256 following NIST FIPS 180-4.
Adapted from https://github.com/trailofbits/scroll-sha256-fv
-/

namespace Sha256Spec

/-! ## Basic types -/

abbrev Word := BitVec 32

/-! ## Bitwise helper operations -/

/-- Right rotation of a 32-bit word by `n` positions. -/
def rotr (x : Word) (n : Nat) : Word :=
  let n := n % 32
  (x >>> n) ||| (x <<< ((32 - n) % 32))

/-- Right shift of a 32-bit word by `n` positions. -/
def shr (x : Word) (n : Nat) : Word :=
  x >>> n

/-! ## SHA-256 logical functions (FIPS 180-4 Section 4.1.2) -/

/-- Ch(x, y, z) = (x AND y) XOR (NOT x AND z) -/
def ch (x y z : Word) : Word :=
  (x &&& y) ^^^ (~~~x &&& z)

/-- Maj(x, y, z) = (x AND y) XOR (x AND z) XOR (y AND z) -/
def maj (x y z : Word) : Word :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Σ₀(x) = ROTR²(x) XOR ROTR¹³(x) XOR ROTR²²(x) -/
def bigSigma0 (x : Word) : Word :=
  rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22

/-- Σ₁(x) = ROTR⁶(x) XOR ROTR¹¹(x) XOR ROTR²⁵(x) -/
def bigSigma1 (x : Word) : Word :=
  rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

/-- σ₀(x) = ROTR⁷(x) XOR ROTR¹⁸(x) XOR SHR³(x) -/
def smallSigma0 (x : Word) : Word :=
  rotr x 7 ^^^ rotr x 18 ^^^ shr x 3

/-- σ₁(x) = ROTR¹⁷(x) XOR ROTR¹⁹(x) XOR SHR¹⁰(x) -/
def smallSigma1 (x : Word) : Word :=
  rotr x 17 ^^^ rotr x 19 ^^^ shr x 10

/-! ## Message schedule (FIPS 180-4 Section 6.2.2) -/

/-- W[t] = σ₁(W[t-2]) + σ₀(W[t-15]) + W[t-16] + W[t-7]  for 16 ≤ t ≤ 63. -/
def messageScheduleWord (w_t2 w_t15 w_t16 w_t7 : Word) : Word :=
  smallSigma1 w_t2 + smallSigma0 w_t15 + w_t16 + w_t7

end Sha256Spec
