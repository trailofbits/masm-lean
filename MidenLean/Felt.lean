import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

namespace MidenLean

/-- The Goldilocks prime: p = 2^64 - 2^32 + 1 -/
def GOLDILOCKS_PRIME : Nat := 2^64 - 2^32 + 1

/-- Miden field element type. -/
abbrev Felt := ZMod GOLDILOCKS_PRIME

-- This is the one remaining `native_decide` in the library, and it puts
-- `Lean.ofReduceBool`/`Lean.trustCompiler` into the axiom footprint of every
-- theorem that touches `Felt` (via this `Fact` instance). A kernel-checked
-- alternative was attempted (`norm_num` Pratt certificate for the primality
-- of 2^64 - 2^32 + 1) but did not finish within an hour of kernel checking;
-- removing this axiom would need a precomputed, inlined primality
-- certificate.
set_option maxHeartbeats 800000 in
instance : Fact (Nat.Prime GOLDILOCKS_PRIME) := ⟨by native_decide⟩

/-- The canonical natural number representative of a field element. -/
def Felt.IsU32 (a : Felt) : Prop :=
  a.val < 2^32

/-- Boolean check for whether a felt fits in 32 bits. -/
def Felt.isU32 (a : Felt) : Bool :=
  a.val < 2^32

/-- Boolean check for whether a felt is 0 or 1 (a boolean). -/
def Felt.isBool (a : Felt) : Bool :=
  a.val == 0 || a.val == 1

/-- Convert a natural number to a felt. -/
def Felt.ofNat (n : Nat) : Felt := (n : Felt)

/-- The low 32 bits of a felt's canonical representative. -/
def Felt.lo32 (a : Felt) : Felt := Felt.ofNat (a.val % 2^32)

/-- The high 32 bits of a felt's canonical representative. -/
def Felt.hi32 (a : Felt) : Felt := Felt.ofNat (a.val / 2^32)

end MidenLean
