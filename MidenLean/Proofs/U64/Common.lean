import MidenLean.Proofs.Helpers
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean

/-- Procedure environment for manual u64 proofs that call other u64 procedures. -/
def u64ProcEnv : ProcEnv := fun name =>
  match name with
  | "overflowing_add" => some Miden.Core.U64.overflowing_add
  | "gt" => some Miden.Core.U64.gt
  | "lt" => some Miden.Core.U64.lt
  | "divmod" => some Miden.Core.U64.divmod
  | "wrapping_mul" => some Miden.Core.U64.wrapping_mul
  | _ => none

-- ============================================================================
-- U64 type: a 64-bit unsigned integer as two u32 Felt limbs
-- ============================================================================

/-- A 64-bit unsigned integer represented as two u32 Felt limbs (little-endian).
    `lo` is the low 32-bit limb, `hi` is the high 32-bit limb.
    The u32 invariant is enforced by the structure fields. -/
structure U64 where
  lo : Felt
  hi : Felt
  lo_u32 : lo.isU32 = true
  hi_u32 : hi.isU32 = true

namespace U64

/-- Reconstruct the natural number value: `hi * 2^32 + lo`. -/
def toNat (x : U64) : Nat := x.hi.val * 2^32 + x.lo.val

theorem toNat_lt (x : U64) : x.toNat < 2^64 := by
  unfold toNat
  have hlo := x.lo_u32; have hhi := x.hi_u32
  simp only [Felt.isU32, decide_eq_true_eq] at *
  omega

theorem toNat_def (x : U64) : x.toNat = x.hi.val * 2^32 + x.lo.val := rfl

end U64

end MidenLean.Proofs
