import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean

/-- Procedure environment for manual u128 proofs that call other u128 procedures. -/
def u128ProcEnv : ProcEnv := fun name =>
  match name with
  | "overflowing_add" => some Miden.Core.U128.overflowing_add
  | "overflowing_sub" => some Miden.Core.U128.overflowing_sub
  | "overflowing_mul" => some Miden.Core.U128.overflowing_mul
  | "gt" => some Miden.Core.U128.gt
  | "gte" => some Miden.Core.U128.gte
  | "lt" => some Miden.Core.U128.lt
  | "lte" => some Miden.Core.U128.lte
  | "max" => some Miden.Core.U128.max
  | "min" => some Miden.Core.U128.min
  | "wrapping_mul" => some Miden.Core.U128.wrapping_mul
  | "shr_k0" => some Miden.Core.U128.shr_k0
  | "shr_k1" => some Miden.Core.U128.shr_k1
  | "shr_k2" => some Miden.Core.U128.shr_k2
  | "shr_k3" => some Miden.Core.U128.shr_k3
  | "shl" => some Miden.Core.U128.shl
  | "shr" => some Miden.Core.U128.shr
  | "divmod" => some Miden.Core.U128.divmod
  | _ => none

def u128Sub0 (a0 b0 : Felt) : Nat × Nat :=
  u32OverflowingSub a0.val b0.val

def u128Sub1 (a1 b1 : Felt) : Nat × Nat :=
  u32OverflowingSub a1.val b1.val

def u128Borrow1 (a0 a1 b0 b1 : Felt) : Felt :=
  if decide ((u128Sub1 a1 b1).2 < (u128Sub0 a0 b0).1) || decide (a1.val < b1.val) then
    1
  else
    0

def u128Sub2 (a2 b2 : Felt) : Nat × Nat :=
  u32OverflowingSub a2.val b2.val

def u128Borrow2 (a0 a1 a2 b0 b1 b2 : Felt) : Felt :=
  if decide ((u128Sub2 a2 b2).2 < (u128Borrow1 a0 a1 b0 b1).val) || decide (a2.val < b2.val) then
    1
  else
    0

def u128Sub3 (a3 b3 : Felt) : Nat × Nat :=
  u32OverflowingSub a3.val b3.val

def u128LtBool (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) : Bool :=
  decide ((u128Sub3 a3 b3).2 < (u128Borrow2 a0 a1 a2 b0 b1 b2).val) || decide (a3.val < b3.val)

def u128GtBool (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) : Bool :=
  u128LtBool b0 b1 b2 b3 a0 a1 a2 a3

end MidenLean.Proofs
