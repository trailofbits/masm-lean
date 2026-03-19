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

end MidenLean.Proofs
