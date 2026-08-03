import MidenLean.Proofs.Tactics
import MidenLean.Generated.Word

/-!
# Shared definitions for the `word` proof module

This file collects the pieces that several `word` proofs need:

* `wordProcEnv`, the procedure environment used by the word comparison
  procedures (`gt`, `lt`, `gte`, `lte`), which call each other and
  `arrange_words_adjacent_le`.
-/

namespace MidenLean.Proofs

open MidenLean
open MidenLean.Tactics

/-- Procedure environment for word comparison procedures. -/
def wordProcEnv : ProcEnv := fun name =>
  match name with
  | "arrange_words_adjacent_le" => some Miden.Core.Word.arrange_words_adjacent_le
  | "lt" => some Miden.Core.Word.lt
  | "gt" => some Miden.Core.Word.gt
  | _ => none

end MidenLean.Proofs
