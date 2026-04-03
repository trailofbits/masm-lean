import MidenLean.Proofs.Tactics
import MidenLean.Generated.Sha256

namespace MidenLean.Proofs.Sha256

open MidenLean

/-- Procedure environment for sha256 proofs that call other sha256 procedures. -/
def sha256ProcEnv : ProcEnv := fun name =>
  match name with
  | "small_sigma_0" => some Miden.Core.Sha256.small_sigma_0
  | "small_sigma_1" => some Miden.Core.Sha256.small_sigma_1
  | "cap_sigma_0"   => some Miden.Core.Sha256.cap_sigma_0
  | "cap_sigma_1"   => some Miden.Core.Sha256.cap_sigma_1
  | "ch"            => some Miden.Core.Sha256.ch
  | "maj"           => some Miden.Core.Sha256.maj
  | "compute_message_schedule_word" => some Miden.Core.Sha256.compute_message_schedule_word
  | "consume_message_word"          => some Miden.Core.Sha256.consume_message_word
  | "rev_element_order"             => some Miden.Core.Sha256.rev_element_order
  | "prepare_message_schedule_and_consume" =>
      some Miden.Core.Sha256.prepare_message_schedule_and_consume
  | "consume_padding_message_schedule" =>
      some Miden.Core.Sha256.consume_padding_message_schedule
  | _ => none

end MidenLean.Proofs.Sha256
