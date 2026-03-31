import MidenLean.Generated.Sha256

namespace MidenLean.Proofs

open MidenLean

/-- Procedure environment for SHA-256 proofs that call other SHA-256 procedures. -/
def sha256ProcEnv : ProcEnv := fun name =>
  match name with
  | "small_sigma_0" => some Miden.Crypto.Sha256.small_sigma_0
  | "small_sigma_1" => some Miden.Crypto.Sha256.small_sigma_1
  | "cap_sigma_0" => some Miden.Crypto.Sha256.cap_sigma_0
  | "cap_sigma_1" => some Miden.Crypto.Sha256.cap_sigma_1
  | "ch" => some Miden.Crypto.Sha256.ch
  | "maj" => some Miden.Crypto.Sha256.maj
  | "rev_element_order" => some Miden.Crypto.Sha256.rev_element_order
  | "compute_message_schedule_word" => some Miden.Crypto.Sha256.compute_message_schedule_word
  | "consume_message_word" => some Miden.Crypto.Sha256.consume_message_word
  | "prepare_message_schedule_and_consume" => some Miden.Crypto.Sha256.prepare_message_schedule_and_consume
  | "consume_padding_message_schedule" => some Miden.Crypto.Sha256.consume_padding_message_schedule
  | _ => none

end MidenLean.Proofs
