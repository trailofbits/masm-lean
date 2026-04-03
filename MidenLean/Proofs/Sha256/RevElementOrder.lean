import MidenLean.Proofs.Tactics
import MidenLean.Generated.Sha256

namespace MidenLean.Proofs.Sha256

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `sha256::rev_element_order` reverses the order of the top 4 stack elements.
    Input stack:  [a, b, c, d] ++ rest
    Output stack: [d, c, b, a] ++ rest -/
theorem sha256_rev_element_order_correct
    (a b c d : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: b :: c :: d :: rest) :
    exec 8 s Miden.Core.Sha256.rev_element_order =
    some (s.withStack (d :: c :: b :: a :: rest)) := by
  miden_setup Miden.Core.Sha256.rev_element_order
  miden_swap
  miden_movup
  miden_movup
  simp only [pure, Pure.pure]

end MidenLean.Proofs.Sha256
