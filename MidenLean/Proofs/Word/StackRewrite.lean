import MidenLean.Proofs.Helpers
import MidenLean.Proofs.StepLemmas
import MidenLean.Spec.WordOrder

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas

/-- Raw `reversew` reverses the top word and preserves the tail exactly. -/
theorem reversew_exact
    (mem locs : Nat → Felt) (adv : List Felt)
    (a b c d : Felt) (tail : List Felt) :
    execInstruction ⟨stackWord a b c d ++ tail, mem, locs, adv⟩ .reversew =
      some ⟨stackWord d c b a ++ tail, mem, locs, adv⟩ := by
  simpa [stackWord] using stepReversew mem locs adv a b c d tail

/-- Raw `reversedw` reverses the top double word and preserves the tail exactly. -/
theorem reversedw_exact
    (mem locs : Nat → Felt) (adv : List Felt)
    (a b c d e f g h : Felt) (tail : List Felt) :
    execInstruction ⟨stackDWord a b c d e f g h ++ tail, mem, locs, adv⟩ .reversedw =
      some ⟨stackDWord h g f e d c b a ++ tail, mem, locs, adv⟩ := by
  simpa [stackDWord] using stepReversedw mem locs adv a b c d e f g h tail

end MidenLean.Proofs
