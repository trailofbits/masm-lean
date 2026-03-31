import MidenLean.Proofs.Helpers
import MidenLean.Proofs.StepLemmas
import MidenLean.Spec.WordOrder

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas

/-- Raw `reversew` reverses the top word and preserves the tail exactly. -/
theorem reversew_exact
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b c d : Felt) (tail : List Felt) :
    execInstruction ⟨stackWord a b c d ++ tail, mem, frames, adv⟩ .reversew =
      some ⟨stackWord d c b a ++ tail, mem, frames, adv⟩ := by
  simpa [stackWord] using stepReversew mem frames adv a b c d tail

/-- Raw `reversedw` reverses the top double word and preserves the tail exactly. -/
theorem reversedw_exact
    (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b c d e f g h : Felt) (tail : List Felt) :
    execInstruction ⟨stackDWord a b c d e f g h ++ tail, mem, frames, adv⟩ .reversedw =
      some ⟨stackDWord h g f e d c b a ++ tail, mem, frames, adv⟩ := by
  unfold execInstruction execReversedw
  simp [stackDWord, MidenState.withStack]

end MidenLean.Proofs
