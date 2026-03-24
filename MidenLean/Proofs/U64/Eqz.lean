import MidenLean.Proofs.U64.Common
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 4000000 in
/-- `u64::eqz` tests whether a u64 value is zero, limb by limb.
    Input stack:  [lo, hi] ++ rest
    Output stack: [is_zero] ++ rest
    where is_zero = 1 iff both input limbs are zero. -/
theorem u64_eqz_raw
    (lo hi : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = lo :: hi :: rest) :
    exec 9 s Miden.Core.U64.eqz =
    some (s.withStack (
      (if (lo == (0 : Felt)) && (hi == (0 : Felt))
       then (1 : Felt) else 0) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U64.eqz execWithEnv
  simp only [List.foldlM]
  rw [stepEqImm]
  miden_bind
  miden_swap
  rw [stepEqImm]
  miden_bind
  rw [stepAndIte]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]

/-- `u64::eqz` correctly tests whether a u64 value is zero.
    Input stack:  [a.lo, a.hi] ++ rest
    Output stack: [if a == 0 then 1 else 0] ++ rest -/
theorem u64_eqz_correct (a : U64) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a.lo :: a.hi :: rest) :
    exec 9 s Miden.Core.U64.eqz =
    some (s.withStack (
      (if a == U64.ofNat 0 then (1 : Felt) else 0) :: rest)) := by
  simp only [U64.beq_iff, U64.ofNat]
  exact u64_eqz_raw a.lo a.hi rest s hs

end MidenLean.Proofs
