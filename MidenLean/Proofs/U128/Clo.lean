import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- `u128::clo` correctly counts leading ones of a u128 value.
    Input stack:  [a, b, c, d] ++ rest
    Output stack: [result] ++ rest
    where `a..d` are low-to-high u32 limbs and the result is the number of
    leading one bits in the 128-bit value. -/
theorem u128_clo_correct
    (a b c d : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: b :: c :: d :: rest)
    (ha : a.isU32 = true) (hb : b.isU32 = true)
    (hc : c.isU32 = true) (hd : d.isU32 = true) :
    exec 33 s Miden.Core.U128.clo =
    some (s.withStack (
      (if d == (4294967295 : Felt) then
        if c == (4294967295 : Felt) then
          if b == (4294967295 : Felt) then
            Felt.ofNat (u32CountLeadingZeros (u32Max - 1 - a.val)) + 96
          else
            Felt.ofNat (u32CountLeadingZeros (u32Max - 1 - b.val)) + 64
        else
          Felt.ofNat (u32CountLeadingZeros (u32Max - 1 - c.val)) + 32
      else
        Felt.ofNat (u32CountLeadingZeros (u32Max - 1 - d.val))) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U128.clo execWithEnv
  simp only [List.foldlM]
  miden_movup
  miden_dup
  rw [stepEqImm]
  miden_bind
  by_cases hd1 : d == (4294967295 : Felt)
  · simp [hd1, MidenState.withStack]
    unfold execWithEnv
    simp only [List.foldlM]
    rw [stepDrop]
    miden_bind
    miden_movup
    miden_dup
    rw [stepEqImm]
    miden_bind
    by_cases hc1 : c == (4294967295 : Felt)
    · simp [hc1, MidenState.withStack]
      unfold execWithEnv
      simp only [List.foldlM]
      rw [stepDrop]
      miden_bind
      miden_swap
      miden_dup
      rw [stepEqImm]
      miden_bind
      by_cases hb1 : b == (4294967295 : Felt)
      · simp [hb1, MidenState.withStack]
        unfold execWithEnv
        simp only [List.foldlM]
        rw [stepDrop]
        miden_bind
        rw [stepU32Clo (ha := ha)]
        miden_bind
        rw [stepAddImm]
        have hc_eq : c = 4294967295 := by exact beq_iff_eq.mp hc1
        have hb_eq : b = 4294967295 := by exact beq_iff_eq.mp hb1
        simp [hc_eq, hb_eq]
      · simp [hb1, MidenState.withStack]
        unfold execWithEnv
        simp only [List.foldlM]
        simp (config := { decide := true }) only [bind, Bind.bind, Option.bind, pure, Pure.pure]
        rw [stepSwap (hn := by decide) (htop := rfl) (hnth := rfl)]
        miden_bind
        rw [stepDrop]
        miden_bind
        rw [stepU32Clo (ha := hb)]
        miden_bind
        rw [stepAddImm]
        have hc_eq : c = 4294967295 := by exact beq_iff_eq.mp hc1
        have hb_ne : b ≠ 4294967295 := by
          intro hb_eq
          exact hb1 (by simp [hb_eq])
        simp [hc_eq, hb_ne]
    · simp [hc1, MidenState.withStack]
      unfold execWithEnv
      simp only [List.foldlM]
      simp (config := { decide := true }) only [bind, Bind.bind, Option.bind, pure, Pure.pure]
      miden_movdn
      rw [stepDrop]
      miden_bind
      rw [stepDrop]
      miden_bind
      rw [stepU32Clo (ha := hc)]
      miden_bind
      rw [stepAddImm]
      have hc_ne : c ≠ 4294967295 := by
        intro hc_eq
        exact hc1 (by simp [hc_eq])
      simp [hc_ne]
  · simp [hd1, MidenState.withStack]
    unfold execWithEnv
    simp only [List.foldlM]
    simp (config := { decide := true }) only [bind, Bind.bind, Option.bind, pure, Pure.pure]
    miden_movdn
    rw [stepDrop]
    miden_bind
    rw [stepDrop]
    miden_bind
    rw [stepDrop]
    miden_bind
    rw [stepU32Clo (ha := hd)]

end MidenLean.Proofs
