import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

set_option maxHeartbeats 12000000 in
/-- `u128::clz` correctly counts leading zeros of a u128 value (raw limb version).
    Input stack:  [a, b, c, d] ++ rest
    Output stack: [result] ++ rest
    where `a..d` are low-to-high u32 limbs and the result is the number of
    leading zero bits in the 128-bit value. -/
theorem u128_clz_raw
    (a b c d : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a :: b :: c :: d :: rest)
    (ha : a.isU32 = true) (hb : b.isU32 = true)
    (hc : c.isU32 = true) (hd : d.isU32 = true) :
    exec 33 s Miden.Core.U128.clz =
    some (s.withStack (
      (if d == (0 : Felt) then
        if c == (0 : Felt) then
          if b == (0 : Felt) then
            Felt.ofNat (u32CountLeadingZeros a.val) + 96
          else
            Felt.ofNat (u32CountLeadingZeros b.val) + 64
        else
          Felt.ofNat (u32CountLeadingZeros c.val) + 32
      else
        Felt.ofNat (u32CountLeadingZeros d.val)) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  unfold exec Miden.Core.U128.clz execWithEnv
  simp only [List.foldlM]
  miden_movup
  miden_dup
  rw [stepEqImm]
  miden_bind
  by_cases hd0 : d == (0 : Felt)
  · simp [hd0, MidenState.withStack]
    unfold execWithEnv
    simp only [List.foldlM]
    rw [stepDrop]
    miden_bind
    miden_movup
    miden_dup
    rw [stepEqImm]
    miden_bind
    by_cases hc0 : c == (0 : Felt)
    · simp [hc0, MidenState.withStack]
      unfold execWithEnv
      simp only [List.foldlM]
      rw [stepDrop]
      miden_bind
      miden_swap
      miden_dup
      rw [stepEqImm]
      miden_bind
      by_cases hb0 : b == (0 : Felt)
      · simp [hb0, MidenState.withStack]
        unfold execWithEnv
        simp only [List.foldlM]
        rw [stepDrop]
        miden_bind
        rw [stepU32Clz (ha := ha)]
        miden_bind
        rw [stepAddImm]
        have hc_eq : c = 0 := by exact beq_iff_eq.mp hc0
        have hb_eq : b = 0 := by exact beq_iff_eq.mp hb0
        simp [hc_eq, hb_eq]
      · simp [hb0, MidenState.withStack]
        unfold execWithEnv
        simp only [List.foldlM]
        simp (config := { decide := true }) only [bind, Bind.bind, Option.bind, pure, Pure.pure]
        rw [stepSwap (hn := by decide) (htop := rfl) (hnth := rfl)]
        miden_bind
        rw [stepDrop]
        miden_bind
        rw [stepU32Clz (ha := hb)]
        miden_bind
        rw [stepAddImm]
        have hc_eq : c = 0 := by exact beq_iff_eq.mp hc0
        have hb_ne : b ≠ 0 := by
          intro hb_eq
          exact hb0 (by simp [hb_eq])
        simp [hc_eq, hb_ne]
    · simp [hc0, MidenState.withStack]
      unfold execWithEnv
      simp only [List.foldlM]
      simp (config := { decide := true }) only [bind, Bind.bind, Option.bind, pure, Pure.pure]
      miden_movdn
      rw [stepDrop]
      miden_bind
      rw [stepDrop]
      miden_bind
      rw [stepU32Clz (ha := hc)]
      miden_bind
      rw [stepAddImm]
      have hc_ne : c ≠ 0 := by
        intro hc_eq
        exact hc0 (by simp [hc_eq])
      simp [hc_ne]
  · simp [hd0, MidenState.withStack]
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
    rw [stepU32Clz (ha := hd)]

/-- `u128::clz` pushes the count of leading zeros of a 128-bit value.
    Input stack:  [a.a0, a.a1, a.a2, a.a3] ++ rest
    Output stack: [countLeadingZeros a] ++ rest -/
theorem u128_clz_correct (a : U128) (rest : List Felt) (s : MidenState)
    (hs : s.stack = a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest) :
    exec 33 s Miden.Core.U128.clz =
    some (s.withStack (Felt.ofNat (U128.countLeadingZeros a) :: rest)) := by
  have h := u128_clz_raw a.a0.val a.a1.val a.a2.val a.a3.val rest s hs
    a.a0.isU32 a.a1.isU32 a.a2.isU32 a.a3.isU32
  unfold U128.countLeadingZeros
  by_cases h3 : a.a3.val.val = 0
  · rw [if_pos h3]
    have : a.a3.val = (0 : Felt) := Fin.ext h3
    simp only [this, beq_self_eq_true, ite_true] at h
    by_cases h2 : a.a2.val.val = 0
    · rw [if_pos h2]
      have : a.a2.val = (0 : Felt) := Fin.ext h2
      simp only [this, beq_self_eq_true, ite_true] at h
      by_cases h1 : a.a1.val.val = 0
      · rw [if_pos h1, felt_ofNat_add]
        have : a.a1.val = (0 : Felt) := Fin.ext h1
        simp only [this, beq_self_eq_true, ite_true] at h; exact h
      · rw [if_neg h1, felt_ofNat_add]
        have : a.a1.val ≠ (0 : Felt) := fun heq => h1 (by rw [heq]; rfl)
        simp only [show (a.a1.val == (0 : Felt)) = false from decide_eq_false this] at h
        exact h
    · rw [if_neg h2, felt_ofNat_add]
      have : a.a2.val ≠ (0 : Felt) := fun heq => h2 (by rw [heq]; rfl)
      simp only [show (a.a2.val == (0 : Felt)) = false from decide_eq_false this] at h
      exact h
  · rw [if_neg h3]
    have : a.a3.val ≠ (0 : Felt) := fun heq => h3 (by rw [heq]; rfl)
    simp only [show (a.a3.val == (0 : Felt)) = false from decide_eq_false this] at h
    exact h

end MidenLean.Proofs
