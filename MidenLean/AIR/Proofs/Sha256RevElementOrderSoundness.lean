import MidenLean.Proofs.Sha256.RevElementOrder

namespace MidenLean.AIR.Proofs.Sha256RevElementOrderSoundness

open MidenLean

/-- Reindex positions `2..15` as `Fin 14`. -/
private def pos2 (i : Fin 14) : Fin 16 :=
  ⟨i.val + 2, by
    have hi := i.isLt
    omega⟩

/-- Reindex positions `3..15` as `Fin 13`. -/
private def pos3 (i : Fin 13) : Fin 16 :=
  ⟨i.val + 3, by
    have hi := i.isLt
    omega⟩

/-- Reindex positions `4..15` as `Fin 12`. -/
private def pos4 (i : Fin 12) : Fin 16 :=
  ⟨i.val + 4, by
    have hi := i.isLt
    omega⟩

/-- Full visible-stack model for `swap`. -/
private def air_swap_full_model (s s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 1 ∧
  s' 1 = s 0 ∧
  ∀ i : Fin 14, s' (pos2 i) = s (pos2 i)

/-- Full visible-stack model for `movup.2`. -/
private def air_movup2_full_model (s s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 2 ∧
  s' 1 = s 0 ∧
  s' 2 = s 1 ∧
  ∀ i : Fin 13, s' (pos3 i) = s (pos3 i)

/-- Full visible-stack model for `movup.3`. -/
private def air_movup3_full_model (s s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 3 ∧
  s' 1 = s 0 ∧
  s' 2 = s 1 ∧
  s' 3 = s 2 ∧
  ∀ i : Fin 12, s' (pos4 i) = s (pos4 i)

/-- Canonical visible-stack output for `swap`: exchange the top two elements
and leave positions `2..15` unchanged. -/
private def swapTop2Out (s : Fin 16 → Felt) (i : Fin 16) : Felt :=
  if i.val = 0 then s 1
  else if i.val = 1 then s 0
  else s i

/-- Canonical visible-stack output for `movup.2`. -/
private def movup2Out (s : Fin 16 → Felt) (i : Fin 16) : Felt :=
  if i.val = 0 then s 2
  else if i.val = 1 then s 0
  else if i.val = 2 then s 1
  else s i

/-- Canonical visible-stack output for `movup.3`. -/
private def movup3Out (s : Fin 16 → Felt) (i : Fin 16) : Felt :=
  if i.val = 0 then s 3
  else if i.val = 1 then s 0
  else if i.val = 2 then s 1
  else if i.val = 3 then s 2
  else s i

/-- Canonical visible-stack output for the full `rev_element_order` helper. -/
def revElementOrderAirOut (s : Fin 16 → Felt) : Fin 16 → Felt :=
  movup3Out (movup2Out (swapTop2Out s))

/-- Layer-3 AIR acceptance relation for the visible-stack slice of the lowered
`rev_element_order` helper. This composes the full visible-stack relations for:

- `swap`
- `movup.2`
- `movup.3`

This is intentionally a local visible-stack claim, not a whole-VM verifier
theorem with overflow-stack wiring. -/
def revElementOrderAirAccepts (s s' : Fin 16 → Felt) : Prop :=
  ∃ s1 s2,
    air_swap_full_model s s1 ∧
    air_movup2_full_model s1 s2 ∧
    air_movup3_full_model s2 s'

/-- State-level visible-stack spec enforced by the modeled AIR slice. -/
def sha256_rev_element_order_visible_spec (s s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 3 ∧
  s' 1 = s 2 ∧
  s' 2 = s 1 ∧
  s' 3 = s 0 ∧
  ∀ i : Fin 12, s' (pos4 i) = s (pos4 i)

private theorem swapTop2Out_accepts (s : Fin 16 → Felt) :
    air_swap_full_model s (swapTop2Out s) := by
  refine ⟨by simp [swapTop2Out], by simp [swapTop2Out], ?_⟩
  intro i
  simp [swapTop2Out, pos2]

private theorem movup2Out_accepts (s : Fin 16 → Felt) :
    air_movup2_full_model s (movup2Out s) := by
  refine ⟨by simp [movup2Out], by simp [movup2Out], by simp [movup2Out], ?_⟩
  intro i
  simp [movup2Out, pos3]

private theorem movup3Out_accepts (s : Fin 16 → Felt) :
    air_movup3_full_model s (movup3Out s) := by
  refine ⟨by simp [movup3Out], by simp [movup3Out], by simp [movup3Out],
    by simp [movup3Out], ?_⟩
  intro i
  simp [movup3Out, pos4]

/-- Completeness for the modeled visible-stack AIR slice: the canonical
reversal witness is accepted. -/
theorem sha256_rev_element_order_layer3_visible_complete
    (s : Fin 16 → Felt) :
    revElementOrderAirAccepts s (revElementOrderAirOut s) := by
  refine ⟨swapTop2Out s, movup2Out (swapTop2Out s), ?_, ?_, ?_⟩
  · exact swapTop2Out_accepts s
  · exact movup2Out_accepts (swapTop2Out s)
  · exact movup3Out_accepts (movup2Out (swapTop2Out s))

/-- The canonical visible-stack witness satisfies the expected permutation
spec. -/
theorem sha256_rev_element_order_layer3_visible_out_spec
    (s : Fin 16 → Felt) :
    sha256_rev_element_order_visible_spec s (revElementOrderAirOut s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [revElementOrderAirOut, movup3Out, movup2Out, swapTop2Out]
  · simp [revElementOrderAirOut, movup3Out, movup2Out, swapTop2Out]
  · simp [revElementOrderAirOut, movup3Out, movup2Out, swapTop2Out]
  · simp [revElementOrderAirOut, movup3Out, movup2Out, swapTop2Out]
  · intro i
    simp [revElementOrderAirOut, movup3Out, movup2Out, swapTop2Out, pos4]

/-- Any accepted visible-stack AIR witness for the lowered `rev_element_order`
helper enforces the expected top-4 reversal and preserves visible positions
`4..15`. -/
theorem sha256_rev_element_order_layer3_visible_sound
    {s s' : Fin 16 → Felt} (hacc : revElementOrderAirAccepts s s') :
    sha256_rev_element_order_visible_spec s s' := by
  rcases hacc with ⟨s1, s2, hswap, hmov2, hmov3⟩
  rcases hswap with ⟨hswap0, hswap1, hswap_rest⟩
  rcases hmov2 with ⟨hmov20, hmov21, hmov22, hmov2rest⟩
  rcases hmov3 with ⟨hmov30, hmov31, hmov32, hmov33, hmov3rest⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hswap3 : s1 3 = s 3 := by
      simpa using hswap_rest ⟨1, by decide⟩
    have hmov23 : s2 3 = s1 3 := by
      simpa using hmov2rest ⟨0, by decide⟩
    rw [hmov30, hmov23, hswap3]
  · have hswap2 : s1 2 = s 2 := by
      simpa using hswap_rest ⟨0, by decide⟩
    rw [hmov31, hmov20, hswap2]
  · rw [hmov32, hmov21, hswap0]
  · rw [hmov33, hmov22, hswap1]
  · intro i
    have hmov3_i : s' (pos4 i) = s2 (pos4 i) := hmov3rest i
    have hmov2_i : s2 (pos4 i) = s1 (pos4 i) := by
      have h := hmov2rest ⟨i.val + 1, by
        have hi := i.isLt
        omega⟩
      simpa [pos3, pos4] using h
    have hswap_i : s1 (pos4 i) = s (pos4 i) := by
      have h := hswap_rest ⟨i.val + 2, by
        have hi := i.isLt
        omega⟩
      simpa [pos2, pos4] using h
    rw [hmov3_i, hmov2_i, hswap_i]

/-- Existence form of Layer-3 completeness for the modeled visible-stack slice:
for every visible input stack, there is an accepted witness satisfying the
expected permutation spec. -/
theorem sha256_rev_element_order_layer3_visible_total
    (s : Fin 16 → Felt) :
    ∃ s', revElementOrderAirAccepts s s' ∧ sha256_rev_element_order_visible_spec s s' := by
  exact ⟨revElementOrderAirOut s,
    sha256_rev_element_order_layer3_visible_complete s,
    sha256_rev_element_order_layer3_visible_out_spec s⟩

end MidenLean.AIR.Proofs.Sha256RevElementOrderSoundness
