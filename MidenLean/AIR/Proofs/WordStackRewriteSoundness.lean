import MidenLean.Proofs.Word.StackRewrite

namespace MidenLean.AIR.Proofs.WordStackRewriteSoundness

open MidenLean

/--
Reindex positions `2..15` as `Fin 14`.
-/
private def pos2 (i : Fin 14) : Fin 16 :=
  ⟨i.val + 2, by
    have hi := i.isLt
    omega⟩

/--
Reindex positions `3..15` as `Fin 13`.
-/
private def pos3 (i : Fin 13) : Fin 16 :=
  ⟨i.val + 3, by
    have hi := i.isLt
    omega⟩

/--
Reindex positions `4..15` as `Fin 12`.
-/
private def pos4 (i : Fin 12) : Fin 16 :=
  ⟨i.val + 4, by
    have hi := i.isLt
    omega⟩

/--
Reindex positions `8..15` as `Fin 8`.
-/
private def pos8 (i : Fin 8) : Fin 16 :=
  ⟨i.val + 8, by
    have hi := i.isLt
    omega⟩

/-- Full visible-stack model for `movdn.3`. -/
private def air_movdn3_full_model (s s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 1 ∧
  s' 1 = s 2 ∧
  s' 2 = s 3 ∧
  s' 3 = s 0 ∧
  ∀ i : Fin 12, s' (pos4 i) = s (pos4 i)

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

/-- Full visible-stack model for `swapw`. -/
private def air_swapw_full_model (s s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 4 ∧
  s' 1 = s 5 ∧
  s' 2 = s 6 ∧
  s' 3 = s 7 ∧
  s' 4 = s 0 ∧
  s' 5 = s 1 ∧
  s' 6 = s 2 ∧
  s' 7 = s 3 ∧
  ∀ i : Fin 8, s' (pos8 i) = s (pos8 i)

/-- Canonical visible-stack output for `movdn.3`. -/
private def movdn3Out (s : Fin 16 → Felt) (i : Fin 16) : Felt :=
  if i.val = 0 then s 1
  else if i.val = 1 then s 2
  else if i.val = 2 then s 3
  else if i.val = 3 then s 0
  else s i

/-- Canonical visible-stack output for `swap`. -/
private def swapOut (s : Fin 16 → Felt) (i : Fin 16) : Felt :=
  if i.val = 0 then s 1
  else if i.val = 1 then s 0
  else s i

/-- Canonical visible-stack output for `movup.2`. -/
private def movup2Out (s : Fin 16 → Felt) (i : Fin 16) : Felt :=
  if i.val = 0 then s 2
  else if i.val = 1 then s 0
  else if i.val = 2 then s 1
  else s i

/-- Canonical visible-stack output for `swapw`. -/
private def swapwOut (s : Fin 16 → Felt) (i : Fin 16) : Felt :=
  if i.val = 0 then s 4
  else if i.val = 1 then s 5
  else if i.val = 2 then s 6
  else if i.val = 3 then s 7
  else if i.val = 4 then s 0
  else if i.val = 5 then s 1
  else if i.val = 6 then s 2
  else if i.val = 7 then s 3
  else s i

/--
Canonical visible-stack output for lowered `reversew`.

Lowering source:
`push_reversew` emits `[MovDn3, Swap, MovUp2]`.
-/
def reversewAirOut (s : Fin 16 → Felt) : Fin 16 → Felt :=
  movup2Out (swapOut (movdn3Out s))

/--
Canonical visible-stack output for lowered `reversedw`.

Lowering source:
`reversedw` emits `reversew; swapw; reversew`.
-/
def reversedwAirOut (s : Fin 16 → Felt) : Fin 16 → Felt :=
  reversewAirOut (swapwOut (reversewAirOut s))

/--
Layer-3 AIR acceptance relation for the local visible-stack slice of lowered
`reversew`. This is a local composition theorem, not whole-VM verifier
completeness.
-/
def reversewAirAccepts (s s' : Fin 16 → Felt) : Prop :=
  ∃ s1 s2,
    air_movdn3_full_model s s1 ∧
    air_swap_full_model s1 s2 ∧
    air_movup2_full_model s2 s'

/--
Layer-3 AIR acceptance relation for the local visible-stack slice of lowered
`reversedw`. This is a local composition theorem, not whole-VM verifier
completeness.
-/
def reversedwAirAccepts (s s' : Fin 16 → Felt) : Prop :=
  ∃ s1 s2,
    reversewAirAccepts s s1 ∧
    air_swapw_full_model s1 s2 ∧
    reversewAirAccepts s2 s'

/-- State-level visible-stack spec enforced by lowered `reversew`. -/
def reversew_visible_spec (s s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 3 ∧
  s' 1 = s 2 ∧
  s' 2 = s 1 ∧
  s' 3 = s 0 ∧
  ∀ i : Fin 12, s' (pos4 i) = s (pos4 i)

/-- State-level visible-stack spec enforced by lowered `reversedw`. -/
def reversedw_visible_spec (s s' : Fin 16 → Felt) : Prop :=
  s' 0 = s 7 ∧
  s' 1 = s 6 ∧
  s' 2 = s 5 ∧
  s' 3 = s 4 ∧
  s' 4 = s 3 ∧
  s' 5 = s 2 ∧
  s' 6 = s 1 ∧
  s' 7 = s 0 ∧
  ∀ i : Fin 8, s' (pos8 i) = s (pos8 i)

private theorem movdn3Out_accepts (s : Fin 16 → Felt) :
    air_movdn3_full_model s (movdn3Out s) := by
  refine ⟨by simp [movdn3Out], by simp [movdn3Out], by simp [movdn3Out],
    by simp [movdn3Out], ?_⟩
  intro i
  simp [movdn3Out, pos4]

private theorem swapOut_accepts (s : Fin 16 → Felt) :
    air_swap_full_model s (swapOut s) := by
  refine ⟨by simp [swapOut], by simp [swapOut], ?_⟩
  intro i
  simp [swapOut, pos2]

private theorem movup2Out_accepts (s : Fin 16 → Felt) :
    air_movup2_full_model s (movup2Out s) := by
  refine ⟨by simp [movup2Out], by simp [movup2Out], by simp [movup2Out], ?_⟩
  intro i
  simp [movup2Out, pos3]

private theorem swapwOut_accepts (s : Fin 16 → Felt) :
    air_swapw_full_model s (swapwOut s) := by
  refine ⟨by simp [swapwOut], by simp [swapwOut], by simp [swapwOut], by simp [swapwOut],
    by simp [swapwOut], by simp [swapwOut], by simp [swapwOut], by simp [swapwOut], ?_⟩
  intro i
  simp [swapwOut, pos8]

/-- Completeness for lowered `reversew` on the modeled visible-stack AIR slice. -/
theorem reversew_layer3_visible_complete (s : Fin 16 → Felt) :
    reversewAirAccepts s (reversewAirOut s) := by
  refine ⟨movdn3Out s, swapOut (movdn3Out s), ?_, ?_, ?_⟩
  · exact movdn3Out_accepts s
  · exact swapOut_accepts (movdn3Out s)
  · exact movup2Out_accepts (swapOut (movdn3Out s))

/-- The canonical lowered `reversew` witness satisfies the visible spec. -/
theorem reversew_layer3_visible_out_spec (s : Fin 16 → Felt) :
    reversew_visible_spec s (reversewAirOut s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [reversewAirOut, movup2Out, swapOut, movdn3Out]
  · simp [reversewAirOut, movup2Out, swapOut, movdn3Out]
  · simp [reversewAirOut, movup2Out, swapOut, movdn3Out]
  · simp [reversewAirOut, movup2Out, swapOut, movdn3Out]
  · intro i
    simp [reversewAirOut, movup2Out, swapOut, movdn3Out, pos4]

/--
Soundness for lowered `reversew` on the modeled visible-stack AIR slice:
any accepted witness enforces top-word reversal and preserves positions `4..15`.
-/
theorem reversew_layer3_visible_sound
    {s s' : Fin 16 → Felt} (hacc : reversewAirAccepts s s') :
    reversew_visible_spec s s' := by
  rcases hacc with ⟨s1, s2, hmovdn3, hswap, hmovup2⟩
  rcases hmovdn3 with ⟨hmd0, hmd1, hmd2, hmd3, hmdrest⟩
  rcases hswap with ⟨hsw0, hsw1, hswrest⟩
  rcases hmovup2 with ⟨hmu0, hmu1, hmu2, hmurest⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hsw2 : s2 2 = s1 2 := by
      simpa using hswrest ⟨0, by decide⟩
    rw [hmu0, hsw2, hmd2]
  · rw [hmu1, hsw0, hmd1]
  · rw [hmu2, hsw1, hmd0]
  · have hmu3 : s' 3 = s2 3 := by
      simpa [pos3] using hmurest ⟨0, by decide⟩
    have hsw3 : s2 3 = s1 3 := by
      simpa using hswrest ⟨1, by decide⟩
    rw [hmu3, hsw3, hmd3]
  · intro i
    have hmu_i : s' (pos4 i) = s2 (pos4 i) := by
      have h := hmurest ⟨i.val + 1, by
        have hi := i.isLt
        omega⟩
      simpa [pos3, pos4] using h
    have hsw_i : s2 (pos4 i) = s1 (pos4 i) := by
      have h := hswrest ⟨i.val + 2, by
        have hi := i.isLt
        omega⟩
      simpa [pos2, pos4] using h
    rw [hmu_i, hsw_i, hmdrest i]

/-- Totality form for lowered `reversew` visible-stack soundness/completeness. -/
theorem reversew_layer3_visible_total (s : Fin 16 → Felt) :
    ∃ s', reversewAirAccepts s s' ∧ reversew_visible_spec s s' := by
  exact ⟨reversewAirOut s,
    reversew_layer3_visible_complete s,
    reversew_layer3_visible_out_spec s⟩

/-- Completeness for lowered `reversedw` on the modeled visible-stack AIR slice. -/
theorem reversedw_layer3_visible_complete (s : Fin 16 → Felt) :
    reversedwAirAccepts s (reversedwAirOut s) := by
  refine ⟨reversewAirOut s, swapwOut (reversewAirOut s), ?_, ?_, ?_⟩
  · exact reversew_layer3_visible_complete s
  · exact swapwOut_accepts (reversewAirOut s)
  · exact reversew_layer3_visible_complete (swapwOut (reversewAirOut s))

/-- The canonical lowered `reversedw` witness satisfies the visible spec. -/
theorem reversedw_layer3_visible_out_spec (s : Fin 16 → Felt) :
    reversedw_visible_spec s (reversedwAirOut s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [reversedwAirOut, reversewAirOut, movup2Out, swapOut, movdn3Out, swapwOut]
  · simp [reversedwAirOut, reversewAirOut, movup2Out, swapOut, movdn3Out, swapwOut]
  · simp [reversedwAirOut, reversewAirOut, movup2Out, swapOut, movdn3Out, swapwOut]
  · simp [reversedwAirOut, reversewAirOut, movup2Out, swapOut, movdn3Out, swapwOut]
  · simp [reversedwAirOut, reversewAirOut, movup2Out, swapOut, movdn3Out, swapwOut]
  · simp [reversedwAirOut, reversewAirOut, movup2Out, swapOut, movdn3Out, swapwOut]
  · simp [reversedwAirOut, reversewAirOut, movup2Out, swapOut, movdn3Out, swapwOut]
  · simp [reversedwAirOut, reversewAirOut, movup2Out, swapOut, movdn3Out, swapwOut]
  · intro i
    simp [reversedwAirOut, reversewAirOut, movup2Out, swapOut, movdn3Out, swapwOut, pos8]

/--
Soundness for lowered `reversedw` on the modeled visible-stack AIR slice:
any accepted witness enforces top-double-word reversal and preserves positions
`8..15`.
-/
theorem reversedw_layer3_visible_sound
    {s s' : Fin 16 → Felt} (hacc : reversedwAirAccepts s s') :
    reversedw_visible_spec s s' := by
  rcases hacc with ⟨s1, s2, hrev1, hswapw, hrev2⟩
  rcases reversew_layer3_visible_sound hrev1 with ⟨h10, h11, h12, h13, h1rest⟩
  rcases hswapw with ⟨hsw0, hsw1, hsw2, hsw3, hsw4, hsw5, hsw6, hsw7, hswrest⟩
  rcases reversew_layer3_visible_sound hrev2 with ⟨h20, h21, h22, h23, h2rest⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hs1_7 : s1 7 = s 7 := by
      simpa [pos4] using h1rest ⟨3, by decide⟩
    rw [h20, hsw3, hs1_7]
  · have hs1_6 : s1 6 = s 6 := by
      simpa [pos4] using h1rest ⟨2, by decide⟩
    rw [h21, hsw2, hs1_6]
  · have hs1_5 : s1 5 = s 5 := by
      simpa [pos4] using h1rest ⟨1, by decide⟩
    rw [h22, hsw1, hs1_5]
  · have hs1_4 : s1 4 = s 4 := by
      simpa [pos4] using h1rest ⟨0, by decide⟩
    rw [h23, hsw0, hs1_4]
  · have hs'4 : s' 4 = s2 4 := by
      simpa [pos4] using h2rest ⟨0, by decide⟩
    rw [hs'4, hsw4, h10]
  · have hs'5 : s' 5 = s2 5 := by
      simpa [pos4] using h2rest ⟨1, by decide⟩
    rw [hs'5, hsw5, h11]
  · have hs'6 : s' 6 = s2 6 := by
      simpa [pos4] using h2rest ⟨2, by decide⟩
    rw [hs'6, hsw6, h12]
  · have hs'7 : s' 7 = s2 7 := by
      simpa [pos4] using h2rest ⟨3, by decide⟩
    rw [hs'7, hsw7, h13]
  · intro i
    have h2_i : s' (pos8 i) = s2 (pos8 i) := by
      have h := h2rest ⟨i.val + 4, by
        have hi := i.isLt
        omega⟩
      simpa [pos4, pos8] using h
    have hsw_i : s2 (pos8 i) = s1 (pos8 i) := hswrest i
    have h1_i : s1 (pos8 i) = s (pos8 i) := by
      have h := h1rest ⟨i.val + 4, by
        have hi := i.isLt
        omega⟩
      simpa [pos4, pos8] using h
    rw [h2_i, hsw_i, h1_i]

/-- Totality form for lowered `reversedw` visible-stack soundness/completeness. -/
theorem reversedw_layer3_visible_total (s : Fin 16 → Felt) :
    ∃ s', reversedwAirAccepts s s' ∧ reversedw_visible_spec s s' := by
  exact ⟨reversedwAirOut s,
    reversedw_layer3_visible_complete s,
    reversedw_layer3_visible_out_spec s⟩

end MidenLean.AIR.Proofs.WordStackRewriteSoundness
