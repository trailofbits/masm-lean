import MidenLean.Felt
/-!
# Range Checker Constraint Model

Formalizes the Miden VM range checker. The V column goes from 0 to 65535
with non-negative increments from {0, 1, 3, 9, 27, 81, 243, 729, 2187}.
This guarantees every V[i] ∈ [0, 65535], justifying `Frame.RangeChecked`.
-/

namespace MidenLean.AIR.RangeChecker

/-- A valid range checker trace over natural numbers. -/
structure ValidRangeTrace (n : Nat) where
  v : Fin n → Nat
  pos : n > 0
  first : v ⟨0, pos⟩ = 0
  last : v ⟨n - 1, by omega⟩ = 65535
  mono : ∀ (j : Nat) (hj : j + 1 < n), v ⟨j, by omega⟩ ≤ v ⟨j + 1, by omega⟩

/-- Chain monotonicity: V[a] ≤ V[b] for a ≤ b. -/
theorem ValidRangeTrace.chain_le {n : Nat} (t : ValidRangeTrace n)
    (a b : Nat) (hab : a ≤ b) (ha : a < n) (hb : b < n) :
    t.v ⟨a, ha⟩ ≤ t.v ⟨b, hb⟩ := by
  induction hab with
  | refl => rfl
  | step hab ih => exact le_trans (ih (by omega)) (t.mono _ (by omega))

/-- All values in a valid range trace are at most 65535. -/
theorem ValidRangeTrace.bounded {n : Nat} (t : ValidRangeTrace n)
    (i : Fin n) : t.v i ≤ 65535 := by
  have hn := t.pos
  have := t.chain_le i.val (n - 1) (by omega) i.isLt (by omega)
  simp [t.last] at this; exact this

/-- All values in a valid range trace are less than 2^16. -/
theorem ValidRangeTrace.lt_pow16 {n : Nat} (t : ValidRangeTrace n)
    (i : Fin n) : t.v i < 2 ^ 16 := by
  have := t.bounded i; omega

end MidenLean.AIR.RangeChecker
