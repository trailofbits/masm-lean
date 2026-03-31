import MidenLean.AIR.Constraints.StackArith
import MidenLean.AIR.Frame
import MidenLean.Proofs.Helpers
/-!
# Generic Layer-3 Counterexamples For Lowered `u32rotr.b` / `u32shr.b`

This file records a more compositional counterexample family than the earlier
one-off `small_sigma_0` slice witness.

The key observation is that for every immediate shift/rotate `b ∈ {1, ..., 31}`,
the non-`u32` field element `2^32` has visible low word `0`, but the lowered AIR
paths for `u32rotr.b` and `u32shr.b` admit nonzero accepted outputs:

- lowered `u32rotr.b`:
  `push.2^(32-b); u32mul; add`
- lowered `u32shr.b`:
  `push.2^b; u32div; drop`

Thus the soundness failure is not special to `rotr.7`; it is a whole family of
lowered building-block counterexamples. This is the right level to compose into
`small_sigma_0` and `small_sigma_1`.
-/

namespace MidenLean.AIR.Proofs.U32ImmediateLoweringCounterexamples

open MidenLean MidenLean.AIR MidenLean.AIR.Constraints

/-- Immediate shifts/rotates range over `1..31`. -/
abbrev ImmShift := Fin 31

/-- Convert a bounded immediate into the corresponding natural in `1..31`. -/
def shiftNat (k : ImmShift) : Nat := k.val + 1

/-- Canonical hidden-high-limb input used for the generic counterexample family. -/
abbrev hiddenHighLimbInput : Felt := Felt.ofNat (2 ^ 32)

/-- Intended 32-bit rotate-right of the visible low word. -/
def visibleRotrSpec (x : Felt) (k : ImmShift) : Felt :=
  Felt.ofNat (u32RotateRight (x.val % 2 ^ 32) (shiftNat k))

/-- Intended 32-bit shift-right of the visible low word. -/
def visibleShrSpec (x : Felt) (k : ImmShift) : Felt :=
  Felt.ofNat ((x.val % 2 ^ 32) / 2 ^ (shiftNat k))

/-- AIR-visible output forced by the lowered `u32rotr.b` witness on `2^32`. -/
def rotrImmAirOutput (k : ImmShift) : Felt := Felt.ofNat (2 ^ (32 - shiftNat k))

/-- AIR-visible quotient forced by the lowered `u32shr.b` witness on `2^32`. -/
def shrImmAirOutput (k : ImmShift) : Felt := Felt.ofNat (2 ^ (32 - shiftNat k))

/-- Concrete `u32mul` frame used by the generic lowered `u32rotr.b`
counterexample. -/
def rotrMulFrame (k : ImmShift) : Frame :=
  let q := 2 ^ (32 - shiftNat k)
  Frame.ofLists [q, 2 ^ 32] [0, q] [0, 0, q % 2 ^ 16, q / 2 ^ 16, 0, 0]

/-- Concrete `add` frame folding the split limbs back into the final rotate
result. -/
def rotrAddFrame (k : ImmShift) : Frame :=
  let q := 2 ^ (32 - shiftNat k)
  Frame.ofLists [0, q] [q] []

/-- Concrete `u32div` frame used by the generic lowered `u32shr.b`
counterexample. The post-`drop` output is the quotient `q`. -/
def shrDivFrame (k : ImmShift) : Frame :=
  let q := 2 ^ (32 - shiftNat k)
  let vlo := 2 ^ 32 - q
  let vhi := 2 ^ (shiftNat k) - 1
  Frame.ofLists [2 ^ (shiftNat k), 2 ^ 32] [0, q]
    [vlo % 2 ^ 16, vlo / 2 ^ 16, vhi % 2 ^ 16, vhi / 2 ^ 16, 0, 0]

/-- Package the lowered `u32rotr.b` witness family as one counterexample shape. -/
def rotrImmediateCounterexample (k : ImmShift) : Prop :=
  (rotrMulFrame k).check Constraints.u32mul = true ∧
  (rotrAddFrame k).check Constraints.add = true ∧
  ¬ hiddenHighLimbInput.IsU32 ∧
  rotrImmAirOutput k ≠ visibleRotrSpec hiddenHighLimbInput k

/-- Package the lowered `u32shr.b` witness family as one counterexample shape. -/
def shrImmediateCounterexample (k : ImmShift) : Prop :=
  (shrDivFrame k).check Constraints.u32div = true ∧
  ¬ hiddenHighLimbInput.IsU32 ∧
  shrImmAirOutput k ≠ visibleShrSpec hiddenHighLimbInput k

theorem hiddenHighLimbInput_not_u32 : ¬ hiddenHighLimbInput.IsU32 := by
  unfold hiddenHighLimbInput Felt.IsU32
  rw [felt_ofNat_val_lt (2 ^ 32)]
  · native_decide
  · unfold GOLDILOCKS_PRIME
    native_decide

theorem rotrMulFrame_check_all : ∀ k : ImmShift, (rotrMulFrame k).check Constraints.u32mul = true := by
  native_decide

theorem rotrAddFrame_check_all : ∀ k : ImmShift, (rotrAddFrame k).check Constraints.add = true := by
  native_decide

theorem shrDivFrame_check_all : ∀ k : ImmShift, (shrDivFrame k).check Constraints.u32div = true := by
  native_decide

theorem visibleRotrSpec_hiddenHighLimb_all : ∀ k : ImmShift, visibleRotrSpec hiddenHighLimbInput k = 0 := by
  native_decide

theorem visibleShrSpec_hiddenHighLimb_all : ∀ k : ImmShift, visibleShrSpec hiddenHighLimbInput k = 0 := by
  native_decide

theorem rotrImmAirOutput_ne_visibleRotrSpec_all :
    ∀ k : ImmShift, rotrImmAirOutput k ≠ visibleRotrSpec hiddenHighLimbInput k := by
  native_decide

theorem shrImmAirOutput_ne_visibleShrSpec_all :
    ∀ k : ImmShift, shrImmAirOutput k ≠ visibleShrSpec hiddenHighLimbInput k := by
  native_decide

/-- Every immediate lowered `u32rotr.b` admits the same hidden-high-limb
counterexample family. -/
theorem rotrImmediateCounterexample_all : ∀ k : ImmShift, rotrImmediateCounterexample k := by
  intro k
  exact ⟨rotrMulFrame_check_all k, rotrAddFrame_check_all k,
    hiddenHighLimbInput_not_u32, rotrImmAirOutput_ne_visibleRotrSpec_all k⟩

/-- Every immediate lowered `u32shr.b` admits the same hidden-high-limb
counterexample family. -/
theorem shrImmediateCounterexample_all : ∀ k : ImmShift, shrImmediateCounterexample k := by
  intro k
  exact ⟨shrDivFrame_check_all k, hiddenHighLimbInput_not_u32,
    shrImmAirOutput_ne_visibleShrSpec_all k⟩

/-- The three lowered building blocks relevant to `small_sigma_0` are all
individually unsound at Layer 3. -/
theorem sigma0_relevant_building_blocks_unsound :
    rotrImmediateCounterexample ⟨6, by decide⟩ ∧
    rotrImmediateCounterexample ⟨17, by decide⟩ ∧
    shrImmediateCounterexample ⟨2, by decide⟩ := by
  exact ⟨rotrImmediateCounterexample_all ⟨6, by decide⟩,
    rotrImmediateCounterexample_all ⟨17, by decide⟩,
    shrImmediateCounterexample_all ⟨2, by decide⟩⟩

end MidenLean.AIR.Proofs.U32ImmediateLoweringCounterexamples
