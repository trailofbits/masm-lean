import MidenLean.AIR.Proofs.StackArith
import MidenLean.Proofs.Helpers

namespace MidenLean.AIR.Proofs

open MidenLean
open MidenLean.AIR
open MidenLean.AIR.Constraints

/-- Local AIR acceptance relation for the lowered `u32not` sequence

`push (2^32 - 1) ; u32assert2 ; swap ; u32sub ; drop`

at its verifier-visible IO boundary. The relation records only the two
nontrivial constrained steps:

- `u32assert2` certifies that both `x` and the constant `2^32 - 1` are valid
  `u32` values.
- `u32sub` computes the subtraction `((2^32 - 1) - x)` with zero borrow and
  leaves the final word `out`.

Stack shuffles are tracked through explicit equalities between the intermediate
frame outputs and inputs. -/
def u32NotLoweringAccepts (x out : Felt) : Prop :=
  ∃ assertFrame subFrame : Frame,
    assertFrame.s' 0 = Felt.ofNat (u32Max - 1) ∧
    assertFrame.s' 1 = x ∧
    assertFrame.satisfies Constraints.u32assert2 ∧
    Frame.RangeChecked assertFrame ∧
    subFrame.s 0 = x ∧
    subFrame.s 1 = Felt.ofNat (u32Max - 1) ∧
    subFrame.s' 0 = 0 ∧
    subFrame.s' 1 = out ∧
    subFrame.satisfies Constraints.u32sub ∧
    Frame.RangeChecked subFrame

/-- Any accepted lowered `u32not` sequence enforces a valid `u32` input and
computes the correct bitwise-NOT output. -/
theorem u32NotLoweringAccepts_sound
    {x out : Felt} (hacc : u32NotLoweringAccepts x out) :
    x.IsU32 ∧ out.IsU32 ∧ out = Felt.ofNat (u32Max - 1 - x.val) := by
  rcases hacc with ⟨assertFrame, subFrame,
    hAssertMax, hAssertX, hAssertSat, hAssertRc,
    hSubX, hSubMax, hBorrow, hSubOut, hSubSat, hSubRc⟩
  have hx_u32 : x.IsU32 := by
    rcases air_u32assert2_outputs_u32 assertFrame hAssertSat hAssertRc with ⟨_, hx⟩
    rw [hAssertX] at hx
    exact hx
  have hout_u32 : out.IsU32 := by
    rcases air_u32sub_sound subFrame hSubSat with ⟨_, _, hout⟩
    rw [hSubOut] at hout
    rw [hout]
    exact v_lo_isU32_of_rangeChecked subFrame hSubRc
  have hx_lt : x.val < 2 ^ 32 := hx_u32
  have hout_lt : out.val < 2 ^ 32 := hout_u32
  have hsub_eq : Felt.ofNat (u32Max - 1) = x + out := by
    rcases air_u32sub_sound subFrame hSubSat with ⟨heq, _, _⟩
    rw [hSubMax, hSubX, hSubOut, hBorrow] at heq
    simpa using heq
  have hmax_lt : u32Max - 1 < GOLDILOCKS_PRIME := by
    unfold u32Max GOLDILOCKS_PRIME
    omega
  have hsum_lt : x.val + out.val < GOLDILOCKS_PRIME := by
    unfold GOLDILOCKS_PRIME
    omega
  have hnat : u32Max - 1 = x.val + out.val := by
    have hval := congrArg (fun a : Felt => a.val) hsub_eq
    have hleft : (fun a : Felt => a.val) (Felt.ofNat (u32Max - 1)) = u32Max - 1 := by
      simpa using felt_ofNat_val_lt (u32Max - 1) hmax_lt
    have hright : (fun a : Felt => a.val) (x + out) = x.val + out.val := by
      simpa using (ZMod.val_add_of_lt (a := x) (b := out) hsum_lt)
    calc
      u32Max - 1 = (fun a : Felt => a.val) (Felt.ofNat (u32Max - 1)) := by simpa using hleft.symm
      _ = (fun a : Felt => a.val) (x + out) := hval
      _ = x.val + out.val := hright
  have hout_nat : out.val = u32Max - 1 - x.val := by
    omega
  refine ⟨hx_u32, hout_u32, ?_⟩
  calc
    out = Felt.ofNat out.val := by
      symm
      exact ZMod.natCast_zmod_val out
    _ = Felt.ofNat (u32Max - 1 - x.val) := by
      rw [hout_nat]

end MidenLean.AIR.Proofs
