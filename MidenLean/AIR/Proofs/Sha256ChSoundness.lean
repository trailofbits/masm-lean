import MidenLean.AIR.Proofs.BitwiseChiplet
import MidenLean.AIR.Proofs.U32NotLowering
import MidenLean.Proofs.Helpers
import MidenLean.Proofs.Sha256.Ch

namespace MidenLean.AIR.Proofs.Sha256ChSoundness

open MidenLean
open MidenLean.AIR

private theorem u32_not_lt_prime (a : Nat) (ha : a < 2 ^ 32) :
    u32Max - 1 - a < GOLDILOCKS_PRIME := by
  unfold u32Max GOLDILOCKS_PRIME
  omega

private theorem u32_and_lt_prime (a b : Nat) (hb : b < 2 ^ 32) :
    a &&& b < GOLDILOCKS_PRIME := by
  calc
    a &&& b < 2 ^ 32 := Nat.and_lt_two_pow _ hb
    _ < GOLDILOCKS_PRIME := by
      unfold GOLDILOCKS_PRIME
      omega

/-- Layer-3 AIR acceptance relation for the full lowered `ch` helper. This
composes:

- lowered `u32not`
- lowered `u32and`
- lowered `u32and`
- lowered `u32xor`

at the helper IO boundary. -/
def chAirAccepts (x y z out : Felt) : Prop :=
  ∃ notx and1 and2,
    MidenLean.AIR.Proofs.u32NotLoweringAccepts x notx ∧
    MidenLean.AIR.Proofs.andCycleAccepts x y and1 ∧
    MidenLean.AIR.Proofs.andCycleAccepts notx z and2 ∧
    MidenLean.AIR.Proofs.xorCycleAccepts and1 and2 out

/-- State-level lifting of the Layer-3 `ch` AIR boundary. -/
def chAirStateAccepts (s s' : MidenState) : Prop :=
  ∃ x y z rest out,
    s.stack = x :: y :: z :: rest ∧
    chAirAccepts x y z out ∧
    s' = s.withStack (out :: rest)

/-- Any accepted lowered `ch` trace enforces `u32` inputs and computes the same
local helper summary used by the honest MASM proof. -/
theorem sha256_ch_layer3_local_out
    {x y z out : Felt} (hacc : chAirAccepts x y z out) :
    x.IsU32 ∧ y.IsU32 ∧ z.IsU32 ∧ out = MidenLean.Proofs.sha256_ch_local_out x y z := by
  rcases hacc with ⟨notx, and1, and2, hnot, hand1, hand2, hxor⟩
  rcases MidenLean.AIR.Proofs.u32NotLoweringAccepts_sound hnot with ⟨hx, _, hnot_eq⟩
  rcases MidenLean.AIR.Proofs.andCycleAccepts_sound hand1 with ⟨_, hy, hand1_eq⟩
  rcases MidenLean.AIR.Proofs.andCycleAccepts_sound hand2 with ⟨_, hz, hand2_eq0⟩
  rcases MidenLean.AIR.Proofs.xorCycleAccepts_sound hxor with ⟨_, _, hxor_eq0⟩
  have hand2_eq : and2 = Felt.ofNat ((u32Max - 1 - x.val) &&& z.val) := by
    rw [hnot_eq, felt_ofNat_val_lt _ (u32_not_lt_prime x.val hx)] at hand2_eq0
    exact hand2_eq0
  have h_and1_lt : x.val &&& y.val < GOLDILOCKS_PRIME := u32_and_lt_prime x.val y.val hy
  have h_and2_lt : (u32Max - 1 - x.val) &&& z.val < GOLDILOCKS_PRIME :=
    u32_and_lt_prime (u32Max - 1 - x.val) z.val hz
  have hxor_eq : out = MidenLean.Proofs.sha256_ch_local_out x y z := by
    unfold MidenLean.Proofs.sha256_ch_local_out
    rw [hxor_eq0, hand1_eq, hand2_eq]
    rw [felt_ofNat_val_lt _ h_and1_lt, felt_ofNat_val_lt _ h_and2_lt]
  exact ⟨hx, hy, hz, hxor_eq⟩

/-- Layer-3 soundness at the code-level IO boundary: accepted lowered `ch`
traces satisfy the same partial IO spec used at Layer 2. -/
theorem sha256_ch_layer3_io_spec_sound
    {x y z out : Felt} (hacc : chAirAccepts x y z out) :
    MidenLean.Proofs.sha256_ch_io_spec x y z out := by
  rcases sha256_ch_layer3_local_out hacc with ⟨hx, hy, hz, hout⟩
  have hx' : x.isU32 = true := by
    simpa [Felt.isU32, decide_eq_true_eq] using hx
  have hy' : y.isU32 = true := by
    simpa [Felt.isU32, decide_eq_true_eq] using hy
  have hz' : z.isU32 = true := by
    simpa [Felt.isU32, decide_eq_true_eq] using hz
  rw [hout]
  exact MidenLean.Proofs.sha256_ch_layer2_io_spec x y z hx' hy' hz'

/-- Layer-3 soundness at the helper state boundary: accepted lowered `ch`
traces refine the same state-level partial spec used by the Layer 1/2 proofs. -/
theorem sha256_ch_layer3_state_spec_sound
    {s s' : MidenState} (hacc : chAirStateAccepts s s') :
    MidenLean.Proofs.sha256_ch_state_spec s s' := by
  rcases hacc with ⟨x, y, z, rest, out, hs, hio, hs'⟩
  refine ⟨x, y, z, rest, out, hs, ?_, hs'⟩
  exact sha256_ch_layer3_io_spec_sound hio

end MidenLean.AIR.Proofs.Sha256ChSoundness
