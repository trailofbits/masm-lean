import MidenLean.AIR.Proofs.BitwiseChiplet
import MidenLean.Proofs.Helpers
import MidenLean.Proofs.Sha256.Maj

namespace MidenLean.AIR.Proofs.Sha256MajSoundness

open MidenLean
open MidenLean.AIR

private theorem u32_and_lt_prime (a b : Nat) (hb : b < 2 ^ 32) :
    a &&& b < GOLDILOCKS_PRIME := by
  calc
    a &&& b < 2 ^ 32 := Nat.and_lt_two_pow _ hb
    _ < GOLDILOCKS_PRIME := by
      unfold GOLDILOCKS_PRIME
      omega

private theorem u32_xor_lt_prime (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    a ^^^ b < GOLDILOCKS_PRIME := by
  calc
    a ^^^ b < 2 ^ 32 := Nat_xor_lt_of_lt ha hb
    _ < GOLDILOCKS_PRIME := by
      unfold GOLDILOCKS_PRIME
      omega

/-- Layer-3 AIR acceptance relation for the full lowered `maj` helper. This
composes:

- lowered `u32and`
- lowered `u32and`
- lowered `u32and`
- lowered `u32xor`
- lowered `u32xor`

at the helper IO boundary. -/
def majAirAccepts (x y z out : Felt) : Prop :=
  ∃ and1 and2 and3 xor1,
    MidenLean.AIR.Proofs.andCycleAccepts x y and1 ∧
    MidenLean.AIR.Proofs.andCycleAccepts x z and2 ∧
    MidenLean.AIR.Proofs.andCycleAccepts y z and3 ∧
    MidenLean.AIR.Proofs.xorCycleAccepts and2 and3 xor1 ∧
    MidenLean.AIR.Proofs.xorCycleAccepts and1 xor1 out

/-- State-level lifting of the Layer-3 `maj` AIR boundary. -/
def majAirStateAccepts (s s' : MidenState) : Prop :=
  ∃ x y z rest out,
    s.stack = x :: y :: z :: rest ∧
    majAirAccepts x y z out ∧
    s' = s.withStack (out :: rest)

/-- Any accepted lowered `maj` trace enforces `u32` inputs and computes the
same local helper summary used by the honest MASM proof. -/
theorem sha256_maj_layer3_local_out
    {x y z out : Felt} (hacc : majAirAccepts x y z out) :
    x.IsU32 ∧ y.IsU32 ∧ z.IsU32 ∧ out = MidenLean.Proofs.sha256_maj_local_out x y z := by
  rcases hacc with ⟨and1, and2, and3, xor1, hand1, hand2, hand3, hxor1, hxor2⟩
  rcases MidenLean.AIR.Proofs.andCycleAccepts_sound hand1 with ⟨hx, hy, hand1_eq⟩
  rcases MidenLean.AIR.Proofs.andCycleAccepts_sound hand2 with ⟨_, hz, hand2_eq0⟩
  rcases MidenLean.AIR.Proofs.andCycleAccepts_sound hand3 with ⟨_, _, hand3_eq0⟩
  rcases MidenLean.AIR.Proofs.xorCycleAccepts_sound hxor1 with ⟨_, _, hxor1_eq0⟩
  rcases MidenLean.AIR.Proofs.xorCycleAccepts_sound hxor2 with ⟨_, _, hxor2_eq0⟩
  have h_and1_lt : x.val &&& y.val < GOLDILOCKS_PRIME := u32_and_lt_prime x.val y.val hy
  have h_and2_lt : x.val &&& z.val < GOLDILOCKS_PRIME := u32_and_lt_prime x.val z.val hz
  have h_and3_lt : y.val &&& z.val < GOLDILOCKS_PRIME := u32_and_lt_prime y.val z.val hz
  have hxor1_eq : xor1 = Felt.ofNat ((x.val &&& z.val) ^^^ (y.val &&& z.val)) := by
    rw [hxor1_eq0, hand2_eq0, hand3_eq0]
    rw [felt_ofNat_val_lt _ h_and2_lt, felt_ofNat_val_lt _ h_and3_lt]
  have h_xor1_lt : (x.val &&& z.val) ^^^ (y.val &&& z.val) < GOLDILOCKS_PRIME := by
    exact u32_xor_lt_prime _ _
      (Nat.and_lt_two_pow x.val hz)
      (Nat.and_lt_two_pow y.val hz)
  have hxor2_eq : out = MidenLean.Proofs.sha256_maj_local_out x y z := by
    unfold MidenLean.Proofs.sha256_maj_local_out
    rw [hxor2_eq0, hand1_eq, hxor1_eq]
    rw [felt_ofNat_val_lt _ h_and1_lt, felt_ofNat_val_lt _ h_xor1_lt]
  exact ⟨hx, hy, hz, hxor2_eq⟩

/-- Layer-3 soundness at the code-level IO boundary: accepted lowered `maj`
traces satisfy the same partial IO spec used at Layer 2. -/
theorem sha256_maj_layer3_io_spec_sound
    {x y z out : Felt} (hacc : majAirAccepts x y z out) :
    MidenLean.Proofs.sha256_maj_io_spec x y z out := by
  rcases sha256_maj_layer3_local_out hacc with ⟨hx, hy, hz, hout⟩
  have hx' : x.isU32 = true := by
    simpa [Felt.isU32, decide_eq_true_eq] using hx
  have hy' : y.isU32 = true := by
    simpa [Felt.isU32, decide_eq_true_eq] using hy
  have hz' : z.isU32 = true := by
    simpa [Felt.isU32, decide_eq_true_eq] using hz
  rw [hout]
  exact MidenLean.Proofs.sha256_maj_layer2_io_spec x y z hx' hy' hz'

/-- Layer-3 soundness at the helper state boundary: accepted lowered `maj`
traces refine the same state-level partial spec used by the Layer 1/2 proofs. -/
theorem sha256_maj_layer3_state_spec_sound
    {s s' : MidenState} (hacc : majAirStateAccepts s s') :
    MidenLean.Proofs.sha256_maj_state_spec s s' := by
  rcases hacc with ⟨x, y, z, rest, out, hs, hio, hs'⟩
  refine ⟨x, y, z, rest, out, hs, ?_, hs'⟩
  exact sha256_maj_layer3_io_spec_sound hio

end MidenLean.AIR.Proofs.Sha256MajSoundness
