import MidenLean.Proofs.Tactics
import MidenLean.Generated.U64

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

private theorem exec_append (fuel : Nat) (s : MidenState)
    (xs ys : List Op) :
    exec fuel s (xs ++ ys) = (do
      let s' ← exec fuel s xs
      exec fuel s' ys) := by
  unfold exec execWithEnv
  cases fuel <;> simp [List.foldlM_append]

-- Split at instruction 12 boundary
private def wmul_h1 : List Op := [
  .inst .reversew, .inst (.dup 3), .inst (.dup 2),
  .inst .u32WidenMul, .inst (.swap 1),
  .inst (.dup 4), .inst (.movup 4),
  .inst .u32WidenMadd,
  .inst (.movup 5), .inst (.dup 4),
  .inst .u32WidenMadd, .inst (.swap 1)]
private def wmul_h2 : List Op := [
  .inst (.movup 5), .inst (.movup 5),
  .inst .u32WidenMadd, .inst (.swap 1),
  .inst (.movup 3), .inst (.movup 2),
  .inst .u32WidenAdd, .inst (.swap 1),
  .inst (.movup 2), .inst .add, .inst .reversew]

private theorem wmul_split :
    Miden.Core.U64.widening_mul = wmul_h1 ++ wmul_h2 :=
  by simp [Miden.Core.U64.widening_mul, wmul_h1, wmul_h2]

-- Helper lemmas for u32 bounds
private theorem wmul_c1hi_u32 (a_lo b_lo b_hi : Felt)
    (h1 : a_lo.isU32 = true) (h2 : b_lo.isU32 = true)
    (h3 : b_hi.isU32 = true) :
    (Felt.ofNat ((b_hi.val * a_lo.val +
      b_lo.val * a_lo.val / 2^32) / 2^32)).isU32 =
    true := by
  apply felt_ofNat_isU32_of_lt
  simp only [Felt.isU32, decide_eq_true_eq, u32Max] at *
  have hbhi : b_hi.val ≤ 2^32 - 1 := by omega
  have halo : a_lo.val ≤ 2^32 - 1 := by omega
  have hblo : b_lo.val ≤ 2^32 - 1 := by omega
  calc (b_hi.val * a_lo.val +
      b_lo.val * a_lo.val / 2^32) / 2^32
      ≤ ((2^32-1)*(2^32-1) + (2^32-1)) / 2^32 :=
        Nat.div_le_div_right (Nat.add_le_add
          (Nat.mul_le_mul hbhi halo)
          (Nat.le_trans (Nat.div_le_div_right
            (Nat.mul_le_mul hblo halo))
            (by native_decide)))
    _ < 2^32 := by native_decide

private theorem wmul_c2hi_u32 (a_lo a_hi b_lo b_hi : Felt)
    (h1 : a_lo.isU32 = true) (h2 : a_hi.isU32 = true)
    (h3 : b_lo.isU32 = true) (h4 : b_hi.isU32 = true) :
    (Felt.ofNat ((b_lo.val * a_hi.val +
      (b_hi.val * a_lo.val +
        b_lo.val * a_lo.val / 2^32) % 2^32) /
      2^32)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  simp only [Felt.isU32, decide_eq_true_eq, u32Max] at *
  calc (b_lo.val * a_hi.val +
      (b_hi.val * a_lo.val +
        b_lo.val * a_lo.val / 2^32) % 2^32) / 2^32
      ≤ ((2^32-1)*(2^32-1) + (2^32-1)) / 2^32 :=
        Nat.div_le_div_right (Nat.add_le_add
          (Nat.mul_le_mul (by omega) (by omega))
          (by omega))
    _ < 2^32 := by native_decide

private theorem wmul_c2hi_val (a_lo a_hi b_lo b_hi : Felt)
    (h1 : a_lo.isU32 = true) (h2 : a_hi.isU32 = true)
    (h3 : b_lo.isU32 = true) (h4 : b_hi.isU32 = true) :
    (Felt.ofNat ((b_lo.val * a_hi.val +
      (b_hi.val * a_lo.val +
        b_lo.val * a_lo.val / 2^32) % 2^32) /
      2^32)).val = (b_lo.val * a_hi.val +
      (b_hi.val * a_lo.val +
        b_lo.val * a_lo.val / 2^32) % 2^32) /
      2^32 := by
  apply felt_ofNat_val_lt
  simp only [Felt.isU32, decide_eq_true_eq, u32Max] at *
  calc (b_lo.val * a_hi.val +
      (b_hi.val * a_lo.val +
        b_lo.val * a_lo.val / 2^32) % 2^32) / 2^32
      ≤ ((2^32-1)*(2^32-1) + (2^32-1)) / 2^32 :=
        Nat.div_le_div_right (Nat.add_le_add
          (Nat.mul_le_mul (by omega) (by omega))
          (by omega))
    _ < GOLDILOCKS_PRIME := by
        unfold GOLDILOCKS_PRIME; native_decide

private theorem wmul_c1hi_val (a_lo b_lo b_hi : Felt)
    (h1 : a_lo.isU32 = true) (h2 : b_lo.isU32 = true)
    (h3 : b_hi.isU32 = true) :
    (Felt.ofNat ((b_hi.val * a_lo.val +
      b_lo.val * a_lo.val / 2^32) / 2^32)).val =
    (b_hi.val * a_lo.val +
      b_lo.val * a_lo.val / 2^32) / 2^32 := by
  apply felt_ofNat_val_lt
  simp only [Felt.isU32, decide_eq_true_eq, u32Max] at *
  have hbhi : b_hi.val ≤ 2^32 - 1 := by omega
  have halo : a_lo.val ≤ 2^32 - 1 := by omega
  have hblo : b_lo.val ≤ 2^32 - 1 := by omega
  calc (b_hi.val * a_lo.val +
      b_lo.val * a_lo.val / 2^32) / 2^32
      ≤ ((2^32-1)*(2^32-1) + (2^32-1)) / 2^32 :=
        Nat.div_le_div_right (Nat.add_le_add
          (Nat.mul_le_mul hbhi halo)
          (Nat.le_trans (Nat.div_le_div_right
            (Nat.mul_le_mul hblo halo))
            (by native_decide)))
    _ < GOLDILOCKS_PRIME := by
        unfold GOLDILOCKS_PRIME; native_decide

set_option maxHeartbeats 4000000 in
private theorem wmul_h1_ok
    (a_lo a_hi b_lo b_hi : Felt)
    (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (ha_lo : a_lo.isU32 = true)
    (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true)
    (hb_hi : b_hi.isU32 = true) :
    exec 30
      ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest,
       mem, locs, adv⟩ wmul_h1 =
    some ⟨
      Felt.ofNat ((b_lo.val * a_hi.val +
        (b_hi.val * a_lo.val +
          b_lo.val * a_lo.val / 2^32) % 2^32) /
        2^32) ::
      Felt.ofNat ((b_lo.val * a_hi.val +
        (b_hi.val * a_lo.val +
          b_lo.val * a_lo.val / 2^32) % 2^32) %
        2^32) ::
      Felt.ofNat ((b_hi.val * a_lo.val +
        b_lo.val * a_lo.val / 2^32) / 2^32) ::
      Felt.ofNat (b_lo.val * a_lo.val % 2^32) ::
      a_hi :: b_hi ::
      rest, mem, locs, adv⟩ := by
  unfold exec wmul_h1 execWithEnv
  simp only [List.foldlM]
  rw [stepReversew]; miden_bind
  miden_dup; miden_dup
  rw [stepU32WidenMul (ha := hb_lo) (hb := ha_lo)]
  miden_bind; miden_swap; miden_dup; miden_movup
  rw [stepU32WidenMadd (ha := hb_hi) (hb := ha_lo)
    (hc := u32_prod_div_isU32 b_lo a_lo hb_lo ha_lo)]
  miden_bind
  rw [felt_ofNat_val_lt _
    (u32_prod_div_lt_prime b_lo a_lo hb_lo ha_lo)]
  miden_movup; miden_dup
  rw [stepU32WidenMadd (ha := hb_lo) (hb := ha_hi)
    (hc := u32_mod_isU32 _)]
  miden_bind
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  miden_swap
  dsimp only [pure, Pure.pure]

set_option maxHeartbeats 4000000 in
private theorem wmul_h2_ok
    (a_hi b_hi c2hi c2lo c1hi prod0 : Felt)
    (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (ha_hi : a_hi.isU32 = true)
    (hb_hi : b_hi.isU32 = true)
    (hc2hi_u32 : c2hi.isU32 = true)
    (hc1hi_u32 : c1hi.isU32 = true) :
    exec 30
      ⟨c2hi :: c2lo :: c1hi :: prod0 :: a_hi ::
        b_hi :: rest, mem, locs, adv⟩ wmul_h2 =
    some ⟨
      prod0 :: c2lo ::
      Felt.ofNat ((c1hi.val +
        (b_hi.val * a_hi.val + c2hi.val) % 2^32) %
        2^32) ::
      (Felt.ofNat ((c1hi.val +
        (b_hi.val * a_hi.val + c2hi.val) % 2^32) /
        2^32) +
       Felt.ofNat ((b_hi.val * a_hi.val + c2hi.val) /
        2^32)) :: rest, mem, locs, adv⟩ := by
  unfold exec wmul_h2 execWithEnv
  simp only [List.foldlM]
  miden_movup; miden_movup
  rw [stepU32WidenMadd (ha := hb_hi) (hb := ha_hi)
    (hc := hc2hi_u32)]
  miden_bind; miden_swap
  miden_movup; miden_movup
  have hhilo_u32 :
    (Felt.ofNat ((b_hi.val * a_hi.val + c2hi.val) %
      2^32)).isU32 = true := u32_mod_isU32 _
  rw [stepU32WidenAdd (ha := hc1hi_u32)
    (hb := hhilo_u32)]
  miden_bind
  have hhilo_val :
    (Felt.ofNat ((b_hi.val * a_hi.val + c2hi.val) %
      2^32)).val =
    (b_hi.val * a_hi.val + c2hi.val) % 2^32 :=
    felt_ofNat_val_lt _ (u32_mod_lt_prime _)
  rw [hhilo_val]
  miden_swap; miden_movup
  rw [stepAdd]; miden_bind
  rw [stepReversew]
  dsimp only [pure, Pure.pure]

set_option maxHeartbeats 4000000 in
/-- u64.widening_mul computes the full 128-bit product. -/
theorem u64_widening_mul_correct
    (a_lo a_hi b_lo b_hi : Felt)
    (rest : List Felt) (s : MidenState)
    (hs : s.stack = b_lo :: b_hi :: a_lo :: a_hi :: rest)
    (ha_lo : a_lo.isU32 = true)
    (ha_hi : a_hi.isU32 = true)
    (hb_lo : b_lo.isU32 = true)
    (hb_hi : b_hi.isU32 = true) :
    exec 30 s Miden.Core.U64.widening_mul =
    some (s.withStack (
      let prod0 := b_lo.val * a_lo.val
      let cross1 := b_hi.val * a_lo.val + prod0 / 2^32
      let cross2 := b_lo.val * a_hi.val + cross1 % 2^32
      let high := b_hi.val * a_hi.val + cross2 / 2^32
      let widenAdd := cross1 / 2^32 + high % 2^32
      Felt.ofNat (prod0 % 2^32) ::
      Felt.ofNat (cross2 % 2^32) ::
      Felt.ofNat (widenAdd % 2^32) ::
      (Felt.ofNat (widenAdd / 2^32) +
        Felt.ofNat (high / 2^32)) :: rest)) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  rw [wmul_split, exec_append,
    wmul_h1_ok a_lo a_hi b_lo b_hi rest
      mem locs adv ha_lo ha_hi hb_lo hb_hi]
  simp only [bind, Bind.bind, Option.bind]
  rw [wmul_h2_ok a_hi b_hi _ _ _ _
    rest mem locs adv ha_hi hb_hi
    (wmul_c2hi_u32 a_lo a_hi b_lo b_hi
      ha_lo ha_hi hb_lo hb_hi)
    (wmul_c1hi_u32 a_lo b_lo b_hi
      ha_lo hb_lo hb_hi)]
  simp only [wmul_c2hi_val a_lo a_hi b_lo b_hi
    ha_lo ha_hi hb_lo hb_hi,
    wmul_c1hi_val a_lo b_lo b_hi ha_lo hb_lo hb_hi]

end MidenLean.Proofs
