import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.U128.OverflowingMul
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- Execute a concatenation of op lists in two phases. -/
private theorem exec_append (fuel : Nat) (s : MidenState) (xs ys : List Op) :
    exec fuel s (xs ++ ys) = (do
      let s' ← exec fuel s xs
      exec fuel s' ys) := by
  simpa [exec] using execWithEnv_append (env := fun _ => none) fuel s xs ys

private theorem stepU32AssertWLocal (mem locs : Nat → Felt) (adv : List Felt)
    (a b c d : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) (hd : d.isU32 = true) :
    execInstruction ⟨a :: b :: c :: d :: rest, mem, locs, adv⟩ .u32AssertW =
      some ⟨a :: b :: c :: d :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32AssertW
  simp [ha, hb, hc, hd]

private theorem stepAdvLoadWLocal (mem locs : Nat → Felt)
    (top0 top1 top2 top3 : Felt) (rest : List Felt)
    (v0 v1 v2 v3 : Felt) (adv_rest : List Felt) :
    execInstruction ⟨top0 :: top1 :: top2 :: top3 :: rest, mem, locs, v0 :: v1 :: v2 :: v3 :: adv_rest⟩
        .advLoadW =
      some ⟨v0 :: v1 :: v2 :: v3 :: rest, mem, locs, adv_rest⟩ := by
  unfold execInstruction execAdvLoadW
  simp [MidenState.withAdvice, MidenState.withStack]

private theorem stepAssertzWithErrorLocal (msg : String) (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.val = 0) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ (.assertzWithError msg) =
      some ⟨rest, mem, locs, adv⟩ := by
  unfold execInstruction execAssertz
  simp [ha, MidenState.withStack]

private theorem stepAssertzWithError_noneLocal (msg : String) (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.val ≠ 0) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ (.assertzWithError msg) = none := by
  unfold execInstruction execAssertz
  simp [show ¬ (a.val == 0) = true from by simp [ha]]

private theorem stepSwapw2Local (mem locs : Nat → Felt) (adv : List Felt)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 : Felt) (rest : List Felt) :
    execInstruction ⟨a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: c0 :: c1 :: c2 :: c3 :: rest,
        mem, locs, adv⟩ (.swapw 2) =
      some ⟨c0 :: c1 :: c2 :: c3 :: b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest,
        mem, locs, adv⟩ := by
  unfold execInstruction execSwapw
  simp [MidenState.withStack]

private theorem felt_ite_val_local (p : Prop) [Decidable p] :
    (if p then (1 : Felt) else (0 : Felt)).val = if p then 1 else 0 := by
  split <;> simp [Felt.val_one']

private theorem two_pow_32 : (2 ^ 32 : Nat) = 4294967296 := by
  native_decide

private theorem felt_ofNat_eq_zero_iff {n : Nat} (hn : n < GOLDILOCKS_PRIME) :
    Felt.ofNat n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have hval := congrArg (fun x : Felt => x.val) h
    simpa [felt_ofNat_val_lt _ hn] using hval
  · intro h
    subst h
    rfl

private theorem u32OverflowingSub_snd_eq_zero_iff
    (a b : Felt) (ha : a.isU32 = true) (hb : b.isU32 = true) :
    Felt.ofNat (u32OverflowingSub a.val b.val).2 = 0 ↔ a.val = b.val := by
  have ha_lt : a.val < 2 ^ 32 := by
    simpa [Felt.isU32, decide_eq_true_eq] using ha
  have hb_lt : b.val < 2 ^ 32 := by
    simpa [Felt.isU32, decide_eq_true_eq] using hb
  rw [felt_ofNat_eq_zero_iff (u32_overflow_sub_snd_lt _ _ (felt_val_lt_prime a) (felt_val_lt_prime b))]
  unfold u32OverflowingSub u32Max
  by_cases hge : a.val ≥ b.val
  · simp [hge]
    omega
  · have hlt : a.val < b.val := by omega
    simp [hge]
    omega

private theorem divmodBorrow1_eq (a0 a1 b0 b1 : Felt)
    (ha0 : a0.isU32 = true) (hb0 : b0.isU32 = true) :
    u128Borrow1 a0 a1 b0 b1 =
    if decide (a1.val * 2 ^ 32 + a0.val < b1.val * 2 ^ 32 + b0.val) then (1 : Felt) else 0 := by
  simp only [Felt.isU32, decide_eq_true_eq] at ha0 hb0
  unfold u128Borrow1 u128Sub0 u128Sub1 u32OverflowingSub u32Max
  congr 1
  apply propext
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    rcases h with h | h
    · split_ifs at h <;> omega
    · omega
  · intro h
    by_cases h1 : a1.val < b1.val
    · right
      exact h1
    · left
      split_ifs <;> omega

private theorem divmodBorrow1_prop_eq (a0 a1 b0 b1 : Felt)
    (ha0 : a0.isU32 = true) (hb0 : b0.isU32 = true) :
    (((u128Sub1 a1 b1).2 < (u128Sub0 a0 b0).1) ∨ a1.val < b1.val) ↔
      a1.val * 2 ^ 32 + a0.val < b1.val * 2 ^ 32 + b0.val := by
  simp only [Felt.isU32, decide_eq_true_eq] at ha0 hb0
  unfold u128Sub0 u128Sub1 u32OverflowingSub u32Max
  constructor
  · intro h
    rcases h with h | h
    · split_ifs at h <;> omega
    · omega
  · intro h
    by_cases h1 : a1.val < b1.val
    · exact Or.inr h1
    · exact Or.inl (by split_ifs <;> omega)

private theorem divmodBorrow2_eq (a0 a1 a2 b0 b1 b2 : Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) :
    u128Borrow2 a0 a1 a2 b0 b1 b2 =
    if decide (a2.val * 2 ^ 64 + a1.val * 2 ^ 32 + a0.val <
        b2.val * 2 ^ 64 + b1.val * 2 ^ 32 + b0.val) then (1 : Felt) else 0 := by
  simp only [Felt.isU32, decide_eq_true_eq] at ha0 ha1 hb0 hb1
  unfold u128Borrow2 u128Sub2 u32OverflowingSub u32Max
  rw [divmodBorrow1_eq a0 a1 b0 b1 (by simpa [Felt.isU32]) (by simpa [Felt.isU32])]
  rw [felt_ite_val_local]
  congr 1
  apply propext
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    rcases h with h | h
    · split_ifs at h <;> omega
    · omega
  · intro h
    by_cases h2 : a2.val < b2.val
    · right
      exact h2
    · left
      split_ifs <;> omega

private theorem divmodBorrow2_prop_eq (a0 a1 a2 b0 b1 b2 : Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true) (_ha2 : a2.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) (_hb2 : b2.isU32 = true) :
    (((u128Sub2 a2 b2).2 < (u128Borrow1 a0 a1 b0 b1).val) ∨ a2.val < b2.val) ↔
      a2.val * 2 ^ 64 + a1.val * 2 ^ 32 + a0.val <
        b2.val * 2 ^ 64 + b1.val * 2 ^ 32 + b0.val := by
  have hEq := divmodBorrow2_eq a0 a1 a2 b0 b1 b2 ha0 ha1 hb0 hb1
  unfold u128Borrow2 at hEq
  have hval := congrArg (fun x : Felt => x.val) hEq
  simp at hval
  constructor
  · intro hp
    by_cases hq :
        a2.val * 2 ^ 64 + a1.val * 2 ^ 32 + a0.val <
          b2.val * 2 ^ 64 + b1.val * 2 ^ 32 + b0.val
    · exact hq
    · exfalso
      have hq' :
          ¬ (a2.val * 18446744073709551616 + a1.val * 4294967296 + a0.val <
              b2.val * 18446744073709551616 + b1.val * 4294967296 + b0.val) := by
        simpa using hq
      simp [hp, hq'] at hval
  · intro hq
    by_cases hp : ((u128Sub2 a2 b2).2 < (u128Borrow1 a0 a1 b0 b1).val) ∨ a2.val < b2.val
    · exact hp
    · exfalso
      have hq' :
          a2.val * 18446744073709551616 + a1.val * 4294967296 + a0.val <
            b2.val * 18446744073709551616 + b1.val * 4294967296 + b0.val := by
        simpa using hq
      simp [hp, hq'] at hval

private theorem divmodLow64_lt_iff (r0 r1 b0 b1 : Felt)
    (hr0 : r0.val < 2 ^ 32) (_hr1 : r1.val < 2 ^ 32)
    (hb0 : b0.val < 2 ^ 32) (_hb1 : b1.val < 2 ^ 32) :
    (r1.val < b1.val ∨ r1.val = b1.val ∧ r0.val < b0.val) ↔
      r1.val * 2 ^ 32 + r0.val < b1.val * 2 ^ 32 + b0.val := by
  constructor
  · intro h
    rcases h with h | ⟨hEq, h0⟩ <;> omega
  · intro h
    by_cases h1 : r1.val < b1.val
    · exact Or.inl h1
    · right
      refine ⟨?_, ?_⟩ <;> omega

private theorem divmodLow96_lt_iff (r0 r1 r2 b0 b1 b2 : Felt)
    (hr0 : r0.val < 2 ^ 32) (hr1 : r1.val < 2 ^ 32) (_hr2 : r2.val < 2 ^ 32)
    (hb0 : b0.val < 2 ^ 32) (hb1 : b1.val < 2 ^ 32) (_hb2 : b2.val < 2 ^ 32) :
    (r2.val < b2.val ∨
      r2.val = b2.val ∧ (r1.val * 2 ^ 32 + r0.val < b1.val * 2 ^ 32 + b0.val)) ↔
      r2.val * 2 ^ 64 + r1.val * 2 ^ 32 + r0.val <
        b2.val * 2 ^ 64 + b1.val * 2 ^ 32 + b0.val := by
  constructor
  · intro h
    rcases h with h | ⟨hEq, hlow⟩ <;> omega
  · intro h
    by_cases h2 : r2.val < b2.val
    · exact Or.inl h2
    · right
      refine ⟨?_, ?_⟩ <;> omega

private theorem divmodLow128_lt_iff (r0 r1 r2 r3 b0 b1 b2 b3 : Felt)
    (hr0 : r0.val < 2 ^ 32) (hr1 : r1.val < 2 ^ 32) (hr2 : r2.val < 2 ^ 32) (_hr3 : r3.val < 2 ^ 32)
    (hb0 : b0.val < 2 ^ 32) (hb1 : b1.val < 2 ^ 32) (hb2 : b2.val < 2 ^ 32) (_hb3 : b3.val < 2 ^ 32) :
    (r3.val < b3.val ∨
      r3.val = b3.val ∧
        (r2.val * 2 ^ 64 + r1.val * 2 ^ 32 + r0.val <
          b2.val * 2 ^ 64 + b1.val * 2 ^ 32 + b0.val)) ↔
      r3.val * 2 ^ 96 + r2.val * 2 ^ 64 + r1.val * 2 ^ 32 + r0.val <
        b3.val * 2 ^ 96 + b2.val * 2 ^ 64 + b1.val * 2 ^ 32 + b0.val := by
  constructor
  · intro h
    rcases h with h | ⟨hEq, hlow⟩ <;> omega
  · intro h
    by_cases h3 : r3.val < b3.val
    · exact Or.inl h3
    · right
      refine ⟨?_, ?_⟩ <;> omega

private theorem divmodLtBool_eqRaw
    (r0 r1 r2 r3 b0 b1 b2 b3 : Felt)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true) (hr2 : r2.isU32 = true) (hr3 : r3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    u128LtBool r0 r1 r2 r3 b0 b1 b2 b3 =
      decide
        (r3.val * 2 ^ 96 + r2.val * 2 ^ 64 + r1.val * 2 ^ 32 + r0.val <
          b3.val * 2 ^ 96 + b2.val * 2 ^ 64 + b1.val * 2 ^ 32 + b0.val) := by
  have hr0' : r0.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hr0
  have hr1' : r1.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hr1
  have hr2' : r2.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hr2
  have hr3' : r3.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hr3
  have hb0' : b0.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb0
  have hb1' : b1.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb1
  have hb2' : b2.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb2
  have hb3' : b3.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb3
  unfold u128LtBool u128Sub3 u32OverflowingSub u32Max
  rw [divmodBorrow2_eq r0 r1 r2 b0 b1 b2 hr0 hr1 hb0 hb1]
  rw [felt_ite_val_local]
  by_cases h3 : r3.val < b3.val
  · simp [decide_eq_true h3]
    omega
  · by_cases h3e : r3.val = b3.val
    · simp only [h3e]
      split_ifs <;> simp_all <;> omega
    · have h3gt : r3.val > b3.val := by omega
      simp [show ¬ (r3.val < b3.val) from h3]
      split_ifs <;> simp_all <;> omega

private def divmodSetup : List Op := [
  .inst (.emitImm 15463989275656898604),
  .inst (.padw),
  .inst (.advLoadW),
  .inst (.u32AssertW),
  .inst (.padw),
  .inst (.advLoadW),
  .inst (.u32AssertW)
]

private theorem divmodSetup_run
    (q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a0 a1 a2 a3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq0 : q0.isU32 = true) (hq1 : q1.isU32 = true) (hq2 : q2.isU32 = true) (hq3 : q3.isU32 = true)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true) (hr2 : r2.isU32 = true) (hr3 : r3.isU32 = true) :
    exec 163
      ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest,
        mem, locs, r0 :: r1 :: r2 :: r3 :: q0 :: q1 :: q2 :: q3 :: adv_rest⟩
      divmodSetup =
    some ⟨q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
            b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest,
          mem, locs, adv_rest⟩ := by
  unfold divmodSetup exec execWithEnv
  simp only [List.foldlM]
  rw [show execInstruction
      ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs,
        r0 :: r1 :: r2 :: r3 :: q0 :: q1 :: q2 :: q3 :: adv_rest⟩
      (.emitImm 15463989275656898604) =
      some ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs,
        r0 :: r1 :: r2 :: r3 :: q0 :: q1 :: q2 :: q3 :: adv_rest⟩ by
      unfold execInstruction
      rfl]
  miden_bind
  rw [stepPadw]
  miden_bind
  rw [stepAdvLoadWLocal mem locs 0 0 0 0 (b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
      r0 r1 r2 r3 (q0 :: q1 :: q2 :: q3 :: adv_rest)]
  miden_bind
  rw [stepU32AssertWLocal mem locs (q0 :: q1 :: q2 :: q3 :: adv_rest)
      r0 r1 r2 r3 (b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
      hr0 hr1 hr2 hr3]
  miden_bind
  rw [stepPadw]
  miden_bind
  rw [stepAdvLoadWLocal mem locs 0 0 0 0
      (r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
      q0 q1 q2 q3 adv_rest]
  miden_bind
  rw [stepU32AssertWLocal mem locs adv_rest
      q0 q1 q2 q3 (r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
      hq0 hq1 hq2 hq3]
  simp [pure, Pure.pure]

private def divmodCol0 : List Op := [
  .inst (.dup 8),
  .inst (.dup 1),
  .inst (.u32WidenMul),
  .inst (.dup 6),
  .inst (.u32WidenAdd),
  .inst (.movup 15),
  .inst (.assertEqWithError "u128 divmod: col 0"),
  .inst (.add)
]

private theorem divmodCol0Carry_lt
    (q0 b0 r0 : Felt)
    (hq0 : q0.isU32 = true) (hb0 : b0.isU32 = true) (hr0 : r0.isU32 = true) :
    u128DivmodCol0 q0.val b0.val r0.val / 2 ^ 32 < 2 ^ 32 := by
  simp [Felt.isU32, decide_eq_true_eq] at hq0 hb0 hr0
  have hsum :
      u128DivmodCol0 q0.val b0.val r0.val ≤
        (2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1) := by
    unfold u128DivmodCol0
    have hprod : q0.val * b0.val ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := by
      exact Nat.mul_le_mul (Nat.le_pred_of_lt hq0) (Nat.le_pred_of_lt hb0)
    exact Nat.add_le_add hprod (Nat.le_pred_of_lt hr0)
  calc
    u128DivmodCol0 q0.val b0.val r0.val / 2 ^ 32
        ≤ ((2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := by
            exact Nat.div_le_div_right hsum
    _ < 2 ^ 32 := by native_decide

private theorem divmodCol0Lo_eq
    (q0 b0 r0 : Felt) :
    Felt.ofNat (u128DivmodCol0 q0.val b0.val r0.val % 2 ^ 32) =
      Felt.ofNat (((b0.val * q0.val) % 2 ^ 32 + r0.val) % 2 ^ 32) := by
  congr 1
  simp [u128DivmodCol0, Nat.mul_comm]

private theorem divmodCol0Carry_eq
    (q0 b0 r0 : Felt)
    (hq0 : q0.isU32 = true) (hb0 : b0.isU32 = true) (hr0 : r0.isU32 = true) :
    Felt.ofNat (u128DivmodCol0 q0.val b0.val r0.val / 2 ^ 32) =
      Felt.ofNat ((b0.val * q0.val) / 2 ^ 32) +
        Felt.ofNat (((b0.val * q0.val) % 2 ^ 32 + r0.val) / 2 ^ 32) := by
  have hnat :
      u128DivmodCol0 q0.val b0.val r0.val / 2 ^ 32 =
        (b0.val * q0.val) / 2 ^ 32 +
          (((b0.val * q0.val) % 2 ^ 32 + r0.val) / 2 ^ 32) := by
    let base := 2 ^ 32
    let prod := b0.val * q0.val
    have hsplit : prod % base + base * (prod / base) = q0.val * b0.val := by
      simpa [prod, base, Nat.mul_comm] using (Nat.mod_add_div prod base)
    calc
      u128DivmodCol0 q0.val b0.val r0.val / 2 ^ 32
          = (base * (prod / base) + (prod % base + r0.val)) / base := by
              change (q0.val * b0.val + r0.val) / 2 ^ 32 =
                (base * (prod / base) + (prod % base + r0.val)) / base
              rw [← hsplit]
              congr 1
              omega
      _ = prod / base + (prod % base + r0.val) / base := by
            rw [Nat.mul_add_div (show 0 < base by native_decide)]
      _ = (b0.val * q0.val) / 2 ^ 32 +
            (((b0.val * q0.val) % 2 ^ 32 + r0.val) / 2 ^ 32) := by
            simp [prod, base]
  have hcarry0_val :
      (Felt.ofNat (((b0.val * q0.val) % 2 ^ 32 + r0.val) / 2 ^ 32)).val =
        ((b0.val * q0.val) % 2 ^ 32 + r0.val) / 2 ^ 32 := by
    simpa [Nat.mul_comm] using u32_prod_mod_add_div_val b0 q0 r0 hb0 hq0 hr0
  have hsum_val :
      (Felt.ofNat (u128DivmodCol0 q0.val b0.val r0.val / 2 ^ 32)).val =
        u128DivmodCol0 q0.val b0.val r0.val / 2 ^ 32 := by
    apply felt_ofNat_val_lt
    exact u32_val_lt_prime _ (divmodCol0Carry_lt q0 b0 r0 hq0 hb0 hr0)
  have hsum_lt :
      (b0.val * q0.val) / 2 ^ 32 +
          (((b0.val * q0.val) % 2 ^ 32 + r0.val) / 2 ^ 32) < 2 ^ 32 := by
    have h1 : (b0.val * q0.val) / 2 ^ 32 ≤ 2 ^ 32 - 2 := by
      calc
        (b0.val * q0.val) / 2 ^ 32 ≤ ((2 ^ 32 - 1) * (2 ^ 32 - 1)) / 2 ^ 32 := by
          apply Nat.div_le_div_right
          simp [Felt.isU32, decide_eq_true_eq] at hq0 hb0
          exact Nat.mul_le_mul (Nat.le_pred_of_lt hb0) (Nat.le_pred_of_lt hq0)
        _ ≤ 2 ^ 32 - 2 := by native_decide
    have h2 : (((b0.val * q0.val) % 2 ^ 32 + r0.val) / 2 ^ 32) ≤ 1 := by
      simpa [Nat.mul_comm] using u32_prod_mod_add_div_le_one b0 q0 r0 hb0 hq0 hr0
    omega
  apply ZMod.val_injective
  rw [hsum_val]
  rw [felt_add_val_no_wrap _ _ (by
    rw [felt_ofNat_val_lt _ (u32_prod_div_lt_prime b0 q0 hb0 hq0)]
    rw [hcarry0_val]
    exact u32_val_lt_prime _ hsum_lt)]
  rw [felt_ofNat_val_lt _ (u32_prod_div_lt_prime b0 q0 hb0 hq0)]
  rw [hcarry0_val]
  rw [hnat]

private theorem divmodCol0_run
    (q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a0 a1 a2 a3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq0 : q0.isU32 = true) (_hq1 : q1.isU32 = true) (_hq2 : q2.isU32 = true) (_hq3 : q3.isU32 = true)
    (hr0 : r0.isU32 = true) (ha0_eq : a0 = Felt.ofNat (u128DivmodCol0 q0.val b0.val r0.val % 2 ^ 32))
    (hb0 : b0.isU32 = true) :
    exec 163
      ⟨q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
        b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest,
        mem, locs, adv_rest⟩
      divmodCol0 =
    some ⟨Felt.ofNat (u128DivmodCol0 q0.val b0.val r0.val / 2 ^ 32) ::
            q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
            b0 :: b1 :: b2 :: b3 :: a1 :: a2 :: a3 :: rest,
          mem, locs, adv_rest⟩ := by
  unfold divmodCol0 exec execWithEnv
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepU32WidenMul (ha := hb0) (hb := hq0)]
  miden_bind
  miden_dup
  rw [stepU32WidenAdd (ha := u32_mod_isU32 _) (hb := hr0)]
  miden_bind
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  miden_movup
  rw [ha0_eq]
  rw [divmodCol0Lo_eq q0 b0 r0]
  rw [stepAssertEqWithError]
  miden_bind
  rw [stepAdd]
  miden_bind
  simpa [pure, Pure.pure] using
    (congrArg
      (fun x : Felt =>
        some
          ({ stack := x :: q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
              b0 :: b1 :: b2 :: b3 :: a1 :: a2 :: a3 :: rest
            , memory := mem
            , locals := locs
            , advice := adv_rest } : MidenState))
      (divmodCol0Carry_eq q0 b0 r0 hq0 hb0 hr0).symm)

private theorem divmodCol0_none
    (q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a0 a1 a2 a3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq0 : q0.isU32 = true) (_hq1 : q1.isU32 = true) (_hq2 : q2.isU32 = true) (_hq3 : q3.isU32 = true)
    (hr0 : r0.isU32 = true)
    (hb0 : b0.isU32 = true)
    (ha0_ne : a0 ≠ Felt.ofNat (u128DivmodCol0 q0.val b0.val r0.val % 2 ^ 32)) :
    exec 163
      ⟨q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
        b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest,
        mem, locs, adv_rest⟩
      divmodCol0 =
    none := by
  unfold divmodCol0 exec execWithEnv
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepU32WidenMul (ha := hb0) (hb := hq0)]
  miden_bind
  miden_dup
  rw [stepU32WidenAdd (ha := u32_mod_isU32 _) (hb := hr0)]
  miden_bind
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  miden_movup
  have ha0_ne' : a0 ≠ Felt.ofNat (((b0.val * q0.val) % 2 ^ 32 + r0.val) % 2 ^ 32) := by
    simpa [u128DivmodCol0, Nat.mul_comm, Nat.add_mod, Nat.mod_mod] using ha0_ne
  rw [stepAssertEqWithError_none (msg := "u128 divmod: col 0") (h := ha0_ne'.symm)]

private def divmodCol1 : List Op := [
  .inst (.dup 9),
  .inst (.dup 3),
  .inst (.u32WidenMadd),
  .inst (.dup 11),
  .inst (.dup 3),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.add),
  .inst (.swap 1),
  .inst (.dup 7),
  .inst (.u32WidenAdd),
  .inst (.movup 15),
  .inst (.assertEqWithError "u128 divmod: col 1"),
  .inst (.add),
  .inst (.u32Split)
]

set_option maxHeartbeats 12000000 in
private theorem divmodCol1_run
    (c0 q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a1 a2 a3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq0 : q0.isU32 = true) (hq1 : q1.isU32 = true)
    (hr1 : r1.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hc0_u32 : c0.isU32 = true)
    (hc0_val : c0.val = u128DivmodCol0 q0.val b0.val r0.val / 2 ^ 32)
    (ha1_eq : a1 = Felt.ofNat (u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val % 2 ^ 32)) :
    exec 163
      ⟨c0 :: q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
        b0 :: b1 :: b2 :: b3 :: a1 :: a2 :: a3 :: rest,
        mem, locs, adv_rest⟩
      divmodCol1 =
    some ⟨Felt.ofNat (u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / 2 ^ 32 % 2 ^ 32) ::
            Felt.ofNat (u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / 2 ^ 32 / 2 ^ 32) ::
            q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
            b0 :: b1 :: b2 :: b3 :: a2 :: a3 :: rest,
          mem, locs, adv_rest⟩ := by
  let base := 2 ^ 32
  let carry0 := u128DivmodCol0 q0.val b0.val r0.val / base
  let madd0Lo := (b0.val * q1.val + carry0) % base
  let madd0Hi := (b0.val * q1.val + carry0) / base
  let madd1Lo := (b1.val * q0.val + madd0Lo) % base
  let madd1Hi := (b1.val * q0.val + madd0Lo) / base
  let addLo := (madd1Lo + r1.val) % base
  let addHi := (madd1Lo + r1.val) / base
  let carry := madd0Hi + madd1Hi + addHi
  have hmadd0Lo_val : (Felt.ofNat madd0Lo).val = madd0Lo := by
    apply felt_ofNat_val_lt
    dsimp [madd0Lo, base]
    exact u32_mod_lt_prime _
  have hmadd1Lo_val : (Felt.ofNat madd1Lo).val = madd1Lo := by
    apply felt_ofNat_val_lt
    dsimp [madd1Lo, base]
    exact u32_mod_lt_prime _
  have hmadd0Hi_lt : madd0Hi < base := by
    dsimp [madd0Hi]
    simpa [base, carry0, hc0_val, Nat.mul_comm] using
      (u32_madd_div_lt_2_32 b0 q1 c0 hb0 hq1 hc0_u32)
  have hmadd1Hi_lt : madd1Hi < base := by
    dsimp [madd1Hi]
    have h := u32_madd_div_lt_2_32 b1 q0 (Felt.ofNat madd0Lo) hb1 hq0 (u32_mod_isU32 _)
    rw [hmadd0Lo_val] at h
    simpa [base, madd0Lo, Nat.mul_comm] using h
  have haddHi_le_one : addHi ≤ 1 := by
    dsimp [addHi]
    have h := u32_add_div_le_one (Felt.ofNat madd1Lo) r1 (u32_mod_isU32 _) hr1
    rw [hmadd1Lo_val] at h
    simpa [base, madd1Lo] using h
  have hrepr : u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val = addLo + carry * base := by
    have h0 : madd0Lo + madd0Hi * base = q1.val * b0.val + carry0 := by
      simpa [madd0Lo, madd0Hi, base, Nat.mul_comm] using
        (Nat.mod_add_div (b0.val * q1.val + carry0) base)
    have h1 : madd1Lo + madd1Hi * base = q0.val * b1.val + madd0Lo := by
      simpa [madd1Lo, madd1Hi, base, Nat.mul_comm] using
        (Nat.mod_add_div (b1.val * q0.val + madd0Lo) base)
    have h2 : addLo + addHi * base = madd1Lo + r1.val := by
      simpa [addLo, addHi, base, Nat.mul_comm] using
        (Nat.mod_add_div (madd1Lo + r1.val) base)
    calc
      u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val
          = q0.val * b1.val + r1.val + (q1.val * b0.val + carry0) := by
              unfold u128DivmodCol1
              simp [carry0, base, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      _ = q0.val * b1.val + r1.val + (madd0Lo + madd0Hi * base) := by rw [← h0]
      _ = q0.val * b1.val + madd0Lo + r1.val + madd0Hi * base := by ac_rfl
      _ = (madd1Lo + madd1Hi * base) + r1.val + madd0Hi * base := by rw [h1]
      _ = madd1Lo + r1.val + madd1Hi * base + madd0Hi * base := by ac_rfl
      _ = addLo + addHi * base + madd1Hi * base + madd0Hi * base := by rw [h2]
      _ = addLo + (madd0Hi + madd1Hi + addHi) * base := by
            simp [base, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hlo_lt : addLo < base := by
    dsimp [addLo, base]
    exact Nat.mod_lt _ (by positivity)
  have hlo_nat : u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val % base = addLo := by
    calc
      u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val % base = (addLo + carry * base) % base := by
        rw [hrepr]
      _ = addLo % base := by rw [Nat.add_mul_mod_self_right]
      _ = addLo := Nat.mod_eq_of_lt hlo_lt
  have hcarry_nat : u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / base = carry := by
    rw [hrepr, Nat.add_mul_div_right _ _ (show 0 < base by positivity), Nat.div_eq_of_lt hlo_lt]
    simp [carry]
  have hcarry_lt_prime : carry < GOLDILOCKS_PRIME := by
    unfold GOLDILOCKS_PRIME carry
    omega
  have hcarry_val : (Felt.ofNat carry).val = carry := by
    exact felt_ofNat_val_lt _ hcarry_lt_prime
  unfold divmodCol1 exec execWithEnv
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepU32WidenMadd (a := b0) (b := q1) (c := c0) (ha := hb0) (hb := hq1) (hc := hc0_u32)]
  miden_bind
  rw [hc0_val]
  miden_dup
  miden_dup
  rw [stepU32WidenMadd
    (a := b1) (b := q0) (c := Felt.ofNat madd0Lo)
    (ha := hb1) (hb := hq0) (hc := u32_mod_isU32 _)]
  miden_bind
  rw [hmadd0Lo_val]
  miden_swap
  miden_movup
  rw [stepAdd]
  miden_bind
  rw [← felt_ofNat_add]
  miden_swap
  miden_dup
  rw [stepU32WidenAdd
    (a := Felt.ofNat madd1Lo) (b := r1)
    (ha := u32_mod_isU32 _) (hb := hr1)]
  miden_bind
  rw [hmadd1Lo_val]
  miden_movup
  rw [ha1_eq]
  have hlo_eq :
      Felt.ofNat (u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val % base) =
        Felt.ofNat addLo := by
    exact congrArg Felt.ofNat hlo_nat
  rw [hlo_eq]
  rw [stepAssertEqWithError]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [← felt_ofNat_add]
  rw [show Felt.ofNat (madd1Hi + madd0Hi + addHi) = Felt.ofNat carry by
    simp [carry, Nat.add_assoc, Nat.add_comm]]
  rw [stepU32Split]
  simp [pure, Pure.pure]
  constructor
  · simpa [Felt.lo32, hcarry_val, base] using
      congrArg (fun n => Felt.ofNat (n % 2 ^ 32)) hcarry_nat.symm
  · simpa [Felt.hi32, hcarry_val, base] using
      congrArg (fun n => Felt.ofNat (n / 2 ^ 32)) hcarry_nat.symm

private theorem divmodCol1_none
    (c0 q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a1 a2 a3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq0 : q0.isU32 = true) (hq1 : q1.isU32 = true)
    (hr1 : r1.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hc0_u32 : c0.isU32 = true)
    (hc0_val : c0.val = u128DivmodCol0 q0.val b0.val r0.val / 2 ^ 32)
    (ha1_ne : a1 ≠ Felt.ofNat (u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val % 2 ^ 32)) :
    exec 163
      ⟨c0 :: q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
        b0 :: b1 :: b2 :: b3 :: a1 :: a2 :: a3 :: rest,
        mem, locs, adv_rest⟩
      divmodCol1 =
    none := by
  let base := 2 ^ 32
  let carry0 := u128DivmodCol0 q0.val b0.val r0.val / base
  let madd0Lo := (b0.val * q1.val + carry0) % base
  let madd0Hi := (b0.val * q1.val + carry0) / base
  let madd1Lo := (b1.val * q0.val + madd0Lo) % base
  let madd1Hi := (b1.val * q0.val + madd0Lo) / base
  let addLo := (madd1Lo + r1.val) % base
  let addHi := (madd1Lo + r1.val) / base
  let carry := madd0Hi + madd1Hi + addHi
  have hmadd0Lo_val : (Felt.ofNat madd0Lo).val = madd0Lo := by
    apply felt_ofNat_val_lt
    dsimp [madd0Lo, base]
    exact u32_mod_lt_prime _
  have hmadd1Lo_val : (Felt.ofNat madd1Lo).val = madd1Lo := by
    apply felt_ofNat_val_lt
    dsimp [madd1Lo, base]
    exact u32_mod_lt_prime _
  have hrepr : u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val = addLo + carry * base := by
    have h0 : madd0Lo + madd0Hi * base = q1.val * b0.val + carry0 := by
      simpa [madd0Lo, madd0Hi, base, Nat.mul_comm] using
        (Nat.mod_add_div (b0.val * q1.val + carry0) base)
    have h1 : madd1Lo + madd1Hi * base = q0.val * b1.val + madd0Lo := by
      simpa [madd1Lo, madd1Hi, base, Nat.mul_comm] using
        (Nat.mod_add_div (b1.val * q0.val + madd0Lo) base)
    have h2 : addLo + addHi * base = madd1Lo + r1.val := by
      simpa [addLo, addHi, base, Nat.mul_comm] using
        (Nat.mod_add_div (madd1Lo + r1.val) base)
    calc
      u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val
          = q0.val * b1.val + r1.val + (q1.val * b0.val + carry0) := by
              unfold u128DivmodCol1
              simp [carry0, base, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      _ = q0.val * b1.val + r1.val + (madd0Lo + madd0Hi * base) := by rw [← h0]
      _ = q0.val * b1.val + madd0Lo + r1.val + madd0Hi * base := by ac_rfl
      _ = (madd1Lo + madd1Hi * base) + r1.val + madd0Hi * base := by rw [h1]
      _ = madd1Lo + r1.val + madd1Hi * base + madd0Hi * base := by ac_rfl
      _ = addLo + addHi * base + madd1Hi * base + madd0Hi * base := by rw [h2]
      _ = addLo + (madd0Hi + madd1Hi + addHi) * base := by
            simp [base, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have haddLo_lt : addLo < base := by
    dsimp [addLo, base]
    exact Nat.mod_lt _ (by positivity)
  have hlo_nat : u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val % base = addLo := by
    calc
      u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val % base = (addLo + carry * base) % base := by
        rw [hrepr]
      _ = addLo % base := by rw [Nat.add_mul_mod_self_right]
      _ = addLo := Nat.mod_eq_of_lt haddLo_lt
  have ha1_ne' : a1 ≠ Felt.ofNat addLo := by
    intro hEq
    apply ha1_ne
    calc
      a1 = Felt.ofNat addLo := hEq
      _ = Felt.ofNat (u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val % 2 ^ 32) := by
            exact congrArg Felt.ofNat hlo_nat.symm
  unfold divmodCol1 exec execWithEnv
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepU32WidenMadd (a := b0) (b := q1) (c := c0) (ha := hb0) (hb := hq1) (hc := hc0_u32)]
  miden_bind
  rw [hc0_val]
  miden_dup
  miden_dup
  rw [stepU32WidenMadd
    (a := b1) (b := q0) (c := Felt.ofNat madd0Lo)
    (ha := hb1) (hb := hq0) (hc := u32_mod_isU32 _)]
  miden_bind
  rw [hmadd0Lo_val]
  miden_swap
  miden_movup
  rw [stepAdd]
  miden_bind
  rw [← felt_ofNat_add]
  miden_swap
  miden_dup
  rw [stepU32WidenAdd
    (a := Felt.ofNat madd1Lo) (b := r1)
    (ha := u32_mod_isU32 _) (hb := hr1)]
  miden_bind
  rw [hmadd1Lo_val]
  miden_movup
  rw [show Felt.ofNat ((madd1Lo + r1.val) % 2 ^ 32) = Felt.ofNat addLo by rfl]
  rw [stepAssertEqWithError_none (msg := "u128 divmod: col 1") (h := ha1_ne'.symm)]

private def divmodCol2a : List Op := [
  .inst (.dup 10),
  .inst (.dup 5),
  .inst (.u32WidenMadd),
  .inst (.dup 12),
  .inst (.dup 5),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.movup 3),
  .inst (.add),
  .inst (.add),
  .inst (.swap 1)
]

private def divmodCol2b : List Op := [
  .inst (.dup 12),
  .inst (.dup 3),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.add),
  .inst (.swap 1)
]

private def divmodCol2c : List Op := [
  .inst (.dup 8),
  .inst (.u32WidenAdd),
  .inst (.movup 15),
  .inst (.assertEqWithError "u128 divmod: col 2"),
  .inst (.add),
  .inst (.u32Split)
]

private def divmodCol2 : List Op :=
  divmodCol2a ++ divmodCol2b ++ divmodCol2c

private theorem divmodCol2_eq :
    divmodCol2 = divmodCol2a ++ (divmodCol2b ++ divmodCol2c) := by
  simp [divmodCol2]

set_option maxHeartbeats 12000000 in
private theorem divmodCol2a_run
    (c1Lo c1Hi q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a2 a3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq1 : q1.isU32 = true) (hq2 : q2.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hc1Lo_u32 : c1Lo.isU32 = true)
    (hc1Lo_val :
      c1Lo.val = u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / 2 ^ 32 % 2 ^ 32) :
    let base := 2 ^ 32
    let lo0 := (b0.val * q2.val + c1Lo.val) % base
    let hi0 := (b0.val * q2.val + c1Lo.val) / base
    let lo1 := (b1.val * q1.val + lo0) % base
    let hi1 := (b1.val * q1.val + lo0) / base
    let sumHi := c1Hi.val + hi0 + hi1
    exec 163
      ⟨c1Lo :: c1Hi :: q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
        b0 :: b1 :: b2 :: b3 :: a2 :: a3 :: rest,
        mem, locs, adv_rest⟩
      divmodCol2a =
    some ⟨Felt.ofNat lo1 :: Felt.ofNat sumHi ::
            q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
            b0 :: b1 :: b2 :: b3 :: a2 :: a3 :: rest,
          mem, locs, adv_rest⟩ := by
  let base := 2 ^ 32
  let lo0 := (b0.val * q2.val + c1Lo.val) % base
  let hi0 := (b0.val * q2.val + c1Lo.val) / base
  let lo1 := (b1.val * q1.val + lo0) % base
  let hi1 := (b1.val * q1.val + lo0) / base
  let sumHi := c1Hi.val + hi0 + hi1
  have hc1Hi_eq : c1Hi = Felt.ofNat c1Hi.val := by
    exact felt_eq_ofNat_of_val_eq c1Hi c1Hi.val rfl (felt_val_lt_prime _)
  have hlo0_val : (Felt.ofNat lo0).val = lo0 := by
    apply felt_ofNat_val_lt
    dsimp [lo0, base]
    exact u32_mod_lt_prime _
  have hhi0_eq :
      Felt.ofNat
          ((b0.val * q2.val +
                u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / 2 ^ 32 % 2 ^ 32) /
            2 ^ 32) =
        Felt.ofNat hi0 := by
    simp [hi0, base, hc1Lo_val]
  have hlo0_eq :
      Felt.ofNat
          ((b0.val * q2.val +
                u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / 2 ^ 32 % 2 ^ 32) %
            2 ^ 32) =
        Felt.ofNat lo0 := by
    simp [lo0, base, hc1Lo_val]
  unfold divmodCol2a exec execWithEnv
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepU32WidenMadd (a := b0) (b := q2) (c := c1Lo) (ha := hb0) (hb := hq2) (hc := hc1Lo_u32)]
  miden_bind
  rw [hc1Lo_val]
  miden_dup
  miden_dup
  rw [hlo0_eq]
  rw [stepU32WidenMadd
    (a := b1) (b := q1) (c := Felt.ofNat lo0)
    (ha := hb1) (hb := hq1) (hc := u32_mod_isU32 _)]
  miden_bind
  rw [hlo0_val]
  miden_swap
  miden_movup
  miden_movup
  rw [stepAdd]
  miden_bind
  rw [hhi0_eq]
  rw [hc1Hi_eq]
  rw [← felt_ofNat_add]
  rw [show hi0 + c1Hi.val = c1Hi.val + hi0 by omega]
  rw [stepAdd]
  miden_bind
  rw [show Felt.ofNat ((b1.val * q1.val + lo0) / 2 ^ 32) = Felt.ofNat hi1 by rfl]
  rw [← felt_ofNat_add]
  rw [show hi1 + (c1Hi.val + hi0) = sumHi by
    dsimp [sumHi]
    omega]
  rw [show Felt.ofNat ((b1.val * q1.val + lo0) % 2 ^ 32) = Felt.ofNat lo1 by rfl]
  miden_swap
  simp [pure, Pure.pure]
  constructor
  · apply congrArg Felt.ofNat
    dsimp [lo1, lo0, base]
    rw [hc1Lo_val]
    exact add_add_mod_right_mod
      (b1.val * q1.val)
      (b0.val * q2.val)
      (u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / 2 ^ 32)
      base
  · rw [felt_ofNat_val_lt _ (felt_val_lt_prime c1Hi)]
    simp [sumHi, hi0, hi1, lo0, base, hc1Lo_val]

set_option maxHeartbeats 12000000 in
private theorem divmodCol2b_run
    (c1Lo c1Hi q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a2 a3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq0 : q0.isU32 = true) (hb2 : b2.isU32 = true) :
    let base := 2 ^ 32
    let lo0 := (b0.val * q2.val + c1Lo.val) % base
    let hi0 := (b0.val * q2.val + c1Lo.val) / base
    let lo1 := (b1.val * q1.val + lo0) % base
    let hi1 := (b1.val * q1.val + lo0) / base
    let sumHi := c1Hi.val + hi0 + hi1
    let madd2Lo := (b2.val * q0.val + lo1) % base
    let madd2Hi := (b2.val * q0.val + lo1) / base
    exec 163
      ⟨Felt.ofNat lo1 :: Felt.ofNat sumHi ::
        q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
        b0 :: b1 :: b2 :: b3 :: a2 :: a3 :: rest,
        mem, locs, adv_rest⟩
      divmodCol2b =
    some ⟨Felt.ofNat madd2Lo :: Felt.ofNat (sumHi + madd2Hi) ::
            q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
            b0 :: b1 :: b2 :: b3 :: a2 :: a3 :: rest,
          mem, locs, adv_rest⟩ := by
  let base := 2 ^ 32
  let lo0 := (b0.val * q2.val + c1Lo.val) % base
  let hi0 := (b0.val * q2.val + c1Lo.val) / base
  let lo1 := (b1.val * q1.val + lo0) % base
  let hi1 := (b1.val * q1.val + lo0) / base
  let sumHi := c1Hi.val + hi0 + hi1
  let madd2Lo := (b2.val * q0.val + lo1) % base
  let madd2Hi := (b2.val * q0.val + lo1) / base
  have hlo1_flat :
      lo1 = (b1.val * q1.val + (b0.val * q2.val + c1Lo.val)) % base := by
    dsimp [lo1, lo0]
    rw [add_mod_right_mod]
  unfold divmodCol2b exec execWithEnv
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepU32WidenMadd
    (a := b2) (b := q0) (c := Felt.ofNat lo1)
    (ha := hb2) (hb := hq0) (hc := u32_mod_isU32 _)]
  miden_bind
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  miden_swap
  miden_movup
  rw [stepAdd]
  miden_bind
  rw [show Felt.ofNat ((b2.val * q0.val + lo1) / 2 ^ 32) = Felt.ofNat madd2Hi by rfl]
  rw [← felt_ofNat_add]
  rw [show madd2Hi + sumHi = sumHi + madd2Hi by omega]
  rw [show Felt.ofNat ((b2.val * q0.val + lo1) % 2 ^ 32) = Felt.ofNat madd2Lo by rfl]
  miden_swap
  simp [pure, Pure.pure]
  dsimp [sumHi, madd2Hi, hi0, hi1]
  rw [hlo1_flat]
  rfl

set_option maxHeartbeats 12000000 in
private theorem divmodCol2c_run
    (c1Lo c1Hi q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a2 a3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq0 : q0.isU32 = true) (hq1 : q1.isU32 = true) (hq2 : q2.isU32 = true)
    (hr2 : r2.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) (hb2 : b2.isU32 = true)
    (hc1Lo_u32 : c1Lo.isU32 = true) (hc1Hi_u32 : c1Hi.isU32 = true)
    (hc1Lo_val :
      c1Lo.val = u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / 2 ^ 32 % 2 ^ 32)
    (hc1Hi_val :
      c1Hi.val = u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / 2 ^ 32 / 2 ^ 32)
    (ha2_eq :
      a2 = Felt.ofNat (u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val % 2 ^ 32)) :
    let base := 2 ^ 32
    let _carry1 := u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / base
    let lo0 := (b0.val * q2.val + c1Lo.val) % base
    let hi0 := (b0.val * q2.val + c1Lo.val) / base
    let lo1 := (b1.val * q1.val + lo0) % base
    let hi1 := (b1.val * q1.val + lo0) / base
    let sumHi := c1Hi.val + hi0 + hi1
    let madd2Lo := (b2.val * q0.val + lo1) % base
    let madd2Hi := (b2.val * q0.val + lo1) / base
    exec 163
      ⟨Felt.ofNat madd2Lo :: Felt.ofNat (sumHi + madd2Hi) ::
        q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
        b0 :: b1 :: b2 :: b3 :: a2 :: a3 :: rest,
        mem, locs, adv_rest⟩
      divmodCol2c =
    some ⟨Felt.ofNat
              (u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val /
                  2 ^ 32 %
                2 ^ 32) ::
            Felt.ofNat
              (u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val /
                  2 ^ 32 /
                2 ^ 32) ::
            q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
            b0 :: b1 :: b2 :: b3 :: a3 :: rest,
          mem, locs, adv_rest⟩ := by
  let base := 2 ^ 32
  let carry1 := u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / base
  let lo0 := (b0.val * q2.val + c1Lo.val) % base
  let hi0 := (b0.val * q2.val + c1Lo.val) / base
  let lo1 := (b1.val * q1.val + lo0) % base
  let hi1 := (b1.val * q1.val + lo0) / base
  let sumHi := c1Hi.val + hi0 + hi1
  let madd2Lo := (b2.val * q0.val + lo1) % base
  let madd2Hi := (b2.val * q0.val + lo1) / base
  let addLo := (madd2Lo + r2.val) % base
  let addHi := (madd2Lo + r2.val) / base
  let carry := sumHi + madd2Hi + addHi
  have hc1Hi_lt : c1Hi.val < base := by
    simp [Felt.isU32, decide_eq_true_eq] at hc1Hi_u32
    simpa [base] using hc1Hi_u32
  have hhi0_lt : hi0 < base := by
    dsimp [hi0]
    simpa [base, Nat.mul_comm] using
      (u32_madd_div_lt_2_32 b0 q2 c1Lo hb0 hq2 hc1Lo_u32)
  have hhi1_lt : hi1 < base := by
    dsimp [hi1]
    have h := u32_madd_div_lt_2_32 b1 q1 (Felt.ofNat lo0) hb1 hq1 (u32_mod_isU32 _)
    rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)] at h
    simpa [base, lo0, Nat.mul_comm] using h
  have hmadd2Hi_lt : madd2Hi < base := by
    dsimp [madd2Hi]
    have h := u32_madd_div_lt_2_32 b2 q0 (Felt.ofNat lo1) hb2 hq0 (u32_mod_isU32 _)
    rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)] at h
    simpa [base, lo1, Nat.mul_comm] using h
  have haddHi_le_one : addHi ≤ 1 := by
    dsimp [addHi]
    have h := u32_add_div_le_one (Felt.ofNat madd2Lo) r2 (u32_mod_isU32 _) hr2
    rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)] at h
    simpa [base, madd2Lo] using h
  have hcarry_lt_prime : carry < GOLDILOCKS_PRIME := by
    unfold carry sumHi GOLDILOCKS_PRIME
    omega
  have hcarry_val : (Felt.ofNat carry).val = carry := by
    exact felt_ofNat_val_lt _ hcarry_lt_prime
  have hcarry1_repr : c1Lo.val + c1Hi.val * base = carry1 := by
    rw [hc1Lo_val, hc1Hi_val]
    dsimp [carry1]
    simpa [base, Nat.mul_comm] using
      (Nat.mod_add_div (u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / 2 ^ 32) base)
  have hlo0_repr : lo0 + hi0 * base = q2.val * b0.val + c1Lo.val := by
    simpa [lo0, hi0, base, Nat.mul_comm] using
      (Nat.mod_add_div (b0.val * q2.val + c1Lo.val) base)
  have hlo1_repr : lo1 + hi1 * base = q1.val * b1.val + lo0 := by
    simpa [lo1, hi1, base, Nat.mul_comm] using
      (Nat.mod_add_div (b1.val * q1.val + lo0) base)
  have hpre_repr :
      q2.val * b0.val + q1.val * b1.val + carry1 = lo1 + sumHi * base := by
    calc
      q2.val * b0.val + q1.val * b1.val + carry1
          = q1.val * b1.val + (q2.val * b0.val + c1Lo.val) + c1Hi.val * base := by
              rw [← hcarry1_repr]
              ring
      _ = q1.val * b1.val + (lo0 + hi0 * base) + c1Hi.val * base := by rw [hlo0_repr]
      _ = (lo1 + hi1 * base) + (hi0 + c1Hi.val) * base := by
            rw [hlo1_repr]
            ring
      _ = lo1 + sumHi * base := by
            dsimp [sumHi]
            ring
  have hrepr :
      u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val =
        addLo + carry * base := by
    have hmadd2_repr : madd2Lo + madd2Hi * base = q0.val * b2.val + lo1 := by
      simpa [madd2Lo, madd2Hi, base, Nat.mul_comm] using
        (Nat.mod_add_div (b2.val * q0.val + lo1) base)
    have hadd_repr : addLo + addHi * base = madd2Lo + r2.val := by
      simpa [addLo, addHi, base, Nat.mul_comm] using
        (Nat.mod_add_div (madd2Lo + r2.val) base)
    calc
      u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val
          = q0.val * b2.val + r2.val + (q2.val * b0.val + q1.val * b1.val + carry1) := by
              unfold u128DivmodCol2
              dsimp [carry1, base]
              ring
      _ = q0.val * b2.val + r2.val + (lo1 + sumHi * base) := by rw [hpre_repr]
      _ = q0.val * b2.val + lo1 + r2.val + sumHi * base := by ring
      _ = (madd2Lo + madd2Hi * base) + r2.val + sumHi * base := by rw [hmadd2_repr]
      _ = madd2Lo + r2.val + (sumHi + madd2Hi) * base := by ring
      _ = addLo + addHi * base + (sumHi + madd2Hi) * base := by rw [hadd_repr]
      _ = addLo + (sumHi + madd2Hi + addHi) * base := by ring
  have haddLo_lt : addLo < base := by
    dsimp [addLo, base]
    exact Nat.mod_lt _ (by positivity)
  have hcarry_nat :
      u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / base = carry := by
    rw [hrepr, Nat.add_mul_div_right _ _ (show 0 < base by positivity), Nat.div_eq_of_lt haddLo_lt]
    simp [carry]
  unfold divmodCol2c exec execWithEnv
  simp only [List.foldlM]
  miden_dup
  rw [stepU32WidenAdd (a := Felt.ofNat madd2Lo) (b := r2) (ha := u32_mod_isU32 _) (hb := hr2)]
  miden_bind
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  miden_movup
  rw [ha2_eq]
  have hlo_eq :
      Felt.ofNat
          (u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val % base) =
        Felt.ofNat addLo := by
    exact congrArg Felt.ofNat <| by
      calc
        u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val % base
            = (addLo + carry * base) % base := by rw [hrepr]
        _ = addLo % base := by rw [Nat.add_mul_mod_self_right]
        _ = addLo := Nat.mod_eq_of_lt haddLo_lt
  rw [hlo_eq]
  rw [stepAssertEqWithError]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [← felt_ofNat_add]
  rw [show sumHi + madd2Hi + addHi = carry by
    dsimp [carry]]
  rw [stepU32Split]
  simp [pure, Pure.pure]
  constructor
  · simpa [Felt.lo32, hcarry_val, base] using
      congrArg (fun n => Felt.ofNat (n % 2 ^ 32)) hcarry_nat.symm
  · simpa [Felt.hi32, hcarry_val, base] using
      congrArg (fun n => Felt.ofNat (n / 2 ^ 32)) hcarry_nat.symm

private theorem divmodCol2c_none
    (c1Lo c1Hi q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a2 a3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (_hq0 : q0.isU32 = true) (_hq1 : q1.isU32 = true) (_hq2 : q2.isU32 = true)
    (hr2 : r2.isU32 = true)
    (_hb0 : b0.isU32 = true) (_hb1 : b1.isU32 = true) (_hb2 : b2.isU32 = true)
    (_hc1Lo_u32 : c1Lo.isU32 = true) (_hc1Hi_u32 : c1Hi.isU32 = true)
    (hc1Lo_val :
      c1Lo.val = u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / 2 ^ 32 % 2 ^ 32)
    (hc1Hi_val :
      c1Hi.val = u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / 2 ^ 32 / 2 ^ 32)
    (ha2_ne :
      a2 ≠ Felt.ofNat (u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val % 2 ^ 32)) :
    exec 163
      ⟨Felt.ofNat
          (((b2.val * q0.val +
                ((b1.val * q1.val + ((b0.val * q2.val + c1Lo.val) % 2 ^ 32)) % 2 ^ 32)) %
              2 ^ 32)) ::
        Felt.ofNat
          (c1Hi.val +
            ((b0.val * q2.val + c1Lo.val) / 2 ^ 32) +
            ((b1.val * q1.val + ((b0.val * q2.val + c1Lo.val) % 2 ^ 32)) / 2 ^ 32) +
            ((b2.val * q0.val +
                  ((b1.val * q1.val + ((b0.val * q2.val + c1Lo.val) % 2 ^ 32)) % 2 ^ 32)) /
                2 ^ 32)) ::
        q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
        b0 :: b1 :: b2 :: b3 :: a2 :: a3 :: rest,
        mem, locs, adv_rest⟩
      divmodCol2c =
    none := by
  let base := 2 ^ 32
  let carry1 := u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / base
  let lo0 := (b0.val * q2.val + c1Lo.val) % base
  let hi0 := (b0.val * q2.val + c1Lo.val) / base
  let lo1 := (b1.val * q1.val + lo0) % base
  let hi1 := (b1.val * q1.val + lo0) / base
  let sumHi := c1Hi.val + hi0 + hi1
  let madd2Lo := (b2.val * q0.val + lo1) % base
  let madd2Hi := (b2.val * q0.val + lo1) / base
  let addLo := (madd2Lo + r2.val) % base
  let addHi := (madd2Lo + r2.val) / base
  let carry := sumHi + madd2Hi + addHi
  have hcarry1_repr : c1Lo.val + c1Hi.val * base = carry1 := by
    rw [hc1Lo_val, hc1Hi_val]
    dsimp [carry1]
    simpa [base, Nat.mul_comm] using
      (Nat.mod_add_div (u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / 2 ^ 32) base)
  have hlo0_repr : lo0 + hi0 * base = q2.val * b0.val + c1Lo.val := by
    simpa [lo0, hi0, base, Nat.mul_comm] using
      (Nat.mod_add_div (b0.val * q2.val + c1Lo.val) base)
  have hlo1_repr : lo1 + hi1 * base = q1.val * b1.val + lo0 := by
    simpa [lo1, hi1, base, Nat.mul_comm] using
      (Nat.mod_add_div (b1.val * q1.val + lo0) base)
  have hpre_repr :
      q2.val * b0.val + q1.val * b1.val + carry1 = lo1 + sumHi * base := by
    calc
      q2.val * b0.val + q1.val * b1.val + carry1
          = q1.val * b1.val + (q2.val * b0.val + c1Lo.val) + c1Hi.val * base := by
              rw [← hcarry1_repr]
              ring
      _ = q1.val * b1.val + (lo0 + hi0 * base) + c1Hi.val * base := by rw [hlo0_repr]
      _ = (lo1 + hi1 * base) + (hi0 + c1Hi.val) * base := by
            rw [hlo1_repr]
            ring
      _ = lo1 + sumHi * base := by
            dsimp [sumHi]
            ring
  have hmadd2_repr : madd2Lo + madd2Hi * base = q0.val * b2.val + lo1 := by
    simpa [madd2Lo, madd2Hi, base, Nat.mul_comm] using
      (Nat.mod_add_div (b2.val * q0.val + lo1) base)
  have hadd_repr : addLo + addHi * base = madd2Lo + r2.val := by
    simpa [addLo, addHi, base, Nat.mul_comm] using
      (Nat.mod_add_div (madd2Lo + r2.val) base)
  have hrepr :
      u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val =
        addLo + carry * base := by
    calc
      u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val
          = q0.val * b2.val + r2.val + (q2.val * b0.val + q1.val * b1.val + carry1) := by
              unfold u128DivmodCol2
              dsimp [carry1, base]
              ring
      _ = q0.val * b2.val + r2.val + (lo1 + sumHi * base) := by rw [hpre_repr]
      _ = q0.val * b2.val + lo1 + r2.val + sumHi * base := by ring
      _ = (madd2Lo + madd2Hi * base) + r2.val + sumHi * base := by rw [hmadd2_repr]
      _ = madd2Lo + r2.val + (sumHi + madd2Hi) * base := by ring
      _ = addLo + addHi * base + (sumHi + madd2Hi) * base := by rw [hadd_repr]
      _ = addLo + (sumHi + madd2Hi + addHi) * base := by ring
  have haddLo_lt : addLo < base := by
    dsimp [addLo, base]
    exact Nat.mod_lt _ (by positivity)
  have hlo_nat :
      u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val % base = addLo := by
    calc
      u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val % base
          = (addLo + carry * base) % base := by rw [hrepr]
      _ = addLo % base := by rw [Nat.add_mul_mod_self_right]
      _ = addLo := Nat.mod_eq_of_lt haddLo_lt
  have ha2_ne' : a2 ≠ Felt.ofNat addLo := by
    intro hEq
    apply ha2_ne
    calc
      a2 = Felt.ofNat addLo := hEq
      _ = Felt.ofNat
            (u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val %
              2 ^ 32) := by
              exact congrArg Felt.ofNat hlo_nat.symm
  unfold divmodCol2c exec execWithEnv
  simp only [List.foldlM]
  miden_dup
  rw [stepU32WidenAdd (a := Felt.ofNat madd2Lo) (b := r2) (ha := u32_mod_isU32 _) (hb := hr2)]
  miden_bind
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  miden_movup
  rw [show Felt.ofNat
      (((b2.val * q0.val + lo1) % 2 ^ 32 + r2.val) % 2 ^ 32) =
      Felt.ofNat addLo by rfl]
  rw [stepAssertEqWithError_none (msg := "u128 divmod: col 2") (h := ha2_ne'.symm)]

set_option maxHeartbeats 12000000 in
private theorem divmodCol2_run
    (c1Lo c1Hi q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a2 a3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq0 : q0.isU32 = true) (hq1 : q1.isU32 = true) (hq2 : q2.isU32 = true)
    (hr2 : r2.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) (hb2 : b2.isU32 = true)
    (hc1Lo_u32 : c1Lo.isU32 = true) (hc1Hi_u32 : c1Hi.isU32 = true)
    (hc1Lo_val :
      c1Lo.val = u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / 2 ^ 32 % 2 ^ 32)
    (hc1Hi_val :
      c1Hi.val = u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / 2 ^ 32 / 2 ^ 32)
    (ha2_eq :
      a2 = Felt.ofNat (u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val % 2 ^ 32)) :
    exec 163
      ⟨c1Lo :: c1Hi :: q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
        b0 :: b1 :: b2 :: b3 :: a2 :: a3 :: rest,
        mem, locs, adv_rest⟩
      divmodCol2 =
    some ⟨Felt.ofNat
              (u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val /
                  2 ^ 32 %
                2 ^ 32) ::
            Felt.ofNat
              (u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val /
                  2 ^ 32 /
                2 ^ 32) ::
            q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
            b0 :: b1 :: b2 :: b3 :: a3 :: rest,
          mem, locs, adv_rest⟩ := by
  rw [divmodCol2_eq, exec_append]
  rw [divmodCol2a_run c1Lo c1Hi q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a2 a3 rest adv_rest mem locs
      hq1 hq2 hb0 hb1 hc1Lo_u32 hc1Lo_val]
  miden_bind
  rw [exec_append]
  rw [divmodCol2b_run c1Lo c1Hi q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a2 a3 rest adv_rest mem locs
      hq0 hb2]
  miden_bind
  rw [divmodCol2c_run c1Lo c1Hi q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a2 a3 rest adv_rest mem locs
      hq0 hq1 hq2 hr2 hb0 hb1 hb2 hc1Lo_u32 hc1Hi_u32 hc1Lo_val hc1Hi_val ha2_eq]

private def divmodCol3a : List Op := [
  .inst (.dup 10),
  .inst (.dup 6),
  .inst (.u32WidenMadd),
  .inst (.dup 12),
  .inst (.dup 6),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.movup 3),
  .inst (.add),
  .inst (.add),
  .inst (.swap 1)
]

private def divmodCol3b : List Op := [
  .inst (.dup 12),
  .inst (.dup 4),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.add),
  .inst (.swap 1)
]

private def divmodCol3c : List Op := [
  .inst (.dup 13),
  .inst (.dup 3),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.add),
  .inst (.swap 1),
  .inst (.dup 9),
  .inst (.u32WidenAdd),
  .inst (.movup 15),
  .inst (.assertEqWithError "u128 divmod: col 3"),
  .inst (.add),
  .inst (.assertzWithError "u128 divmod: carry overflow")
]

private def divmodCol3 : List Op :=
  divmodCol3a ++ divmodCol3b ++ divmodCol3c

private theorem divmodCol3_eq :
    divmodCol3 = divmodCol3a ++ (divmodCol3b ++ divmodCol3c) := by
  simp [divmodCol3]

set_option maxHeartbeats 12000000 in
private theorem divmodCol3a_run
    (c2Lo c2Hi q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq2 : q2.isU32 = true) (hq3 : q3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hc2Lo_u32 : c2Lo.isU32 = true) :
    let base := 2 ^ 32
    let lo0 := (b0.val * q3.val + c2Lo.val) % base
    let hi0 := (b0.val * q3.val + c2Lo.val) / base
    let lo1 := (b1.val * q2.val + lo0) % base
    let hi1 := (b1.val * q2.val + lo0) / base
    let sumHi := c2Hi.val + hi0 + hi1
    exec 163
      ⟨c2Lo :: c2Hi :: q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
        b0 :: b1 :: b2 :: b3 :: a3 :: rest,
        mem, locs, adv_rest⟩
      divmodCol3a =
    some ⟨Felt.ofNat lo1 :: Felt.ofNat sumHi ::
            q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
            b0 :: b1 :: b2 :: b3 :: a3 :: rest,
          mem, locs, adv_rest⟩ := by
  let base := 2 ^ 32
  let lo0 := (b0.val * q3.val + c2Lo.val) % base
  let hi0 := (b0.val * q3.val + c2Lo.val) / base
  let lo1 := (b1.val * q2.val + lo0) % base
  let hi1 := (b1.val * q2.val + lo0) / base
  let sumHi := c2Hi.val + hi0 + hi1
  have hc2Hi_eq : c2Hi = Felt.ofNat c2Hi.val := by
    exact felt_eq_ofNat_of_val_eq c2Hi c2Hi.val rfl (felt_val_lt_prime _)
  have hlo0_val : (Felt.ofNat lo0).val = lo0 := by
    apply felt_ofNat_val_lt
    dsimp [lo0, base]
    exact u32_mod_lt_prime _
  have hlo0_eq :
      Felt.ofNat ((b0.val * q3.val + c2Lo.val) % 2 ^ 32) = Felt.ofNat lo0 := by
    rfl
  have hhi0_eq :
      Felt.ofNat ((b0.val * q3.val + c2Lo.val) / 2 ^ 32) = Felt.ofNat hi0 := by
    rfl
  unfold divmodCol3a exec execWithEnv
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepU32WidenMadd (a := b0) (b := q3) (c := c2Lo) (ha := hb0) (hb := hq3) (hc := hc2Lo_u32)]
  miden_bind
  miden_dup
  miden_dup
  rw [hlo0_eq]
  rw [stepU32WidenMadd
    (a := b1) (b := q2) (c := Felt.ofNat lo0)
    (ha := hb1) (hb := hq2) (hc := u32_mod_isU32 _)]
  miden_bind
  rw [hlo0_val]
  miden_swap
  miden_movup
  miden_movup
  rw [stepAdd]
  miden_bind
  rw [hhi0_eq]
  rw [hc2Hi_eq]
  rw [← felt_ofNat_add]
  rw [show hi0 + c2Hi.val = c2Hi.val + hi0 by omega]
  rw [stepAdd]
  miden_bind
  rw [show Felt.ofNat ((b1.val * q2.val + lo0) / 2 ^ 32) = Felt.ofNat hi1 by rfl]
  rw [← felt_ofNat_add]
  rw [show hi1 + (c2Hi.val + hi0) = sumHi by
    dsimp [sumHi]
    omega]
  rw [show Felt.ofNat ((b1.val * q2.val + lo0) % 2 ^ 32) = Felt.ofNat lo1 by rfl]
  miden_swap
  simp [pure, Pure.pure]
  rw [felt_ofNat_val_lt _ (felt_val_lt_prime c2Hi)]
  simp [sumHi, hi0, hi1, lo0, base]

set_option maxHeartbeats 12000000 in
private theorem divmodCol3b_run
    (c2Lo c2Hi q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq1 : q1.isU32 = true) (hb2 : b2.isU32 = true) :
    let base := 2 ^ 32
    let lo0 := (b0.val * q3.val + c2Lo.val) % base
    let hi0 := (b0.val * q3.val + c2Lo.val) / base
    let lo1 := (b1.val * q2.val + lo0) % base
    let hi1 := (b1.val * q2.val + lo0) / base
    let sumHi := c2Hi.val + hi0 + hi1
    let madd2Lo := (b2.val * q1.val + lo1) % base
    let madd2Hi := (b2.val * q1.val + lo1) / base
    exec 163
      ⟨Felt.ofNat lo1 :: Felt.ofNat sumHi ::
        q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
        b0 :: b1 :: b2 :: b3 :: a3 :: rest,
        mem, locs, adv_rest⟩
      divmodCol3b =
    some ⟨Felt.ofNat madd2Lo :: Felt.ofNat (sumHi + madd2Hi) ::
            q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
            b0 :: b1 :: b2 :: b3 :: a3 :: rest,
          mem, locs, adv_rest⟩ := by
  let base := 2 ^ 32
  let lo0 := (b0.val * q3.val + c2Lo.val) % base
  let hi0 := (b0.val * q3.val + c2Lo.val) / base
  let lo1 := (b1.val * q2.val + lo0) % base
  let hi1 := (b1.val * q2.val + lo0) / base
  let sumHi := c2Hi.val + hi0 + hi1
  let madd2Lo := (b2.val * q1.val + lo1) % base
  let madd2Hi := (b2.val * q1.val + lo1) / base
  have hlo1_flat :
      lo1 = (b1.val * q2.val + (b0.val * q3.val + c2Lo.val)) % base := by
    dsimp [lo1, lo0]
    rw [add_mod_right_mod]
  unfold divmodCol3b exec execWithEnv
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepU32WidenMadd
    (a := b2) (b := q1) (c := Felt.ofNat lo1)
    (ha := hb2) (hb := hq1) (hc := u32_mod_isU32 _)]
  miden_bind
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  miden_swap
  miden_movup
  rw [stepAdd]
  miden_bind
  rw [show Felt.ofNat ((b2.val * q1.val + lo1) / 2 ^ 32) = Felt.ofNat madd2Hi by rfl]
  rw [← felt_ofNat_add]
  rw [show madd2Hi + sumHi = sumHi + madd2Hi by omega]
  rw [show Felt.ofNat ((b2.val * q1.val + lo1) % 2 ^ 32) = Felt.ofNat madd2Lo by rfl]
  miden_swap
  simp [pure, Pure.pure]
  dsimp [sumHi, madd2Hi, hi0, hi1]
  rw [hlo1_flat]
  rfl

private theorem divmodCol3c_run
    (c2Lo c2Hi q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq0 : q0.isU32 = true) (_hq1 : q1.isU32 = true) (_hq2 : q2.isU32 = true) (_hq3 : q3.isU32 = true)
    (hr3 : r3.isU32 = true)
    (_hb0 : b0.isU32 = true) (_hb1 : b1.isU32 = true) (_hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true)
    (_hc2Lo_u32 : c2Lo.isU32 = true)
    (hc2Lo_val :
      c2Lo.val = u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / 2 ^ 32 % 2 ^ 32)
    (hc2Hi_val :
      c2Hi.val = u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / 2 ^ 32 / 2 ^ 32)
    (ha3_eq :
      a3 =
        Felt.ofNat
          (u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val
              r0.val r1.val r2.val r3.val %
            2 ^ 32))
    (hcarry_zero :
      u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val
          r0.val r1.val r2.val r3.val /
        2 ^ 32 =
      0) :
    let base := 2 ^ 32
    let _carry2 := u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / base
    let lo0 := (b0.val * q3.val + c2Lo.val) % base
    let hi0 := (b0.val * q3.val + c2Lo.val) / base
    let lo1 := (b1.val * q2.val + lo0) % base
    let hi1 := (b1.val * q2.val + lo0) / base
    let sumHi := c2Hi.val + hi0 + hi1
    let madd2Lo := (b2.val * q1.val + lo1) % base
    let madd2Hi := (b2.val * q1.val + lo1) / base
    let sumHi' := sumHi + madd2Hi
    let madd3Lo := (b3.val * q0.val + madd2Lo) % base
    let _madd3Hi := (b3.val * q0.val + madd2Lo) / base
    let _addLo := (madd3Lo + r3.val) % base
    let _addHi := (madd3Lo + r3.val) / base
    exec 163
      ⟨Felt.ofNat madd2Lo :: Felt.ofNat sumHi' ::
        q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
        b0 :: b1 :: b2 :: b3 :: a3 :: rest,
        mem, locs, adv_rest⟩
      divmodCol3c =
    some ⟨q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
            b0 :: b1 :: b2 :: b3 :: rest,
          mem, locs, adv_rest⟩ := by
  let base := 2 ^ 32
  let carry2 := u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / base
  let lo0 := (b0.val * q3.val + c2Lo.val) % base
  let hi0 := (b0.val * q3.val + c2Lo.val) / base
  let lo1 := (b1.val * q2.val + lo0) % base
  let hi1 := (b1.val * q2.val + lo0) / base
  let sumHi := c2Hi.val + hi0 + hi1
  let madd2Lo := (b2.val * q1.val + lo1) % base
  let madd2Hi := (b2.val * q1.val + lo1) / base
  let sumHi' := sumHi + madd2Hi
  let madd3Lo := (b3.val * q0.val + madd2Lo) % base
  let madd3Hi := (b3.val * q0.val + madd2Lo) / base
  let addLo := (madd3Lo + r3.val) % base
  let addHi := (madd3Lo + r3.val) / base
  let carry := sumHi' + madd3Hi + addHi
  have hcarry2_repr : c2Lo.val + c2Hi.val * base = carry2 := by
    rw [hc2Lo_val, hc2Hi_val]
    dsimp [carry2]
    simpa [base, Nat.mul_comm] using
      (Nat.mod_add_div (u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / 2 ^ 32) base)
  have hlo0_repr : lo0 + hi0 * base = q3.val * b0.val + c2Lo.val := by
    simpa [lo0, hi0, base, Nat.mul_comm] using
      (Nat.mod_add_div (b0.val * q3.val + c2Lo.val) base)
  have hlo1_repr : lo1 + hi1 * base = q2.val * b1.val + lo0 := by
    simpa [lo1, hi1, base, Nat.mul_comm] using
      (Nat.mod_add_div (b1.val * q2.val + lo0) base)
  have hmadd2_repr : madd2Lo + madd2Hi * base = q1.val * b2.val + lo1 := by
    simpa [madd2Lo, madd2Hi, base, Nat.mul_comm] using
      (Nat.mod_add_div (b2.val * q1.val + lo1) base)
  have hpre_repr :
      q3.val * b0.val + q2.val * b1.val + q1.val * b2.val + carry2 = madd2Lo + sumHi' * base := by
    calc
      q3.val * b0.val + q2.val * b1.val + q1.val * b2.val + carry2
          = q2.val * b1.val + q1.val * b2.val + (q3.val * b0.val + c2Lo.val) + c2Hi.val * base := by
              rw [← hcarry2_repr]
              ring
      _ = q2.val * b1.val + q1.val * b2.val + (lo0 + hi0 * base) + c2Hi.val * base := by
            rw [hlo0_repr]
      _ = q1.val * b2.val + (lo1 + hi1 * base) + (hi0 + c2Hi.val) * base := by
            rw [hlo1_repr]
            ring
      _ = (madd2Lo + madd2Hi * base) + (hi1 + hi0 + c2Hi.val) * base := by
            rw [hmadd2_repr]
            ring
      _ = madd2Lo + sumHi' * base := by
            dsimp [sumHi', sumHi]
            ring
  have hmadd3_repr : madd3Lo + madd3Hi * base = q0.val * b3.val + madd2Lo := by
    simpa [madd3Lo, madd3Hi, base, Nat.mul_comm] using
      (Nat.mod_add_div (b3.val * q0.val + madd2Lo) base)
  have hadd_repr : addLo + addHi * base = madd3Lo + r3.val := by
    simpa [addLo, addHi, base, Nat.mul_comm] using
      (Nat.mod_add_div (madd3Lo + r3.val) base)
  have hrepr :
      u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val r0.val r1.val r2.val r3.val =
        addLo + carry * base := by
    calc
      u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val r0.val r1.val r2.val r3.val
          = q0.val * b3.val + r3.val + (q3.val * b0.val + q2.val * b1.val + q1.val * b2.val + carry2) := by
              unfold u128DivmodCol3
              dsimp [carry2, base]
              ring
      _ = q0.val * b3.val + r3.val + (madd2Lo + sumHi' * base) := by rw [hpre_repr]
      _ = q0.val * b3.val + madd2Lo + r3.val + sumHi' * base := by ring
      _ = (madd3Lo + madd3Hi * base) + r3.val + sumHi' * base := by rw [hmadd3_repr]
      _ = madd3Lo + r3.val + (sumHi' + madd3Hi) * base := by ring
      _ = addLo + addHi * base + (sumHi' + madd3Hi) * base := by rw [hadd_repr]
      _ = addLo + (sumHi' + madd3Hi + addHi) * base := by ring
      _ = addLo + carry * base := by
            dsimp [carry]
  have haddLo_lt : addLo < base := by
    dsimp [addLo, base]
    exact Nat.mod_lt _ (by positivity)
  have hlo_eq :
      Felt.ofNat
          (u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val
              r0.val r1.val r2.val r3.val %
            base) =
        Felt.ofNat addLo := by
    exact congrArg Felt.ofNat <| by
      calc
        u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val
              r0.val r1.val r2.val r3.val %
            base
            = (addLo + carry * base) % base := by rw [hrepr]
        _ = addLo % base := by rw [Nat.add_mul_mod_self_right]
        _ = addLo := Nat.mod_eq_of_lt haddLo_lt
  have hcarry_eq : carry = 0 := by
    have hcarry_nat :
        u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val
            r0.val r1.val r2.val r3.val /
          base =
        carry := by
      rw [hrepr]
      rw [Nat.add_mul_div_right _ _ (show 0 < base by positivity), Nat.div_eq_of_lt haddLo_lt]
      simp
    rw [← hcarry_nat, hcarry_zero]
  unfold divmodCol3c exec execWithEnv
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepU32WidenMadd
    (a := b3) (b := q0) (c := Felt.ofNat madd2Lo)
    (ha := hb3) (hb := hq0) (hc := u32_mod_isU32 _)]
  miden_bind
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  miden_swap
  miden_movup
  rw [stepAdd]
  miden_bind
  rw [show Felt.ofNat ((b3.val * q0.val + madd2Lo) / 2 ^ 32) = Felt.ofNat madd3Hi by rfl]
  rw [← felt_ofNat_add]
  rw [show madd3Hi + sumHi' = sumHi' + madd3Hi by omega]
  rw [show Felt.ofNat ((b3.val * q0.val + madd2Lo) % 2 ^ 32) = Felt.ofNat madd3Lo by rfl]
  miden_swap
  miden_dup
  rw [stepU32WidenAdd
    (a := Felt.ofNat madd3Lo) (b := r3)
    (ha := u32_mod_isU32 _) (hb := hr3)]
  miden_bind
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  miden_movup
  rw [ha3_eq]
  rw [hlo_eq]
  rw [stepAssertEqWithError]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [← felt_ofNat_add]
  rw [show sumHi' + madd3Hi + addHi = carry by dsimp [carry]]
  rw [show Felt.ofNat carry = 0 by
    calc
      Felt.ofNat carry = Felt.ofNat 0 := by rw [hcarry_eq]
      _ = 0 := by exact Nat.cast_zero]
  rw [stepAssertzWithErrorLocal "u128 divmod: carry overflow" mem locs adv_rest (0 : Felt)
    (q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest) rfl]
  simp

private theorem divmodCol3c_none_a3
    (c2Lo c2Hi q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq0 : q0.isU32 = true) (_hq1 : q1.isU32 = true) (_hq2 : q2.isU32 = true) (_hq3 : q3.isU32 = true)
    (hr3 : r3.isU32 = true)
    (_hb0 : b0.isU32 = true) (_hb1 : b1.isU32 = true) (_hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true)
    (_hc2Lo_u32 : c2Lo.isU32 = true)
    (hc2Lo_val :
      c2Lo.val = u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / 2 ^ 32 % 2 ^ 32)
    (hc2Hi_val :
      c2Hi.val = u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / 2 ^ 32 / 2 ^ 32)
    (ha3_ne :
      a3 ≠
        Felt.ofNat
          (u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val
              r0.val r1.val r2.val r3.val %
            2 ^ 32)) :
    let base := 2 ^ 32
    let _carry2 := u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / base
    let lo0 := (b0.val * q3.val + c2Lo.val) % base
    let hi0 := (b0.val * q3.val + c2Lo.val) / base
    let lo1 := (b1.val * q2.val + lo0) % base
    let hi1 := (b1.val * q2.val + lo0) / base
    let sumHi := c2Hi.val + hi0 + hi1
    let madd2Lo := (b2.val * q1.val + lo1) % base
    let madd2Hi := (b2.val * q1.val + lo1) / base
    let sumHi' := sumHi + madd2Hi
    exec 163
      ⟨Felt.ofNat madd2Lo :: Felt.ofNat sumHi' ::
        q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
        b0 :: b1 :: b2 :: b3 :: a3 :: rest,
        mem, locs, adv_rest⟩
      divmodCol3c =
    none := by
  let base := 2 ^ 32
  let carry2 := u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / base
  let lo0 := (b0.val * q3.val + c2Lo.val) % base
  let hi0 := (b0.val * q3.val + c2Lo.val) / base
  let lo1 := (b1.val * q2.val + lo0) % base
  let hi1 := (b1.val * q2.val + lo0) / base
  let sumHi := c2Hi.val + hi0 + hi1
  let madd2Lo := (b2.val * q1.val + lo1) % base
  let madd2Hi := (b2.val * q1.val + lo1) / base
  let sumHi' := sumHi + madd2Hi
  let madd3Lo := (b3.val * q0.val + madd2Lo) % base
  let madd3Hi := (b3.val * q0.val + madd2Lo) / base
  let addLo := (madd3Lo + r3.val) % base
  let addHi := (madd3Lo + r3.val) / base
  let carry := sumHi' + madd3Hi + addHi
  have hcarry2_repr : c2Lo.val + c2Hi.val * base = carry2 := by
    rw [hc2Lo_val, hc2Hi_val]
    dsimp [carry2]
    simpa [base, Nat.mul_comm] using
      (Nat.mod_add_div (u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / 2 ^ 32) base)
  have hlo0_repr : lo0 + hi0 * base = q3.val * b0.val + c2Lo.val := by
    simpa [lo0, hi0, base, Nat.mul_comm] using
      (Nat.mod_add_div (b0.val * q3.val + c2Lo.val) base)
  have hlo1_repr : lo1 + hi1 * base = q2.val * b1.val + lo0 := by
    simpa [lo1, hi1, base, Nat.mul_comm] using
      (Nat.mod_add_div (b1.val * q2.val + lo0) base)
  have hmadd2_repr : madd2Lo + madd2Hi * base = q1.val * b2.val + lo1 := by
    simpa [madd2Lo, madd2Hi, base, Nat.mul_comm] using
      (Nat.mod_add_div (b2.val * q1.val + lo1) base)
  have hpre_repr :
      q3.val * b0.val + q2.val * b1.val + q1.val * b2.val + carry2 = madd2Lo + sumHi' * base := by
    calc
      q3.val * b0.val + q2.val * b1.val + q1.val * b2.val + carry2
          = q2.val * b1.val + q1.val * b2.val + (q3.val * b0.val + c2Lo.val) + c2Hi.val * base := by
              rw [← hcarry2_repr]
              ring
      _ = q2.val * b1.val + q1.val * b2.val + (lo0 + hi0 * base) + c2Hi.val * base := by
            rw [hlo0_repr]
      _ = q1.val * b2.val + (lo1 + hi1 * base) + (hi0 + c2Hi.val) * base := by
            rw [hlo1_repr]
            ring
      _ = (madd2Lo + madd2Hi * base) + (hi1 + hi0 + c2Hi.val) * base := by
            rw [hmadd2_repr]
            ring
      _ = madd2Lo + sumHi' * base := by
            dsimp [sumHi', sumHi]
            ring
  have hmadd3_repr : madd3Lo + madd3Hi * base = q0.val * b3.val + madd2Lo := by
    simpa [madd3Lo, madd3Hi, base, Nat.mul_comm] using
      (Nat.mod_add_div (b3.val * q0.val + madd2Lo) base)
  have hadd_repr : addLo + addHi * base = madd3Lo + r3.val := by
    simpa [addLo, addHi, base, Nat.mul_comm] using
      (Nat.mod_add_div (madd3Lo + r3.val) base)
  have hrepr :
      u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val r0.val r1.val r2.val r3.val =
        addLo + carry * base := by
    calc
      u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val r0.val r1.val r2.val r3.val
          = q0.val * b3.val + r3.val + (q3.val * b0.val + q2.val * b1.val + q1.val * b2.val + carry2) := by
              unfold u128DivmodCol3
              dsimp [carry2, base]
              ring
      _ = q0.val * b3.val + r3.val + (madd2Lo + sumHi' * base) := by rw [hpre_repr]
      _ = q0.val * b3.val + madd2Lo + r3.val + sumHi' * base := by ring
      _ = (madd3Lo + madd3Hi * base) + r3.val + sumHi' * base := by rw [hmadd3_repr]
      _ = madd3Lo + r3.val + (sumHi' + madd3Hi) * base := by ring
      _ = addLo + addHi * base + (sumHi' + madd3Hi) * base := by rw [hadd_repr]
      _ = addLo + (sumHi' + madd3Hi + addHi) * base := by ring
      _ = addLo + carry * base := by
            dsimp [carry]
  have haddLo_lt : addLo < base := by
    dsimp [addLo, base]
    exact Nat.mod_lt _ (by positivity)
  have hlo_nat :
      u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val
          r0.val r1.val r2.val r3.val %
        base =
      addLo := by
    calc
      u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val
            r0.val r1.val r2.val r3.val %
          base
          = (addLo + carry * base) % base := by rw [hrepr]
      _ = addLo % base := by rw [Nat.add_mul_mod_self_right]
      _ = addLo := Nat.mod_eq_of_lt haddLo_lt
  have ha3_ne' : a3 ≠ Felt.ofNat addLo := by
    intro hEq
    apply ha3_ne
    calc
      a3 = Felt.ofNat addLo := hEq
      _ = Felt.ofNat
            (u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val
                r0.val r1.val r2.val r3.val %
              2 ^ 32) := by
              exact congrArg Felt.ofNat hlo_nat.symm
  unfold divmodCol3c exec execWithEnv
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepU32WidenMadd
    (a := b3) (b := q0) (c := Felt.ofNat madd2Lo)
    (ha := hb3) (hb := hq0) (hc := u32_mod_isU32 _)]
  miden_bind
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  miden_swap
  miden_movup
  rw [stepAdd]
  miden_bind
  rw [show Felt.ofNat ((b3.val * q0.val + madd2Lo) / 2 ^ 32) = Felt.ofNat madd3Hi by rfl]
  rw [← felt_ofNat_add]
  rw [show madd3Hi + sumHi' = sumHi' + madd3Hi by omega]
  rw [show Felt.ofNat ((b3.val * q0.val + madd2Lo) % 2 ^ 32) = Felt.ofNat madd3Lo by rfl]
  miden_swap
  miden_dup
  rw [stepU32WidenAdd
    (a := Felt.ofNat madd3Lo) (b := r3)
    (ha := u32_mod_isU32 _) (hb := hr3)]
  miden_bind
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  miden_movup
  rw [show Felt.ofNat (((b3.val * q0.val + madd2Lo) % 2 ^ 32 + r3.val) % 2 ^ 32) = Felt.ofNat addLo by
    rfl]
  rw [stepAssertEqWithError_none (msg := "u128 divmod: col 3") (h := ha3_ne'.symm)]

private theorem divmodCol3c_none_carry
    (c2Lo c2Hi q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq0 : q0.isU32 = true) (_hq1 : q1.isU32 = true) (_hq2 : q2.isU32 = true) (_hq3 : q3.isU32 = true)
    (hr2 : r2.isU32 = true)
    (hr3 : r3.isU32 = true)
    (_hb0 : b0.isU32 = true) (_hb1 : b1.isU32 = true) (_hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true)
    (_hc2Lo_u32 : c2Lo.isU32 = true) (hc2Hi_u32 : c2Hi.isU32 = true)
    (hc2Lo_val :
      c2Lo.val = u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / 2 ^ 32 % 2 ^ 32)
    (hc2Hi_val :
      c2Hi.val = u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / 2 ^ 32 / 2 ^ 32)
    (ha3_eq :
      a3 =
        Felt.ofNat
          (u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val
              r0.val r1.val r2.val r3.val %
            2 ^ 32))
    (hcarry_ne :
      u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val
          r0.val r1.val r2.val r3.val /
        2 ^ 32 ≠
      0) :
    let base := 2 ^ 32
    let _carry2 := u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / base
    let lo0 := (b0.val * q3.val + c2Lo.val) % base
    let hi0 := (b0.val * q3.val + c2Lo.val) / base
    let lo1 := (b1.val * q2.val + lo0) % base
    let hi1 := (b1.val * q2.val + lo0) / base
    let sumHi := c2Hi.val + hi0 + hi1
    let madd2Lo := (b2.val * q1.val + lo1) % base
    let madd2Hi := (b2.val * q1.val + lo1) / base
    let sumHi' := sumHi + madd2Hi
    exec 163
      ⟨Felt.ofNat madd2Lo :: Felt.ofNat sumHi' ::
        q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
        b0 :: b1 :: b2 :: b3 :: a3 :: rest,
        mem, locs, adv_rest⟩
      divmodCol3c =
    none := by
  let base := 2 ^ 32
  let carry2 := u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / base
  let lo0 := (b0.val * q3.val + c2Lo.val) % base
  let hi0 := (b0.val * q3.val + c2Lo.val) / base
  let lo1 := (b1.val * q2.val + lo0) % base
  let hi1 := (b1.val * q2.val + lo0) / base
  let sumHi := c2Hi.val + hi0 + hi1
  let madd2Lo := (b2.val * q1.val + lo1) % base
  let madd2Hi := (b2.val * q1.val + lo1) / base
  let sumHi' := sumHi + madd2Hi
  let madd3Lo := (b3.val * q0.val + madd2Lo) % base
  let madd3Hi := (b3.val * q0.val + madd2Lo) / base
  let addLo := (madd3Lo + r3.val) % base
  let addHi := (madd3Lo + r3.val) / base
  let carry := sumHi' + madd3Hi + addHi
  have hcarry2_repr : c2Lo.val + c2Hi.val * base = carry2 := by
    rw [hc2Lo_val, hc2Hi_val]
    dsimp [carry2]
    simpa [base, Nat.mul_comm] using
      (Nat.mod_add_div (u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / 2 ^ 32) base)
  have hlo0_repr : lo0 + hi0 * base = q3.val * b0.val + c2Lo.val := by
    simpa [lo0, hi0, base, Nat.mul_comm] using
      (Nat.mod_add_div (b0.val * q3.val + c2Lo.val) base)
  have hlo1_repr : lo1 + hi1 * base = q2.val * b1.val + lo0 := by
    simpa [lo1, hi1, base, Nat.mul_comm] using
      (Nat.mod_add_div (b1.val * q2.val + lo0) base)
  have hmadd2_repr : madd2Lo + madd2Hi * base = q1.val * b2.val + lo1 := by
    simpa [madd2Lo, madd2Hi, base, Nat.mul_comm] using
      (Nat.mod_add_div (b2.val * q1.val + lo1) base)
  have hpre_repr :
      q3.val * b0.val + q2.val * b1.val + q1.val * b2.val + carry2 = madd2Lo + sumHi' * base := by
    calc
      q3.val * b0.val + q2.val * b1.val + q1.val * b2.val + carry2
          = q2.val * b1.val + q1.val * b2.val + (q3.val * b0.val + c2Lo.val) + c2Hi.val * base := by
              rw [← hcarry2_repr]
              ring
      _ = q2.val * b1.val + q1.val * b2.val + (lo0 + hi0 * base) + c2Hi.val * base := by
            rw [hlo0_repr]
      _ = q1.val * b2.val + (lo1 + hi1 * base) + (hi0 + c2Hi.val) * base := by
            rw [hlo1_repr]
            ring
      _ = (madd2Lo + madd2Hi * base) + (hi1 + hi0 + c2Hi.val) * base := by
            rw [hmadd2_repr]
            ring
      _ = madd2Lo + sumHi' * base := by
            dsimp [sumHi', sumHi]
            ring
  have hmadd3_repr : madd3Lo + madd3Hi * base = q0.val * b3.val + madd2Lo := by
    simpa [madd3Lo, madd3Hi, base, Nat.mul_comm] using
      (Nat.mod_add_div (b3.val * q0.val + madd2Lo) base)
  have hadd_repr : addLo + addHi * base = madd3Lo + r3.val := by
    simpa [addLo, addHi, base, Nat.mul_comm] using
      (Nat.mod_add_div (madd3Lo + r3.val) base)
  have hrepr :
      u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val r0.val r1.val r2.val r3.val =
        addLo + carry * base := by
    calc
      u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val r0.val r1.val r2.val r3.val
          = q0.val * b3.val + r3.val + (q3.val * b0.val + q2.val * b1.val + q1.val * b2.val + carry2) := by
              unfold u128DivmodCol3
              dsimp [carry2, base]
              ring
      _ = q0.val * b3.val + r3.val + (madd2Lo + sumHi' * base) := by rw [hpre_repr]
      _ = q0.val * b3.val + madd2Lo + r3.val + sumHi' * base := by ring
      _ = (madd3Lo + madd3Hi * base) + r3.val + sumHi' * base := by rw [hmadd3_repr]
      _ = madd3Lo + r3.val + (sumHi' + madd3Hi) * base := by ring
      _ = addLo + addHi * base + (sumHi' + madd3Hi) * base := by rw [hadd_repr]
      _ = addLo + (sumHi' + madd3Hi + addHi) * base := by ring
      _ = addLo + carry * base := by
            dsimp [carry]
  have haddLo_lt : addLo < base := by
    dsimp [addLo, base]
    exact Nat.mod_lt _ (by positivity)
  have hlo_nat :
      u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val
          r0.val r1.val r2.val r3.val %
        base =
      addLo := by
    calc
      u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val
            r0.val r1.val r2.val r3.val %
          base
          = (addLo + carry * base) % base := by rw [hrepr]
      _ = addLo % base := by rw [Nat.add_mul_mod_self_right]
      _ = addLo := Nat.mod_eq_of_lt haddLo_lt
  have hcarry_nat :
      u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val
          r0.val r1.val r2.val r3.val /
        base =
      carry := by
    rw [hrepr, Nat.add_mul_div_right _ _ (show 0 < base by positivity), Nat.div_eq_of_lt haddLo_lt]
    simp [carry]
  have hq0_lt : q0.val < 2 ^ 32 := by
    simpa [Felt.isU32, decide_eq_true_eq] using hq0
  have hq1_lt : q1.val < 2 ^ 32 := by
    simpa [Felt.isU32, decide_eq_true_eq] using _hq1
  have hq2_lt : q2.val < 2 ^ 32 := by
    simpa [Felt.isU32, decide_eq_true_eq] using _hq2
  have hq3_lt : q3.val < 2 ^ 32 := by
    simpa [Felt.isU32, decide_eq_true_eq] using _hq3
  have hb0_lt : b0.val < 2 ^ 32 := by
    simpa [Felt.isU32, decide_eq_true_eq] using _hb0
  have hb1_lt : b1.val < 2 ^ 32 := by
    simpa [Felt.isU32, decide_eq_true_eq] using _hb1
  have hb2_lt : b2.val < 2 ^ 32 := by
    simpa [Felt.isU32, decide_eq_true_eq] using _hb2
  have hb3_lt : b3.val < 2 ^ 32 := by
    simpa [Felt.isU32, decide_eq_true_eq] using hb3
  have hr2_lt : r2.val < 2 ^ 32 := by
    simpa [Felt.isU32, decide_eq_true_eq] using hr2
  have hr3_lt : r3.val < 2 ^ 32 := by
    simpa [Felt.isU32, decide_eq_true_eq] using hr3
  have hc2Hi_lt : c2Hi.val < 2 ^ 32 := by
    simpa [Felt.isU32, decide_eq_true_eq] using hc2Hi_u32
  have hhi0_lt : hi0 < 2 ^ 32 := by
    dsimp [hi0, base]
    simpa [Nat.mul_comm] using
      (u32_madd_div_lt_2_32 b0 q3 c2Lo _hb0 _hq3 _hc2Lo_u32)
  have hhi1_lt : hi1 < 2 ^ 32 := by
    dsimp [hi1, base]
    have h := u32_madd_div_lt_2_32 b1 q2 (Felt.ofNat lo0) _hb1 _hq2 (u32_mod_isU32 _)
    rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)] at h
    simpa [lo0, lo1, Nat.mul_comm] using h
  have hmadd2Hi_lt : madd2Hi < 2 ^ 32 := by
    dsimp [madd2Hi, base]
    have h := u32_madd_div_lt_2_32 b2 q1 (Felt.ofNat lo1) _hb2 _hq1 (u32_mod_isU32 _)
    rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)] at h
    simpa [lo1, madd2Lo, Nat.mul_comm] using h
  have hmadd3Hi_lt : madd3Hi < 2 ^ 32 := by
    dsimp [madd3Hi, base]
    have h := u32_madd_div_lt_2_32 b3 q0 (Felt.ofNat madd2Lo) hb3 hq0 (u32_mod_isU32 _)
    rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)] at h
    simpa [madd2Lo, madd3Lo, Nat.mul_comm] using h
  have haddHi_le_one : addHi ≤ 1 := by
    dsimp [addHi, base]
    have h := u32_add_div_le_one (Felt.ofNat madd3Lo) r3 (u32_mod_isU32 _) hr3
    rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)] at h
    simpa [madd3Lo] using h
  have hcarry_lt_prime : carry < GOLDILOCKS_PRIME := by
    unfold carry sumHi' sumHi GOLDILOCKS_PRIME
    omega
  have hcarry_ne' : carry ≠ 0 := by
    intro hEq
    apply hcarry_ne
    rw [hcarry_nat]
    exact hEq
  have hfelt_nonzero : (Felt.ofNat carry).val ≠ 0 := by
    rw [felt_ofNat_val_lt _ hcarry_lt_prime]
    exact hcarry_ne'
  unfold divmodCol3c exec execWithEnv
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepU32WidenMadd
    (a := b3) (b := q0) (c := Felt.ofNat madd2Lo)
    (ha := hb3) (hb := hq0) (hc := u32_mod_isU32 _)]
  miden_bind
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  miden_swap
  miden_movup
  rw [stepAdd]
  miden_bind
  rw [show Felt.ofNat ((b3.val * q0.val + madd2Lo) / 2 ^ 32) = Felt.ofNat madd3Hi by rfl]
  rw [← felt_ofNat_add]
  rw [show madd3Hi + sumHi' = sumHi' + madd3Hi by omega]
  rw [show Felt.ofNat ((b3.val * q0.val + madd2Lo) % 2 ^ 32) = Felt.ofNat madd3Lo by rfl]
  miden_swap
  miden_dup
  rw [stepU32WidenAdd
    (a := Felt.ofNat madd3Lo) (b := r3)
    (ha := u32_mod_isU32 _) (hb := hr3)]
  miden_bind
  rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)]
  miden_movup
  rw [ha3_eq]
  rw [show Felt.ofNat
      (u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val
          r0.val r1.val r2.val r3.val %
        base) =
      Felt.ofNat addLo by
    exact congrArg Felt.ofNat hlo_nat]
  rw [stepAssertEqWithError]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [← felt_ofNat_add]
  rw [show sumHi' + madd3Hi + addHi = carry by dsimp [carry]]
  rw [stepAssertzWithError_noneLocal "u128 divmod: carry overflow" mem locs adv_rest
    (Felt.ofNat carry) (q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest)
    hfelt_nonzero]

private theorem divmodCol3_run
    (c2Lo c2Hi q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq0 : q0.isU32 = true) (hq1 : q1.isU32 = true) (hq2 : q2.isU32 = true) (hq3 : q3.isU32 = true)
    (hr3 : r3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true)
    (hc2Lo_u32 : c2Lo.isU32 = true)
    (hc2Lo_val :
      c2Lo.val = u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / 2 ^ 32 % 2 ^ 32)
    (hc2Hi_val :
      c2Hi.val = u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / 2 ^ 32 / 2 ^ 32)
    (ha3_eq :
      a3 =
        Felt.ofNat
          (u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val
              r0.val r1.val r2.val r3.val %
            2 ^ 32))
    (hcarry_zero :
      u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val
          r0.val r1.val r2.val r3.val /
        2 ^ 32 =
      0) :
    exec 163
      ⟨c2Lo :: c2Hi :: q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
        b0 :: b1 :: b2 :: b3 :: a3 :: rest,
        mem, locs, adv_rest⟩
      divmodCol3 =
    some ⟨q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
            b0 :: b1 :: b2 :: b3 :: rest,
          mem, locs, adv_rest⟩ := by
  rw [divmodCol3_eq, exec_append]
  rw [divmodCol3a_run c2Lo c2Hi q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a3 rest adv_rest mem locs
      hq2 hq3 hb0 hb1 hc2Lo_u32]
  miden_bind
  rw [exec_append]
  rw [divmodCol3b_run c2Lo c2Hi q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a3 rest adv_rest mem locs
      hq1 hb2]
  miden_bind
  rw [divmodCol3c_run c2Lo c2Hi q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a3 rest adv_rest mem locs
      hq0 hq1 hq2 hq3 hr3 hb0 hb1 hb2 hb3 hc2Lo_u32 hc2Lo_val hc2Hi_val ha3_eq hcarry_zero]

private def divmodOverflowP41Bool (q3 b1 : Felt) : Bool :=
  Felt.ofNat ((b1.val * q3.val) % 2 ^ 32) + Felt.ofNat ((b1.val * q3.val) / 2 ^ 32) != (0 : Felt)

private def divmodOverflowP42Bool (q2 b2 : Felt) : Bool :=
  Felt.ofNat ((b2.val * q2.val) % 2 ^ 32) + Felt.ofNat ((b2.val * q2.val) / 2 ^ 32) != (0 : Felt)

private def divmodOverflowP43Bool (q1 b3 : Felt) : Bool :=
  Felt.ofNat ((b3.val * q1.val) % 2 ^ 32) + Felt.ofNat ((b3.val * q1.val) / 2 ^ 32) != (0 : Felt)

private def divmodOverflowP52Bool (q3 b2 : Felt) : Bool :=
  Felt.ofNat ((b2.val * q3.val) % 2 ^ 32) + Felt.ofNat ((b2.val * q3.val) / 2 ^ 32) != (0 : Felt)

private def divmodOverflowP53Bool (q2 b3 : Felt) : Bool :=
  Felt.ofNat ((b3.val * q2.val) % 2 ^ 32) + Felt.ofNat ((b3.val * q2.val) / 2 ^ 32) != (0 : Felt)

private def divmodOverflowP63Bool (q3 b3 : Felt) : Bool :=
  Felt.ofNat ((b3.val * q3.val) % 2 ^ 32) + Felt.ofNat ((b3.val * q3.val) / 2 ^ 32) != (0 : Felt)

private def divmodOverflowBool (q1 q2 q3 b1 b2 b3 : Felt) : Bool :=
  (((((divmodOverflowP41Bool q3 b1 || divmodOverflowP42Bool q2 b2) ||
          divmodOverflowP43Bool q1 b3) ||
        divmodOverflowP52Bool q3 b2) ||
      divmodOverflowP53Bool q2 b3) ||
    divmodOverflowP63Bool q3 b3)

private def divmodOverflow : List Op := [
  .inst (.push 0),
  .inst (.dup 10),
  .inst (.dup 5),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 11),
  .inst (.dup 4),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 12),
  .inst (.dup 3),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 11),
  .inst (.dup 5),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 12),
  .inst (.dup 4),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 12),
  .inst (.dup 5),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.assertzWithError "u128 divmod: q*b overflow")
]

set_option maxHeartbeats 12000000 in
private def divmodOverflow1 : List Op := [
  .inst (.push 0),
  .inst (.dup 10),
  .inst (.dup 5),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 11),
  .inst (.dup 4),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or)
]

private def divmodOverflow2 : List Op := [
  .inst (.dup 12),
  .inst (.dup 3),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 11),
  .inst (.dup 5),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or)
]

private def divmodOverflow3 : List Op := [
  .inst (.dup 12),
  .inst (.dup 4),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 12),
  .inst (.dup 5),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.assertzWithError "u128 divmod: q*b overflow")
]

private theorem divmodOverflow_eq :
    divmodOverflow = divmodOverflow1 ++ (divmodOverflow2 ++ divmodOverflow3) := by
  simp [divmodOverflow, divmodOverflow1, divmodOverflow2, divmodOverflow3]

private theorem divmodOverflow1_bool_run
    (q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq2 : q2.isU32 = true) (hq3 : q3.isU32 = true)
    (hb1 : b1.isU32 = true) (hb2 : b2.isU32 = true) :
    exec 163
      ⟨q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      divmodOverflow1 =
    some ⟨(if divmodOverflowP41Bool q3 b1 || divmodOverflowP42Bool q2 b2 then (1 : Felt) else 0) ::
            q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
          mem, locs, adv_rest⟩ := by
  unfold divmodOverflow1 exec execWithEnv
  simp only [List.foldlM]
  rw [stepPush]
  miden_bind
  miden_dup
  miden_dup
  rw [stepU32WidenMul (a := b1) (b := q3) (ha := hb1) (hb := hq3)]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [stepNeqImm]
  miden_bind
  have hor :
      execInstruction
        ⟨(if
              (Felt.ofNat ((b1.val * q3.val) / 2 ^ 32) + Felt.ofNat ((b1.val * q3.val) % 2 ^ 32) !=
                (0 : Felt))
            then (1 : Felt) else 0) ::
          (0 : Felt) ::
          q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
          mem, locs, adv_rest⟩
        Instruction.or =
      some ⟨(if false ||
              (Felt.ofNat ((b1.val * q3.val) / 2 ^ 32) + Felt.ofNat ((b1.val * q3.val) % 2 ^ 32) !=
                (0 : Felt))
            then (1 : Felt) else 0) ::
            q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
          mem, locs, adv_rest⟩ := by
    change execInstruction
      ⟨(if
            (Felt.ofNat ((b1.val * q3.val) / 2 ^ 32) + Felt.ofNat ((b1.val * q3.val) % 2 ^ 32) !=
              (0 : Felt))
          then (1 : Felt) else 0) ::
        (if false then (1 : Felt) else 0) ::
        q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      Instruction.or =
      some ⟨(if false ||
              (Felt.ofNat ((b1.val * q3.val) / 2 ^ 32) + Felt.ofNat ((b1.val * q3.val) % 2 ^ 32) !=
                (0 : Felt))
            then (1 : Felt) else 0) ::
            q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
          mem, locs, adv_rest⟩
    rw [stepOrIte]
  rw [hor]
  miden_bind
  miden_dup
  miden_dup
  rw [stepU32WidenMul (a := b2) (b := q2) (ha := hb2) (hb := hq2)]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [stepNeqImm]
  miden_bind
  rw [stepOrIte]
  miden_bind
  simp [pure, Pure.pure, divmodOverflowP41Bool, divmodOverflowP42Bool, add_comm]

private theorem divmodOverflow2_bool_run
    (q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq1 : q1.isU32 = true) (_hq2 : q2.isU32 = true) (hq3 : q3.isU32 = true)
    (_hb1 : b1.isU32 = true) (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    exec 163
      ⟨(if divmodOverflowP41Bool q3 b1 || divmodOverflowP42Bool q2 b2 then (1 : Felt) else 0) ::
        q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      divmodOverflow2 =
    some ⟨(if (((divmodOverflowP41Bool q3 b1 || divmodOverflowP42Bool q2 b2) ||
              divmodOverflowP43Bool q1 b3) ||
            divmodOverflowP52Bool q3 b2) then
            (1 : Felt)
          else 0) ::
            q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
          mem, locs, adv_rest⟩ := by
  unfold divmodOverflow2 exec execWithEnv
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepU32WidenMul (a := b3) (b := q1) (ha := hb3) (hb := hq1)]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [stepNeqImm]
  miden_bind
  rw [stepOrIte]
  miden_bind
  miden_dup
  miden_dup
  rw [stepU32WidenMul (a := b2) (b := q3) (ha := hb2) (hb := hq3)]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [stepNeqImm]
  miden_bind
  rw [stepOrIte]
  miden_bind
  simp [pure, Pure.pure, divmodOverflowP41Bool, divmodOverflowP42Bool, divmodOverflowP43Bool,
    divmodOverflowP52Bool, add_comm, Bool.or_assoc]

private def divmodOverflow3Check : List Op := [
  .inst (.dup 12),
  .inst (.dup 4),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 12),
  .inst (.dup 5),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or)
]

private theorem divmodOverflow3_decomp :
    divmodOverflow3 =
      divmodOverflow3Check ++ [.inst (.assertzWithError "u128 divmod: q*b overflow")] := by
  simp [divmodOverflow3, divmodOverflow3Check]

private theorem divmodOverflow3Check_run
    (q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq2 : q2.isU32 = true) (hq3 : q3.isU32 = true)
    (hb3 : b3.isU32 = true) :
    exec 163
      ⟨(if (((divmodOverflowP41Bool q3 b1 || divmodOverflowP42Bool q2 b2) ||
              divmodOverflowP43Bool q1 b3) ||
            divmodOverflowP52Bool q3 b2) then
            (1 : Felt)
          else 0) ::
        q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      divmodOverflow3Check =
    some ⟨(if divmodOverflowBool q1 q2 q3 b1 b2 b3 then (1 : Felt) else 0) ::
            q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
          mem, locs, adv_rest⟩ := by
  unfold divmodOverflow3Check exec execWithEnv
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepU32WidenMul (a := b3) (b := q2) (ha := hb3) (hb := hq2)]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [stepNeqImm]
  miden_bind
  rw [stepOrIte]
  miden_bind
  miden_dup
  miden_dup
  rw [stepU32WidenMul (a := b3) (b := q3) (ha := hb3) (hb := hq3)]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [stepNeqImm]
  miden_bind
  rw [stepOrIte]
  miden_bind
  simp [pure, Pure.pure, divmodOverflowBool, divmodOverflowP41Bool, divmodOverflowP42Bool,
    divmodOverflowP43Bool, divmodOverflowP52Bool, divmodOverflowP53Bool, divmodOverflowP63Bool,
    add_comm, Bool.or_assoc]

private theorem divmodOverflow3_eval
    (q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq2 : q2.isU32 = true) (hq3 : q3.isU32 = true)
    (hb3 : b3.isU32 = true) :
    exec 163
      ⟨(if (((divmodOverflowP41Bool q3 b1 || divmodOverflowP42Bool q2 b2) ||
              divmodOverflowP43Bool q1 b3) ||
            divmodOverflowP52Bool q3 b2) then
            (1 : Felt)
          else 0) ::
        q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      divmodOverflow3 =
    if divmodOverflowBool q1 q2 q3 b1 b2 b3 then
      none
    else
      some ⟨q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩ := by
  rw [divmodOverflow3_decomp, exec_append]
  rw [divmodOverflow3Check_run q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 rest adv_rest mem locs
      hq2 hq3 hb3]
  miden_bind
  by_cases hover : divmodOverflowBool q1 q2 q3 b1 b2 b3
  · rw [show ((if divmodOverflowBool q1 q2 q3 b1 b2 b3 then (1 : Felt) else 0) : Felt) = 1 by simp [hover]]
    unfold exec execWithEnv
    simp only [List.foldlM]
    rw [stepAssertzWithError_noneLocal "u128 divmod: q*b overflow" mem locs adv_rest (1 : Felt)
      (q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest) (by simp)]
    simp [hover]
  · rw [show ((if divmodOverflowBool q1 q2 q3 b1 b2 b3 then (1 : Felt) else 0) : Felt) = 0 by simp [hover]]
    unfold exec execWithEnv
    simp only [List.foldlM]
    rw [stepAssertzWithErrorLocal "u128 divmod: q*b overflow" mem locs adv_rest (0 : Felt)
      (q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest) rfl]
    simp [hover, pure, Pure.pure]

private theorem divmodOverflow_eval
    (q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq1 : q1.isU32 = true) (hq2 : q2.isU32 = true) (hq3 : q3.isU32 = true)
    (hb1 : b1.isU32 = true) (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    exec 163
      ⟨q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      divmodOverflow =
    if divmodOverflowBool q1 q2 q3 b1 b2 b3 then
      none
    else
      some ⟨q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩ := by
  rw [divmodOverflow_eq, exec_append]
  rw [divmodOverflow1_bool_run q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 rest adv_rest mem locs
      hq2 hq3 hb1 hb2]
  miden_bind
  rw [exec_append]
  rw [divmodOverflow2_bool_run q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 rest adv_rest mem locs
      hq1 hq2 hq3 hb1 hb2 hb3]
  miden_bind
  rw [divmodOverflow3_eval q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 rest adv_rest mem locs
      hq2 hq3 hb3]

private theorem divmodOverflowProdBool_false
    (x y : Felt) (hx : x.isU32 = true) (hy : y.isU32 = true)
    (h :
      (Felt.ofNat ((y.val * x.val) % 2 ^ 32) + Felt.ofNat ((y.val * x.val) / 2 ^ 32) != (0 : Felt)) =
        false) :
    y.val * x.val = 0 := by
  have hEq : Felt.ofNat ((y.val * x.val) % 2 ^ 32) + Felt.ofNat ((y.val * x.val) / 2 ^ 32) = 0 := by
    simpa using h
  have hlo_val :
      (Felt.ofNat ((y.val * x.val) % 2 ^ 32)).val = (y.val * x.val) % 2 ^ 32 := by
    exact felt_ofNat_val_lt _ (u32_mod_lt_prime _)
  have hhi_val :
      (Felt.ofNat ((y.val * x.val) / 2 ^ 32)).val = (y.val * x.val) / 2 ^ 32 := by
    exact felt_ofNat_val_lt _ (u32_prod_div_lt_prime y x hy hx)
  have hhi_lt : (y.val * x.val) / 2 ^ 32 < 2 ^ 32 := by
    simpa [Nat.mul_comm] using u32_prod_div_lt_2_32 y x hy hx
  have hsum_lt :
      (y.val * x.val) % 2 ^ 32 + (y.val * x.val) / 2 ^ 32 < GOLDILOCKS_PRIME := by
    unfold GOLDILOCKS_PRIME
    omega
  have hsum_val :
      (Felt.ofNat ((y.val * x.val) % 2 ^ 32) + Felt.ofNat ((y.val * x.val) / 2 ^ 32)).val =
        (y.val * x.val) % 2 ^ 32 + (y.val * x.val) / 2 ^ 32 := by
    rw [felt_add_val_no_wrap _ _ (by
      rw [hlo_val, hhi_val]
      exact hsum_lt), hlo_val, hhi_val]
  have hval' :
      (Felt.ofNat ((y.val * x.val) % 2 ^ 32) + Felt.ofNat ((y.val * x.val) / 2 ^ 32)).val = 0 := by
    exact congrArg (fun z : Felt => z.val) hEq
  have hval :
      (y.val * x.val) % 2 ^ 32 + (y.val * x.val) / 2 ^ 32 = 0 := by
    rw [hsum_val] at hval'
    exact hval'
  have hlo_zero : (y.val * x.val) % 2 ^ 32 = 0 := by omega
  have hhi_zero : (y.val * x.val) / 2 ^ 32 = 0 := by omega
  calc
    y.val * x.val = (y.val * x.val) % 2 ^ 32 + 2 ^ 32 * ((y.val * x.val) / 2 ^ 32) := by
      symm
      exact Nat.mod_add_div _ _
    _ = 0 := by rw [hlo_zero, hhi_zero]; simp

private theorem divmodOverflow1_run
    (q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq2 : q2.isU32 = true) (hq3 : q3.isU32 = true)
    (hb1 : b1.isU32 = true) (hb2 : b2.isU32 = true)
    (hq3b1_zero : q3.val * b1.val = 0)
    (hq2b2_zero : q2.val * b2.val = 0) :
    exec 163
      ⟨q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      divmodOverflow1 =
    some ⟨(0 : Felt) :: q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
          mem, locs, adv_rest⟩ := by
  unfold divmodOverflow1 exec execWithEnv
  simp only [List.foldlM]
  have hq3b1_zero' : b1.val * q3.val = 0 := by
    simpa [Nat.mul_comm] using hq3b1_zero
  have hq2b2_zero' : b2.val * q2.val = 0 := by
    simpa [Nat.mul_comm] using hq2b2_zero
  rw [stepPush]
  miden_bind
  miden_dup
  miden_dup
  rw [stepU32WidenMul (a := b1) (b := q3) (ha := hb1) (hb := hq3)]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [show Felt.ofNat ((b1.val * q3.val) / 2 ^ 32) + Felt.ofNat ((b1.val * q3.val) % 2 ^ 32) = 0 by
    rw [hq3b1_zero']
    native_decide]
  rw [show execInstruction
      ⟨(0 : Felt) :: (0 : Felt) :: q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
        b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      (.neqImm 0) =
      some ⟨(if false then (1 : Felt) else 0) :: (if false then (1 : Felt) else 0) ::
        q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩ by
    rw [stepNeqImm]
    simp]
  miden_bind
  rw [stepOrIte (p := false) (q := false)]
  miden_bind
  simp
  miden_dup
  miden_dup
  rw [stepU32WidenMul (a := b2) (b := q2) (ha := hb2) (hb := hq2)]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [show Felt.ofNat ((b2.val * q2.val) / 2 ^ 32) + Felt.ofNat ((b2.val * q2.val) % 2 ^ 32) = 0 by
    rw [hq2b2_zero']
    native_decide]
  rw [show execInstruction
      ⟨(0 : Felt) :: (0 : Felt) :: q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
        b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      (.neqImm 0) =
      some ⟨(if false then (1 : Felt) else 0) :: (if false then (1 : Felt) else 0) ::
        q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩ by
    rw [stepNeqImm]
    simp]
  miden_bind
  rw [stepOrIte (p := false) (q := false)]
  simp

private theorem divmodOverflow2_run
    (q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq1 : q1.isU32 = true) (hq3 : q3.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true)
    (hq1b3_zero : q1.val * b3.val = 0)
    (hq3b2_zero : q3.val * b2.val = 0) :
    exec 163
      ⟨(0 : Felt) :: q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      divmodOverflow2 =
    some ⟨(0 : Felt) :: q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
          mem, locs, adv_rest⟩ := by
  unfold divmodOverflow2 exec execWithEnv
  simp only [List.foldlM]
  have hq1b3_zero' : b3.val * q1.val = 0 := by
    simpa [Nat.mul_comm] using hq1b3_zero
  have hq3b2_zero' : b2.val * q3.val = 0 := by
    simpa [Nat.mul_comm] using hq3b2_zero
  miden_dup
  miden_dup
  rw [stepU32WidenMul (a := b3) (b := q1) (ha := hb3) (hb := hq1)]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [show Felt.ofNat ((b3.val * q1.val) / 2 ^ 32) + Felt.ofNat ((b3.val * q1.val) % 2 ^ 32) = 0 by
    rw [hq1b3_zero']
    native_decide]
  rw [show execInstruction
      ⟨(0 : Felt) :: (0 : Felt) :: q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
        b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      (.neqImm 0) =
      some ⟨(if false then (1 : Felt) else 0) :: (if false then (1 : Felt) else 0) ::
        q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩ by
    rw [stepNeqImm]
    simp]
  miden_bind
  rw [stepOrIte (p := false) (q := false)]
  miden_bind
  simp
  miden_dup
  miden_dup
  rw [stepU32WidenMul (a := b2) (b := q3) (ha := hb2) (hb := hq3)]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [show Felt.ofNat ((b2.val * q3.val) / 2 ^ 32) + Felt.ofNat ((b2.val * q3.val) % 2 ^ 32) = 0 by
    rw [hq3b2_zero']
    native_decide]
  rw [show execInstruction
      ⟨(0 : Felt) :: (0 : Felt) :: q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
        b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      (.neqImm 0) =
      some ⟨(if false then (1 : Felt) else 0) :: (if false then (1 : Felt) else 0) ::
        q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩ by
    rw [stepNeqImm]
    simp]
  miden_bind
  rw [stepOrIte (p := false) (q := false)]
  simp

private theorem divmodOverflow3_run
    (q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq2 : q2.isU32 = true) (hq3 : q3.isU32 = true)
    (hb3 : b3.isU32 = true)
    (hq2b3_zero : q2.val * b3.val = 0)
    (hq3b3_zero : q3.val * b3.val = 0) :
    exec 163
      ⟨(0 : Felt) :: q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      divmodOverflow3 =
    some ⟨q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
          mem, locs, adv_rest⟩ := by
  unfold divmodOverflow3 exec execWithEnv
  simp only [List.foldlM]
  have hq2b3_zero' : b3.val * q2.val = 0 := by
    simpa [Nat.mul_comm] using hq2b3_zero
  miden_dup
  miden_dup
  rw [stepU32WidenMul (a := b3) (b := q2) (ha := hb3) (hb := hq2)]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [show Felt.ofNat ((b3.val * q2.val) / 2 ^ 32) + Felt.ofNat ((b3.val * q2.val) % 2 ^ 32) = 0 by
    rw [hq2b3_zero']
    native_decide]
  rw [show execInstruction
      ⟨(0 : Felt) :: (0 : Felt) :: q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
        b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      (.neqImm 0) =
      some ⟨(if false then (1 : Felt) else 0) :: (if false then (1 : Felt) else 0) ::
        q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩ by
    rw [stepNeqImm]
    simp]
  miden_bind
  rw [stepOrIte (p := false) (q := false)]
  miden_bind
  simp
  miden_dup
  miden_dup
  rw [stepU32WidenMul (a := b3) (b := q3) (ha := hb3) (hb := hq3)]
  miden_bind
  rw [stepAdd]
  miden_bind
  have hq3b3_zero' : b3.val * q3.val = 0 := by
    simpa [Nat.mul_comm] using hq3b3_zero
  rw [show Felt.ofNat ((b3.val * q3.val) / 2 ^ 32) + Felt.ofNat ((b3.val * q3.val) % 2 ^ 32) = 0 by
    rw [hq3b3_zero']
    native_decide]
  rw [show execInstruction
      ⟨(0 : Felt) :: (0 : Felt) :: q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 ::
        b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      (.neqImm 0) =
      some ⟨(if false then (1 : Felt) else 0) :: (if false then (1 : Felt) else 0) ::
        q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩ by
    rw [stepNeqImm]
    simp]
  miden_bind
  rw [stepOrIte (p := false) (q := false)]
  miden_bind
  simp
  rw [stepAssertzWithErrorLocal "u128 divmod: q*b overflow" mem locs adv_rest (0 : Felt)
    (q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest) rfl]

private theorem divmodOverflow_run
    (q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq1 : q1.isU32 = true) (hq2 : q2.isU32 = true) (hq3 : q3.isU32 = true)
    (hb1 : b1.isU32 = true) (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true)
    (hq3b1_zero : q3.val * b1.val = 0)
    (hq2b2_zero : q2.val * b2.val = 0)
    (hq1b3_zero : q1.val * b3.val = 0)
    (hq3b2_zero : q3.val * b2.val = 0)
    (hq2b3_zero : q2.val * b3.val = 0)
    (hq3b3_zero : q3.val * b3.val = 0) :
    exec 163
      ⟨q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      divmodOverflow =
    some ⟨q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
          mem, locs, adv_rest⟩ := by
  rw [divmodOverflow_eq, exec_append]
  rw [divmodOverflow1_run q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 rest adv_rest mem locs
      hq2 hq3 hb1 hb2 hq3b1_zero hq2b2_zero]
  miden_bind
  rw [exec_append]
  rw [divmodOverflow2_run q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 rest adv_rest mem locs
      hq1 hq3 hb2 hb3 hq1b3_zero hq3b2_zero]
  miden_bind
  rw [divmodOverflow3_run q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 rest adv_rest mem locs
      hq2 hq3 hb3 hq2b3_zero hq3b3_zero]

private def divmodCompare1 : List Op := [
  .inst (.dup 4),
  .inst (.dup 9),
  .inst (.u32OverflowSub),
  .inst (.swap 1),
  .inst (.drop)
]

private def divmodCompare2 : List Op := [
  .inst (.dup 6),
  .inst (.dup 11),
  .inst (.u32OverflowSub),
  .inst (.swap 1),
  .inst (.eqImm 0),
  .inst (.movup 2),
  .inst (.and),
  .inst (.or)
]

private def divmodCompare3 : List Op := [
  .inst (.dup 7),
  .inst (.dup 12),
  .inst (.u32OverflowSub),
  .inst (.swap 1),
  .inst (.eqImm 0),
  .inst (.movup 2),
  .inst (.and),
  .inst (.or)
]

private def divmodCompare4 : List Op := [
  .inst (.dup 8),
  .inst (.dup 13),
  .inst (.u32OverflowSub),
  .inst (.swap 1),
  .inst (.eqImm 0),
  .inst (.movup 2),
  .inst (.and),
  .inst (.or),
  .inst (.assertWithError "u128 divmod: remainder >= divisor"),
  .inst (.swapw 2),
  .inst (.dropw)
]

private def divmodTail : List Op :=
  divmodOverflow ++ (divmodCompare1 ++ (divmodCompare2 ++ (divmodCompare3 ++ divmodCompare4)))

private theorem divmodTail_eq :
    divmodTail = divmodOverflow ++ (divmodCompare1 ++ (divmodCompare2 ++ (divmodCompare3 ++ divmodCompare4))) := by
  simp [divmodTail]

private theorem divmodCompare1_run
    (q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hr0 : r0.isU32 = true) (hb0 : b0.isU32 = true) :
    exec 163
      ⟨q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      divmodCompare1 =
    some ⟨Felt.ofNat (u32OverflowingSub r0.val b0.val).1 ::
            q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
          mem, locs, adv_rest⟩ := by
  unfold divmodCompare1 exec execWithEnv
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepU32OverflowSub (a := r0) (b := b0) (ha := hr0) (hb := hb0)]
  miden_bind
  miden_swap
  rw [stepDrop]
  simp [pure, Pure.pure]

private theorem divmodCompare2_run
    (q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) :
    exec 163
      ⟨Felt.ofNat (u32OverflowingSub r0.val b0.val).1 ::
        q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      divmodCompare2 =
    some ⟨u128Borrow1 r0 r1 b0 b1 ::
            q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
          mem, locs, adv_rest⟩ := by
  unfold divmodCompare2 exec execWithEnv
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepU32OverflowSub (a := r1) (b := b1) (ha := hr1) (hb := hb1)]
  miden_bind
  miden_swap
  rw [stepEqImm]
  miden_bind
  miden_movup
  rw [u32OverflowingSub_borrow_ite r0.val b0.val]
  rw [stepAndIte]
  miden_bind
  rw [u32OverflowingSub_borrow_ite r1.val b1.val]
  rw [stepOrIte]
  miden_bind
  simp [pure, Pure.pure, u32OverflowingSub_snd_eq_zero_iff r1 b1 hr1 hb1]
  have hlow64 :
      (r1.val < b1.val ∨ r1.val = b1.val ∧ r0.val < b0.val) ↔
        r1.val * 2 ^ 32 + r0.val < b1.val * 2 ^ 32 + b0.val :=
    divmodLow64_lt_iff r0 r1 b0 b1
      (by simpa [Felt.isU32, decide_eq_true_eq] using hr0)
      (by simpa [Felt.isU32, decide_eq_true_eq] using hr1)
      (by simpa [Felt.isU32, decide_eq_true_eq] using hb0)
      (by simpa [Felt.isU32, decide_eq_true_eq] using hb1)
  rw [divmodBorrow1_eq r0 r1 b0 b1 hr0 hb0]
  by_cases h :
      r1.val < b1.val ∨ r1.val = b1.val ∧ r0.val < b0.val
  · have h' : r1.val * 2 ^ 32 + r0.val < b1.val * 2 ^ 32 + b0.val := hlow64.mp h
    simpa [h] using h'
  · have h' : ¬ (r1.val * 2 ^ 32 + r0.val < b1.val * 2 ^ 32 + b0.val) := by
      intro hc
      exact h (hlow64.mpr hc)
    simpa [h] using Nat.le_of_not_gt h'

private theorem divmodCompare3_run
    (q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true) (hr2 : r2.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) (hb2 : b2.isU32 = true) :
    exec 163
      ⟨u128Borrow1 r0 r1 b0 b1 ::
        q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      divmodCompare3 =
    some ⟨u128Borrow2 r0 r1 r2 b0 b1 b2 ::
            q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
          mem, locs, adv_rest⟩ := by
  unfold divmodCompare3 exec execWithEnv
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepU32OverflowSub (a := r2) (b := b2) (ha := hr2) (hb := hb2)]
  miden_bind
  miden_swap
  rw [stepEqImm]
  miden_bind
  miden_movup
  rw [show u128Borrow1 r0 r1 b0 b1 =
    if decide ((u128Sub1 r1 b1).2 < (u128Sub0 r0 b0).1) || decide (r1.val < b1.val) then (1 : Felt) else 0 by
    rfl]
  rw [stepAndIte]
  miden_bind
  rw [u32OverflowingSub_borrow_ite r2.val b2.val]
  rw [stepOrIte]
  miden_bind
  simp [pure, Pure.pure, u32OverflowingSub_snd_eq_zero_iff r2 b2 hr2 hb2]
  have hlow96 :
      (r2.val < b2.val ∨
        r2.val = b2.val ∧ ((u128Sub1 r1 b1).2 < (u128Sub0 r0 b0).1 ∨ r1.val < b1.val)) ↔
        r2.val * 2 ^ 64 + r1.val * 2 ^ 32 + r0.val <
          b2.val * 2 ^ 64 + b1.val * 2 ^ 32 + b0.val := by
    constructor
    · intro h
      rcases h with h | ⟨hEq, hLow⟩
      · exact (divmodLow96_lt_iff r0 r1 r2 b0 b1 b2
          (by simpa [Felt.isU32, decide_eq_true_eq] using hr0)
          (by simpa [Felt.isU32, decide_eq_true_eq] using hr1)
          (by simpa [Felt.isU32, decide_eq_true_eq] using hr2)
          (by simpa [Felt.isU32, decide_eq_true_eq] using hb0)
          (by simpa [Felt.isU32, decide_eq_true_eq] using hb1)
          (by simpa [Felt.isU32, decide_eq_true_eq] using hb2)).mp (Or.inl h)
      · exact (divmodLow96_lt_iff r0 r1 r2 b0 b1 b2
          (by simpa [Felt.isU32, decide_eq_true_eq] using hr0)
          (by simpa [Felt.isU32, decide_eq_true_eq] using hr1)
          (by simpa [Felt.isU32, decide_eq_true_eq] using hr2)
          (by simpa [Felt.isU32, decide_eq_true_eq] using hb0)
          (by simpa [Felt.isU32, decide_eq_true_eq] using hb1)
          (by simpa [Felt.isU32, decide_eq_true_eq] using hb2)).mp
          (Or.inr ⟨hEq, (divmodBorrow1_prop_eq r0 r1 b0 b1 hr0 hb0).mp hLow⟩)
    · intro h
      rcases (divmodLow96_lt_iff r0 r1 r2 b0 b1 b2
          (by simpa [Felt.isU32, decide_eq_true_eq] using hr0)
          (by simpa [Felt.isU32, decide_eq_true_eq] using hr1)
          (by simpa [Felt.isU32, decide_eq_true_eq] using hr2)
          (by simpa [Felt.isU32, decide_eq_true_eq] using hb0)
          (by simpa [Felt.isU32, decide_eq_true_eq] using hb1)
          (by simpa [Felt.isU32, decide_eq_true_eq] using hb2)).mpr h with h | ⟨hEq, hLow⟩
      · exact Or.inl h
      · exact Or.inr ⟨hEq, (divmodBorrow1_prop_eq r0 r1 b0 b1 hr0 hb0).mpr hLow⟩
  rw [divmodBorrow2_eq r0 r1 r2 b0 b1 b2 hr0 hr1 hb0 hb1]
  by_cases h :
      r2.val < b2.val ∨
        r2.val = b2.val ∧ ((u128Sub1 r1 b1).2 < (u128Sub0 r0 b0).1 ∨ r1.val < b1.val)
  · have h' :
        r2.val * 2 ^ 64 + r1.val * 2 ^ 32 + r0.val <
          b2.val * 2 ^ 64 + b1.val * 2 ^ 32 + b0.val := hlow96.mp h
    simpa [h] using h'
  · have h' :
        ¬ (r2.val * 2 ^ 64 + r1.val * 2 ^ 32 + r0.val <
            b2.val * 2 ^ 64 + b1.val * 2 ^ 32 + b0.val) := by
      intro hc
      exact h (hlow96.mpr hc)
    simpa [h] using Nat.le_of_not_gt h'

private theorem divmodCompare4_run
    (q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true) (hr2 : r2.isU32 = true) (hr3 : r3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true)
    (h_lt_result : u128LtBool r0 r1 r2 r3 b0 b1 b2 b3 = true) :
    exec 163
      ⟨u128Borrow2 r0 r1 r2 b0 b1 b2 ::
        q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      divmodCompare4 =
    some ⟨r0 :: r1 :: r2 :: r3 :: q0 :: q1 :: q2 :: q3 :: rest,
          mem, locs, adv_rest⟩ := by
  unfold divmodCompare4 exec execWithEnv
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepU32OverflowSub (a := r3) (b := b3) (ha := hr3) (hb := hb3)]
  miden_bind
  miden_swap
  rw [stepEqImm]
  miden_bind
  miden_movup
  rw [show u128Borrow2 r0 r1 r2 b0 b1 b2 =
    if decide ((u128Sub2 r2 b2).2 < (u128Borrow1 r0 r1 b0 b1).val) || decide (r2.val < b2.val)
      then (1 : Felt) else 0 by
    rfl]
  rw [stepAndIte]
  miden_bind
  rw [u32OverflowingSub_borrow_ite r3.val b3.val]
  rw [stepOrIte]
  miden_bind
  have h_lt_felt :
      (if
          decide (r3.val < b3.val) ||
            ((Felt.ofNat (u32OverflowingSub r3.val b3.val).2 = 0) &&
              (decide ((u128Sub2 r2 b2).2 < (u128Borrow1 r0 r1 b0 b1).val) ||
                decide (r2.val < b2.val))) = true
        then
          (1 : Felt)
        else
          0) =
      (if u128LtBool r0 r1 r2 r3 b0 b1 b2 b3 then (1 : Felt) else 0) := by
    have hlow128 :
        (r3.val < b3.val ∨
          r3.val = b3.val ∧
            ((u128Sub2 r2 b2).2 < (u128Borrow1 r0 r1 b0 b1).val ∨ r2.val < b2.val)) ↔
          r3.val * 2 ^ 96 + r2.val * 2 ^ 64 + r1.val * 2 ^ 32 + r0.val <
            b3.val * 2 ^ 96 + b2.val * 2 ^ 64 + b1.val * 2 ^ 32 + b0.val := by
      constructor
      · intro h
        rcases h with h | ⟨hEq, hLow⟩
        · exact (divmodLow128_lt_iff r0 r1 r2 r3 b0 b1 b2 b3
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr0)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr1)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr2)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr3)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb0)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb1)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb2)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb3)).mp (Or.inl h)
        · exact (divmodLow128_lt_iff r0 r1 r2 r3 b0 b1 b2 b3
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr0)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr1)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr2)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr3)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb0)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb1)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb2)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb3)).mp
            (Or.inr ⟨hEq, (divmodBorrow2_prop_eq r0 r1 r2 b0 b1 b2 hr0 hr1 hr2 hb0 hb1 hb2).mp hLow⟩)
      · intro h
        rcases (divmodLow128_lt_iff r0 r1 r2 r3 b0 b1 b2 b3
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr0)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr1)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr2)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr3)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb0)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb1)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb2)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb3)).mpr h with h | ⟨hEq, hLow⟩
        · exact Or.inl h
        · exact Or.inr ⟨hEq, (divmodBorrow2_prop_eq r0 r1 r2 b0 b1 b2 hr0 hr1 hr2 hb0 hb1 hb2).mpr hLow⟩
    have hleft :
        (if
            r3.val < b3.val ∨
              r3.val = b3.val ∧
                ((u128Sub2 r2 b2).2 < (u128Borrow1 r0 r1 b0 b1).val ∨ r2.val < b2.val)
          then
            (1 : Felt)
          else
            0) =
        (if
            decide
              (r3.val * 2 ^ 96 + r2.val * 2 ^ 64 + r1.val * 2 ^ 32 + r0.val <
                b3.val * 2 ^ 96 + b2.val * 2 ^ 64 + b1.val * 2 ^ 32 + b0.val)
          then
            (1 : Felt)
          else
            0) := by
      by_cases h :
          r3.val < b3.val ∨
            r3.val = b3.val ∧
              ((u128Sub2 r2 b2).2 < (u128Borrow1 r0 r1 b0 b1).val ∨ r2.val < b2.val)
      · have h' :
          r3.val * 2 ^ 96 + r2.val * 2 ^ 64 + r1.val * 2 ^ 32 + r0.val <
            b3.val * 2 ^ 96 + b2.val * 2 ^ 64 + b1.val * 2 ^ 32 + b0.val := hlow128.mp h
        simpa [h] using h'
      · have h' :
          ¬ (r3.val * 2 ^ 96 + r2.val * 2 ^ 64 + r1.val * 2 ^ 32 + r0.val <
              b3.val * 2 ^ 96 + b2.val * 2 ^ 64 + b1.val * 2 ^ 32 + b0.val) := by
          intro hc
          exact h (hlow128.mpr hc)
        simpa [h] using Nat.le_of_not_gt h'
    calc
      (if
          decide (r3.val < b3.val) ||
            ((Felt.ofNat (u32OverflowingSub r3.val b3.val).2 = 0) &&
              (decide ((u128Sub2 r2 b2).2 < (u128Borrow1 r0 r1 b0 b1).val) ||
                decide (r2.val < b2.val))) = true
        then
          (1 : Felt)
        else
          0)
          =
        (if
          r3.val < b3.val ∨
            r3.val = b3.val ∧
              ((u128Sub2 r2 b2).2 < (u128Borrow1 r0 r1 b0 b1).val ∨ r2.val < b2.val)
        then
          (1 : Felt)
        else
          0) := by
            simp [u32OverflowingSub_snd_eq_zero_iff r3 b3 hr3 hb3]
      _ =
        (if
            decide
              (r3.val * 2 ^ 96 + r2.val * 2 ^ 64 + r1.val * 2 ^ 32 + r0.val <
                b3.val * 2 ^ 96 + b2.val * 2 ^ 64 + b1.val * 2 ^ 32 + b0.val)
          then
            (1 : Felt)
          else
            0) := hleft
      _ = (if u128LtBool r0 r1 r2 r3 b0 b1 b2 b3 then (1 : Felt) else 0) := by
            simp [divmodLtBool_eqRaw r0 r1 r2 r3 b0 b1 b2 b3 hr0 hr1 hr2 hr3 hb0 hb1 hb2 hb3]
  have h_lt_felt' :
      (if
          (decide (r3.val < b3.val) ||
              Felt.ofNat (u32OverflowingSub r3.val b3.val).2 == 0 &&
                (decide ((u128Sub2 r2 b2).2 < (u128Borrow1 r0 r1 b0 b1).val) ||
                  decide (r2.val < b2.val))) =
            true then
        (1 : Felt)
      else
        0) =
      (if u128LtBool r0 r1 r2 r3 b0 b1 b2 b3 then (1 : Felt) else 0) := by
    simpa using h_lt_felt
  rw [h_lt_felt']
  rw [stepAssertWithError (msg := "u128 divmod: remainder >= divisor")
      (h := by simp [h_lt_result])]
  miden_bind
  rw [stepSwapw2Local mem locs adv_rest q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 rest]
  miden_bind
  rw [stepDropw]
  simp [pure, Pure.pure]

private theorem divmodCompare4_none
    (q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true) (hr2 : r2.isU32 = true) (hr3 : r3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true)
    (h_lt_result : u128LtBool r0 r1 r2 r3 b0 b1 b2 b3 ≠ true) :
    exec 163
      ⟨u128Borrow2 r0 r1 r2 b0 b1 b2 ::
        q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      divmodCompare4 =
    none := by
  unfold divmodCompare4 exec execWithEnv
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepU32OverflowSub (a := r3) (b := b3) (ha := hr3) (hb := hb3)]
  miden_bind
  miden_swap
  rw [stepEqImm]
  miden_bind
  miden_movup
  rw [show u128Borrow2 r0 r1 r2 b0 b1 b2 =
    if decide ((u128Sub2 r2 b2).2 < (u128Borrow1 r0 r1 b0 b1).val) || decide (r2.val < b2.val)
      then (1 : Felt) else 0 by
    rfl]
  rw [stepAndIte]
  miden_bind
  rw [u32OverflowingSub_borrow_ite r3.val b3.val]
  rw [stepOrIte]
  miden_bind
  have h_lt_felt :
      (if
          decide (r3.val < b3.val) ||
            ((Felt.ofNat (u32OverflowingSub r3.val b3.val).2 = 0) &&
              (decide ((u128Sub2 r2 b2).2 < (u128Borrow1 r0 r1 b0 b1).val) ||
                decide (r2.val < b2.val))) = true
        then
          (1 : Felt)
        else
          0) =
      (if u128LtBool r0 r1 r2 r3 b0 b1 b2 b3 then (1 : Felt) else 0) := by
    have hlow128 :
        (r3.val < b3.val ∨
          r3.val = b3.val ∧
            ((u128Sub2 r2 b2).2 < (u128Borrow1 r0 r1 b0 b1).val ∨ r2.val < b2.val)) ↔
          r3.val * 2 ^ 96 + r2.val * 2 ^ 64 + r1.val * 2 ^ 32 + r0.val <
            b3.val * 2 ^ 96 + b2.val * 2 ^ 64 + b1.val * 2 ^ 32 + b0.val := by
      constructor
      · intro h
        rcases h with h | ⟨hEq, hLow⟩
        · exact (divmodLow128_lt_iff r0 r1 r2 r3 b0 b1 b2 b3
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr0)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr1)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr2)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr3)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb0)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb1)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb2)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb3)).mp (Or.inl h)
        · exact (divmodLow128_lt_iff r0 r1 r2 r3 b0 b1 b2 b3
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr0)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr1)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr2)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr3)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb0)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb1)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb2)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb3)).mp
            (Or.inr ⟨hEq, (divmodBorrow2_prop_eq r0 r1 r2 b0 b1 b2 hr0 hr1 hr2 hb0 hb1 hb2).mp hLow⟩)
      · intro h
        rcases (divmodLow128_lt_iff r0 r1 r2 r3 b0 b1 b2 b3
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr0)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr1)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr2)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hr3)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb0)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb1)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb2)
            (by simpa [Felt.isU32, decide_eq_true_eq] using hb3)).mpr h with h | ⟨hEq, hLow⟩
        · exact Or.inl h
        · exact Or.inr ⟨hEq, (divmodBorrow2_prop_eq r0 r1 r2 b0 b1 b2 hr0 hr1 hr2 hb0 hb1 hb2).mpr hLow⟩
    have hleft :
        (if
            r3.val < b3.val ∨
              r3.val = b3.val ∧
                ((u128Sub2 r2 b2).2 < (u128Borrow1 r0 r1 b0 b1).val ∨ r2.val < b2.val)
          then
            (1 : Felt)
          else
            0) =
        (if
            decide
              (r3.val * 2 ^ 96 + r2.val * 2 ^ 64 + r1.val * 2 ^ 32 + r0.val <
                b3.val * 2 ^ 96 + b2.val * 2 ^ 64 + b1.val * 2 ^ 32 + b0.val)
          then
            (1 : Felt)
          else
            0) := by
      by_cases h :
          r3.val < b3.val ∨
            r3.val = b3.val ∧
              ((u128Sub2 r2 b2).2 < (u128Borrow1 r0 r1 b0 b1).val ∨ r2.val < b2.val)
      · have h' :
          r3.val * 2 ^ 96 + r2.val * 2 ^ 64 + r1.val * 2 ^ 32 + r0.val <
            b3.val * 2 ^ 96 + b2.val * 2 ^ 64 + b1.val * 2 ^ 32 + b0.val := hlow128.mp h
        simpa [h] using h'
      · have h' :
          ¬ (r3.val * 2 ^ 96 + r2.val * 2 ^ 64 + r1.val * 2 ^ 32 + r0.val <
              b3.val * 2 ^ 96 + b2.val * 2 ^ 64 + b1.val * 2 ^ 32 + b0.val) := by
          intro hc
          exact h (hlow128.mpr hc)
        simpa [h] using Nat.le_of_not_gt h'
    calc
      (if
          decide (r3.val < b3.val) ||
            ((Felt.ofNat (u32OverflowingSub r3.val b3.val).2 = 0) &&
              (decide ((u128Sub2 r2 b2).2 < (u128Borrow1 r0 r1 b0 b1).val) ||
                decide (r2.val < b2.val))) = true
        then
          (1 : Felt)
        else
          0)
          =
        (if
          r3.val < b3.val ∨
            r3.val = b3.val ∧
              ((u128Sub2 r2 b2).2 < (u128Borrow1 r0 r1 b0 b1).val ∨ r2.val < b2.val)
        then
          (1 : Felt)
        else
          0) := by
            simp [u32OverflowingSub_snd_eq_zero_iff r3 b3 hr3 hb3]
      _ =
        (if
            decide
              (r3.val * 2 ^ 96 + r2.val * 2 ^ 64 + r1.val * 2 ^ 32 + r0.val <
                b3.val * 2 ^ 96 + b2.val * 2 ^ 64 + b1.val * 2 ^ 32 + b0.val)
          then
            (1 : Felt)
          else
            0) := hleft
      _ = (if u128LtBool r0 r1 r2 r3 b0 b1 b2 b3 then (1 : Felt) else 0) := by
            simp [divmodLtBool_eqRaw r0 r1 r2 r3 b0 b1 b2 b3 hr0 hr1 hr2 hr3 hb0 hb1 hb2 hb3]
  have h_lt_felt' :
      (if
          (decide (r3.val < b3.val) ||
              Felt.ofNat (u32OverflowingSub r3.val b3.val).2 == 0 &&
                (decide ((u128Sub2 r2 b2).2 < (u128Borrow1 r0 r1 b0 b1).val) ||
                  decide (r2.val < b2.val))) =
            true then
        (1 : Felt)
      else
        0) =
      (if u128LtBool r0 r1 r2 r3 b0 b1 b2 b3 then (1 : Felt) else 0) := by
    simpa using h_lt_felt
  rw [h_lt_felt']
  have h_lt_false : u128LtBool r0 r1 r2 r3 b0 b1 b2 b3 = false := by
    by_cases h : u128LtBool r0 r1 r2 r3 b0 b1 b2 b3 = true
    · exact (h_lt_result h).elim
    · cases hlt : u128LtBool r0 r1 r2 r3 b0 b1 b2 b3 <;> simp_all
  rw [stepAssertWithError_none (msg := "u128 divmod: remainder >= divisor")
      (h := by simp [h_lt_false])]

private theorem divmodTail_run
    (q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 : Felt)
    (rest adv_rest : List Felt) (mem locs : Nat → Felt)
    (hq1 : q1.isU32 = true) (hq2 : q2.isU32 = true) (hq3 : q3.isU32 = true)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true) (hr2 : r2.isU32 = true) (hr3 : r3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true)
    (hq3b1_zero : q3.val * b1.val = 0)
    (hq2b2_zero : q2.val * b2.val = 0)
    (hq1b3_zero : q1.val * b3.val = 0)
    (hq3b2_zero : q3.val * b2.val = 0)
    (hq2b3_zero : q2.val * b3.val = 0)
    (hq3b3_zero : q3.val * b3.val = 0)
    (h_lt_result : u128LtBool r0 r1 r2 r3 b0 b1 b2 b3 = true) :
    exec 163
      ⟨q0 :: q1 :: q2 :: q3 :: r0 :: r1 :: r2 :: r3 :: b0 :: b1 :: b2 :: b3 :: rest,
        mem, locs, adv_rest⟩
      divmodTail =
    some ⟨r0 :: r1 :: r2 :: r3 :: q0 :: q1 :: q2 :: q3 :: rest,
          mem, locs, adv_rest⟩ := by
  rw [divmodTail_eq, exec_append]
  rw [divmodOverflow_run q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 rest adv_rest mem locs
      hq1 hq2 hq3 hb1 hb2 hb3 hq3b1_zero hq2b2_zero hq1b3_zero hq3b2_zero hq2b3_zero hq3b3_zero]
  miden_bind
  rw [exec_append]
  rw [divmodCompare1_run q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 rest adv_rest mem locs hr0 hb0]
  miden_bind
  rw [exec_append]
  rw [divmodCompare2_run q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 rest adv_rest mem locs
      hr0 hr1 hb0 hb1]
  miden_bind
  rw [exec_append]
  rw [divmodCompare3_run q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 rest adv_rest mem locs
      hr0 hr1 hr2 hb0 hb1 hb2]
  miden_bind
  rw [divmodCompare4_run q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 rest adv_rest mem locs
      hr0 hr1 hr2 hr3 hb0 hb1 hb2 hb3 h_lt_result]

private theorem divmod_decomp :
    Miden.Core.U128.divmod =
      divmodSetup ++ (divmodCol0 ++ (divmodCol1 ++ (divmodCol2 ++ (divmodCol3 ++ divmodTail)))) := by
  simp [Miden.Core.U128.divmod, divmodSetup, divmodCol0, divmodCol1,
    divmodCol2, divmodCol2a, divmodCol2b, divmodCol2c,
    divmodCol3, divmodCol3a, divmodCol3b, divmodCol3c,
    divmodTail, divmodOverflow, divmodCompare1, divmodCompare2, divmodCompare3, divmodCompare4]

private theorem u128RawValue_lt_2_128
    (a0 a1 a2 a3 : Nat)
    (ha0 : a0 < 2 ^ 32) (ha1 : a1 < 2 ^ 32) (ha2 : a2 < 2 ^ 32) (ha3 : a3 < 2 ^ 32) :
    u128RawValue a0 a1 a2 a3 < 2 ^ 128 := by
  unfold u128RawValue
  omega

private theorem divmodStage0_repr
    (q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 : Nat) :
    let base := 2 ^ 32
    u128RawValue q0 q1 q2 q3 * u128RawValue b0 b1 b2 b3 + u128RawValue r0 r1 r2 r3 =
      u128DivmodCol0 q0 b0 r0
        + (q0 * b1 + q1 * b0 + r1) * base
        + (q0 * b2 + q1 * b1 + q2 * b0 + r2) * base ^ 2
        + (q0 * b3 + q1 * b2 + q2 * b1 + q3 * b0 + r3) * base ^ 3
        + (q1 * b3 + q2 * b2 + q3 * b1) * base ^ 4
        + (q2 * b3 + q3 * b2) * base ^ 5
        + (q3 * b3) * base ^ 6 := by
  dsimp [u128RawValue, u128DivmodCol0]
  ring

private theorem divmodStage1_repr
    (q0 q1 b0 b1 r0 r1 : Nat) :
    let base := 2 ^ 32
    u128DivmodCol0 q0 b0 r0 + (q0 * b1 + q1 * b0 + r1) * base =
      (u128DivmodCol0 q0 b0 r0 % base) + u128DivmodCol1 q0 q1 b0 b1 r0 r1 * base := by
  let base := 2 ^ 32
  have h0 := (Nat.mod_add_div (u128DivmodCol0 q0 b0 r0) base).symm
  rw [h0]
  dsimp [base]
  unfold u128DivmodCol1
  ring_nf
  omega

private theorem divmodStage2_repr
    (q0 q1 q2 b0 b1 b2 r0 r1 r2 : Nat) :
    let base := 2 ^ 32
    u128DivmodCol1 q0 q1 b0 b1 r0 r1 * base + (q0 * b2 + q1 * b1 + q2 * b0 + r2) * base ^ 2 =
      (u128DivmodCol1 q0 q1 b0 b1 r0 r1 % base) * base +
        u128DivmodCol2 q0 q1 q2 b0 b1 b2 r0 r1 r2 * base ^ 2 := by
  let base := 2 ^ 32
  have h1 := (Nat.mod_add_div (u128DivmodCol1 q0 q1 b0 b1 r0 r1) base).symm
  rw [h1]
  dsimp [base]
  unfold u128DivmodCol2
  ring_nf
  omega

private theorem divmodStage3_repr
    (q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 : Nat) :
    let base := 2 ^ 32
    u128DivmodCol2 q0 q1 q2 b0 b1 b2 r0 r1 r2 * base ^ 2
      + (q0 * b3 + q1 * b2 + q2 * b1 + q3 * b0 + r3) * base ^ 3 =
      (u128DivmodCol2 q0 q1 q2 b0 b1 b2 r0 r1 r2 % base) * base ^ 2 +
        u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * base ^ 3 := by
  let base := 2 ^ 32
  have h2 := (Nat.mod_add_div (u128DivmodCol2 q0 q1 q2 b0 b1 b2 r0 r1 r2) base).symm
  rw [h2]
  dsimp [base]
  unfold u128DivmodCol3
  ring_nf
  omega

private theorem divmodStage4_repr
    (q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 : Nat) :
    let base := 2 ^ 32
    u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * base ^ 3
      + (q1 * b3 + q2 * b2 + q3 * b1) * base ^ 4
      + (q2 * b3 + q3 * b2) * base ^ 5
      + (q3 * b3) * base ^ 6 =
      (u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 % base) * base ^ 3
        + (u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 / base +
            q1 * b3 + q2 * b2 + q3 * b1) * base ^ 4
        + (q2 * b3 + q3 * b2) * base ^ 5
        + (q3 * b3) * base ^ 6 := by
  dsimp
  have h3 := (Nat.mod_add_div (u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3) (2 ^ 32)).symm
  have hbase_pos : 0 < 2 ^ 32 := by
    positivity
  rw [h3]
  have hmod :
      (u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 % (2 ^ 32) +
          (2 ^ 32) * (u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 / (2 ^ 32))) %
        (2 ^ 32) =
        u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 % (2 ^ 32) := by
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (Nat.mod_lt _ hbase_pos)
  have hdiv :
      (u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 % (2 ^ 32) +
          (2 ^ 32) * (u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 / (2 ^ 32))) /
        (2 ^ 32) =
        u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 / (2 ^ 32) := by
    rw [Nat.add_mul_div_left _ _ hbase_pos, Nat.div_eq_of_lt (Nat.mod_lt _ hbase_pos)]
    simp
  have hmod' :
      (u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 % 2 ^ 32 +
          2 ^ 32 * (u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 / 2 ^ 32)) %
        4294967296 =
        u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 % 2 ^ 32 := by
    convert hmod using 1
  have hdiv' :
      (u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 % 2 ^ 32 +
          2 ^ 32 * (u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 / 2 ^ 32)) /
        4294967296 =
        u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 / 2 ^ 32 := by
    convert hdiv using 1
  have hrhs :
      (u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 % 2 ^ 32 +
            2 ^ 32 * (u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 / 2 ^ 32)) %
          4294967296 *
        79228162514264337593543950336 +
      ((u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 % 2 ^ 32 +
              2 ^ 32 * (u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 / 2 ^ 32)) /
            4294967296 +
          q1 * b3 + q2 * b2 + q3 * b1) *
        340282366920938463463374607431768211456 +
      (q2 * b3 + q3 * b2) * 1461501637330902918203684832716283019655932542976 +
      q3 * b3 * 6277101735386680763835789423207666416102355444464034512896 =
      (u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 % 2 ^ 32) *
        79228162514264337593543950336 +
      (u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 / 2 ^ 32 +
          q1 * b3 + q2 * b2 + q3 * b1) *
        340282366920938463463374607431768211456 +
      (q2 * b3 + q3 * b2) * 1461501637330902918203684832716283019655932542976 +
      q3 * b3 * 6277101735386680763835789423207666416102355444464034512896 := by
    rw [hmod', hdiv']
  calc
    (u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 % 2 ^ 32 +
            2 ^ 32 * (u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 / 2 ^ 32)) *
          79228162514264337593543950336 +
        (q1 * b3 + q2 * b2 + q3 * b1) * 340282366920938463463374607431768211456 +
      (q2 * b3 + q3 * b2) * 1461501637330902918203684832716283019655932542976 +
      q3 * b3 * 6277101735386680763835789423207666416102355444464034512896 =
      (u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 % 2 ^ 32) *
        79228162514264337593543950336 +
      (u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 / 2 ^ 32 +
          q1 * b3 + q2 * b2 + q3 * b1) *
        340282366920938463463374607431768211456 +
      (q2 * b3 + q3 * b2) * 1461501637330902918203684832716283019655932542976 +
      q3 * b3 * 6277101735386680763835789423207666416102355444464034512896 := by ring
    _ = _ := hrhs.symm

private theorem u128RawValue_injective_of_u32
    (a0 a1 a2 a3 c0 c1 c2 c3 : Nat)
    (ha0 : a0 < 2 ^ 32) (ha1 : a1 < 2 ^ 32) (ha2 : a2 < 2 ^ 32) (ha3 : a3 < 2 ^ 32)
    (hc0 : c0 < 2 ^ 32) (hc1 : c1 < 2 ^ 32) (hc2 : c2 < 2 ^ 32) (hc3 : c3 < 2 ^ 32)
    (h : u128RawValue a0 a1 a2 a3 = u128RawValue c0 c1 c2 c3) :
    a0 = c0 ∧ a1 = c1 ∧ a2 = c2 ∧ a3 = c3 := by
  have hU : U128.ofNat (u128RawValue a0 a1 a2 a3) = U128.ofNat (u128RawValue c0 c1 c2 c3) :=
    congrArg U128.ofNat h
  obtain ⟨ha0_felt, ha1_felt, ha2_felt, ha3_felt⟩ := by
    simpa [u128RawValue] using U128.ofNat_of_limbs a3 a2 a1 a0 ha3 ha2 ha1 ha0
  obtain ⟨hc0_felt, hc1_felt, hc2_felt, hc3_felt⟩ := by
    simpa [u128RawValue] using U128.ofNat_of_limbs c3 c2 c1 c0 hc3 hc2 hc1 hc0
  have h0_felt : Felt.ofNat a0 = Felt.ofNat c0 := by
    calc
      Felt.ofNat a0 = (U128.ofNat (u128RawValue a0 a1 a2 a3)).a0.val := by symm; exact ha0_felt
      _ = (U128.ofNat (u128RawValue c0 c1 c2 c3)).a0.val := congrArg (fun x => x.a0.val) hU
      _ = Felt.ofNat c0 := hc0_felt
  have h1_felt : Felt.ofNat a1 = Felt.ofNat c1 := by
    calc
      Felt.ofNat a1 = (U128.ofNat (u128RawValue a0 a1 a2 a3)).a1.val := by symm; exact ha1_felt
      _ = (U128.ofNat (u128RawValue c0 c1 c2 c3)).a1.val := congrArg (fun x => x.a1.val) hU
      _ = Felt.ofNat c1 := hc1_felt
  have h2_felt : Felt.ofNat a2 = Felt.ofNat c2 := by
    calc
      Felt.ofNat a2 = (U128.ofNat (u128RawValue a0 a1 a2 a3)).a2.val := by symm; exact ha2_felt
      _ = (U128.ofNat (u128RawValue c0 c1 c2 c3)).a2.val := congrArg (fun x => x.a2.val) hU
      _ = Felt.ofNat c2 := hc2_felt
  have h3_felt : Felt.ofNat a3 = Felt.ofNat c3 := by
    calc
      Felt.ofNat a3 = (U128.ofNat (u128RawValue a0 a1 a2 a3)).a3.val := by symm; exact ha3_felt
      _ = (U128.ofNat (u128RawValue c0 c1 c2 c3)).a3.val := congrArg (fun x => x.a3.val) hU
      _ = Felt.ofNat c3 := hc3_felt
  have h0 : a0 = c0 := by
    have := congrArg (fun x => x.val) h0_felt
    simpa [felt_ofNat_val_lt _ (u32_val_lt_prime _ ha0), felt_ofNat_val_lt _ (u32_val_lt_prime _ hc0)] using this
  have h1 : a1 = c1 := by
    have := congrArg (fun x => x.val) h1_felt
    simpa [felt_ofNat_val_lt _ (u32_val_lt_prime _ ha1), felt_ofNat_val_lt _ (u32_val_lt_prime _ hc1)] using this
  have h2 : a2 = c2 := by
    have := congrArg (fun x => x.val) h2_felt
    simpa [felt_ofNat_val_lt _ (u32_val_lt_prime _ ha2), felt_ofNat_val_lt _ (u32_val_lt_prime _ hc2)] using this
  have h3 : a3 = c3 := by
    have := congrArg (fun x => x.val) h3_felt
    simpa [felt_ofNat_val_lt _ (u32_val_lt_prime _ ha3), felt_ofNat_val_lt _ (u32_val_lt_prime _ hc3)] using this
  exact ⟨h0, h1, h2, h3⟩

private def u32Base : Nat := 2 ^ 32

private def divmodCol0Lo (q0 b0 r0 : Nat) : Nat :=
  u128DivmodCol0 q0 b0 r0 % 2 ^ 32

private def divmodCol1Lo (q0 q1 b0 b1 r0 r1 : Nat) : Nat :=
  u128DivmodCol1 q0 q1 b0 b1 r0 r1 % 2 ^ 32

private def divmodCol2Lo (q0 q1 q2 b0 b1 b2 r0 r1 r2 : Nat) : Nat :=
  u128DivmodCol2 q0 q1 q2 b0 b1 b2 r0 r1 r2 % 2 ^ 32

private def divmodCol3Lo (q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 : Nat) : Nat :=
  u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 % 2 ^ 32

private def divmodCarry (q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 : Nat) : Nat :=
  u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 / 2 ^ 32

private def divmodX1 (q0 q1 b0 b1 r1 : Nat) : Nat :=
  q0 * b1 + q1 * b0 + r1

private def divmodX2 (q0 q1 q2 b0 b1 b2 r2 : Nat) : Nat :=
  q0 * b2 + q1 * b1 + q2 * b0 + r2

private def divmodX3 (q0 q1 q2 q3 b0 b1 b2 b3 r3 : Nat) : Nat :=
  q0 * b3 + q1 * b2 + q2 * b1 + q3 * b0 + r3

private def divmodX4 (q1 q2 q3 b1 b2 b3 : Nat) : Nat :=
  q1 * b3 + q2 * b2 + q3 * b1

private def divmodX5 (q2 q3 b2 b3 : Nat) : Nat :=
  q2 * b3 + q3 * b2

private def divmodX6 (q3 b3 : Nat) : Nat :=
  q3 * b3

private theorem carry_zero_of_packed_u128
    (a0 a1 a2 a3 c0 c1 c2 c3 carry : Nat)
    (ha0 : a0 < 2 ^ 32) (ha1 : a1 < 2 ^ 32) (ha2 : a2 < 2 ^ 32) (ha3 : a3 < 2 ^ 32)
    (hpacked :
      u128RawValue a0 a1 a2 a3 =
        c0 + c1 * u32Base + c2 * u32Base ^ 2 + c3 * u32Base ^ 3 + carry * u32Base ^ 4) :
    carry = 0 := by
  have hpackedA_lt : u128RawValue a0 a1 a2 a3 < u32Base ^ 4 := by
    dsimp [u32Base]
    simpa using u128RawValue_lt_2_128 a0 a1 a2 a3 ha0 ha1 ha2 ha3
  by_contra hne
  have hpos : 0 < carry := Nat.pos_of_ne_zero hne
  have hge : u32Base ^ 4 ≤ u128RawValue a0 a1 a2 a3 := by
    calc
      u32Base ^ 4 ≤ carry * u32Base ^ 4 := by
        exact Nat.mul_le_mul_right (u32Base ^ 4) (Nat.succ_le_of_lt hpos)
      _ ≤ c0 + c1 * u32Base + c2 * u32Base ^ 2 + c3 * u32Base ^ 3 + carry * u32Base ^ 4 := by omega
      _ = u128RawValue a0 a1 a2 a3 := by rw [← hpacked]
  exact (not_lt_of_ge hge) hpackedA_lt

private theorem digits_of_packed_u128
    (a0 a1 a2 a3 c0 c1 c2 c3 carry : Nat)
    (ha0 : a0 < 2 ^ 32) (ha1 : a1 < 2 ^ 32) (ha2 : a2 < 2 ^ 32) (ha3 : a3 < 2 ^ 32)
    (hc0 : c0 < 2 ^ 32) (hc1 : c1 < 2 ^ 32) (hc2 : c2 < 2 ^ 32) (hc3 : c3 < 2 ^ 32)
    (hpacked :
      u128RawValue a0 a1 a2 a3 =
        c0 + c1 * u32Base + c2 * u32Base ^ 2 + c3 * u32Base ^ 3 + carry * u32Base ^ 4)
    (hcarry : carry = 0) :
    a0 = c0 ∧ a1 = c1 ∧ a2 = c2 ∧ a3 = c3 := by
  have hdigits : u128RawValue a0 a1 a2 a3 = u128RawValue c0 c1 c2 c3 := by
    calc
      u128RawValue a0 a1 a2 a3 =
          c0 + c1 * u32Base + c2 * u32Base ^ 2 + c3 * u32Base ^ 3 + carry * u32Base ^ 4 := hpacked
      _ = c0 + c1 * u32Base + c2 * u32Base ^ 2 + c3 * u32Base ^ 3 := by simp [hcarry]
      _ = u128RawValue c0 c1 c2 c3 := by
          dsimp [u32Base]
          unfold u128RawValue
          ring
  exact u128RawValue_injective_of_u32 a0 a1 a2 a3 c0 c1 c2 c3
    ha0 ha1 ha2 ha3 hc0 hc1 hc2 hc3 hdigits

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private theorem divmod_high_terms_zero
    (q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 a0 a1 a2 a3 : Nat)
    (hq0 : q0 < 2 ^ 32) (hq1 : q1 < 2 ^ 32) (hq2 : q2 < 2 ^ 32) (hq3 : q3 < 2 ^ 32)
    (hb0 : b0 < 2 ^ 32) (hb1 : b1 < 2 ^ 32) (hb2 : b2 < 2 ^ 32) (hb3 : b3 < 2 ^ 32)
    (_hr0 : r0 < 2 ^ 32) (_hr1 : r1 < 2 ^ 32) (_hr2 : r2 < 2 ^ 32) (_hr3 : r3 < 2 ^ 32)
    (ha0 : a0 < 2 ^ 32) (ha1 : a1 < 2 ^ 32) (ha2 : a2 < 2 ^ 32) (ha3 : a3 < 2 ^ 32)
    (hdiv :
      u128RawValue q0 q1 q2 q3 * u128RawValue b0 b1 b2 b3 + u128RawValue r0 r1 r2 r3 =
        u128RawValue a0 a1 a2 a3) :
    q1 * b3 = 0 ∧
    q2 * b2 = 0 ∧
    q3 * b1 = 0 ∧
    q2 * b3 = 0 ∧
    q3 * b2 = 0 ∧
    q3 * b3 = 0 := by
  have htotal_lt :
      u128RawValue q0 q1 q2 q3 * u128RawValue b0 b1 b2 b3 + u128RawValue r0 r1 r2 r3 < 2 ^ 128 := by
    rw [hdiv]
    simpa using u128RawValue_lt_2_128 a0 a1 a2 a3 ha0 ha1 ha2 ha3
  have hmul_lt :
      u128RawValue q0 q1 q2 q3 * u128RawValue b0 b1 b2 b3 < 2 ^ 128 := by
    omega
  obtain ⟨hq1b3_zero, hq2b2_zero, hq3b1_zero, hq2b3_zero, hq3b2_zero, hq3b3_zero⟩ :=
    u128HighTermsZeroOfMulLt q0 q1 q2 q3 b0 b1 b2 b3 hq0 hq1 hq2 hq3 hb0 hb1 hb2 hb3 (by
      simpa [u128RawValue] using hmul_lt)
  exact ⟨hq1b3_zero, hq2b2_zero, hq3b1_zero, hq2b3_zero, hq3b2_zero, hq3b3_zero⟩

private theorem divmod_stage0Nat
    (q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 a0 a1 a2 a3 : Nat)
    (hdiv :
      u128RawValue q0 q1 q2 q3 * u128RawValue b0 b1 b2 b3 + u128RawValue r0 r1 r2 r3 =
        u128RawValue a0 a1 a2 a3) :
    u128RawValue a0 a1 a2 a3 =
      u128DivmodCol0 q0 b0 r0
        + divmodX1 q0 q1 b0 b1 r1 * u32Base
        + divmodX2 q0 q1 q2 b0 b1 b2 r2 * u32Base ^ 2
        + divmodX3 q0 q1 q2 q3 b0 b1 b2 b3 r3 * u32Base ^ 3
        + divmodX4 q1 q2 q3 b1 b2 b3 * u32Base ^ 4
        + divmodX5 q2 q3 b2 b3 * u32Base ^ 5
        + divmodX6 q3 b3 * u32Base ^ 6 := by
  calc
    u128RawValue a0 a1 a2 a3 =
        u128RawValue q0 q1 q2 q3 * u128RawValue b0 b1 b2 b3 + u128RawValue r0 r1 r2 r3 := by
          rw [← hdiv]
    _ = _ := by
          simpa [u32Base, divmodX1, divmodX2, divmodX3, divmodX4, divmodX5, divmodX6] using
            divmodStage0_repr q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3

private theorem divmod_stage1Nat
    (q0 q1 b0 b1 r0 r1 : Nat) :
    u128DivmodCol0 q0 b0 r0 + divmodX1 q0 q1 b0 b1 r1 * u32Base =
      divmodCol0Lo q0 b0 r0 + u128DivmodCol1 q0 q1 b0 b1 r0 r1 * u32Base := by
  simpa [u32Base, divmodCol0Lo, divmodX1] using divmodStage1_repr q0 q1 b0 b1 r0 r1

private theorem divmod_stage2Nat
    (q0 q1 q2 b0 b1 b2 r0 r1 r2 : Nat) :
    u128DivmodCol1 q0 q1 b0 b1 r0 r1 * u32Base + divmodX2 q0 q1 q2 b0 b1 b2 r2 * u32Base ^ 2 =
      divmodCol1Lo q0 q1 b0 b1 r0 r1 * u32Base
        + u128DivmodCol2 q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2 := by
  simpa [u32Base, divmodCol1Lo, divmodX2] using divmodStage2_repr q0 q1 q2 b0 b1 b2 r0 r1 r2

private theorem divmod_stage3Nat
    (q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 : Nat) :
    u128DivmodCol2 q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
      + divmodX3 q0 q1 q2 q3 b0 b1 b2 b3 r3 * u32Base ^ 3 =
      divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
        + u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3 := by
  simpa [u32Base, divmodCol2Lo, divmodX3] using
    divmodStage3_repr q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 65536 in
private theorem divmod_stage4Nat
    (q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 : Nat) :
    u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
      + divmodX4 q1 q2 q3 b1 b2 b3 * u32Base ^ 4
      + divmodX5 q2 q3 b2 b3 * u32Base ^ 5
      + divmodX6 q3 b3 * u32Base ^ 6 =
      divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
        + (divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 + divmodX4 q1 q2 q3 b1 b2 b3) * u32Base ^ 4
        + divmodX5 q2 q3 b2 b3 * u32Base ^ 5
        + divmodX6 q3 b3 * u32Base ^ 6 := by
  have h := divmodStage4_repr q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3
  dsimp [u32Base, divmodCol3Lo, divmodCarry, divmodX4, divmodX5, divmodX6] at h ⊢
  omega

private theorem divmod_repr1Nat
    (q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 a0 a1 a2 a3 : Nat)
    (hdiv :
      u128RawValue q0 q1 q2 q3 * u128RawValue b0 b1 b2 b3 + u128RawValue r0 r1 r2 r3 =
        u128RawValue a0 a1 a2 a3) :
    u128RawValue a0 a1 a2 a3 =
      divmodCol0Lo q0 b0 r0
        + u128DivmodCol1 q0 q1 b0 b1 r0 r1 * u32Base
        + divmodX2 q0 q1 q2 b0 b1 b2 r2 * u32Base ^ 2
        + divmodX3 q0 q1 q2 q3 b0 b1 b2 b3 r3 * u32Base ^ 3
        + divmodX4 q1 q2 q3 b1 b2 b3 * u32Base ^ 4
        + divmodX5 q2 q3 b2 b3 * u32Base ^ 5
        + divmodX6 q3 b3 * u32Base ^ 6 := by
  have h0 := divmod_stage0Nat q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 a0 a1 a2 a3 hdiv
  have h1 := divmod_stage1Nat q0 q1 b0 b1 r0 r1
  omega

private theorem divmod_repr2Nat
    (q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 a0 a1 a2 a3 : Nat)
    (hdiv :
      u128RawValue q0 q1 q2 q3 * u128RawValue b0 b1 b2 b3 + u128RawValue r0 r1 r2 r3 =
        u128RawValue a0 a1 a2 a3) :
    u128RawValue a0 a1 a2 a3 =
      divmodCol0Lo q0 b0 r0
        + divmodCol1Lo q0 q1 b0 b1 r0 r1 * u32Base
        + u128DivmodCol2 q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
        + divmodX3 q0 q1 q2 q3 b0 b1 b2 b3 r3 * u32Base ^ 3
        + divmodX4 q1 q2 q3 b1 b2 b3 * u32Base ^ 4
        + divmodX5 q2 q3 b2 b3 * u32Base ^ 5
        + divmodX6 q3 b3 * u32Base ^ 6 := by
  have h1 := divmod_repr1Nat q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 a0 a1 a2 a3 hdiv
  have h2 := divmod_stage2Nat q0 q1 q2 b0 b1 b2 r0 r1 r2
  omega

private theorem divmod_repr3Nat
    (q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 a0 a1 a2 a3 : Nat)
    (hdiv :
      u128RawValue q0 q1 q2 q3 * u128RawValue b0 b1 b2 b3 + u128RawValue r0 r1 r2 r3 =
        u128RawValue a0 a1 a2 a3) :
    u128RawValue a0 a1 a2 a3 =
      divmodCol0Lo q0 b0 r0
        + divmodCol1Lo q0 q1 b0 b1 r0 r1 * u32Base
        + divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
        + u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
        + divmodX4 q1 q2 q3 b1 b2 b3 * u32Base ^ 4
        + divmodX5 q2 q3 b2 b3 * u32Base ^ 5
        + divmodX6 q3 b3 * u32Base ^ 6 := by
  have h2 := divmod_repr2Nat q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 a0 a1 a2 a3 hdiv
  have h3 := divmod_stage3Nat q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3
  omega

private theorem divmod_repr4Nat
    (q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 a0 a1 a2 a3 : Nat)
    (hdiv :
      u128RawValue q0 q1 q2 q3 * u128RawValue b0 b1 b2 b3 + u128RawValue r0 r1 r2 r3 =
        u128RawValue a0 a1 a2 a3) :
    u128RawValue a0 a1 a2 a3 =
      divmodCol0Lo q0 b0 r0
        + divmodCol1Lo q0 q1 b0 b1 r0 r1 * u32Base
        + divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
        + divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
        + (divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 + divmodX4 q1 q2 q3 b1 b2 b3) * u32Base ^ 4
        + divmodX5 q2 q3 b2 b3 * u32Base ^ 5
        + divmodX6 q3 b3 * u32Base ^ 6 := by
  have h3 := divmod_repr3Nat q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 a0 a1 a2 a3 hdiv
  have h4 := divmod_stage4Nat q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3
  omega

private theorem divmod_packedBaseNat
    (q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 a0 a1 a2 a3 : Nat)
    (hq1b3_zero : q1 * b3 = 0)
    (hq2b2_zero : q2 * b2 = 0)
    (hq3b1_zero : q3 * b1 = 0)
    (hq2b3_zero : q2 * b3 = 0)
    (hq3b2_zero : q3 * b2 = 0)
    (hq3b3_zero : q3 * b3 = 0)
    (hdiv :
      u128RawValue q0 q1 q2 q3 * u128RawValue b0 b1 b2 b3 + u128RawValue r0 r1 r2 r3 =
        u128RawValue a0 a1 a2 a3) :
    u128RawValue a0 a1 a2 a3 =
      divmodCol0Lo q0 b0 r0
        + divmodCol1Lo q0 q1 b0 b1 r0 r1 * u32Base
        + divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
        + divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
        + divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 4 := by
  calc
    u128RawValue a0 a1 a2 a3 =
        divmodCol0Lo q0 b0 r0
          + divmodCol1Lo q0 q1 b0 b1 r0 r1 * u32Base
          + divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
          + divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
          + (divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 + divmodX4 q1 q2 q3 b1 b2 b3) * u32Base ^ 4
          + divmodX5 q2 q3 b2 b3 * u32Base ^ 5
          + divmodX6 q3 b3 * u32Base ^ 6 := divmod_repr4Nat q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 a0 a1 a2 a3 hdiv
    _ =
        divmodCol0Lo q0 b0 r0
          + divmodCol1Lo q0 q1 b0 b1 r0 r1 * u32Base
          + divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
          + divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
          + divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 4 := by
            simp [divmodX4, divmodX5, divmodX6, hq1b3_zero, hq2b2_zero, hq3b1_zero, hq2b3_zero,
              hq3b2_zero, hq3b3_zero]

private theorem divmod_digit_recovery
    (a0 a1 a2 a3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 : Nat)
    (ha0 : a0 < 2 ^ 32) (ha1 : a1 < 2 ^ 32) (ha2 : a2 < 2 ^ 32) (ha3 : a3 < 2 ^ 32)
    (hpacked :
      u128RawValue a0 a1 a2 a3 =
        divmodCol0Lo q0 b0 r0
          + divmodCol1Lo q0 q1 b0 b1 r0 r1 * u32Base
          + divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
          + divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
          + divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 4) :
    a0 = divmodCol0Lo q0 b0 r0 ∧
    a1 = divmodCol1Lo q0 q1 b0 b1 r0 r1 ∧
    a2 = divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2 ∧
    a3 = divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 ∧
    divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 = 0 := by
  have hcarry_zero :
      divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 = 0 := by
    exact carry_zero_of_packed_u128
      a0 a1 a2 a3
      (divmodCol0Lo q0 b0 r0)
      (divmodCol1Lo q0 q1 b0 b1 r0 r1)
      (divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2)
      (divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3)
      (divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3)
      ha0 ha1 ha2 ha3 hpacked
  obtain ⟨ha0_eq, ha1_eq, ha2_eq, ha3_eq⟩ :=
    digits_of_packed_u128
      a0 a1 a2 a3
      (divmodCol0Lo q0 b0 r0)
      (divmodCol1Lo q0 q1 b0 b1 r0 r1)
      (divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2)
      (divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3)
      (divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3)
      ha0 ha1 ha2 ha3
      (by
        dsimp [divmodCol0Lo]
        exact Nat.mod_lt _ (by positivity))
      (by
        dsimp [divmodCol1Lo]
        exact Nat.mod_lt _ (by positivity))
      (by
        dsimp [divmodCol2Lo]
        exact Nat.mod_lt _ (by positivity))
      (by
        dsimp [divmodCol3Lo]
        exact Nat.mod_lt _ (by positivity))
      hpacked hcarry_zero
  exact ⟨ha0_eq, ha1_eq, ha2_eq, ha3_eq, hcarry_zero⟩

private theorem divmodCol1CarryCarry_lt
    (q0 q1 b0 b1 r0 r1 : Felt)
    (hq0 : q0.isU32 = true) (hq1 : q1.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true) :
    u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / 2 ^ 32 / 2 ^ 32 < 2 ^ 32 := by
  let base := 2 ^ 32
  change u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / base / base < base
  let carry0 := u128DivmodCol0 q0.val b0.val r0.val / base
  let madd0Lo := (b0.val * q1.val + carry0) % base
  let madd0Hi := (b0.val * q1.val + carry0) / base
  let madd1Lo := (b1.val * q0.val + madd0Lo) % base
  let madd1Hi := (b1.val * q0.val + madd0Lo) / base
  let addLo := (madd1Lo + r1.val) % base
  let addHi := (madd1Lo + r1.val) / base
  let carry := madd0Hi + madd1Hi + addHi
  have hcarry0_lt : carry0 < base := by
    dsimp [carry0]
    simpa [base] using divmodCol0Carry_lt q0 b0 r0 hq0 hb0 hr0
  have hc0_u32 : (Felt.ofNat carry0).isU32 = true := by
    exact felt_ofNat_isU32_of_lt _ hcarry0_lt
  have hc0_val : (Felt.ofNat carry0).val = carry0 := by
    exact felt_ofNat_val_lt _ (u32_val_lt_prime _ hcarry0_lt)
  have hmadd0Lo_val : (Felt.ofNat madd0Lo).val = madd0Lo := by
    exact felt_ofNat_val_lt _ (u32_mod_lt_prime _)
  have hmadd1Lo_val : (Felt.ofNat madd1Lo).val = madd1Lo := by
    exact felt_ofNat_val_lt _ (u32_mod_lt_prime _)
  have hmadd0Hi_lt : madd0Hi < base := by
    dsimp [madd0Hi]
    have h := u32_madd_div_lt_2_32 b0 q1 (Felt.ofNat carry0) hb0 hq1 hc0_u32
    rw [hc0_val] at h
    simpa [base, carry0, Nat.mul_comm] using h
  have hmadd1Hi_lt : madd1Hi < base := by
    dsimp [madd1Hi]
    have h := u32_madd_div_lt_2_32 b1 q0 (Felt.ofNat madd0Lo) hb1 hq0 (u32_mod_isU32 _)
    rw [hmadd0Lo_val] at h
    simpa [base, madd0Lo, Nat.mul_comm] using h
  have haddHi_le_one : addHi ≤ 1 := by
    dsimp [addHi]
    have h := u32_add_div_le_one (Felt.ofNat madd1Lo) r1 (u32_mod_isU32 _) hr1
    rw [hmadd1Lo_val] at h
    simpa [base, madd1Lo] using h
  have hrepr : u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val = addLo + carry * base := by
    have h0 : madd0Lo + madd0Hi * base = q1.val * b0.val + carry0 := by
      simpa [madd0Lo, madd0Hi, base, Nat.mul_comm] using
        (Nat.mod_add_div (b0.val * q1.val + carry0) base)
    have h1 : madd1Lo + madd1Hi * base = q0.val * b1.val + madd0Lo := by
      simpa [madd1Lo, madd1Hi, base, Nat.mul_comm] using
        (Nat.mod_add_div (b1.val * q0.val + madd0Lo) base)
    have h2 : addLo + addHi * base = madd1Lo + r1.val := by
      simpa [addLo, addHi, base, Nat.mul_comm] using
        (Nat.mod_add_div (madd1Lo + r1.val) base)
    calc
      u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val
          = q0.val * b1.val + r1.val + (q1.val * b0.val + carry0) := by
              unfold u128DivmodCol1
              simp [carry0, base, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      _ = q0.val * b1.val + r1.val + (madd0Lo + madd0Hi * base) := by rw [← h0]
      _ = q0.val * b1.val + madd0Lo + r1.val + madd0Hi * base := by ac_rfl
      _ = (madd1Lo + madd1Hi * base) + r1.val + madd0Hi * base := by rw [h1]
      _ = madd1Lo + r1.val + madd1Hi * base + madd0Hi * base := by ac_rfl
      _ = addLo + addHi * base + madd1Hi * base + madd0Hi * base := by rw [h2]
      _ = addLo + (madd0Hi + madd1Hi + addHi) * base := by
            simp [base, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have haddLo_lt : addLo < base := by
    dsimp [addLo, base]
    exact Nat.mod_lt _ (by positivity)
  have hcarry_nat : u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / base = carry := by
    rw [hrepr, Nat.add_mul_div_right _ _ (show 0 < base by positivity), Nat.div_eq_of_lt haddLo_lt]
    simp [carry]
  have hcarry_lt : carry < 2 * base + 1 := by
    dsimp [carry]
    omega
  rw [hcarry_nat]
  calc
    carry / base ≤ (2 * base + 1) / base := by
      exact Nat.div_le_div_right (Nat.le_of_lt hcarry_lt)
    _ < base := by
          dsimp [base]
          native_decide

private theorem divmodCol2CarryCarry_lt
    (q0 q1 q2 b0 b1 b2 r0 r1 r2 : Felt)
    (hq0 : q0.isU32 = true) (hq1 : q1.isU32 = true) (hq2 : q2.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) (hb2 : b2.isU32 = true)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true) (hr2 : r2.isU32 = true) :
    u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / 2 ^ 32 / 2 ^ 32 < 2 ^ 32 := by
  let base := 2 ^ 32
  change
    u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / base / base <
      base
  let carry1 := u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / base
  let c1Lo := carry1 % base
  let c1Hi := carry1 / base
  let lo0 := (b0.val * q2.val + c1Lo) % base
  let hi0 := (b0.val * q2.val + c1Lo) / base
  let lo1 := (b1.val * q1.val + lo0) % base
  let hi1 := (b1.val * q1.val + lo0) / base
  let sumHi := c1Hi + hi0 + hi1
  let madd2Lo := (b2.val * q0.val + lo1) % base
  let madd2Hi := (b2.val * q0.val + lo1) / base
  let addLo := (madd2Lo + r2.val) % base
  let addHi := (madd2Lo + r2.val) / base
  let carry := sumHi + madd2Hi + addHi
  have hc1Hi_lt : c1Hi < base := by
    dsimp [c1Hi, carry1]
    simpa [base] using divmodCol1CarryCarry_lt q0 q1 b0 b1 r0 r1 hq0 hq1 hb0 hb1 hr0 hr1
  have hc1Lo_val : (Felt.ofNat c1Lo).val = c1Lo := by
    exact felt_ofNat_val_lt _ (u32_mod_lt_prime _)
  have hlo0_val : (Felt.ofNat lo0).val = lo0 := by
    exact felt_ofNat_val_lt _ (u32_mod_lt_prime _)
  have hlo1_val : (Felt.ofNat lo1).val = lo1 := by
    exact felt_ofNat_val_lt _ (u32_mod_lt_prime _)
  have hhi0_lt : hi0 < base := by
    dsimp [hi0]
    have h := u32_madd_div_lt_2_32 b0 q2 (Felt.ofNat c1Lo) hb0 hq2 (u32_mod_isU32 _)
    rw [hc1Lo_val] at h
    simpa [base, Nat.mul_comm] using h
  have hhi1_lt : hi1 < base := by
    dsimp [hi1]
    have h := u32_madd_div_lt_2_32 b1 q1 (Felt.ofNat lo0) hb1 hq1 (u32_mod_isU32 _)
    rw [hlo0_val] at h
    simpa [base, lo0, Nat.mul_comm] using h
  have hmadd2Hi_lt : madd2Hi < base := by
    dsimp [madd2Hi]
    have h := u32_madd_div_lt_2_32 b2 q0 (Felt.ofNat lo1) hb2 hq0 (u32_mod_isU32 _)
    rw [hlo1_val] at h
    simpa [base, lo1, Nat.mul_comm] using h
  have haddHi_le_one : addHi ≤ 1 := by
    dsimp [addHi]
    have h := u32_add_div_le_one (Felt.ofNat madd2Lo) r2 (u32_mod_isU32 _) hr2
    rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)] at h
    simpa [base, madd2Lo] using h
  have hcarry1_repr : c1Lo + c1Hi * base = carry1 := by
    dsimp [c1Lo, c1Hi, carry1]
    simpa [base, Nat.mul_comm] using
      (Nat.mod_add_div (u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / base) base)
  have hlo0_repr : lo0 + hi0 * base = q2.val * b0.val + c1Lo := by
    simpa [lo0, hi0, base, Nat.mul_comm] using
      (Nat.mod_add_div (b0.val * q2.val + c1Lo) base)
  have hlo1_repr : lo1 + hi1 * base = q1.val * b1.val + lo0 := by
    simpa [lo1, hi1, base, Nat.mul_comm] using
      (Nat.mod_add_div (b1.val * q1.val + lo0) base)
  have hpre_repr :
      q2.val * b0.val + q1.val * b1.val + carry1 = lo1 + sumHi * base := by
    calc
      q2.val * b0.val + q1.val * b1.val + carry1
          = q1.val * b1.val + (q2.val * b0.val + c1Lo) + c1Hi * base := by
              rw [← hcarry1_repr]
              ring
      _ = q1.val * b1.val + (lo0 + hi0 * base) + c1Hi * base := by rw [hlo0_repr]
      _ = (lo1 + hi1 * base) + (hi0 + c1Hi) * base := by
            rw [hlo1_repr]
            ring
      _ = lo1 + sumHi * base := by
            dsimp [sumHi]
            ring
  have hmadd2_repr : madd2Lo + madd2Hi * base = q0.val * b2.val + lo1 := by
    simpa [madd2Lo, madd2Hi, base, Nat.mul_comm] using
      (Nat.mod_add_div (b2.val * q0.val + lo1) base)
  have hadd_repr : addLo + addHi * base = madd2Lo + r2.val := by
    simpa [addLo, addHi, base, Nat.mul_comm] using
      (Nat.mod_add_div (madd2Lo + r2.val) base)
  have hrepr :
      u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val =
        addLo + carry * base := by
    calc
      u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val
          = q0.val * b2.val + r2.val + (q2.val * b0.val + q1.val * b1.val + carry1) := by
              unfold u128DivmodCol2
              dsimp [carry1, base]
              ring
      _ = q0.val * b2.val + r2.val + (lo1 + sumHi * base) := by rw [hpre_repr]
      _ = q0.val * b2.val + lo1 + r2.val + sumHi * base := by ring
      _ = (madd2Lo + madd2Hi * base) + r2.val + sumHi * base := by rw [hmadd2_repr]
      _ = madd2Lo + r2.val + (sumHi + madd2Hi) * base := by ring
      _ = addLo + addHi * base + (sumHi + madd2Hi) * base := by rw [hadd_repr]
      _ = addLo + (sumHi + madd2Hi + addHi) * base := by ring
  have haddLo_lt : addLo < base := by
    dsimp [addLo, base]
    exact Nat.mod_lt _ (by positivity)
  have hcarry_nat :
      u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / base = carry := by
    rw [hrepr, Nat.add_mul_div_right _ _ (show 0 < base by positivity), Nat.div_eq_of_lt haddLo_lt]
    simp [carry]
  have hcarry_lt : carry < 4 * base + 1 := by
    dsimp [carry, sumHi]
    omega
  rw [hcarry_nat]
  calc
    carry / base ≤ (4 * base + 1) / base := by
      exact Nat.div_le_div_right (Nat.le_of_lt hcarry_lt)
    _ < base := by
          dsimp [base]
          native_decide

private theorem divmod_forward_arith
    (q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 a0 a1 a2 a3 : Nat)
    (hq1b3_zero : q1 * b3 = 0)
    (hq2b2_zero : q2 * b2 = 0)
    (hq3b1_zero : q3 * b1 = 0)
    (hq2b3_zero : q2 * b3 = 0)
    (hq3b2_zero : q3 * b2 = 0)
    (hq3b3_zero : q3 * b3 = 0)
    (hcarry_zero : divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 = 0)
    (ha0_eq : a0 = divmodCol0Lo q0 b0 r0)
    (ha1_eq : a1 = divmodCol1Lo q0 q1 b0 b1 r0 r1)
    (ha2_eq : a2 = divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2)
    (ha3_eq : a3 = divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3) :
    u128RawValue q0 q1 q2 q3 * u128RawValue b0 b1 b2 b3 + u128RawValue r0 r1 r2 r3 =
      u128RawValue a0 a1 a2 a3 := by
  have hpacked :
      divmodCol0Lo q0 b0 r0
        + divmodCol1Lo q0 q1 b0 b1 r0 r1 * u32Base
        + divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
        + divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
        + divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 4 =
      u128RawValue q0 q1 q2 q3 * u128RawValue b0 b1 b2 b3 + u128RawValue r0 r1 r2 r3 := by
    have h0 :
        u128DivmodCol0 q0 b0 r0
          + divmodX1 q0 q1 b0 b1 r1 * u32Base
          + divmodX2 q0 q1 q2 b0 b1 b2 r2 * u32Base ^ 2
          + divmodX3 q0 q1 q2 q3 b0 b1 b2 b3 r3 * u32Base ^ 3
          + divmodX4 q1 q2 q3 b1 b2 b3 * u32Base ^ 4
          + divmodX5 q2 q3 b2 b3 * u32Base ^ 5
          + divmodX6 q3 b3 * u32Base ^ 6 =
        u128RawValue q0 q1 q2 q3 * u128RawValue b0 b1 b2 b3 + u128RawValue r0 r1 r2 r3 := by
      simpa [u32Base, divmodX1, divmodX2, divmodX3, divmodX4, divmodX5, divmodX6] using
        (divmodStage0_repr q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3).symm
    have h1 := divmod_stage1Nat q0 q1 b0 b1 r0 r1
    have h2 := divmod_stage2Nat q0 q1 q2 b0 b1 b2 r0 r1 r2
    have h3 := divmod_stage3Nat q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3
    have h4 := divmod_stage4Nat q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3
    have hx4_zero : divmodX4 q1 q2 q3 b1 b2 b3 = 0 := by
      simp [divmodX4, hq1b3_zero, hq2b2_zero, hq3b1_zero]
    have hx5_zero : divmodX5 q2 q3 b2 b3 = 0 := by
      simp [divmodX5, hq2b3_zero, hq3b2_zero]
    have hx6_zero : divmodX6 q3 b3 = 0 := by
      simp [divmodX6, hq3b3_zero]
    have h4' :
        u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
          + divmodX4 q1 q2 q3 b1 b2 b3 * u32Base ^ 4
          + divmodX5 q2 q3 b2 b3 * u32Base ^ 5
          + divmodX6 q3 b3 * u32Base ^ 6 =
        divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
          + divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 4 := by
      simpa [hx4_zero, hx5_zero, hx6_zero] using h4
    have h234 :
        u128DivmodCol2 q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
          + divmodX3 q0 q1 q2 q3 b0 b1 b2 b3 r3 * u32Base ^ 3
          + divmodX4 q1 q2 q3 b1 b2 b3 * u32Base ^ 4
          + divmodX5 q2 q3 b2 b3 * u32Base ^ 5
          + divmodX6 q3 b3 * u32Base ^ 6 =
        divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
          + divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
          + divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 4 := by
      calc
        u128DivmodCol2 q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
            + divmodX3 q0 q1 q2 q3 b0 b1 b2 b3 r3 * u32Base ^ 3
            + divmodX4 q1 q2 q3 b1 b2 b3 * u32Base ^ 4
            + divmodX5 q2 q3 b2 b3 * u32Base ^ 5
            + divmodX6 q3 b3 * u32Base ^ 6
            =
          divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
            + (u128DivmodCol3 q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
                + divmodX4 q1 q2 q3 b1 b2 b3 * u32Base ^ 4
                + divmodX5 q2 q3 b2 b3 * u32Base ^ 5
                + divmodX6 q3 b3 * u32Base ^ 6) := by
                rw [h3]
                ring
        _ =
          divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
            + (divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
                + divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 4) := by
                rw [h4']
        _ =
          divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
            + divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
            + divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 4 := by
                ring
    have h1234 :
        u128DivmodCol1 q0 q1 b0 b1 r0 r1 * u32Base
          + divmodX2 q0 q1 q2 b0 b1 b2 r2 * u32Base ^ 2
          + divmodX3 q0 q1 q2 q3 b0 b1 b2 b3 r3 * u32Base ^ 3
          + divmodX4 q1 q2 q3 b1 b2 b3 * u32Base ^ 4
          + divmodX5 q2 q3 b2 b3 * u32Base ^ 5
          + divmodX6 q3 b3 * u32Base ^ 6 =
        divmodCol1Lo q0 q1 b0 b1 r0 r1 * u32Base
          + divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
          + divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
          + divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 4 := by
      calc
        u128DivmodCol1 q0 q1 b0 b1 r0 r1 * u32Base
            + divmodX2 q0 q1 q2 b0 b1 b2 r2 * u32Base ^ 2
            + divmodX3 q0 q1 q2 q3 b0 b1 b2 b3 r3 * u32Base ^ 3
            + divmodX4 q1 q2 q3 b1 b2 b3 * u32Base ^ 4
            + divmodX5 q2 q3 b2 b3 * u32Base ^ 5
            + divmodX6 q3 b3 * u32Base ^ 6
            =
          divmodCol1Lo q0 q1 b0 b1 r0 r1 * u32Base
            + (u128DivmodCol2 q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
                + divmodX3 q0 q1 q2 q3 b0 b1 b2 b3 r3 * u32Base ^ 3
                + divmodX4 q1 q2 q3 b1 b2 b3 * u32Base ^ 4
                + divmodX5 q2 q3 b2 b3 * u32Base ^ 5
                + divmodX6 q3 b3 * u32Base ^ 6) := by
                rw [h2]
                ring
        _ =
          divmodCol1Lo q0 q1 b0 b1 r0 r1 * u32Base
            + (divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
                + divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
                + divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 4) := by
                rw [h234]
        _ =
          divmodCol1Lo q0 q1 b0 b1 r0 r1 * u32Base
            + divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
            + divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
            + divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 4 := by
                ring
    have hall :
        u128DivmodCol0 q0 b0 r0
          + divmodX1 q0 q1 b0 b1 r1 * u32Base
          + divmodX2 q0 q1 q2 b0 b1 b2 r2 * u32Base ^ 2
          + divmodX3 q0 q1 q2 q3 b0 b1 b2 b3 r3 * u32Base ^ 3
          + divmodX4 q1 q2 q3 b1 b2 b3 * u32Base ^ 4
          + divmodX5 q2 q3 b2 b3 * u32Base ^ 5
          + divmodX6 q3 b3 * u32Base ^ 6 =
        divmodCol0Lo q0 b0 r0
          + divmodCol1Lo q0 q1 b0 b1 r0 r1 * u32Base
          + divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
          + divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
          + divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 4 := by
      calc
        u128DivmodCol0 q0 b0 r0
            + divmodX1 q0 q1 b0 b1 r1 * u32Base
            + divmodX2 q0 q1 q2 b0 b1 b2 r2 * u32Base ^ 2
            + divmodX3 q0 q1 q2 q3 b0 b1 b2 b3 r3 * u32Base ^ 3
            + divmodX4 q1 q2 q3 b1 b2 b3 * u32Base ^ 4
            + divmodX5 q2 q3 b2 b3 * u32Base ^ 5
            + divmodX6 q3 b3 * u32Base ^ 6
            =
          divmodCol0Lo q0 b0 r0
            + (u128DivmodCol1 q0 q1 b0 b1 r0 r1 * u32Base
                + divmodX2 q0 q1 q2 b0 b1 b2 r2 * u32Base ^ 2
                + divmodX3 q0 q1 q2 q3 b0 b1 b2 b3 r3 * u32Base ^ 3
                + divmodX4 q1 q2 q3 b1 b2 b3 * u32Base ^ 4
                + divmodX5 q2 q3 b2 b3 * u32Base ^ 5
                + divmodX6 q3 b3 * u32Base ^ 6) := by
                rw [h1]
                ring
        _ =
          divmodCol0Lo q0 b0 r0
            + (divmodCol1Lo q0 q1 b0 b1 r0 r1 * u32Base
                + divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
                + divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
                + divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 4) := by
                rw [h1234]
        _ =
          divmodCol0Lo q0 b0 r0
            + divmodCol1Lo q0 q1 b0 b1 r0 r1 * u32Base
            + divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
            + divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
            + divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 4 := by
                ring
    rw [← hall]
    exact h0
  calc
    u128RawValue q0 q1 q2 q3 * u128RawValue b0 b1 b2 b3 + u128RawValue r0 r1 r2 r3
        =
      divmodCol0Lo q0 b0 r0
        + divmodCol1Lo q0 q1 b0 b1 r0 r1 * u32Base
        + divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
        + divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3
        + divmodCarry q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 4 := by
          exact hpacked.symm
    _ =
      divmodCol0Lo q0 b0 r0
        + divmodCol1Lo q0 q1 b0 b1 r0 r1 * u32Base
        + divmodCol2Lo q0 q1 q2 b0 b1 b2 r0 r1 r2 * u32Base ^ 2
        + divmodCol3Lo q0 q1 q2 q3 b0 b1 b2 b3 r0 r1 r2 r3 * u32Base ^ 3 := by
          simp [hcarry_zero]
    _ = u128RawValue a0 a1 a2 a3 := by
          rw [ha0_eq, ha1_eq, ha2_eq, ha3_eq]
          unfold u128RawValue
          dsimp [u32Base]
          ring

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 65536 in
theorem u128_divmod_raw
    (a0 a1 a2 a3 b0 b1 b2 b3 q0 q1 q2 q3 r0 r1 r2 r3 : Felt)
    (rest adv_rest : List Felt) (s : MidenState)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
    (hadv : s.advice = r0 :: r1 :: r2 :: r3 :: q0 :: q1 :: q2 :: q3 :: adv_rest)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true) (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true)
    (hq0 : q0.isU32 = true) (hq1 : q1.isU32 = true) (hq2 : q2.isU32 = true) (hq3 : q3.isU32 = true)
    (hr0 : r0.isU32 = true) (hr1 : r1.isU32 = true) (hr2 : r2.isU32 = true) (hr3 : r3.isU32 = true)
    (hdiv :
      u128RawValue q0.val q1.val q2.val q3.val * u128RawValue b0.val b1.val b2.val b3.val
        + u128RawValue r0.val r1.val r2.val r3.val =
        u128RawValue a0.val a1.val a2.val a3.val)
    (hlt : u128RawValue r0.val r1.val r2.val r3.val < u128RawValue b0.val b1.val b2.val b3.val) :
    exec 163 s Miden.Core.U128.divmod =
    some { stack := r0 :: r1 :: r2 :: r3 :: q0 :: q1 :: q2 :: q3 :: rest,
           memory := s.memory,
           locals := s.locals,
           advice := adv_rest } := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only at hs ⊢
  subst hs
  subst hadv
  have ha0_lt : a0.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using ha0
  have ha1_lt : a1.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using ha1
  have ha2_lt : a2.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using ha2
  have ha3_lt : a3.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using ha3
  have hb0_lt : b0.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb0
  have hb1_lt : b1.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb1
  have hb2_lt : b2.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb2
  have hb3_lt : b3.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb3
  have hq0_lt : q0.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hq0
  have hq1_lt : q1.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hq1
  have hq2_lt : q2.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hq2
  have hq3_lt : q3.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hq3
  have hr0_lt : r0.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hr0
  have hr1_lt : r1.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hr1
  have hr2_lt : r2.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hr2
  have hr3_lt : r3.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hr3
  obtain ⟨hq1b3_zero, hq2b2_zero, hq3b1_zero, hq2b3_zero, hq3b2_zero, hq3b3_zero⟩ :=
    divmod_high_terms_zero q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val
      r0.val r1.val r2.val r3.val a0.val a1.val a2.val a3.val
      hq0_lt hq1_lt hq2_lt hq3_lt hb0_lt hb1_lt hb2_lt hb3_lt
      hr0_lt hr1_lt hr2_lt hr3_lt ha0_lt ha1_lt ha2_lt ha3_lt hdiv
  have hpackedBaseNat :
      u128RawValue a0.val a1.val a2.val a3.val =
        divmodCol0Lo q0.val b0.val r0.val
          + divmodCol1Lo q0.val q1.val b0.val b1.val r0.val r1.val * u32Base
          + divmodCol2Lo q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val * u32Base ^ 2
          + divmodCol3Lo q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val
              r0.val r1.val r2.val r3.val * u32Base ^ 3
          + divmodCarry q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val
              r0.val r1.val r2.val r3.val * u32Base ^ 4 :=
    divmod_packedBaseNat
      q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val
      r0.val r1.val r2.val r3.val a0.val a1.val a2.val a3.val
      hq1b3_zero hq2b2_zero hq3b1_zero hq2b3_zero hq3b2_zero hq3b3_zero hdiv
  obtain ⟨ha0_eq_nat, ha1_eq_nat, ha2_eq_nat, ha3_eq_nat, hcarry_zero⟩ :=
    divmod_digit_recovery
      a0.val a1.val a2.val a3.val
      q0.val q1.val q2.val q3.val
      b0.val b1.val b2.val b3.val
      r0.val r1.val r2.val r3.val
      ha0_lt ha1_lt ha2_lt ha3_lt hpackedBaseNat
  have htotal_lt :
      u128RawValue q0.val q1.val q2.val q3.val * u128RawValue b0.val b1.val b2.val b3.val
        + u128RawValue r0.val r1.val r2.val r3.val < 2 ^ 128 := by
    rw [hdiv]
    exact u128RawValue_lt_2_128 a0.val a1.val a2.val a3.val ha0_lt ha1_lt ha2_lt ha3_lt
  have hc1Hi_lt :
      u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / 2 ^ 32 / 2 ^ 32 < 2 ^ 32 := by
    have hcarry_in_lt := u128DivmodCol2CarryIn_div_lt_2_32
      q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val r0.val r1.val r2.val r3.val htotal_lt
    have hle :
        u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / 2 ^ 32 / 2 ^ 32 ≤
          u128DivmodCol2CarryIn q0.val q1.val q2.val b0.val b1.val r0.val r1.val / 2 ^ 32 := by
      apply Nat.div_le_div_right
      unfold u128DivmodCol2CarryIn
      omega
    exact lt_of_le_of_lt hle hcarry_in_lt
  have hc2Hi_zero_nat :
      u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / 2 ^ 32 / 2 ^ 32 = 0 := by
    apply Nat.eq_zero_of_le_zero
    calc
      u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / 2 ^ 32 / 2 ^ 32
        ≤ u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val r0.val r1.val r2.val r3.val / 2 ^ 32 := by
            apply Nat.div_le_div_right
            unfold u128DivmodCol3
            omega
      _ = 0 := by simpa [divmodCarry] using hcarry_zero
  have ha0_eq :
      a0 = Felt.ofNat (u128DivmodCol0 q0.val b0.val r0.val % 2 ^ 32) := by
    exact felt_eq_ofNat_of_val_eq a0 _ (by simpa [divmodCol0Lo] using ha0_eq_nat) (u32_mod_lt_prime _)
  have ha1_eq :
      a1 = Felt.ofNat (u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val % 2 ^ 32) := by
    exact felt_eq_ofNat_of_val_eq a1 _ (by simpa [divmodCol1Lo] using ha1_eq_nat) (u32_mod_lt_prime _)
  have ha2_eq :
      a2 = Felt.ofNat (u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val % 2 ^ 32) := by
    exact felt_eq_ofNat_of_val_eq a2 _ (by simpa [divmodCol2Lo] using ha2_eq_nat) (u32_mod_lt_prime _)
  have ha3_eq :
      a3 =
        Felt.ofNat
          (u128DivmodCol3 q0.val q1.val q2.val q3.val b0.val b1.val b2.val b3.val r0.val r1.val r2.val r3.val %
            2 ^ 32) := by
    exact felt_eq_ofNat_of_val_eq a3 _ (by simpa [divmodCol3Lo] using ha3_eq_nat) (u32_mod_lt_prime _)
  have h_lt_result : u128LtBool r0 r1 r2 r3 b0 b1 b2 b3 = true := by
    rw [divmodLtBool_eqRaw r0 r1 r2 r3 b0 b1 b2 b3 hr0 hr1 hr2 hr3 hb0 hb1 hb2 hb3]
    simpa using hlt
  rw [divmod_decomp, exec_append]
  rw [divmodSetup_run q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a0 a1 a2 a3 rest adv_rest mem locs
      hq0 hq1 hq2 hq3 hr0 hr1 hr2 hr3]
  miden_bind
  rw [exec_append]
  rw [divmodCol0_run q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a0 a1 a2 a3 rest adv_rest mem locs
      hq0 hq1 hq2 hq3 hr0 ha0_eq hb0]
  miden_bind
  rw [exec_append]
  rw [divmodCol1_run
      (Felt.ofNat (u128DivmodCol0 q0.val b0.val r0.val / 2 ^ 32))
      q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a1 a2 a3 rest adv_rest mem locs
      hq0 hq1 hr1 hb0 hb1
      (felt_ofNat_isU32_of_lt _ (divmodCol0Carry_lt q0 b0 r0 hq0 hb0 hr0))
      (felt_ofNat_val_lt _ (u32_val_lt_prime _ (divmodCol0Carry_lt q0 b0 r0 hq0 hb0 hr0)))
      ha1_eq]
  miden_bind
  rw [exec_append]
  rw [divmodCol2_run
      (Felt.ofNat (u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / 2 ^ 32 % 2 ^ 32))
      (Felt.ofNat (u128DivmodCol1 q0.val q1.val b0.val b1.val r0.val r1.val / 2 ^ 32 / 2 ^ 32))
      q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a2 a3 rest adv_rest mem locs
      hq0 hq1 hq2 hr2 hb0 hb1 hb2
      (u32_mod_isU32 _)
      (felt_ofNat_isU32_of_lt _ hc1Hi_lt)
      (felt_ofNat_val_lt _ (u32_mod_lt_prime _))
      (felt_ofNat_val_lt _ (u32_val_lt_prime _ hc1Hi_lt))
      ha2_eq]
  miden_bind
  rw [exec_append]
  rw [show Felt.ofNat
        (u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / 2 ^ 32 / 2 ^ 32) =
      (0 : Felt) by
        rw [hc2Hi_zero_nat]
        rfl]
  rw [divmodCol3_run
      (Felt.ofNat (u128DivmodCol2 q0.val q1.val q2.val b0.val b1.val b2.val r0.val r1.val r2.val / 2 ^ 32 % 2 ^ 32))
      0
      q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 a3 rest adv_rest mem locs
      hq0 hq1 hq2 hq3 hr3 hb0 hb1 hb2 hb3
      (u32_mod_isU32 _)
      (felt_ofNat_val_lt _ (u32_mod_lt_prime _))
      (by
        rw [hc2Hi_zero_nat]
        exact Felt.val_zero')
      ha3_eq
      (by simpa [divmodCarry] using hcarry_zero)]
  miden_bind
  rw [divmodTail_run q0 q1 q2 q3 r0 r1 r2 r3 b0 b1 b2 b3 rest adv_rest mem locs
      hq1 hq2 hq3 hr0 hr1 hr2 hr3 hb0 hb1 hb2 hb3
      hq3b1_zero hq2b2_zero hq1b3_zero hq3b2_zero hq2b3_zero hq3b3_zero h_lt_result]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 65536 in
theorem u128_divmod_conditions_of_exec
    (a b q r : U128) (rest adv_rest : List Felt) (s : MidenState)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                    a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest)
    (hadv : s.advice = r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
                      q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val :: adv_rest)
    {s' : MidenState}
    (hexec : exec 163 s Miden.Core.U128.divmod = some s') :
    q.toNat * b.toNat + r.toNat = a.toNat ∧ r.toNat < b.toNat := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [] at hs hadv
  subst hs
  subst hadv
  rw [divmod_decomp, exec_append] at hexec
  rw [divmodSetup_run
      q.a0.val q.a1.val q.a2.val q.a3.val
      r.a0.val r.a1.val r.a2.val r.a3.val
      b.a0.val b.a1.val b.a2.val b.a3.val
      a.a0.val a.a1.val a.a2.val a.a3.val
      rest adv_rest mem locs
      q.a0.isU32 q.a1.isU32 q.a2.isU32 q.a3.isU32
      r.a0.isU32 r.a1.isU32 r.a2.isU32 r.a3.isU32] at hexec
  simp at hexec
  rw [exec_append] at hexec
  have ha0_eq :
      a.a0.val = Felt.ofNat (u128DivmodCol0 q.a0.val.val b.a0.val.val r.a0.val.val % 2 ^ 32) := by
    by_contra h_not
    rw [divmodCol0_none
        q.a0.val q.a1.val q.a2.val q.a3.val
        r.a0.val r.a1.val r.a2.val r.a3.val
        b.a0.val b.a1.val b.a2.val b.a3.val
        a.a0.val a.a1.val a.a2.val a.a3.val
        rest adv_rest mem locs
        q.a0.isU32 q.a1.isU32 q.a2.isU32 q.a3.isU32
        r.a0.isU32 b.a0.isU32 h_not] at hexec
    simp at hexec
  rw [divmodCol0_run
      q.a0.val q.a1.val q.a2.val q.a3.val
      r.a0.val r.a1.val r.a2.val r.a3.val
      b.a0.val b.a1.val b.a2.val b.a3.val
      a.a0.val a.a1.val a.a2.val a.a3.val
      rest adv_rest mem locs
      q.a0.isU32 q.a1.isU32 q.a2.isU32 q.a3.isU32
      r.a0.isU32 ha0_eq b.a0.isU32] at hexec
  simp at hexec
  simp only [← two_pow_32] at hexec
  rw [exec_append] at hexec
  have hc0_lt :
      u128DivmodCol0 q.a0.val.val b.a0.val.val r.a0.val.val / 2 ^ 32 < 2 ^ 32 := by
    simpa using divmodCol0Carry_lt q.a0.val b.a0.val r.a0.val q.a0.isU32 b.a0.isU32 r.a0.isU32
  have hc0_u32 :
      (Felt.ofNat (u128DivmodCol0 q.a0.val.val b.a0.val.val r.a0.val.val / 2 ^ 32)).isU32 = true := by
    exact felt_ofNat_isU32_of_lt _ hc0_lt
  have hc0_val :
      (Felt.ofNat (u128DivmodCol0 q.a0.val.val b.a0.val.val r.a0.val.val / 2 ^ 32)).val =
        u128DivmodCol0 q.a0.val.val b.a0.val.val r.a0.val.val / 2 ^ 32 := by
    exact felt_ofNat_val_lt _ (u32_val_lt_prime _ hc0_lt)
  have ha1_eq :
      a.a1.val =
        Felt.ofNat
          (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val r.a0.val.val r.a1.val.val %
            2 ^ 32) := by
    by_contra h_not
    rw [divmodCol1_none
        (Felt.ofNat (u128DivmodCol0 q.a0.val.val b.a0.val.val r.a0.val.val / 2 ^ 32))
        q.a0.val q.a1.val q.a2.val q.a3.val
        r.a0.val r.a1.val r.a2.val r.a3.val
        b.a0.val b.a1.val b.a2.val b.a3.val
        a.a1.val a.a2.val a.a3.val
        rest adv_rest mem locs
        q.a0.isU32 q.a1.isU32 r.a1.isU32
        b.a0.isU32 b.a1.isU32
        hc0_u32 hc0_val h_not] at hexec
    simp at hexec
  rw [divmodCol1_run
      (Felt.ofNat (u128DivmodCol0 q.a0.val.val b.a0.val.val r.a0.val.val / 2 ^ 32))
      q.a0.val q.a1.val q.a2.val q.a3.val
      r.a0.val r.a1.val r.a2.val r.a3.val
      b.a0.val b.a1.val b.a2.val b.a3.val
      a.a1.val a.a2.val a.a3.val
      rest adv_rest mem locs
      q.a0.isU32 q.a1.isU32 r.a1.isU32
      b.a0.isU32 b.a1.isU32
      hc0_u32 hc0_val ha1_eq] at hexec
  simp at hexec
  simp only [← two_pow_32] at hexec
  rw [divmodCol2_eq, exec_append] at hexec
  rw [exec_append] at hexec
  have hc1Hi_lt :
      u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val r.a0.val.val r.a1.val.val / 2 ^ 32 / 2 ^ 32 <
        2 ^ 32 := by
    exact divmodCol1CarryCarry_lt
      q.a0.val q.a1.val b.a0.val b.a1.val r.a0.val r.a1.val
      q.a0.isU32 q.a1.isU32 b.a0.isU32 b.a1.isU32 r.a0.isU32 r.a1.isU32
  rw [divmodCol2a_run
      (Felt.ofNat
        (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val r.a0.val.val r.a1.val.val /
          2 ^ 32 %
          2 ^ 32))
      (Felt.ofNat
        (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val r.a0.val.val r.a1.val.val /
          2 ^ 32 /
          2 ^ 32))
      q.a0.val q.a1.val q.a2.val q.a3.val
      r.a0.val r.a1.val r.a2.val r.a3.val
      b.a0.val b.a1.val b.a2.val b.a3.val
      a.a2.val a.a3.val
      rest adv_rest mem locs
      q.a1.isU32 q.a2.isU32 b.a0.isU32 b.a1.isU32
      (u32_mod_isU32 _)
      (felt_ofNat_val_lt _ (u32_mod_lt_prime _))] at hexec
  simp at hexec
  simp only [← two_pow_32] at hexec
  let c1Lo : Felt :=
    Felt.ofNat
      (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val r.a0.val.val r.a1.val.val /
        2 ^ 32 %
        2 ^ 32)
  let c1Hi : Felt :=
    Felt.ofNat
      (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val r.a0.val.val r.a1.val.val /
        2 ^ 32 /
        2 ^ 32)
  let col2Lo0 : Nat := (b.a0.val.val * q.a2.val.val + c1Lo.val) % 2 ^ 32
  let col2Hi0 : Nat := (b.a0.val.val * q.a2.val.val + c1Lo.val) / 2 ^ 32
  let col2Lo1 : Nat := (b.a1.val.val * q.a1.val.val + col2Lo0) % 2 ^ 32
  let col2Hi1 : Nat := (b.a1.val.val * q.a1.val.val + col2Lo0) / 2 ^ 32
  let col2SumHi : Nat := c1Hi.val + col2Hi0 + col2Hi1
  let col2Madd2Lo : Nat := (b.a2.val.val * q.a0.val.val + col2Lo1) % 2 ^ 32
  let col2Madd2Hi : Nat := (b.a2.val.val * q.a0.val.val + col2Lo1) / 2 ^ 32
  rw [exec_append] at hexec
  have hCol2b :
      exec 163
        ⟨Felt.ofNat
            ((b.a1.val.val * q.a1.val.val +
                (b.a0.val.val * q.a2.val.val +
                    (Felt.ofNat
                      (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val
                        r.a0.val.val r.a1.val.val /
                        2 ^ 32 %
                        2 ^ 32)).val) %
                  2 ^ 32) %
              2 ^ 32) ::
          Felt.ofNat
            ((Felt.ofNat
                (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val
                  r.a0.val.val r.a1.val.val /
                  2 ^ 32 /
                  2 ^ 32)).val +
              (b.a0.val.val * q.a2.val.val +
                  (Felt.ofNat
                    (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val
                      r.a0.val.val r.a1.val.val /
                      2 ^ 32 %
                      2 ^ 32)).val) /
                2 ^ 32 +
              (b.a1.val.val * q.a1.val.val +
                  (b.a0.val.val * q.a2.val.val +
                      (Felt.ofNat
                        (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val
                          r.a0.val.val r.a1.val.val /
                          2 ^ 32 %
                          2 ^ 32)).val) %
                2 ^ 32) /
              2 ^ 32) ::
          q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val ::
          r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
          b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
          a.a2.val :: a.a3.val :: rest,
          mem, locs, adv_rest⟩
        divmodCol2b =
      some ⟨Felt.ofNat col2Madd2Lo :: Felt.ofNat (col2SumHi + col2Madd2Hi) ::
              q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val ::
              r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
              b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
              a.a2.val :: a.a3.val :: rest,
            mem, locs, adv_rest⟩ := by
    dsimp [c1Lo, c1Hi, col2Lo0, col2Hi0, col2Lo1, col2Hi1, col2SumHi, col2Madd2Lo,
      col2Madd2Hi]
    simpa using
      (divmodCol2b_run
        (Felt.ofNat
          (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val r.a0.val.val r.a1.val.val /
            2 ^ 32 %
            2 ^ 32))
        (Felt.ofNat
          (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val r.a0.val.val r.a1.val.val /
            2 ^ 32 /
            2 ^ 32))
        q.a0.val q.a1.val q.a2.val q.a3.val
        r.a0.val r.a1.val r.a2.val r.a3.val
        b.a0.val b.a1.val b.a2.val b.a3.val
        a.a2.val a.a3.val
        rest adv_rest mem locs
        q.a0.isU32 b.a2.isU32)
  have hexecCol2c :
      ((exec 163
          ⟨Felt.ofNat col2Madd2Lo :: Felt.ofNat (col2SumHi + col2Madd2Hi) ::
              q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val ::
              r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
              b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
              a.a2.val :: a.a3.val :: rest,
            mem, locs, adv_rest⟩
          divmodCol2c).bind
        fun a => exec 163 a (divmodCol3 ++ divmodTail)) =
      some s' := by
    have hCol2bc :
        (exec 163
            ⟨Felt.ofNat
                ((b.a1.val.val * q.a1.val.val +
                    (b.a0.val.val * q.a2.val.val +
                        (Felt.ofNat
                          (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val
                            r.a0.val.val r.a1.val.val /
                            2 ^ 32 %
                            2 ^ 32)).val) %
                      2 ^ 32) %
                  2 ^ 32) ::
              Felt.ofNat
                ((Felt.ofNat
                    (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val
                      r.a0.val.val r.a1.val.val /
                      2 ^ 32 /
                      2 ^ 32)).val +
                  (b.a0.val.val * q.a2.val.val +
                      (Felt.ofNat
                        (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val
                          r.a0.val.val r.a1.val.val /
                          2 ^ 32 %
                          2 ^ 32)).val) /
                    2 ^ 32 +
                  (b.a1.val.val * q.a1.val.val +
                      (b.a0.val.val * q.a2.val.val +
                          (Felt.ofNat
                            (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val
                              r.a0.val.val r.a1.val.val /
                              2 ^ 32 %
                              2 ^ 32)).val) %
                    2 ^ 32) /
                  2 ^ 32) ::
              q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val ::
              r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
              b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
              a.a2.val :: a.a3.val :: rest,
            mem, locs, adv_rest⟩
            divmodCol2b).bind
          (fun st => exec 163 st divmodCol2c) =
        exec 163
          ⟨Felt.ofNat col2Madd2Lo :: Felt.ofNat (col2SumHi + col2Madd2Hi) ::
              q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val ::
              r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
              b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
              a.a2.val :: a.a3.val :: rest,
            mem, locs, adv_rest⟩
          divmodCol2c := by
      rw [hCol2b]
      simp [Option.bind]
    have hexec_bind :
        ((exec 163
            ⟨Felt.ofNat
                ((b.a1.val.val * q.a1.val.val +
                    (b.a0.val.val * q.a2.val.val +
                        (Felt.ofNat
                          (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val
                            r.a0.val.val r.a1.val.val /
                            2 ^ 32 %
                            2 ^ 32)).val) %
                      2 ^ 32) %
                  2 ^ 32) ::
              Felt.ofNat
                ((Felt.ofNat
                    (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val
                      r.a0.val.val r.a1.val.val /
                      2 ^ 32 /
                      2 ^ 32)).val +
                  (b.a0.val.val * q.a2.val.val +
                      (Felt.ofNat
                        (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val
                          r.a0.val.val r.a1.val.val /
                          2 ^ 32 %
                          2 ^ 32)).val) /
                    2 ^ 32 +
                  (b.a1.val.val * q.a1.val.val +
                      (b.a0.val.val * q.a2.val.val +
                          (Felt.ofNat
                            (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val
                              r.a0.val.val r.a1.val.val /
                              2 ^ 32 %
                              2 ^ 32)).val) %
                    2 ^ 32) /
                  2 ^ 32) ::
              q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val ::
              r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
              b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
              a.a2.val :: a.a3.val :: rest,
            mem, locs, adv_rest⟩
            divmodCol2b).bind
          (fun st => exec 163 st divmodCol2c)).bind
        (fun a => exec 163 a (divmodCol3 ++ divmodTail)) =
      some s' := by
      simpa [bind, Bind.bind, Option.bind] using hexec
    rw [hCol2bc] at hexec_bind
    exact hexec_bind
  have hexec := hexecCol2c
  clear hexecCol2c
  have ha2_eq :
      a.a2.val =
        Felt.ofNat
          (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val b.a2.val.val
              r.a0.val.val r.a1.val.val r.a2.val.val %
            2 ^ 32) := by
    by_contra h_not
    rw [show exec 163
        ⟨Felt.ofNat col2Madd2Lo :: Felt.ofNat (col2SumHi + col2Madd2Hi) ::
            q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val ::
            r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
            b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
            a.a2.val :: a.a3.val :: rest,
          mem, locs, adv_rest⟩
        divmodCol2c =
      none by
        dsimp [c1Lo, c1Hi, col2Lo0, col2Hi0, col2Lo1, col2Hi1, col2SumHi, col2Madd2Lo,
          col2Madd2Hi]
        simpa using
          (divmodCol2c_none
            (Felt.ofNat
              (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val r.a0.val.val r.a1.val.val /
                2 ^ 32 %
                2 ^ 32))
            (Felt.ofNat
              (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val r.a0.val.val r.a1.val.val /
                2 ^ 32 /
                2 ^ 32))
            q.a0.val q.a1.val q.a2.val q.a3.val
            r.a0.val r.a1.val r.a2.val r.a3.val
            b.a0.val b.a1.val b.a2.val b.a3.val
            a.a2.val a.a3.val
            rest adv_rest mem locs
            q.a0.isU32 q.a1.isU32 q.a2.isU32 r.a2.isU32
            b.a0.isU32 b.a1.isU32 b.a2.isU32
            (u32_mod_isU32 _) (felt_ofNat_isU32_of_lt _ hc1Hi_lt)
            (felt_ofNat_val_lt _ (u32_mod_lt_prime _))
            (felt_ofNat_val_lt _ (u32_val_lt_prime _ hc1Hi_lt))
            h_not)] at hexec
    simp at hexec
  rw [show exec 163
      ⟨Felt.ofNat col2Madd2Lo :: Felt.ofNat (col2SumHi + col2Madd2Hi) ::
          q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val ::
          r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
          b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
          a.a2.val :: a.a3.val :: rest,
        mem, locs, adv_rest⟩
      divmodCol2c =
    some ⟨Felt.ofNat
              (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val b.a2.val.val
                  r.a0.val.val r.a1.val.val r.a2.val.val /
                2 ^ 32 %
                2 ^ 32) ::
            Felt.ofNat
              (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val b.a2.val.val
                  r.a0.val.val r.a1.val.val r.a2.val.val /
                2 ^ 32 /
                2 ^ 32) ::
            q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val ::
            r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
            b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
            a.a3.val :: rest,
          mem, locs, adv_rest⟩ by
      dsimp [c1Lo, c1Hi, col2Lo0, col2Hi0, col2Lo1, col2Hi1, col2SumHi, col2Madd2Lo,
        col2Madd2Hi]
      simpa using
        (divmodCol2c_run
          (Felt.ofNat
            (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val r.a0.val.val r.a1.val.val /
              2 ^ 32 %
              2 ^ 32))
          (Felt.ofNat
            (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val r.a0.val.val r.a1.val.val /
              2 ^ 32 /
              2 ^ 32))
          q.a0.val q.a1.val q.a2.val q.a3.val
          r.a0.val r.a1.val r.a2.val r.a3.val
          b.a0.val b.a1.val b.a2.val b.a3.val
          a.a2.val a.a3.val
          rest adv_rest mem locs
          q.a0.isU32 q.a1.isU32 q.a2.isU32 r.a2.isU32
          b.a0.isU32 b.a1.isU32 b.a2.isU32
          (u32_mod_isU32 _) (felt_ofNat_isU32_of_lt _ hc1Hi_lt)
          (felt_ofNat_val_lt _ (u32_mod_lt_prime _))
          (felt_ofNat_val_lt _ (u32_val_lt_prime _ hc1Hi_lt))
          ha2_eq)] at hexec
  simp at hexec
  simp only [← two_pow_32] at hexec
  rw [divmodCol3_eq, exec_append] at hexec
  rw [exec_append] at hexec
  have hc2Hi_lt :
      u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val b.a2.val.val
          r.a0.val.val r.a1.val.val r.a2.val.val / 2 ^ 32 / 2 ^ 32 <
        2 ^ 32 := by
    exact divmodCol2CarryCarry_lt
      q.a0.val q.a1.val q.a2.val
      b.a0.val b.a1.val b.a2.val
      r.a0.val r.a1.val r.a2.val
      q.a0.isU32 q.a1.isU32 q.a2.isU32
      b.a0.isU32 b.a1.isU32 b.a2.isU32
      r.a0.isU32 r.a1.isU32 r.a2.isU32
  rw [divmodCol3a_run
      (Felt.ofNat
        (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val b.a2.val.val
          r.a0.val.val r.a1.val.val r.a2.val.val / 2 ^ 32 % 2 ^ 32))
      (Felt.ofNat
        (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val b.a2.val.val
          r.a0.val.val r.a1.val.val r.a2.val.val / 2 ^ 32 / 2 ^ 32))
      q.a0.val q.a1.val q.a2.val q.a3.val
      r.a0.val r.a1.val r.a2.val r.a3.val
      b.a0.val b.a1.val b.a2.val b.a3.val
      a.a3.val
      rest adv_rest mem locs
      q.a2.isU32 q.a3.isU32 b.a0.isU32 b.a1.isU32
      (u32_mod_isU32 _)] at hexec
  simp at hexec
  simp only [← two_pow_32] at hexec
  let c2Lo : Felt :=
    Felt.ofNat
      (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val b.a2.val.val
        r.a0.val.val r.a1.val.val r.a2.val.val / 2 ^ 32 % 2 ^ 32)
  let c2Hi : Felt :=
    Felt.ofNat
      (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val b.a2.val.val
        r.a0.val.val r.a1.val.val r.a2.val.val / 2 ^ 32 / 2 ^ 32)
  let col3Lo0 : Nat := (b.a0.val.val * q.a3.val.val + c2Lo.val) % 2 ^ 32
  let col3Hi0 : Nat := (b.a0.val.val * q.a3.val.val + c2Lo.val) / 2 ^ 32
  let col3Lo1 : Nat := (b.a1.val.val * q.a2.val.val + col3Lo0) % 2 ^ 32
  let col3Hi1 : Nat := (b.a1.val.val * q.a2.val.val + col3Lo0) / 2 ^ 32
  let col3SumHi : Nat := c2Hi.val + col3Hi0 + col3Hi1
  let col3Madd2Lo : Nat := (b.a2.val.val * q.a1.val.val + col3Lo1) % 2 ^ 32
  let col3Madd2Hi : Nat := (b.a2.val.val * q.a1.val.val + col3Lo1) / 2 ^ 32
  rw [exec_append] at hexec
  have hCol3b :
      exec 163
        ⟨Felt.ofNat
            ((b.a1.val.val * q.a2.val.val +
                (b.a0.val.val * q.a3.val.val +
                    (Felt.ofNat
                      (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val
                        b.a2.val.val r.a0.val.val r.a1.val.val r.a2.val.val /
                        2 ^ 32 %
                        2 ^ 32)).val) %
                  2 ^ 32) %
              2 ^ 32) ::
          Felt.ofNat
            ((Felt.ofNat
                (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val
                  b.a2.val.val r.a0.val.val r.a1.val.val r.a2.val.val /
                  2 ^ 32 /
                  2 ^ 32)).val +
              (b.a0.val.val * q.a3.val.val +
                  (Felt.ofNat
                    (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val
                      b.a2.val.val r.a0.val.val r.a1.val.val r.a2.val.val /
                      2 ^ 32 %
                      2 ^ 32)).val) /
                2 ^ 32 +
              (b.a1.val.val * q.a2.val.val +
                  (b.a0.val.val * q.a3.val.val +
                      (Felt.ofNat
                        (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val
                          b.a2.val.val r.a0.val.val r.a1.val.val r.a2.val.val /
                          2 ^ 32 %
                          2 ^ 32)).val) %
                2 ^ 32) /
              2 ^ 32) ::
          q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val ::
          r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
          b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
          a.a3.val :: rest,
        mem, locs, adv_rest⟩
        divmodCol3b =
      some ⟨Felt.ofNat col3Madd2Lo :: Felt.ofNat (col3SumHi + col3Madd2Hi) ::
              q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val ::
              r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
              b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
              a.a3.val :: rest,
            mem, locs, adv_rest⟩ := by
    dsimp [c2Lo, c2Hi, col3Lo0, col3Hi0, col3Lo1, col3Hi1, col3SumHi, col3Madd2Lo,
      col3Madd2Hi]
    simpa using
      (divmodCol3b_run
        (Felt.ofNat
          (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val b.a2.val.val
            r.a0.val.val r.a1.val.val r.a2.val.val /
            2 ^ 32 %
            2 ^ 32))
        (Felt.ofNat
          (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val b.a2.val.val
            r.a0.val.val r.a1.val.val r.a2.val.val /
            2 ^ 32 /
            2 ^ 32))
        q.a0.val q.a1.val q.a2.val q.a3.val
        r.a0.val r.a1.val r.a2.val r.a3.val
        b.a0.val b.a1.val b.a2.val b.a3.val
        a.a3.val
        rest adv_rest mem locs
        q.a1.isU32 b.a2.isU32)
  have hexecCol3c :
      ((exec 163
          ⟨Felt.ofNat col3Madd2Lo :: Felt.ofNat (col3SumHi + col3Madd2Hi) ::
              q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val ::
              r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
              b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
              a.a3.val :: rest,
            mem, locs, adv_rest⟩
          divmodCol3c).bind
        fun a => exec 163 a divmodTail) =
      some s' := by
    have hCol3bc :
        (exec 163
            ⟨Felt.ofNat
                ((b.a1.val.val * q.a2.val.val +
                    (b.a0.val.val * q.a3.val.val +
                        (Felt.ofNat
                          (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val
                            b.a2.val.val r.a0.val.val r.a1.val.val r.a2.val.val /
                            2 ^ 32 %
                            2 ^ 32)).val) %
                      2 ^ 32) %
                  2 ^ 32) ::
              Felt.ofNat
                ((Felt.ofNat
                    (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val
                      b.a2.val.val r.a0.val.val r.a1.val.val r.a2.val.val /
                      2 ^ 32 /
                      2 ^ 32)).val +
                  (b.a0.val.val * q.a3.val.val +
                      (Felt.ofNat
                        (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val
                          b.a2.val.val r.a0.val.val r.a1.val.val r.a2.val.val /
                          2 ^ 32 %
                          2 ^ 32)).val) /
                    2 ^ 32 +
                  (b.a1.val.val * q.a2.val.val +
                      (b.a0.val.val * q.a3.val.val +
                          (Felt.ofNat
                            (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val
                              b.a2.val.val r.a0.val.val r.a1.val.val r.a2.val.val /
                              2 ^ 32 %
                              2 ^ 32)).val) %
                    2 ^ 32) /
                  2 ^ 32) ::
              q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val ::
              r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
              b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
              a.a3.val :: rest,
            mem, locs, adv_rest⟩
            divmodCol3b).bind
          (fun st => exec 163 st divmodCol3c) =
        exec 163
          ⟨Felt.ofNat col3Madd2Lo :: Felt.ofNat (col3SumHi + col3Madd2Hi) ::
              q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val ::
              r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
              b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
              a.a3.val :: rest,
            mem, locs, adv_rest⟩
          divmodCol3c := by
      rw [hCol3b]
      simp [Option.bind]
    have hexec_bind :
        ((exec 163
            ⟨Felt.ofNat
                ((b.a1.val.val * q.a2.val.val +
                    (b.a0.val.val * q.a3.val.val +
                        (Felt.ofNat
                          (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val
                            b.a2.val.val r.a0.val.val r.a1.val.val r.a2.val.val /
                            2 ^ 32 %
                            2 ^ 32)).val) %
                      2 ^ 32) %
                  2 ^ 32) ::
              Felt.ofNat
                ((Felt.ofNat
                    (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val
                      b.a2.val.val r.a0.val.val r.a1.val.val r.a2.val.val /
                      2 ^ 32 /
                      2 ^ 32)).val +
                  (b.a0.val.val * q.a3.val.val +
                      (Felt.ofNat
                        (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val
                          b.a2.val.val r.a0.val.val r.a1.val.val r.a2.val.val /
                          2 ^ 32 %
                          2 ^ 32)).val) /
                    2 ^ 32 +
                  (b.a1.val.val * q.a2.val.val +
                      (b.a0.val.val * q.a3.val.val +
                          (Felt.ofNat
                            (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val
                              b.a2.val.val r.a0.val.val r.a1.val.val r.a2.val.val /
                              2 ^ 32 %
                              2 ^ 32)).val) %
                    2 ^ 32) /
                  2 ^ 32) ::
              q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val ::
              r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
              b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
              a.a3.val :: rest,
            mem, locs, adv_rest⟩
            divmodCol3b).bind
          (fun st => exec 163 st divmodCol3c)).bind
        (fun a => exec 163 a divmodTail) =
      some s' := by
      simpa [bind, Bind.bind, Option.bind] using hexec
    rw [hCol3bc] at hexec_bind
    exact hexec_bind
  have hexec := hexecCol3c
  clear hexecCol3c
  have ha3_eq :
      a.a3.val =
        Felt.ofNat
          (u128DivmodCol3 q.a0.val.val q.a1.val.val q.a2.val.val q.a3.val.val
              b.a0.val.val b.a1.val.val b.a2.val.val b.a3.val.val
              r.a0.val.val r.a1.val.val r.a2.val.val r.a3.val.val %
            2 ^ 32) := by
    by_contra h_not
    rw [divmodCol3c_none_a3
        (Felt.ofNat
          (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val b.a2.val.val
            r.a0.val.val r.a1.val.val r.a2.val.val / 2 ^ 32 % 2 ^ 32))
        (Felt.ofNat
          (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val b.a2.val.val
            r.a0.val.val r.a1.val.val r.a2.val.val / 2 ^ 32 / 2 ^ 32))
        q.a0.val q.a1.val q.a2.val q.a3.val
        r.a0.val r.a1.val r.a2.val r.a3.val
        b.a0.val b.a1.val b.a2.val b.a3.val
        a.a3.val
        rest adv_rest mem locs
        q.a0.isU32 q.a1.isU32 q.a2.isU32 q.a3.isU32
        r.a3.isU32
        b.a0.isU32 b.a1.isU32 b.a2.isU32 b.a3.isU32
        (u32_mod_isU32 _)
        (felt_ofNat_val_lt _ (u32_mod_lt_prime _))
        (felt_ofNat_val_lt _ (u32_val_lt_prime _ hc2Hi_lt))
        h_not] at hexec
    simp at hexec
  have hcarry_zero_nat :
      u128DivmodCol3 q.a0.val.val q.a1.val.val q.a2.val.val q.a3.val.val
          b.a0.val.val b.a1.val.val b.a2.val.val b.a3.val.val
          r.a0.val.val r.a1.val.val r.a2.val.val r.a3.val.val / 2 ^ 32 =
        0 := by
    by_contra h_not
    rw [divmodCol3c_none_carry
        (Felt.ofNat
          (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val b.a2.val.val
            r.a0.val.val r.a1.val.val r.a2.val.val / 2 ^ 32 % 2 ^ 32))
        (Felt.ofNat
          (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val b.a2.val.val
            r.a0.val.val r.a1.val.val r.a2.val.val / 2 ^ 32 / 2 ^ 32))
        q.a0.val q.a1.val q.a2.val q.a3.val
        r.a0.val r.a1.val r.a2.val r.a3.val
        b.a0.val b.a1.val b.a2.val b.a3.val
        a.a3.val
        rest adv_rest mem locs
        q.a0.isU32 q.a1.isU32 q.a2.isU32 q.a3.isU32
        r.a2.isU32 r.a3.isU32
        b.a0.isU32 b.a1.isU32 b.a2.isU32 b.a3.isU32
        (u32_mod_isU32 _) (felt_ofNat_isU32_of_lt _ hc2Hi_lt)
        (felt_ofNat_val_lt _ (u32_mod_lt_prime _))
        (felt_ofNat_val_lt _ (u32_val_lt_prime _ hc2Hi_lt))
        ha3_eq h_not] at hexec
    simp at hexec
  rw [divmodCol3c_run
      (Felt.ofNat
        (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val b.a2.val.val
          r.a0.val.val r.a1.val.val r.a2.val.val / 2 ^ 32 % 2 ^ 32))
      (Felt.ofNat
        (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val b.a2.val.val
          r.a0.val.val r.a1.val.val r.a2.val.val / 2 ^ 32 / 2 ^ 32))
      q.a0.val q.a1.val q.a2.val q.a3.val
      r.a0.val r.a1.val r.a2.val r.a3.val
      b.a0.val b.a1.val b.a2.val b.a3.val
      a.a3.val
      rest adv_rest mem locs
      q.a0.isU32 q.a1.isU32 q.a2.isU32 q.a3.isU32
      r.a3.isU32
      b.a0.isU32 b.a1.isU32 b.a2.isU32 b.a3.isU32
      (u32_mod_isU32 _)
      (felt_ofNat_val_lt _ (u32_mod_lt_prime _))
      (felt_ofNat_val_lt _ (u32_val_lt_prime _ hc2Hi_lt))
      ha3_eq hcarry_zero_nat] at hexec
  simp at hexec
  rw [divmodTail_eq, exec_append] at hexec
  have hover_false :
      divmodOverflowBool q.a1.val q.a2.val q.a3.val b.a1.val b.a2.val b.a3.val = false := by
    by_cases hover : divmodOverflowBool q.a1.val q.a2.val q.a3.val b.a1.val b.a2.val b.a3.val = false
    · exact hover
    · have hover_true : divmodOverflowBool q.a1.val q.a2.val q.a3.val b.a1.val b.a2.val b.a3.val = true := by
        cases hbool : divmodOverflowBool q.a1.val q.a2.val q.a3.val b.a1.val b.a2.val b.a3.val <;> simp_all
      rw [divmodOverflow_eval
          q.a0.val q.a1.val q.a2.val q.a3.val
          r.a0.val r.a1.val r.a2.val r.a3.val
          b.a0.val b.a1.val b.a2.val b.a3.val
          rest adv_rest mem locs
          q.a1.isU32 q.a2.isU32 q.a3.isU32
          b.a1.isU32 b.a2.isU32 b.a3.isU32] at hexec
      simp [hover_true] at hexec
  rw [divmodOverflow_eval
      q.a0.val q.a1.val q.a2.val q.a3.val
      r.a0.val r.a1.val r.a2.val r.a3.val
      b.a0.val b.a1.val b.a2.val b.a3.val
      rest adv_rest mem locs
      q.a1.isU32 q.a2.isU32 q.a3.isU32
      b.a1.isU32 b.a2.isU32 b.a3.isU32] at hexec
  simp [hover_false, bind, Bind.bind, Option.bind] at hexec
  have hover_parts := by
    simpa [divmodOverflowBool, Bool.or_eq_false_iff] using hover_false
  rcases hover_parts with ⟨hover_parts, h63_false⟩
  rcases hover_parts with ⟨hover_parts, h53_false⟩
  rcases hover_parts with ⟨hover_parts, h52_false⟩
  rcases hover_parts with ⟨hover_parts, h43_false⟩
  rcases hover_parts with ⟨h41_false, h42_false⟩
  have hq3b1_zero : q.a3.val.val * b.a1.val.val = 0 := by
    simpa [Nat.mul_comm] using
      (divmodOverflowProdBool_false q.a3.val b.a1.val q.a3.isU32 b.a1.isU32 h41_false)
  have hq2b2_zero : q.a2.val.val * b.a2.val.val = 0 := by
    simpa [Nat.mul_comm] using
      (divmodOverflowProdBool_false q.a2.val b.a2.val q.a2.isU32 b.a2.isU32 h42_false)
  have hq1b3_zero : q.a1.val.val * b.a3.val.val = 0 := by
    simpa [Nat.mul_comm] using
      (divmodOverflowProdBool_false q.a1.val b.a3.val q.a1.isU32 b.a3.isU32 h43_false)
  have hq3b2_zero : q.a3.val.val * b.a2.val.val = 0 := by
    simpa [Nat.mul_comm] using
      (divmodOverflowProdBool_false q.a3.val b.a2.val q.a3.isU32 b.a2.isU32 h52_false)
  have hq2b3_zero : q.a2.val.val * b.a3.val.val = 0 := by
    simpa [Nat.mul_comm] using
      (divmodOverflowProdBool_false q.a2.val b.a3.val q.a2.isU32 b.a3.isU32 h53_false)
  have hq3b3_zero : q.a3.val.val * b.a3.val.val = 0 := by
    simpa [Nat.mul_comm] using
      (divmodOverflowProdBool_false q.a3.val b.a3.val q.a3.isU32 b.a3.isU32 h63_false)
  rw [exec_append] at hexec
  rw [divmodCompare1_run
      q.a0.val q.a1.val q.a2.val q.a3.val
      r.a0.val r.a1.val r.a2.val r.a3.val
      b.a0.val b.a1.val b.a2.val b.a3.val
      rest adv_rest mem locs
      r.a0.isU32 b.a0.isU32] at hexec
  simp at hexec
  rw [exec_append] at hexec
  rw [divmodCompare2_run
      q.a0.val q.a1.val q.a2.val q.a3.val
      r.a0.val r.a1.val r.a2.val r.a3.val
      b.a0.val b.a1.val b.a2.val b.a3.val
      rest adv_rest mem locs
      r.a0.isU32 r.a1.isU32 b.a0.isU32 b.a1.isU32] at hexec
  simp at hexec
  rw [exec_append] at hexec
  rw [divmodCompare3_run
      q.a0.val q.a1.val q.a2.val q.a3.val
      r.a0.val r.a1.val r.a2.val r.a3.val
      b.a0.val b.a1.val b.a2.val b.a3.val
      rest adv_rest mem locs
      r.a0.isU32 r.a1.isU32 r.a2.isU32
      b.a0.isU32 b.a1.isU32 b.a2.isU32] at hexec
  simp at hexec
  have h_lt_result : u128LtBool r.a0.val r.a1.val r.a2.val r.a3.val b.a0.val b.a1.val b.a2.val b.a3.val = true := by
    by_contra h_not
    rw [divmodCompare4_none
        q.a0.val q.a1.val q.a2.val q.a3.val
        r.a0.val r.a1.val r.a2.val r.a3.val
        b.a0.val b.a1.val b.a2.val b.a3.val
        rest adv_rest mem locs
        r.a0.isU32 r.a1.isU32 r.a2.isU32 r.a3.isU32
        b.a0.isU32 b.a1.isU32 b.a2.isU32 b.a3.isU32
        h_not] at hexec
    simp at hexec
  have ha0_nat : a.a0.val.val = u128DivmodCol0 q.a0.val.val b.a0.val.val r.a0.val.val % 2 ^ 32 := by
    have h := congrArg (fun z : Felt => z.val) ha0_eq
    change
      ZMod.val a.a0.val =
        ZMod.val (Felt.ofNat (u128DivmodCol0 q.a0.val.val b.a0.val.val r.a0.val.val % 2 ^ 32)) at h
    rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)] at h
    exact h
  have ha1_nat :
      a.a1.val.val =
        u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val r.a0.val.val r.a1.val.val % 2 ^ 32 := by
    have h := congrArg (fun z : Felt => z.val) ha1_eq
    change
      ZMod.val a.a1.val =
        ZMod.val
          (Felt.ofNat
            (u128DivmodCol1 q.a0.val.val q.a1.val.val b.a0.val.val b.a1.val.val r.a0.val.val r.a1.val.val %
              2 ^ 32)) at h
    rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)] at h
    exact h
  have ha2_nat :
      a.a2.val.val =
        u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val b.a2.val.val
            r.a0.val.val r.a1.val.val r.a2.val.val % 2 ^ 32 := by
    have h := congrArg (fun z : Felt => z.val) ha2_eq
    change
      ZMod.val a.a2.val =
        ZMod.val
          (Felt.ofNat
            (u128DivmodCol2 q.a0.val.val q.a1.val.val q.a2.val.val b.a0.val.val b.a1.val.val b.a2.val.val
                r.a0.val.val r.a1.val.val r.a2.val.val %
              2 ^ 32)) at h
    rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)] at h
    exact h
  have ha3_nat :
      a.a3.val.val =
        u128DivmodCol3 q.a0.val.val q.a1.val.val q.a2.val.val q.a3.val.val
            b.a0.val.val b.a1.val.val b.a2.val.val b.a3.val.val
            r.a0.val.val r.a1.val.val r.a2.val.val r.a3.val.val % 2 ^ 32 := by
    have h := congrArg (fun z : Felt => z.val) ha3_eq
    change
      ZMod.val a.a3.val =
        ZMod.val
          (Felt.ofNat
            (u128DivmodCol3 q.a0.val.val q.a1.val.val q.a2.val.val q.a3.val.val
                b.a0.val.val b.a1.val.val b.a2.val.val b.a3.val.val
                r.a0.val.val r.a1.val.val r.a2.val.val r.a3.val.val %
              2 ^ 32)) at h
    rw [felt_ofNat_val_lt _ (u32_mod_lt_prime _)] at h
    exact h
  have hdiv_nat_raw :
      u128RawValue q.a0.val.val q.a1.val.val q.a2.val.val q.a3.val.val *
          u128RawValue b.a0.val.val b.a1.val.val b.a2.val.val b.a3.val.val
        + u128RawValue r.a0.val.val r.a1.val.val r.a2.val.val r.a3.val.val =
      u128RawValue a.a0.val.val a.a1.val.val a.a2.val.val a.a3.val.val := by
    exact divmod_forward_arith
      q.a0.val.val q.a1.val.val q.a2.val.val q.a3.val.val
      b.a0.val.val b.a1.val.val b.a2.val.val b.a3.val.val
      r.a0.val.val r.a1.val.val r.a2.val.val r.a3.val.val
      a.a0.val.val a.a1.val.val a.a2.val.val a.a3.val.val
      hq1b3_zero hq2b2_zero hq3b1_zero hq2b3_zero hq3b2_zero hq3b3_zero
      (by simpa [divmodCarry] using hcarry_zero_nat)
      ha0_nat ha1_nat ha2_nat ha3_nat
  have hlt_nat_raw :
      u128RawValue r.a0.val.val r.a1.val.val r.a2.val.val r.a3.val.val <
        u128RawValue b.a0.val.val b.a1.val.val b.a2.val.val b.a3.val.val := by
    rw [divmodLtBool_eqRaw
        r.a0.val r.a1.val r.a2.val r.a3.val
        b.a0.val b.a1.val b.a2.val b.a3.val
        r.a0.isU32 r.a1.isU32 r.a2.isU32 r.a3.isU32
        b.a0.isU32 b.a1.isU32 b.a2.isU32 b.a3.isU32] at h_lt_result
    exact of_decide_eq_true h_lt_result
  constructor
  · simpa [U128.toNat, u128RawValue] using hdiv_nat_raw
  · simpa [U128.toNat, u128RawValue] using hlt_nat_raw

/-- `u128::divmod` verifies the Euclidean division of two u128 values.
    Execution succeeds iff the advice-supplied quotient q and remainder r
    satisfy q * b + r = a and r < b.
    Input stack:  [b.a0, b.a1, b.a2, b.a3, a.a0, a.a1, a.a2, a.a3] ++ rest
    Advice stack: [r.a0, r.a1, r.a2, r.a3, q.a0, q.a1, q.a2, q.a3] ++ adv_rest
    Output stack: [r.a0, r.a1, r.a2, r.a3, q.a0, q.a1, q.a2, q.a3] ++ rest -/
theorem u128_divmod_correct
    (a b q r : U128) (rest adv_rest : List Felt) (s : MidenState)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                    a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest)
    (hadv : s.advice = r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
                      q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val :: adv_rest) :
    exec 163 s Miden.Core.U128.divmod =
    some { stack := r.a0.val :: r.a1.val :: r.a2.val :: r.a3.val ::
                     q.a0.val :: q.a1.val :: q.a2.val :: q.a3.val :: rest,
           memory := s.memory,
           locals := s.locals,
           advice := adv_rest }
    ↔ (q.toNat * b.toNat + r.toNat = a.toNat ∧ r.toNat < b.toNat) := by
  constructor
  · intro hexec
    exact u128_divmod_conditions_of_exec a b q r rest adv_rest s hs hadv hexec
  · intro ⟨hdiv, hlt⟩
    exact u128_divmod_raw
      a.a0.val a.a1.val a.a2.val a.a3.val
      b.a0.val b.a1.val b.a2.val b.a3.val
      q.a0.val q.a1.val q.a2.val q.a3.val
      r.a0.val r.a1.val r.a2.val r.a3.val
      rest adv_rest s hs hadv
      a.a0.isU32 a.a1.isU32 a.a2.isU32 a.a3.isU32
      b.a0.isU32 b.a1.isU32 b.a2.isU32 b.a3.isU32
      q.a0.isU32 q.a1.isU32 q.a2.isU32 q.a3.isU32
      r.a0.isU32 r.a1.isU32 r.a2.isU32 r.a3.isU32
      (by simpa [U128.toNat, u128RawValue] using hdiv)
      (by simpa [U128.toNat, u128RawValue] using hlt)

end MidenLean.Proofs
