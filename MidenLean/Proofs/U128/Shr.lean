import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.U128.ShrK0
import MidenLean.Proofs.U128.ShrK1
import MidenLean.Proofs.U128.ShrK2
import MidenLean.Proofs.U128.ShrK3
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

-- ============================================================================
-- Helper lemmas
-- ============================================================================

private theorem felt128_val : (128 : Felt).val = 128 :=
  felt_ofNat_val_lt 128 (by unfold GOLDILOCKS_PRIME; omega)

private theorem felt31_val : (31 : Felt).val = 31 :=
  felt_ofNat_val_lt 31 (by unfold GOLDILOCKS_PRIME; omega)

private theorem felt5_val : (5 : Felt).val = 5 :=
  felt_ofNat_val_lt 5 (by unfold GOLDILOCKS_PRIME; omega)

private theorem nat_land_31_lt_32 (n : Nat) : n &&& 31 < 32 := by
  have h : n &&& 31 ≤ 31 := Nat.and_le_right
  omega

private theorem u32and31_isU32 (a : Felt) :
    (Felt.ofNat (a.val &&& 31)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  have := nat_land_31_lt_32 a.val; omega

private theorem u32and31_le31 (a : Felt) :
    (Felt.ofNat (a.val &&& 31)).val ≤ 31 := by
  have hlt : a.val &&& 31 < 32 := nat_land_31_lt_32 a.val
  rw [felt_ofNat_val_lt _ (by unfold GOLDILOCKS_PRIME; omega)]
  omega

private theorem shr5_isU32 (a : Felt) (ha : a.isU32 = true) :
    (Felt.ofNat (a.val / 2 ^ 5)).isU32 = true := by
  apply felt_ofNat_isU32_of_lt
  simp [Felt.isU32, decide_eq_true_eq] at ha
  calc a.val / 2 ^ 5 ≤ a.val := Nat.div_le_self _ _
    _ < 2 ^ 32 := ha

private theorem shr5_val (shift : Felt) (hlt : shift.val < 128) :
    (Felt.ofNat (shift.val / 2 ^ 5)).val = shift.val / 32 := by
  rw [felt_ofNat_val_lt]; · ring_nf
  · unfold GOLDILOCKS_PRIME; omega

private theorem and31_val (shift : Felt) :
    (Felt.ofNat (shift.val &&& 31)).val = shift.val &&& 31 := by
  rw [felt_ofNat_val_lt]
  unfold GOLDILOCKS_PRIME; have := nat_land_31_lt_32 shift.val; omega

-- ============================================================================
-- Environment-irrelevance for pure-inst lists
-- ============================================================================

private theorem execWithEnv_pure_inst (env1 env2 : ProcEnv) (f1 f2 : Nat)
    (s : MidenState) (ops : List Op)
    (hf1 : f1 > 0) (hf2 : f2 > 0)
    (hpure : ∀ op ∈ ops, ∃ i, op = .inst i ∧ ∀ t, i ≠ .exec t) :
    execWithEnv env1 f1 s ops = execWithEnv env2 f2 s ops := by
  obtain ⟨f1', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show f1 ≠ 0 by omega)
  obtain ⟨f2', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show f2 ≠ 0 by omega)
  unfold execWithEnv
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    obtain ⟨i, hop, hi⟩ := hpure op (List.mem_cons.mpr (Or.inl rfl))
    subst hop
    simp only [List.foldlM]
    dsimp only [bind, Bind.bind, Option.bind]
    have hpure' : ∀ op ∈ ops, ∃ i, op = .inst i ∧ ∀ t, i ≠ .exec t :=
      fun op hmem => hpure op (List.mem_cons.mpr (Or.inr hmem))
    cases i with
    | exec t => exact absurd rfl (hi t)
    | _ =>
      cases h : execInstruction s _ with
      | none => rfl
      | some s' => exact ih s' hpure'

/-- Environment-irrelevance for [ifElse A B] with pure-inst branches. -/
private theorem execWithEnv_ifElse_pure_inst (env1 env2 : ProcEnv) (f1 f2 : Nat)
    (s : MidenState) (A B : List Op)
    (hf1 : f1 ≥ 2) (hf2 : f2 ≥ 2)
    (hA : ∀ op ∈ A, ∃ i, op = .inst i ∧ ∀ t, i ≠ .exec t)
    (hB : ∀ op ∈ B, ∃ i, op = .inst i ∧ ∀ t, i ≠ .exec t) :
    execWithEnv env1 f1 s [.ifElse A B] = execWithEnv env2 f2 s [.ifElse A B] := by
  obtain ⟨f1', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show f1 ≠ 0 by omega)
  obtain ⟨f2', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show f2 ≠ 0 by omega)
  simp only [execWithEnv, List.foldlM, MidenState.withStack]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  match hs : s.stack with
  | [] => rfl
  | cond :: rest =>
    -- Both sides have the same condition logic; only the branch body env/fuel differs
    have hA' := execWithEnv_pure_inst env1 env2 f1' f2'
      ⟨rest, s.memory, s.locals, s.advice⟩ A (by omega) (by omega) hA
    have hB' := execWithEnv_pure_inst env1 env2 f1' f2'
      ⟨rest, s.memory, s.locals, s.advice⟩ B (by omega) (by omega) hB
    simp only [hA', hB']

private theorem execWithEnv_append (env : ProcEnv) (fuel : Nat) (s : MidenState) (xs ys : List Op) :
    execWithEnv env fuel s (xs ++ ys) = (do
      let s' ← execWithEnv env fuel s xs
      execWithEnv env fuel s' ys) := by
  unfold execWithEnv
  cases fuel <;> simp [List.foldlM_append]

-- ============================================================================
-- Bridge lemmas for shr_k0..k3
-- ============================================================================

private theorem shr_k0_pure_inst :
    ∀ op ∈ Miden.Core.U128.shr_k0, ∃ i, op = .inst i ∧ ∀ t, i ≠ .exec t := by
  intro op hmem
  simp only [Miden.Core.U128.shr_k0, List.mem_cons, List.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨_, rfl, fun _ h => Instruction.noConfusion h⟩

private theorem shr_k3_pure_inst :
    ∀ op ∈ Miden.Core.U128.shr_k3, ∃ i, op = .inst i ∧ ∀ t, i ≠ .exec t := by
  intro op hmem
  simp only [Miden.Core.U128.shr_k3, List.mem_cons, List.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨_, rfl, fun _ h => Instruction.noConfusion h⟩

private theorem shr_k0_env_bridge (fuel : Nat) (s : MidenState) (hfuel : fuel > 0) :
    execWithEnv u128ProcEnv fuel s Miden.Core.U128.shr_k0 =
    exec 51 s Miden.Core.U128.shr_k0 :=
  execWithEnv_pure_inst u128ProcEnv (fun _ => none) fuel 51 s _ hfuel (by omega) shr_k0_pure_inst

private theorem shr_k3_env_bridge (fuel : Nat) (s : MidenState) (hfuel : fuel > 0) :
    execWithEnv u128ProcEnv fuel s Miden.Core.U128.shr_k3 =
    exec 12 s Miden.Core.U128.shr_k3 :=
  execWithEnv_pure_inst u128ProcEnv (fun _ => none) fuel 12 s _ hfuel (by omega) shr_k3_pure_inst

-- shr_k1: decompose into prefix + [ifElse then else], all pure-inst
private def shr_k1_prefix : List Op := [.inst (.dup 0), .inst (.eqImm 0)]
private def shr_k1_then : List Op := [.inst (.drop), .inst (.drop)]
private def shr_k1_else : List Op := [
  .inst (.push 32), .inst (.dup 1), .inst (.u32WrappingSub), .inst (.pow2),
  .inst (.dup 5), .inst (.dup 2), .inst (.u32Shr),
  .inst (.dup 5), .inst (.dup 3), .inst (.u32Shr),
  .inst (.dup 7), .inst (.dup 3), .inst (.u32WidenMul),
  .inst (.swap 1), .inst (.drop), .inst (.u32Or),
  .inst (.dup 5), .inst (.dup 4), .inst (.u32Shr),
  .inst (.dup 7), .inst (.dup 4), .inst (.u32WidenMul),
  .inst (.swap 1), .inst (.drop), .inst (.u32Or),
  .inst (.movdn 8), .inst (.movdn 8), .inst (.movdn 8),
  .inst (.drop), .inst (.drop), .inst (.drop),
  .inst (.drop), .inst (.drop), .inst (.drop)]

private theorem shr_k1_body_decomp :
    Miden.Core.U128.shr_k1 =
    shr_k1_prefix ++ [.ifElse shr_k1_then shr_k1_else] := by
  simp [Miden.Core.U128.shr_k1, shr_k1_prefix, shr_k1_then, shr_k1_else]

private theorem shr_k1_prefix_pure :
    ∀ op ∈ shr_k1_prefix, ∃ i, op = .inst i ∧ ∀ t, i ≠ .exec t := by
  intro op hmem; simp [shr_k1_prefix] at hmem
  rcases hmem with rfl | rfl <;> exact ⟨_, rfl, fun _ => by simp⟩

private theorem shr_k1_then_pure :
    ∀ op ∈ shr_k1_then, ∃ i, op = .inst i ∧ ∀ t, i ≠ .exec t := by
  intro op hmem; simp [shr_k1_then] at hmem
  rcases hmem with rfl | rfl <;> exact ⟨_, rfl, fun _ => by simp⟩

private theorem shr_k1_else_pure :
    ∀ op ∈ shr_k1_else, ∃ i, op = .inst i ∧ ∀ t, i ≠ .exec t := by
  intro op hmem; simp [shr_k1_else] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨_, rfl, fun _ h => Instruction.noConfusion h⟩

set_option maxHeartbeats 4000000 in
private theorem shr_k1_env_bridge (fuel : Nat) (s : MidenState) (hfuel : fuel ≥ 2) :
    execWithEnv u128ProcEnv fuel s Miden.Core.U128.shr_k1 =
    exec 43 s Miden.Core.U128.shr_k1 := by
  rw [shr_k1_body_decomp]
  show execWithEnv u128ProcEnv fuel s (shr_k1_prefix ++ [.ifElse shr_k1_then shr_k1_else]) =
       execWithEnv (fun _ => none) 43 s (shr_k1_prefix ++ [.ifElse shr_k1_then shr_k1_else])
  rw [execWithEnv_append, execWithEnv_append]
  have hpre := execWithEnv_pure_inst u128ProcEnv (fun _ => none) fuel 43 s shr_k1_prefix
    (by omega) (by omega) shr_k1_prefix_pure
  rw [hpre]
  cases execWithEnv (fun _ => none) 43 s shr_k1_prefix with
  | none => rfl
  | some s' =>
    dsimp only [bind, Bind.bind, Option.bind]
    exact execWithEnv_ifElse_pure_inst u128ProcEnv (fun _ => none) fuel 43 s'
      shr_k1_then shr_k1_else (by omega) (by omega) shr_k1_then_pure shr_k1_else_pure

-- shr_k2: same decomposition pattern
private def shr_k2_prefix : List Op := [.inst (.dup 0), .inst (.eqImm 0)]
private def shr_k2_then : List Op := [.inst (.drop), .inst (.drop), .inst (.drop)]
private def shr_k2_else : List Op := [
  .inst (.push 32), .inst (.dup 1), .inst (.u32WrappingSub), .inst (.pow2),
  .inst (.dup 5), .inst (.dup 2), .inst (.u32Shr),
  .inst (.dup 5), .inst (.dup 3), .inst (.u32Shr),
  .inst (.dup 7), .inst (.dup 3), .inst (.u32WidenMul),
  .inst (.swap 1), .inst (.drop), .inst (.u32Or),
  .inst (.movdn 7), .inst (.movdn 7),
  .inst (.drop), .inst (.drop), .inst (.drop),
  .inst (.drop), .inst (.drop), .inst (.drop)]

private theorem shr_k2_body_decomp :
    Miden.Core.U128.shr_k2 =
    shr_k2_prefix ++ [.ifElse shr_k2_then shr_k2_else] := by
  simp [Miden.Core.U128.shr_k2, shr_k2_prefix, shr_k2_then, shr_k2_else]

private theorem shr_k2_prefix_pure :
    ∀ op ∈ shr_k2_prefix, ∃ i, op = .inst i ∧ ∀ t, i ≠ .exec t := by
  intro op hmem; simp [shr_k2_prefix] at hmem
  rcases hmem with rfl | rfl <;> exact ⟨_, rfl, fun _ => by simp⟩

private theorem shr_k2_then_pure :
    ∀ op ∈ shr_k2_then, ∃ i, op = .inst i ∧ ∀ t, i ≠ .exec t := by
  intro op hmem; simp [shr_k2_then] at hmem
  rcases hmem with rfl | rfl | rfl <;> exact ⟨_, rfl, fun _ => by simp⟩

private theorem shr_k2_else_pure :
    ∀ op ∈ shr_k2_else, ∃ i, op = .inst i ∧ ∀ t, i ≠ .exec t := by
  intro op hmem; simp [shr_k2_else] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals exact ⟨_, rfl, fun _ h => Instruction.noConfusion h⟩

set_option maxHeartbeats 4000000 in
private theorem shr_k2_env_bridge (fuel : Nat) (s : MidenState) (hfuel : fuel ≥ 2) :
    execWithEnv u128ProcEnv fuel s Miden.Core.U128.shr_k2 =
    exec 34 s Miden.Core.U128.shr_k2 := by
  rw [shr_k2_body_decomp]
  show execWithEnv u128ProcEnv fuel s (shr_k2_prefix ++ [.ifElse shr_k2_then shr_k2_else]) =
       execWithEnv (fun _ => none) 34 s (shr_k2_prefix ++ [.ifElse shr_k2_then shr_k2_else])
  rw [execWithEnv_append, execWithEnv_append]
  have hpre := execWithEnv_pure_inst u128ProcEnv (fun _ => none) fuel 34 s shr_k2_prefix
    (by omega) (by omega) shr_k2_prefix_pure
  rw [hpre]
  cases execWithEnv (fun _ => none) 34 s shr_k2_prefix with
  | none => rfl
  | some s' =>
    dsimp only [bind, Bind.bind, Option.bind]
    exact execWithEnv_ifElse_pure_inst u128ProcEnv (fun _ => none) fuel 34 s'
      shr_k2_then shr_k2_else (by omega) (by omega) shr_k2_then_pure shr_k2_else_pure

-- ============================================================================
-- ifElse dispatch helpers
-- ============================================================================

private theorem execWithEnv_ifElse_one
    (env : ProcEnv) (fuel : Nat)
    (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (thenBlk elseBlk : List Op) :
    execWithEnv env (fuel + 2)
      ⟨(1 : Felt) :: rest, mem, locs, adv⟩
      [.ifElse thenBlk elseBlk] =
    execWithEnv env (fuel + 1) ⟨rest, mem, locs, adv⟩ thenBlk := by
  conv_lhs => unfold execWithEnv
  simp only [List.foldlM, MidenState.withStack]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  have hv1 : (1 : Felt).val = 1 := Felt.val_one'
  have hbeq : ((1 : Nat) == 1) = true := by decide
  simp only [hv1, hbeq, ↓reduceIte]
  cases execWithEnv env (fuel + 1) ⟨rest, mem, locs, adv⟩ thenBlk <;> rfl

private theorem execWithEnv_ifElse_zero
    (env : ProcEnv) (fuel : Nat)
    (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (thenBlk elseBlk : List Op) :
    execWithEnv env (fuel + 2)
      ⟨(0 : Felt) :: rest, mem, locs, adv⟩
      [.ifElse thenBlk elseBlk] =
    execWithEnv env (fuel + 1) ⟨rest, mem, locs, adv⟩ elseBlk := by
  conv_lhs => unfold execWithEnv
  simp only [List.foldlM, MidenState.withStack]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  have hv0 : (0 : Felt).val = 0 := Felt.val_zero'
  have hneq : ((0 : Nat) == 1) = false := by decide
  have hbeq : ((0 : Nat) == 0) = true := by decide
  simp only [hv0, hneq, hbeq, ↓reduceIte]
  cases execWithEnv env (fuel + 1) ⟨rest, mem, locs, adv⟩ elseBlk <;> rfl

-- ============================================================================
-- Decomposition of shr
-- ============================================================================

private def shr_prefix : List Op := [
  .inst (.dup 0), .inst (.push 128), .inst (.u32Lt),
  .inst (.assertWithError "shift amount must be in the range [0, 128)"),
  .inst (.dup 0), .inst (.eqImm 0)]

private def shr_nonzero_setup : List Op := [
  .inst (.dup 0), .inst (.push 31), .inst (.u32And),
  .inst (.swap 1), .inst (.push 5), .inst (.u32Shr)]

private def shr_k0_ops : List Op := [.inst (.drop), .inst (.exec "shr_k0")]
private def shr_k1_ops : List Op := [.inst (.drop), .inst (.push 0), .inst (.movdn 5), .inst (.exec "shr_k1")]
private def shr_k2_ops : List Op := [.inst (.drop), .inst (.push 0), .inst (.movdn 5),
  .inst (.push 0), .inst (.movdn 5), .inst (.exec "shr_k2")]
private def shr_k3_ops : List Op := [.inst (.drop), .inst (.push 0), .inst (.movdn 5),
  .inst (.push 0), .inst (.movdn 5), .inst (.push 0), .inst (.movdn 5), .inst (.exec "shr_k3")]

private def shr_k_dispatch : List Op :=
  [.inst (.dup 0), .inst (.eqImm 0),
   .ifElse shr_k0_ops
   [.inst (.dup 0), .inst (.eqImm 1),
    .ifElse shr_k1_ops
    [.inst (.dup 0), .inst (.eqImm 2),
     .ifElse shr_k2_ops shr_k3_ops]]]

private theorem shr_decomp :
    Miden.Core.U128.shr =
    shr_prefix ++ [.ifElse [.inst (.drop)]
      (shr_nonzero_setup ++ shr_k_dispatch)] := by
  simp [Miden.Core.U128.shr, shr_prefix, shr_nonzero_setup, shr_k_dispatch,
        shr_k0_ops, shr_k1_ops, shr_k2_ops, shr_k3_ops]

-- ============================================================================
-- Prefix correctness
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem shr_prefix_correct (env : ProcEnv) (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true)
    (hshift_lt128 : shift.val < 128) :
    execWithEnv env (fuel + 1)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      shr_prefix =
    some ⟨(if shift == (0 : Felt) then (1 : Felt) else 0) ::
          shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩ := by
  unfold shr_prefix execWithEnv
  simp only [List.foldlM]
  dsimp only [bind, Bind.bind, Option.bind]
  miden_dup
  miden_step -- push 128
  rw [stepU32Lt (ha := hshift_u32) (hb := U32.felt128_isU32)]
  miden_bind
  simp only [felt128_val]
  rw [stepAssertWithError (h := by simp [hshift_lt128, Felt.val_one'])]
  miden_bind
  miden_dup
  rw [stepEqImm]
  simp [pure, Pure.pure]

-- ============================================================================
-- Nonzero setup correctness
-- ============================================================================

set_option maxHeartbeats 4000000 in
private theorem shr_nonzero_setup_correct (env : ProcEnv) (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      shr_nonzero_setup =
    some ⟨Felt.ofNat (shift.val / 2 ^ 5) :: Felt.ofNat (shift.val &&& 31) ::
          a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩ := by
  unfold shr_nonzero_setup execWithEnv
  simp only [List.foldlM]
  dsimp only [bind, Bind.bind, Option.bind]
  miden_dup
  miden_step -- push 31
  rw [stepU32And (ha := hshift_u32) (hb := U32.felt31_isU32)]
  miden_bind
  simp only [felt31_val]
  miden_swap
  miden_step -- push 5
  rw [stepU32ShrLocal (ha := hshift_u32) (hb := U32.felt5_isU32) (hshift := by rw [felt5_val]; omega)]
  miden_bind
  simp only [felt5_val]
  simp [pure, Pure.pure]

-- ============================================================================
-- Per-branch correctness: k = 0
-- ============================================================================

set_option maxHeartbeats 8000000 in
private theorem shr_branch_k0 (fuel : Nat)
    (k b a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hb_u32 : b.isU32 = true)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb_le31 : b.val ≤ 31) (hb_pos : 0 < b.val) :
    execWithEnv u128ProcEnv (fuel + 2)
      ⟨k :: b :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      shr_k0_ops =
    some ⟨Felt.ofNat ((a0.val / 2 ^ b.val) ||| ((a1.val * 2 ^ (32 - b.val)) % 2 ^ 32)) ::
      Felt.ofNat ((a1.val / 2 ^ b.val) ||| ((a2.val * 2 ^ (32 - b.val)) % 2 ^ 32)) ::
      Felt.ofNat ((a2.val / 2 ^ b.val) ||| ((a3.val * 2 ^ (32 - b.val)) % 2 ^ 32)) ::
      Felt.ofNat (a3.val / 2 ^ b.val) :: rest, mem, locs, adv⟩ := by
  unfold shr_k0_ops
  conv_lhs => unfold execWithEnv
  simp only [List.foldlM, u128ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  rw [stepDrop]
  simp only []
  -- Now: execWithEnv u128ProcEnv (fuel+1) ⟨b :: a0 :: a1 :: a2 :: a3 :: rest, ...⟩ shr_k0
  rw [shr_k0_env_bridge (fuel + 1) _ (by omega)]
  -- Now: exec 51 ⟨b :: a0 :: ...⟩ shr_k0
  have h := u128_shr_k0_raw b a0 a1 a2 a3 rest
    ⟨b :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
    rfl hb_u32 ha0 ha1 ha2 ha3 hb_pos hb_le31
  simp only [MidenState.withStack] at h
  -- Goal has the form: match (exec 51 ...), fun s => some s with | ...
  -- Need to simplify the match-pure pattern
  rw [h]

-- ============================================================================
-- Per-branch correctness: k = 1
-- ============================================================================

set_option maxHeartbeats 8000000 in
private theorem shr_branch_k1 (fuel : Nat)
    (k b a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hb_u32 : b.isU32 = true)
    (ha1 : a1.isU32 = true) (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb_le31 : b.val ≤ 31) :
    execWithEnv u128ProcEnv (fuel + 3)
      ⟨k :: b :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      shr_k1_ops =
    some ⟨(if b == (0 : Felt) then
        a1 :: a2 :: a3 :: (0 : Felt) :: rest
      else
        let pow := 2 ^ (32 - b.val)
        Felt.ofNat ((a1.val / 2 ^ b.val) ||| ((a2.val * pow) % 4294967296)) ::
        Felt.ofNat ((a2.val / 2 ^ b.val) ||| ((a3.val * pow) % 4294967296)) ::
        Felt.ofNat (a3.val / 2 ^ b.val) :: (0 : Felt) :: rest),
      mem, locs, adv⟩ := by
  unfold shr_k1_ops
  conv_lhs => unfold execWithEnv
  simp only [List.foldlM, u128ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  rw [stepDrop]
  simp only []
  rw [stepPush]
  simp only []
  miden_movdn
  -- Stack: b :: a0 :: a1 :: a2 :: a3 :: 0 :: rest
  rw [shr_k1_env_bridge (fuel + 2) _ (by omega)]
  have h := u128_shr_k1_raw b a0 a1 a2 a3
    ((0 : Felt) :: rest)
    ⟨b :: a0 :: a1 :: a2 :: a3 :: (0 : Felt) :: rest, mem, locs, adv⟩
    rfl hb_u32 ha1 ha2 ha3 hb_le31
  simp only [MidenState.withStack] at h
  rw [h]

-- ============================================================================
-- Per-branch correctness: k = 2
-- ============================================================================

set_option maxHeartbeats 8000000 in
private theorem shr_branch_k2 (fuel : Nat)
    (k b a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hb_u32 : b.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb_le31 : b.val ≤ 31) :
    execWithEnv u128ProcEnv (fuel + 3)
      ⟨k :: b :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      shr_k2_ops =
    some ⟨(if b == (0 : Felt) then
        a2 :: a3 :: (0 : Felt) :: (0 : Felt) :: rest
      else
        let pow := 2 ^ (32 - b.val)
        Felt.ofNat ((a2.val / 2 ^ b.val) ||| ((a3.val * pow) % 4294967296)) ::
        Felt.ofNat (a3.val / 2 ^ b.val) :: (0 : Felt) :: (0 : Felt) :: rest),
      mem, locs, adv⟩ := by
  unfold shr_k2_ops
  conv_lhs => unfold execWithEnv
  simp only [List.foldlM, u128ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  rw [stepDrop]
  simp only []
  rw [stepPush]
  simp only []
  miden_movdn
  rw [stepPush]
  simp only []
  miden_movdn
  -- Stack: b :: a0 :: a1 :: a2 :: a3 :: 0 :: 0 :: rest
  rw [shr_k2_env_bridge (fuel + 2) _ (by omega)]
  have h := u128_shr_k2_raw b a0 a1 a2 a3
    ((0 : Felt) :: (0 : Felt) :: rest)
    ⟨b :: a0 :: a1 :: a2 :: a3 :: (0 : Felt) :: (0 : Felt) :: rest, mem, locs, adv⟩
    rfl hb_u32 ha2 ha3 hb_le31
  simp only [MidenState.withStack] at h
  rw [h]

-- ============================================================================
-- Per-branch correctness: k = 3
-- ============================================================================

set_option maxHeartbeats 8000000 in
private theorem shr_branch_k3 (fuel : Nat)
    (k b a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hb_u32 : b.isU32 = true) (ha3 : a3.isU32 = true)
    (hb_le31 : b.val ≤ 31) :
    execWithEnv u128ProcEnv (fuel + 2)
      ⟨k :: b :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      shr_k3_ops =
    some ⟨Felt.ofNat (a3.val / 2 ^ b.val) ::
      (0 : Felt) :: (0 : Felt) :: (0 : Felt) :: rest,
      mem, locs, adv⟩ := by
  unfold shr_k3_ops
  conv_lhs => unfold execWithEnv
  simp only [List.foldlM, u128ProcEnv]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  rw [stepDrop]
  simp only []
  rw [stepPush]
  simp only []
  miden_movdn
  rw [stepPush]
  simp only []
  miden_movdn
  rw [stepPush]
  simp only []
  miden_movdn
  -- Stack: b :: a0 :: a1 :: a2 :: a3 :: 0 :: 0 :: 0 :: rest
  rw [shr_k3_env_bridge (fuel + 1) _ (by omega)]
  have h := u128_shr_k3_raw b a0 a1 a2 a3
    ((0 : Felt) :: (0 : Felt) :: (0 : Felt) :: rest)
    ⟨b :: a0 :: a1 :: a2 :: a3 :: (0 : Felt) :: (0 : Felt) :: (0 : Felt) :: rest, mem, locs, adv⟩
    rfl hb_u32 ha3 hb_le31
  simp only [MidenState.withStack] at h
  rw [h]

-- ============================================================================
-- Dispatch stepping helpers
-- ============================================================================

private theorem and31_pos_of_pos_lt32 (n : Nat) (hpos : 0 < n) (hlt : n < 32) :
    0 < n &&& 31 := by
  have h31 : (31 : Nat) = 2 ^ 5 - 1 := by norm_num
  rw [h31, Nat.and_two_pow_sub_one_eq_mod]
  omega

private theorem dup_eqImm_eval (env : ProcEnv) (fuel : Nat) (v : Felt)
    (a : Felt) (rest : List Felt) (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv env (fuel + 1) ⟨a :: rest, mem, locs, adv⟩
      [.inst (.dup 0), .inst (.eqImm v)] =
    some ⟨(if a == v then (1 : Felt) else 0) :: a :: rest, mem, locs, adv⟩ := by
  conv_lhs => unfold execWithEnv
  simp only [List.foldlM]
  dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
  miden_dup
  rw [stepEqImm]

private theorem felt_beq_false_of_val_ne (a b : Felt) (h : a.val ≠ b.val) :
    (a == b) = false := by
  rw [beq_eq_false_iff_ne]; intro heq; exact h (congr_arg ZMod.val heq)

-- Dispatch sub-lists and decomposition
private def dispatch_else_1 : List Op :=
  [.inst (.dup 0), .inst (.eqImm 1),
   .ifElse shr_k1_ops
   [.inst (.dup 0), .inst (.eqImm 2), .ifElse shr_k2_ops shr_k3_ops]]

private def dispatch_else_2 : List Op :=
  [.inst (.dup 0), .inst (.eqImm 2), .ifElse shr_k2_ops shr_k3_ops]

private theorem dispatch_decomp_0 :
    shr_k_dispatch = [.inst (.dup 0), .inst (.eqImm 0)] ++
      [.ifElse shr_k0_ops dispatch_else_1] := by
  simp [shr_k_dispatch, dispatch_else_1]

private theorem dispatch_decomp_1 :
    dispatch_else_1 = [.inst (.dup 0), .inst (.eqImm 1)] ++
      [.ifElse shr_k1_ops dispatch_else_2] := by
  simp [dispatch_else_1, dispatch_else_2]

private theorem dispatch_decomp_2 :
    dispatch_else_2 = [.inst (.dup 0), .inst (.eqImm 2)] ++
      [.ifElse shr_k2_ops shr_k3_ops] := by
  simp [dispatch_else_2]

-- ============================================================================
-- Composition: u128_shr_run
-- ============================================================================

set_option maxHeartbeats 16000000 in
private theorem u128_shr_run (fuel : Nat)
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (hshift_u32 : shift.isU32 = true)
    (hshift_lt128 : shift.val < 128)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true) :
    let b := Felt.ofNat (shift.val &&& 31)
    let k := Felt.ofNat (shift.val / 32)
    execWithEnv u128ProcEnv (fuel + 7)
      ⟨shift :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      Miden.Core.U128.shr =
    (if shift == (0 : Felt) then
      some ⟨a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
    else if k == (0 : Felt) then
      some ⟨Felt.ofNat ((a0.val / 2 ^ b.val) ||| ((a1.val * 2 ^ (32 - b.val)) % 2 ^ 32)) ::
        Felt.ofNat ((a1.val / 2 ^ b.val) ||| ((a2.val * 2 ^ (32 - b.val)) % 2 ^ 32)) ::
        Felt.ofNat ((a2.val / 2 ^ b.val) ||| ((a3.val * 2 ^ (32 - b.val)) % 2 ^ 32)) ::
        Felt.ofNat (a3.val / 2 ^ b.val) :: rest, mem, locs, adv⟩
    else if k == (1 : Felt) then
      some ⟨(if b == 0 then
          a1 :: a2 :: a3 :: (0 : Felt) :: rest
        else
          Felt.ofNat ((a1.val / 2 ^ b.val) ||| ((a2.val * 2 ^ (32 - b.val)) % 4294967296)) ::
          Felt.ofNat ((a2.val / 2 ^ b.val) ||| ((a3.val * 2 ^ (32 - b.val)) % 4294967296)) ::
          Felt.ofNat (a3.val / 2 ^ b.val) :: (0 : Felt) :: rest),
        mem, locs, adv⟩
    else if k == (2 : Felt) then
      some ⟨(if b == 0 then
          a2 :: a3 :: (0 : Felt) :: (0 : Felt) :: rest
        else
          Felt.ofNat ((a2.val / 2 ^ b.val) ||| ((a3.val * 2 ^ (32 - b.val)) % 4294967296)) ::
          Felt.ofNat (a3.val / 2 ^ b.val) :: (0 : Felt) :: (0 : Felt) :: rest),
        mem, locs, adv⟩
    else
      some ⟨Felt.ofNat (a3.val / 2 ^ b.val) ::
        (0 : Felt) :: (0 : Felt) :: (0 : Felt) :: rest, mem, locs, adv⟩) := by
  -- Step 1: decompose shr
  rw [shr_decomp, execWithEnv_append]
  rw [shr_prefix_correct u128ProcEnv (fuel + 6) shift a0 a1 a2 a3 rest mem locs adv
    hshift_u32 hshift_lt128]
  simp only [bind, Bind.bind, Option.bind]
  -- Step 2: case split on shift == 0
  by_cases hzero : shift == (0 : Felt)
  · -- shift == 0: take the true branch (drop)
    simp only [hzero, ↓reduceIte]
    rw [execWithEnv_ifElse_one]
    conv_lhs => unfold execWithEnv
    simp only [List.foldlM]
    dsimp only [bind, Bind.bind, Option.bind, pure, Pure.pure]
    rw [stepDrop]
  · -- shift != 0: take the false branch (nonzero setup + dispatch)
    simp only [hzero, ↓reduceIte, Bool.false_eq_true]
    rw [execWithEnv_ifElse_zero]
    rw [execWithEnv_append]
    rw [shr_nonzero_setup_correct u128ProcEnv (fuel + 5) shift a0 a1 a2 a3 rest mem locs adv
      hshift_u32]
    simp only [bind, Bind.bind, Option.bind]
    -- Now dispatch on k = shift.val / 32
    -- State: k :: b :: a0 :: a1 :: a2 :: a3 :: rest
    -- where k = Felt.ofNat (shift.val / 2^5), b = Felt.ofNat (shift.val &&& 31)
    have hk_eq : shift.val / 2 ^ 5 = shift.val / 32 := by norm_num
    rw [hk_eq]
    -- Case split on k value
    have hshift_pos : 0 < shift.val := by
      by_contra h; push_neg at h
      have h0 : shift.val = 0 := by omega
      exact hzero (beq_iff_eq.mpr ((ZMod.val_eq_zero shift).mp h0))
    have hk_lt4 : shift.val / 32 < 4 := by omega
    -- Level 0 dispatch: dup 0, eqImm 0, ifElse k0 else1
    rw [dispatch_decomp_0, execWithEnv_append]
    rw [dup_eqImm_eval]
    simp only [bind, Bind.bind, Option.bind]
    cases hk0 : (Felt.ofNat (shift.val / 32) == (0 : Felt))
    · -- k != 0, take else branch
      simp only [Bool.false_eq_true, ite_false]
      rw [execWithEnv_ifElse_zero]
      -- Level 1 dispatch: dup 0, eqImm 1, ifElse k1 else2
      rw [dispatch_decomp_1, execWithEnv_append]
      rw [dup_eqImm_eval]
      simp only [bind, Bind.bind, Option.bind]
      cases hk1 : (Felt.ofNat (shift.val / 32) == (1 : Felt))
      · -- k != 1, take else branch
        simp only [Bool.false_eq_true, ite_false]
        rw [execWithEnv_ifElse_zero]
        -- Level 2 dispatch: dup 0, eqImm 2, ifElse k2 k3
        rw [dispatch_decomp_2, execWithEnv_append]
        rw [dup_eqImm_eval]
        simp only [bind, Bind.bind, Option.bind]
        cases hk2 : (Felt.ofNat (shift.val / 32) == (2 : Felt))
        · -- k != 2, must be k = 3 → take else branch (k3)
          simp only [Bool.false_eq_true, ite_false]
          rw [execWithEnv_ifElse_zero]
          exact shr_branch_k3 (fuel + 1)
            (Felt.ofNat (shift.val / 32)) (Felt.ofNat (shift.val &&& 31))
            a0 a1 a2 a3 rest mem locs adv
            (u32and31_isU32 shift) ha3 (u32and31_le31 shift)
        · -- k == 2 → take true branch (k2)
          simp only [↓reduceIte]
          rw [execWithEnv_ifElse_one]
          exact shr_branch_k2 fuel
            (Felt.ofNat (shift.val / 32)) (Felt.ofNat (shift.val &&& 31))
            a0 a1 a2 a3 rest mem locs adv
            (u32and31_isU32 shift) ha2 ha3 (u32and31_le31 shift)
      · -- k == 1 → take true branch (k1)
        simp only [↓reduceIte]
        rw [execWithEnv_ifElse_one]
        exact shr_branch_k1 (fuel + 1)
          (Felt.ofNat (shift.val / 32)) (Felt.ofNat (shift.val &&& 31))
          a0 a1 a2 a3 rest mem locs adv
          (u32and31_isU32 shift) ha1 ha2 ha3 (u32and31_le31 shift)
    · -- k == 0 → take true branch (k0)
      simp only [↓reduceIte]
      rw [execWithEnv_ifElse_one]
      have hb_pos : 0 < (Felt.ofNat (shift.val &&& 31)).val := by
        rw [and31_val]
        have hk0_nat : shift.val / 32 = 0 := by
          have heq := beq_iff_eq.mp hk0
          have hval := congr_arg ZMod.val heq
          rw [felt_ofNat_val_lt _ (show shift.val / 32 < GOLDILOCKS_PRIME by
            unfold GOLDILOCKS_PRIME; omega), Felt.val_zero'] at hval
          exact hval
        exact and31_pos_of_pos_lt32 shift.val hshift_pos (by omega)
      exact shr_branch_k0 (fuel + 3)
        (Felt.ofNat (shift.val / 32)) (Felt.ofNat (shift.val &&& 31))
        a0 a1 a2 a3 rest mem locs adv
        (u32and31_isU32 shift) ha0 ha1 ha2 ha3 (u32and31_le31 shift) hb_pos

-- ============================================================================
-- Main correctness theorem
-- ============================================================================

set_option maxHeartbeats 16000000 in
/-- `u128::shr` correctly computes the right shift of a 128-bit value by a given
    amount. Input stack: [shift, a0, a1, a2, a3] ++ rest (shift < 128, a0..a3
    are u32 limbs low-to-high). Dispatches to shr_k0..k3 based on
    k = shift / 32, with b = shift % 32 as the sub-limb shift. -/
theorem u128_shr_raw
    (shift a0 a1 a2 a3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = shift :: a0 :: a1 :: a2 :: a3 :: rest)
    (hshift_u32 : shift.isU32 = true)
    (hshift_lt128 : shift.val < 128)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true) :
    let b := Felt.ofNat (shift.val &&& 31)
    let k := Felt.ofNat (shift.val / 32)
    execWithEnv u128ProcEnv 10 s Miden.Core.U128.shr =
    (if shift == (0 : Felt) then
      some (s.withStack (a0 :: a1 :: a2 :: a3 :: rest))
    else if k == (0 : Felt) then
      some (s.withStack (
        Felt.ofNat ((a0.val / 2 ^ b.val) ||| ((a1.val * 2 ^ (32 - b.val)) % 2 ^ 32)) ::
        Felt.ofNat ((a1.val / 2 ^ b.val) ||| ((a2.val * 2 ^ (32 - b.val)) % 2 ^ 32)) ::
        Felt.ofNat ((a2.val / 2 ^ b.val) ||| ((a3.val * 2 ^ (32 - b.val)) % 2 ^ 32)) ::
        Felt.ofNat (a3.val / 2 ^ b.val) :: rest))
    else if k == (1 : Felt) then
      some (s.withStack (
        if b == 0 then
          a1 :: a2 :: a3 :: (0 : Felt) :: rest
        else
          Felt.ofNat ((a1.val / 2 ^ b.val) ||| ((a2.val * 2 ^ (32 - b.val)) % 4294967296)) ::
          Felt.ofNat ((a2.val / 2 ^ b.val) ||| ((a3.val * 2 ^ (32 - b.val)) % 4294967296)) ::
          Felt.ofNat (a3.val / 2 ^ b.val) :: (0 : Felt) :: rest))
    else if k == (2 : Felt) then
      some (s.withStack (
        if b == 0 then
          a2 :: a3 :: (0 : Felt) :: (0 : Felt) :: rest
        else
          Felt.ofNat ((a2.val / 2 ^ b.val) ||| ((a3.val * 2 ^ (32 - b.val)) % 4294967296)) ::
          Felt.ofNat (a3.val / 2 ^ b.val) :: (0 : Felt) :: (0 : Felt) :: rest))
    else
      some (s.withStack (
        Felt.ofNat (a3.val / 2 ^ b.val) ::
        (0 : Felt) :: (0 : Felt) :: (0 : Felt) :: rest))) := by
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  have h := u128_shr_run 3 shift a0 a1 a2 a3 rest mem locs adv
    hshift_u32 hshift_lt128 ha0 ha1 ha2 ha3
  simpa using h

end MidenLean.Proofs
