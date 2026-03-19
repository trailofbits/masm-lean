import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.Tactics
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- Execute a concatenation of op lists in two phases. -/
private theorem execWithEnv_append (env : ProcEnv) (fuel : Nat) (s : MidenState) (xs ys : List Op) :
    execWithEnv env fuel s (xs ++ ys) = (do
      let s' ← execWithEnv env fuel s xs
      execWithEnv env fuel s' ys) := by
  unfold execWithEnv
  cases fuel <;> simp [List.foldlM_append]

private def sub0 (a0 b0 : Felt) : Nat × Nat :=
  u32OverflowingSub a0.val b0.val

private def sub1 (a1 b1 : Felt) : Nat × Nat :=
  u32OverflowingSub a1.val b1.val

private def sub1Adj (a0 a1 b0 b1 : Felt) : Nat × Nat :=
  u32OverflowingSub (sub1 a1 b1).2 (sub0 a0 b0).1

private def borrow1 (a0 a1 b0 b1 : Felt) : Felt :=
  if decide ((sub1 a1 b1).2 < (sub0 a0 b0).1) || decide (a1.val < b1.val) then 1 else 0

private def sub2 (a2 b2 : Felt) : Nat × Nat :=
  u32OverflowingSub a2.val b2.val

private def sub2Adj (a0 a1 a2 b0 b1 b2 : Felt) : Nat × Nat :=
  u32OverflowingSub (sub2 a2 b2).2 (borrow1 a0 a1 b0 b1).val

private def borrow2 (a0 a1 a2 b0 b1 b2 : Felt) : Felt :=
  if decide ((sub2 a2 b2).2 < (borrow1 a0 a1 b0 b1).val) || decide (a2.val < b2.val) then 1 else 0

private def sub3 (a3 b3 : Felt) : Nat × Nat :=
  u32OverflowingSub a3.val b3.val

private def sub3Adj (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) : Nat × Nat :=
  u32OverflowingSub (sub3 a3 b3).2 (borrow2 a0 a1 a2 b0 b1 b2).val

private def borrow3 (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) : Felt :=
  if decide ((sub3 a3 b3).2 < (borrow2 a0 a1 a2 b0 b1 b2).val) || decide (a3.val < b3.val) then
    1
  else
    0

private theorem boolFelt_isU32 (p : Bool) : (if p then (1 : Felt) else 0).isU32 = true := by
  cases p <;> simp [Felt.isU32]

private def stage1a (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) : List Felt :=
  Felt.ofNat (sub0 a0 b0).1 ::
  Felt.ofNat (sub0 a0 b0).2 ::
  a1 :: a2 :: a3 :: b1 :: b2 :: b3 :: rest

private def stage1b (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) : List Felt :=
  Felt.ofNat (sub1 a1 b1).1 ::
  Felt.ofNat (sub1 a1 b1).2 ::
  Felt.ofNat (sub0 a0 b0).2 ::
  a2 :: a3 :: b2 :: b3 :: Felt.ofNat (sub0 a0 b0).1 :: rest

private def stage1c (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) : List Felt :=
  Felt.ofNat (sub1Adj a0 a1 b0 b1).1 ::
  Felt.ofNat (sub1Adj a0 a1 b0 b1).2 ::
  Felt.ofNat (sub1 a1 b1).1 ::
  Felt.ofNat (sub0 a0 b0).2 ::
  a2 :: a3 :: b2 :: b3 :: rest

private def stage2a (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) : List Felt :=
  Felt.ofNat (sub2 a2 b2).1 ::
  Felt.ofNat (sub2 a2 b2).2 ::
  Felt.ofNat (sub1Adj a0 a1 b0 b1).2 ::
  Felt.ofNat (sub0 a0 b0).2 ::
  a3 :: b3 :: borrow1 a0 a1 b0 b1 :: rest

private def stage2b (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) : List Felt :=
  Felt.ofNat (sub2Adj a0 a1 a2 b0 b1 b2).1 ::
  Felt.ofNat (sub2Adj a0 a1 a2 b0 b1 b2).2 ::
  Felt.ofNat (sub2 a2 b2).1 ::
  Felt.ofNat (sub1Adj a0 a1 b0 b1).2 ::
  Felt.ofNat (sub0 a0 b0).2 ::
  a3 :: b3 :: rest

private def stage3a (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) : List Felt :=
  Felt.ofNat (sub3 a3 b3).1 ::
  Felt.ofNat (sub3 a3 b3).2 ::
  Felt.ofNat (sub2Adj a0 a1 a2 b0 b1 b2).2 ::
  Felt.ofNat (sub1Adj a0 a1 b0 b1).2 ::
  Felt.ofNat (sub0 a0 b0).2 ::
  borrow2 a0 a1 a2 b0 b1 b2 :: rest

private def stage3b (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) : List Felt :=
  Felt.ofNat (sub3Adj a0 a1 a2 a3 b0 b1 b2 b3).1 ::
  Felt.ofNat (sub3Adj a0 a1 a2 a3 b0 b1 b2 b3).2 ::
  Felt.ofNat (sub3 a3 b3).1 ::
  Felt.ofNat (sub2Adj a0 a1 a2 b0 b1 b2).2 ::
  Felt.ofNat (sub1Adj a0 a1 b0 b1).2 ::
  Felt.ofNat (sub0 a0 b0).2 :: rest

def u128OverflowingSubResult
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) : List Felt :=
  (if u128LtBool a0 a1 a2 a3 b0 b1 b2 b3 then (1 : Felt) else 0) ::
  Felt.ofNat (sub0 a0 b0).2 ::
  Felt.ofNat (sub1Adj a0 a1 b0 b1).2 ::
  Felt.ofNat (sub2Adj a0 a1 a2 b0 b1 b2).2 ::
  Felt.ofNat (sub3Adj a0 a1 a2 a3 b0 b1 b2 b3).2 :: rest

def u128WrappingSubResult
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) : List Felt :=
  Felt.ofNat (sub0 a0 b0).2 ::
  Felt.ofNat (sub1Adj a0 a1 b0 b1).2 ::
  Felt.ofNat (sub2Adj a0 a1 a2 b0 b1 b2).2 ::
  Felt.ofNat (sub3Adj a0 a1 a2 a3 b0 b1 b2 b3).2 :: rest

private def chunk1 : List Op := [
  .inst (.movup 7),
  .inst (.movup 7),
  .inst (.movup 7),
  .inst (.movup 7),
  .inst (.movup 4),
  .inst (.u32OverflowSub)
]

private def chunk2 : List Op := [
  .inst (.movdn 7),
  .inst (.movup 4),
  .inst (.movup 2),
  .inst (.swap 1),
  .inst (.u32OverflowSub)
]

private def chunk3 : List Op := [
  .inst (.movup 7),
  .inst (.movup 2),
  .inst (.swap 1),
  .inst (.u32OverflowSub)
]

private def chunk4 : List Op := [
  .inst (.movup 2),
  .inst (.or),
  .inst (.movdn 6),
  .inst (.movup 4),
  .inst (.movup 3),
  .inst (.swap 1),
  .inst (.u32OverflowSub)
]

private def chunk5 : List Op := [
  .inst (.movup 6),
  .inst (.movup 2),
  .inst (.swap 1),
  .inst (.u32OverflowSub)
]

private def chunk6 : List Op := [
  .inst (.movup 2),
  .inst (.or),
  .inst (.movdn 5),
  .inst (.movup 4),
  .inst (.movup 4),
  .inst (.swap 1),
  .inst (.u32OverflowSub)
]

private def chunk7 : List Op := [
  .inst (.movup 5),
  .inst (.movup 2),
  .inst (.swap 1),
  .inst (.u32OverflowSub)
]

private def chunk8 : List Op := [
  .inst (.movup 2),
  .inst (.or),
  .inst (.movdn 4),
  .inst (.movdn 3),
  .inst (.movdn 2),
  .inst (.swap 1),
  .inst (.movup 4)
]

private theorem overflowing_sub_decomp :
    Miden.Core.U128.overflowing_sub =
      chunk1 ++ (chunk2 ++ (chunk3 ++ (chunk4 ++ (chunk5 ++ (chunk6 ++ (chunk7 ++ chunk8)))))) := by
  simp [Miden.Core.U128.overflowing_sub, chunk1, chunk2, chunk3, chunk4, chunk5, chunk6, chunk7,
    chunk8]

private theorem chunk1_correct
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (ha0 : a0.isU32 = true) (hb0 : b0.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv, evts⟩
      chunk1 =
    some ⟨stage1a a0 a1 a2 a3 b0 b1 b2 b3 rest, mem, locs, adv, evts⟩ := by
  unfold chunk1 execWithEnv
  simp only [List.foldlM]
  miden_movup
  miden_movup
  miden_movup
  miden_movup
  miden_movup
  rw [stepU32OverflowSub (ha := ha0) (hb := hb0)]
  miden_bind
  simp only [stage1a, sub0]
  dsimp only [pure, Pure.pure]

private theorem chunk2_correct
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (ha1 : a1.isU32 = true) (hb1 : b1.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨stage1a a0 a1 a2 a3 b0 b1 b2 b3 rest, mem, locs, adv, evts⟩
      chunk2 =
    some ⟨stage1b a0 a1 a2 a3 b0 b1 b2 b3 rest, mem, locs, adv, evts⟩ := by
  unfold stage1a chunk2 execWithEnv
  simp only [List.foldlM]
  miden_movdn
  miden_movup
  miden_movup
  miden_swap
  rw [stepU32OverflowSub (ha := ha1) (hb := hb1)]
  miden_bind
  simp only [stage1b, sub1, sub0]
  dsimp only [pure, Pure.pure]

private theorem chunk3_correct
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (ha1 : a1.isU32 = true) (hb1 : b1.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨stage1b a0 a1 a2 a3 b0 b1 b2 b3 rest, mem, locs, adv, evts⟩
      chunk3 =
    some ⟨stage1c a0 a1 a2 a3 b0 b1 b2 b3 rest, mem, locs, adv, evts⟩ := by
  unfold stage1b chunk3 execWithEnv
  simp only [List.foldlM]
  have ha1_lt : a1.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using ha1
  have hb1_lt : b1.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb1
  have hsub1_val :
      (Felt.ofNat (sub1 a1 b1).2).val = (sub1 a1 b1).2 :=
    felt_ofNat_val_lt _ (u32_overflow_sub_snd_lt _ _ (ZMod.val_lt a1) (ZMod.val_lt b1))
  have hsub0_borrow_val :
      (Felt.ofNat (sub0 a0 b0).1).val = (sub0 a0 b0).1 :=
    felt_ofNat_val_lt _ (u32_overflow_sub_fst_lt _ _)
  have hsub1_isU32 : (Felt.ofNat (sub1 a1 b1).2).isU32 = true :=
    u32OverflowingSub_snd_isU32 _ _ ha1_lt hb1_lt
  have hsub0_borrow_isU32 : (Felt.ofNat (sub0 a0 b0).1).isU32 = true :=
    u32OverflowingSub_fst_isU32 _ _
  miden_movup
  miden_movup
  miden_swap
  rw [stepU32OverflowSub (ha := hsub1_isU32) (hb := hsub0_borrow_isU32)]
  miden_bind
  rw [hsub1_val, hsub0_borrow_val]
  simp only [stage1c, sub1Adj, sub1, sub0]
  dsimp only [pure, Pure.pure]

private theorem chunk4_correct
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (ha2 : a2.isU32 = true) (hb2 : b2.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨stage1c a0 a1 a2 a3 b0 b1 b2 b3 rest, mem, locs, adv, evts⟩
      chunk4 =
    some ⟨stage2a a0 a1 a2 a3 b0 b1 b2 b3 rest, mem, locs, adv, evts⟩ := by
  unfold stage1c chunk4 execWithEnv
  simp only [List.foldlM]
  unfold sub1Adj sub1 sub0
  miden_movup
  rw [u32OverflowingSub_borrow_ite (u32OverflowingSub a1.val b1.val).2
      (u32OverflowingSub a0.val b0.val).1]
  rw [u32OverflowingSub_borrow_ite a1.val b1.val]
  rw [stepOrIte]
  miden_bind
  miden_movdn
  miden_movup
  miden_movup
  miden_swap
  rw [stepU32OverflowSub (ha := ha2) (hb := hb2)]
  miden_bind
  simp only [stage2a, borrow1, sub2, sub1Adj, sub1, sub0]
  dsimp only [pure, Pure.pure]

private theorem chunk5_correct
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (ha2 : a2.isU32 = true) (hb2 : b2.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨stage2a a0 a1 a2 a3 b0 b1 b2 b3 rest, mem, locs, adv, evts⟩
      chunk5 =
    some ⟨stage2b a0 a1 a2 a3 b0 b1 b2 b3 rest, mem, locs, adv, evts⟩ := by
  unfold stage2a chunk5 execWithEnv
  simp only [List.foldlM]
  have ha2_lt : a2.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using ha2
  have hb2_lt : b2.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb2
  have hborrow1_isU32 : (borrow1 a0 a1 b0 b1).isU32 = true := by
    simpa [borrow1] using
      boolFelt_isU32 (decide ((sub1 a1 b1).2 < (sub0 a0 b0).1) || decide (a1.val < b1.val))
  have hsub2_val :
      (Felt.ofNat (sub2 a2 b2).2).val = (sub2 a2 b2).2 :=
    felt_ofNat_val_lt _ (u32_overflow_sub_snd_lt _ _ (ZMod.val_lt a2) (ZMod.val_lt b2))
  have hsub2_isU32 : (Felt.ofNat (sub2 a2 b2).2).isU32 = true :=
    u32OverflowingSub_snd_isU32 _ _ ha2_lt hb2_lt
  miden_movup
  miden_movup
  miden_swap
  rw [stepU32OverflowSub (ha := hsub2_isU32) (hb := hborrow1_isU32)]
  miden_bind
  rw [hsub2_val]
  simp only [stage2b, sub2Adj, sub2, borrow1, sub1Adj, sub1, sub0]
  dsimp only [pure, Pure.pure]

private theorem chunk6_correct
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (ha3 : a3.isU32 = true) (hb3 : b3.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨stage2b a0 a1 a2 a3 b0 b1 b2 b3 rest, mem, locs, adv, evts⟩
      chunk6 =
    some ⟨stage3a a0 a1 a2 a3 b0 b1 b2 b3 rest, mem, locs, adv, evts⟩ := by
  unfold stage2b chunk6 execWithEnv
  simp only [List.foldlM]
  unfold sub2Adj sub2
  miden_movup
  rw [u32OverflowingSub_borrow_ite (u32OverflowingSub a2.val b2.val).2
      (borrow1 a0 a1 b0 b1).val]
  rw [u32OverflowingSub_borrow_ite a2.val b2.val]
  rw [stepOrIte]
  miden_bind
  miden_movdn
  miden_movup
  miden_movup
  miden_swap
  rw [stepU32OverflowSub (ha := ha3) (hb := hb3)]
  miden_bind
  simp only [stage3a, borrow2, sub3, sub2Adj, sub2, borrow1, sub1Adj, sub1, sub0]
  dsimp only [pure, Pure.pure]

private theorem chunk7_correct
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (ha3 : a3.isU32 = true) (hb3 : b3.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨stage3a a0 a1 a2 a3 b0 b1 b2 b3 rest, mem, locs, adv, evts⟩
      chunk7 =
    some ⟨stage3b a0 a1 a2 a3 b0 b1 b2 b3 rest, mem, locs, adv, evts⟩ := by
  unfold stage3a chunk7 execWithEnv
  simp only [List.foldlM]
  have ha3_lt : a3.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using ha3
  have hb3_lt : b3.val < 2 ^ 32 := by simpa [Felt.isU32, decide_eq_true_eq] using hb3
  have hborrow2_isU32 : (borrow2 a0 a1 a2 b0 b1 b2).isU32 = true := by
    simpa [borrow2] using
      boolFelt_isU32
        (decide ((sub2 a2 b2).2 < (borrow1 a0 a1 b0 b1).val) || decide (a2.val < b2.val))
  have hsub3_val :
      (Felt.ofNat (sub3 a3 b3).2).val = (sub3 a3 b3).2 :=
    felt_ofNat_val_lt _ (u32_overflow_sub_snd_lt _ _ (ZMod.val_lt a3) (ZMod.val_lt b3))
  have hsub3_isU32 : (Felt.ofNat (sub3 a3 b3).2).isU32 = true :=
    u32OverflowingSub_snd_isU32 _ _ ha3_lt hb3_lt
  miden_movup
  miden_movup
  miden_swap
  rw [stepU32OverflowSub (ha := hsub3_isU32) (hb := hborrow2_isU32)]
  miden_bind
  rw [hsub3_val]
  simp only [stage3b, sub3Adj, sub3, borrow2, sub2Adj, sub2, borrow1, sub1Adj, sub1, sub0]
  dsimp only [pure, Pure.pure]

private theorem chunk8_correct
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv env (fuel + 1)
      ⟨stage3b a0 a1 a2 a3 b0 b1 b2 b3 rest, mem, locs, adv, evts⟩
      chunk8 =
    some ⟨u128OverflowingSubResult a0 a1 a2 a3 b0 b1 b2 b3 rest, mem, locs, adv, evts⟩ := by
  unfold stage3b chunk8 execWithEnv
  simp only [List.foldlM]
  unfold sub3Adj sub3
  miden_movup
  rw [u32OverflowingSub_borrow_ite (u32OverflowingSub a3.val b3.val).2
      (borrow2 a0 a1 a2 b0 b1 b2).val]
  rw [u32OverflowingSub_borrow_ite a3.val b3.val]
  rw [stepOrIte]
  miden_bind
  miden_movdn
  miden_movdn
  miden_movdn
  miden_swap
  miden_movup
  simp only [u128OverflowingSubResult, u128LtBool, u128Borrow1, u128Borrow2, u128Sub0, u128Sub1,
    u128Sub2, u128Sub3, sub3Adj, sub3, borrow2, sub2Adj, sub2, borrow1, sub1Adj, sub1, sub0]
  dsimp only [pure, Pure.pure]

theorem u128_overflowing_sub_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv, evts⟩
      Miden.Core.U128.overflowing_sub =
    some ⟨u128OverflowingSubResult a0 a1 a2 a3 b0 b1 b2 b3 rest, mem, locs, adv, evts⟩ := by
  rw [overflowing_sub_decomp, execWithEnv_append]
  rw [chunk1_correct env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv ha0 hb0]
  miden_bind
  rw [execWithEnv_append]
  rw [chunk2_correct env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv ha1 hb1]
  miden_bind
  rw [execWithEnv_append]
  rw [chunk3_correct env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv ha1 hb1]
  miden_bind
  rw [execWithEnv_append]
  rw [chunk4_correct env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv ha2 hb2]
  miden_bind
  rw [execWithEnv_append]
  rw [chunk5_correct env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv ha2 hb2]
  miden_bind
  rw [execWithEnv_append]
  rw [chunk6_correct env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv ha3 hb3]
  miden_bind
  rw [execWithEnv_append]
  rw [chunk7_correct env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv ha3 hb3]
  miden_bind
  exact chunk8_correct env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv

/-- `u128::overflowing_sub` correctly computes subtraction of two 128-bit values with borrow.
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [borrow, d0, d1, d2, d3] ++ rest
    where `d0..d3` are the low-to-high limbs of `a - b`,
    and `borrow = 1` iff the subtraction underflowed. -/
theorem u128_overflowing_sub_correct
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    exec 49 s Miden.Core.U128.overflowing_sub =
    some (s.withStack (u128OverflowingSubResult a0 a1 a2 a3 b0 b1 b2 b3 rest)) := by
  obtain ⟨stk, mem, locs, adv, evts⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  simpa [exec] using
    u128_overflowing_sub_run (fun _ => none) 48 a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3

end MidenLean.Proofs
