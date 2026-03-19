import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.Tactics
import MidenLean.Proofs.SimpAttrs
import MidenLean.Generated.U128

namespace MidenLean.Proofs

open MidenLean
open MidenLean.StepLemmas
open MidenLean.Tactics

/-- Execute a concatenation of op lists in two phases. -/
theorem execWithEnv_append (env : ProcEnv) (fuel : Nat) (s : MidenState) (xs ys : List Op) :
    execWithEnv env fuel s (xs ++ ys) = (do
      let s' ← execWithEnv env fuel s xs
      execWithEnv env fuel s' ys) := by
  unfold execWithEnv
  cases fuel <;> simp [List.foldlM_append]

@[miden_dispatch] theorem stepNeqImm (v : Felt) (mem locs : Nat → Felt) (adv : List Felt) (evts : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, locs, adv, evts⟩ (.neqImm v) =
    some ⟨(if a != v then (1 : Felt) else 0) :: rest, mem, locs, adv, evts⟩ := by
  unfold execInstruction execNeqImm
  rfl

private theorem u32_madd_div_lt_2_32 (a b c : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    (a.val * b.val + c.val) / 2 ^ 32 < 2 ^ 32 := by
  simp only [Felt.isU32, decide_eq_true_eq] at ha hb hc
  have ha' : a.val ≤ 2 ^ 32 - 1 := by omega
  have hb' : b.val ≤ 2 ^ 32 - 1 := by omega
  have hc' : c.val ≤ 2 ^ 32 - 1 := by omega
  have hab : a.val * b.val ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul ha' hb'
  have hsum : a.val * b.val + c.val ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1) := by
    exact Nat.add_le_add hab hc'
  calc
    (a.val * b.val + c.val) / 2 ^ 32
      ≤ ((2 ^ 32 - 1) * (2 ^ 32 - 1) + (2 ^ 32 - 1)) / 2 ^ 32 := Nat.div_le_div_right hsum
    _ < 2 ^ 32 := by native_decide

private theorem u32_madd_div_isU32 (a b c : Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    (Felt.ofNat ((a.val * b.val + c.val) / 2 ^ 32)).isU32 = true :=
  felt_ofNat_isU32_of_lt _ (u32_madd_div_lt_2_32 a b c ha hb hc)

def u128MulC0 (a0 b0 : Felt) : Felt := Felt.ofNat ((b0.val * a0.val) % 2 ^ 32)
def u128MulO0 (a0 b0 : Felt) : Felt := Felt.ofNat ((b0.val * a0.val) / 2 ^ 32)

def u128MulP1 (a0 a1 b0 : Felt) : Felt :=
  Felt.ofNat ((b0.val * a1.val + (u128MulO0 a0 b0).val) % 2 ^ 32)

def u128MulO1a (a0 a1 b0 : Felt) : Felt :=
  Felt.ofNat ((b0.val * a1.val + (u128MulO0 a0 b0).val) / 2 ^ 32)

def u128MulC1 (a0 a1 b0 b1 : Felt) : Felt :=
  Felt.ofNat ((b1.val * a0.val + (u128MulP1 a0 a1 b0).val) % 2 ^ 32)

def u128MulO1b (a0 a1 b0 b1 : Felt) : Felt :=
  Felt.ofNat ((b1.val * a0.val + (u128MulP1 a0 a1 b0).val) / 2 ^ 32)

def u128MulO1Sum (a0 a1 b0 b1 : Felt) : Felt :=
  Felt.ofNat (((u128MulO1a a0 a1 b0).val + (u128MulO1b a0 a1 b0 b1).val) % 2 ^ 32)

def u128MulO1Carry (a0 a1 b0 b1 : Felt) : Felt :=
  Felt.ofNat (((u128MulO1a a0 a1 b0).val + (u128MulO1b a0 a1 b0 b1).val) / 2 ^ 32)

def u128MulP2a (a0 a1 a2 b0 b1 : Felt) : Felt :=
  Felt.ofNat ((b0.val * a2.val + (u128MulO1Sum a0 a1 b0 b1).val) % 2 ^ 32)

def u128MulO2a (a0 a1 a2 b0 b1 : Felt) : Felt :=
  Felt.ofNat ((b0.val * a2.val + (u128MulO1Sum a0 a1 b0 b1).val) / 2 ^ 32)

def u128MulP2b (a0 a1 a2 b0 b1 : Felt) : Felt :=
  Felt.ofNat ((b1.val * a1.val + (u128MulP2a a0 a1 a2 b0 b1).val) % 2 ^ 32)

def u128MulO2b (a0 a1 a2 b0 b1 : Felt) : Felt :=
  Felt.ofNat ((b1.val * a1.val + (u128MulP2a a0 a1 a2 b0 b1).val) / 2 ^ 32)

def u128MulC2 (a0 a1 a2 b0 b1 b2 : Felt) : Felt :=
  Felt.ofNat ((b2.val * a0.val + (u128MulP2b a0 a1 a2 b0 b1).val) % 2 ^ 32)

def u128MulO2c (a0 a1 a2 b0 b1 b2 : Felt) : Felt :=
  Felt.ofNat ((b2.val * a0.val + (u128MulP2b a0 a1 a2 b0 b1).val) / 2 ^ 32)

def u128MulO2Partial (a0 a1 a2 b0 b1 b2 : Felt) : Felt :=
  Felt.ofNat
    (((u128MulO2a a0 a1 a2 b0 b1).val + (u128MulO2b a0 a1 a2 b0 b1).val +
          (u128MulO2c a0 a1 a2 b0 b1 b2).val) %
      2 ^ 32)

def u128MulO2Carry1 (a0 a1 a2 b0 b1 b2 : Felt) : Felt :=
  Felt.ofNat
    (((u128MulO2a a0 a1 a2 b0 b1).val + (u128MulO2b a0 a1 a2 b0 b1).val +
          (u128MulO2c a0 a1 a2 b0 b1 b2).val) /
      2 ^ 32)

def u128MulO2Sum (a0 a1 a2 b0 b1 b2 : Felt) : Felt :=
  Felt.ofNat (((u128MulO1Carry a0 a1 b0 b1).val + (u128MulO2Partial a0 a1 a2 b0 b1 b2).val) % 2 ^ 32)

def u128MulO2Carry2 (a0 a1 a2 b0 b1 b2 : Felt) : Felt :=
  Felt.ofNat (((u128MulO1Carry a0 a1 b0 b1).val + (u128MulO2Partial a0 a1 a2 b0 b1 b2).val) / 2 ^ 32)

def u128MulO2Carry (a0 a1 a2 b0 b1 b2 : Felt) : Felt :=
  u128MulO2Carry1 a0 a1 a2 b0 b1 b2 + u128MulO2Carry2 a0 a1 a2 b0 b1 b2

def u128MulP3a (a0 a1 a2 a3 b0 b1 b2 : Felt) : Felt :=
  Felt.ofNat ((b0.val * a3.val + (u128MulO2Sum a0 a1 a2 b0 b1 b2).val) % 2 ^ 32)

def u128MulO3a (a0 a1 a2 a3 b0 b1 b2 : Felt) : Felt :=
  Felt.ofNat ((b0.val * a3.val + (u128MulO2Sum a0 a1 a2 b0 b1 b2).val) / 2 ^ 32)

def u128MulP3b (a0 a1 a2 a3 b0 b1 b2 : Felt) : Felt :=
  Felt.ofNat ((b1.val * a2.val + (u128MulP3a a0 a1 a2 a3 b0 b1 b2).val) % 2 ^ 32)

def u128MulO3b (a0 a1 a2 a3 b0 b1 b2 : Felt) : Felt :=
  Felt.ofNat ((b1.val * a2.val + (u128MulP3a a0 a1 a2 a3 b0 b1 b2).val) / 2 ^ 32)

def u128MulP3c (a0 a1 a2 a3 b0 b1 b2 : Felt) : Felt :=
  Felt.ofNat ((b2.val * a1.val + (u128MulP3b a0 a1 a2 a3 b0 b1 b2).val) % 2 ^ 32)

def u128MulO3c (a0 a1 a2 a3 b0 b1 b2 : Felt) : Felt :=
  Felt.ofNat ((b2.val * a1.val + (u128MulP3b a0 a1 a2 a3 b0 b1 b2).val) / 2 ^ 32)

def u128MulC3 (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) : Felt :=
  Felt.ofNat ((b3.val * a0.val + (u128MulP3c a0 a1 a2 a3 b0 b1 b2).val) % 2 ^ 32)

def u128MulO3d (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) : Felt :=
  Felt.ofNat ((b3.val * a0.val + (u128MulP3c a0 a1 a2 a3 b0 b1 b2).val) / 2 ^ 32)

def u128MulCarryOverflowBool (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) : Bool :=
  u128MulO3d a0 a1 a2 a3 b0 b1 b2 b3 + u128MulO3c a0 a1 a2 a3 b0 b1 b2 +
      u128MulO3b a0 a1 a2 a3 b0 b1 b2 + u128MulO3a a0 a1 a2 a3 b0 b1 b2 +
      u128MulO2Carry a0 a1 a2 b0 b1 b2 !=
    (0 : Felt)

def u128MulP41Bool (_a1 a3 b1 : Felt) : Bool :=
  Felt.ofNat ((b1.val * a3.val) % 2 ^ 32) + Felt.ofNat ((b1.val * a3.val) / 2 ^ 32) != (0 : Felt)

def u128MulP42Bool (a2 b2 : Felt) : Bool :=
  Felt.ofNat ((b2.val * a2.val) % 2 ^ 32) + Felt.ofNat ((b2.val * a2.val) / 2 ^ 32) != (0 : Felt)

def u128MulP43Bool (a1 b3 : Felt) : Bool :=
  Felt.ofNat ((b3.val * a1.val) % 2 ^ 32) + Felt.ofNat ((b3.val * a1.val) / 2 ^ 32) != (0 : Felt)

def u128MulP52Bool (a3 b2 : Felt) : Bool :=
  Felt.ofNat ((b2.val * a3.val) % 2 ^ 32) + Felt.ofNat ((b2.val * a3.val) / 2 ^ 32) != (0 : Felt)

def u128MulP53Bool (a2 b3 : Felt) : Bool :=
  Felt.ofNat ((b3.val * a2.val) % 2 ^ 32) + Felt.ofNat ((b3.val * a2.val) / 2 ^ 32) != (0 : Felt)

def u128MulP63Bool (a3 b3 : Felt) : Bool :=
  Felt.ofNat ((b3.val * a3.val) % 2 ^ 32) + Felt.ofNat ((b3.val * a3.val) / 2 ^ 32) != (0 : Felt)

def u128MulOverflowBool (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) : Bool :=
  (((((u128MulCarryOverflowBool a0 a1 a2 a3 b0 b1 b2 b3 ||
            u128MulP41Bool a1 a3 b1) ||
          u128MulP42Bool a2 b2) ||
        u128MulP43Bool a1 b3) ||
      u128MulP52Bool a3 b2) ||
    u128MulP53Bool a2 b3) ||
  u128MulP63Bool a3 b3

def u128_mul_low_chunk : List Op := [
  .inst (.movup 7),
  .inst (.movup 7),
  .inst (.movup 7),
  .inst (.movup 7),
  .inst (.dup 4),
  .inst (.dup 1),
  .inst (.u32WidenMul),
  .inst (.movdn 9),
  .inst (.dup 5),
  .inst (.dup 3),
  .inst (.u32WidenMadd),
  .inst (.dup 7),
  .inst (.dup 3),
  .inst (.u32WidenMadd),
  .inst (.movdn 11),
  .inst (.u32WidenAdd),
  .inst (.swap 1),
  .inst (.movdn 11),
  .inst (.dup 5),
  .inst (.dup 4),
  .inst (.u32WidenMadd),
  .inst (.dup 7),
  .inst (.dup 4),
  .inst (.u32WidenMadd),
  .inst (.dup 9),
  .inst (.dup 4),
  .inst (.u32WidenMadd),
  .inst (.movdn 13),
  .inst (.u32WidenAdd3),
  .inst (.movup 13),
  .inst (.u32WidenAdd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.add),
  .inst (.swap 1)
]

private def u128_mul_low_chunk1 : List Op := [
  .inst (.movup 7),
  .inst (.movup 7),
  .inst (.movup 7),
  .inst (.movup 7),
  .inst (.dup 4),
  .inst (.dup 1),
  .inst (.u32WidenMul),
  .inst (.movdn 9),
  .inst (.dup 5),
  .inst (.dup 3),
  .inst (.u32WidenMadd),
  .inst (.dup 7)
]

private def u128_mul_low_chunk2 : List Op := [
  .inst (.dup 3),
  .inst (.u32WidenMadd),
  .inst (.movdn 11),
  .inst (.u32WidenAdd),
  .inst (.swap 1),
  .inst (.movdn 11),
  .inst (.dup 5),
  .inst (.dup 4),
  .inst (.u32WidenMadd),
  .inst (.dup 7),
  .inst (.dup 4),
  .inst (.u32WidenMadd)
]

private def u128_mul_low_chunk3 : List Op := [
  .inst (.dup 9),
  .inst (.dup 4),
  .inst (.u32WidenMadd),
  .inst (.movdn 13),
  .inst (.u32WidenAdd3),
  .inst (.movup 13),
  .inst (.u32WidenAdd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.add),
  .inst (.swap 1)
]

def u128_overflowing_mul_c3_chunk : List Op := [
  .inst (.dup 6),
  .inst (.dup 6),
  .inst (.u32WidenMadd),
  .inst (.dup 8),
  .inst (.dup 6),
  .inst (.u32WidenMadd),
  .inst (.dup 10),
  .inst (.dup 6),
  .inst (.u32WidenMadd),
  .inst (.dup 12),
  .inst (.dup 6),
  .inst (.u32WidenMadd)
]

def u128_overflowing_mul_overflow_acc_chunk : List Op := [
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.add),
  .inst (.movup 2),
  .inst (.add),
  .inst (.movup 2),
  .inst (.add),
  .inst (.movup 2),
  .inst (.add),
  .inst (.neqImm 0)
]

def u128_overflowing_mul_overflow_products_chunk : List Op := [
  .inst (.dup 7),
  .inst (.dup 6),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 8),
  .inst (.dup 5),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 9),
  .inst (.dup 4),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 8),
  .inst (.dup 6),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 9),
  .inst (.dup 5),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 9),
  .inst (.dup 6),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or)
]

private def u128_overflowing_mul_overflow_products_chunk1 : List Op := [
  .inst (.dup 7),
  .inst (.dup 6),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 8),
  .inst (.dup 5),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or)
]

private def u128_overflowing_mul_overflow_products_chunk2 : List Op := [
  .inst (.dup 9),
  .inst (.dup 4),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 8),
  .inst (.dup 6),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or)
]

private def u128_overflowing_mul_overflow_products_chunk3 : List Op := [
  .inst (.dup 9),
  .inst (.dup 5),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 9),
  .inst (.dup 6),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or)
]

def u128_overflowing_mul_cleanup_chunk : List Op := [
  .inst (.movup 2),
  .inst (.drop),
  .inst (.movup 2),
  .inst (.drop),
  .inst (.movup 2),
  .inst (.drop),
  .inst (.movup 2),
  .inst (.drop),
  .inst (.movup 2),
  .inst (.drop),
  .inst (.movup 2),
  .inst (.drop),
  .inst (.movup 2),
  .inst (.drop),
  .inst (.movup 2),
  .inst (.drop),
  .inst (.swap 1),
  .inst (.movdn 4)
]

def u128_wrapping_mul_tail : List Op := [
  .inst (.swap 1),
  .inst (.drop),
  .inst (.dup 5),
  .inst (.dup 5),
  .inst (.u32WrappingMadd),
  .inst (.dup 6),
  .inst (.dup 4),
  .inst (.u32WrappingMadd),
  .inst (.dup 7),
  .inst (.dup 3),
  .inst (.u32WrappingMadd),
  .inst (.dup 8),
  .inst (.dup 2),
  .inst (.u32WrappingMadd),
  .inst (.movup 9),
  .inst (.movup 10),
  .inst (.movup 11),
  .inst (.movup 3),
  .inst (.swapw 1),
  .inst (.dropw),
  .inst (.swapw 1),
  .inst (.dropw),
  .inst (.movdn 3),
  .inst (.movdn 2),
  .inst (.swap 1)
]

theorem overflowing_mul_decomp :
    Miden.Core.U128.overflowing_mul =
      u128_mul_low_chunk ++
        (u128_overflowing_mul_c3_chunk ++
          (u128_overflowing_mul_overflow_acc_chunk ++
            (u128_overflowing_mul_overflow_products_chunk ++ u128_overflowing_mul_cleanup_chunk))) := by
  simp [Miden.Core.U128.overflowing_mul, u128_mul_low_chunk, u128_overflowing_mul_c3_chunk,
    u128_overflowing_mul_overflow_acc_chunk, u128_overflowing_mul_overflow_products_chunk,
    u128_overflowing_mul_cleanup_chunk]

private theorem u128_mul_low_chunk_decomp :
    u128_mul_low_chunk = u128_mul_low_chunk1 ++ (u128_mul_low_chunk2 ++ u128_mul_low_chunk3) := by
  simp [u128_mul_low_chunk, u128_mul_low_chunk1, u128_mul_low_chunk2, u128_mul_low_chunk3]

private theorem u128_overflowing_mul_overflow_products_chunk_decomp :
    u128_overflowing_mul_overflow_products_chunk =
      u128_overflowing_mul_overflow_products_chunk1 ++
        (u128_overflowing_mul_overflow_products_chunk2 ++
          u128_overflowing_mul_overflow_products_chunk3) := by
  simp [u128_overflowing_mul_overflow_products_chunk,
    u128_overflowing_mul_overflow_products_chunk1,
    u128_overflowing_mul_overflow_products_chunk2,
    u128_overflowing_mul_overflow_products_chunk3]

private theorem u128_mul_low_chunk1_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) (evts : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (hb0 : b0.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv, evts⟩
      u128_mul_low_chunk1 =
    some ⟨
      b1 ::
      u128MulP1 a0 a1 b0 ::
      u128MulO1a a0 a1 b0 ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
      u128MulC0 a0 b0 ::
      rest,
      mem, locs, adv, evts⟩ := by
  unfold execWithEnv u128_mul_low_chunk1
  simp only [List.foldlM]
  have hO0_u32 : (u128MulO0 a0 b0).isU32 = true := by
    unfold u128MulO0
    simpa [Nat.mul_comm] using u32_prod_div_isU32 b0 a0 hb0 ha0
  miden_movup
  miden_movup
  miden_movup
  miden_movup
  miden_dup
  miden_dup
  rw [stepU32WidenMul (ha := hb0) (hb := ha0)]
  miden_bind
  miden_movdn
  miden_dup
  miden_dup
  rw [stepU32WidenMadd
    (a := b0) (b := a1) (c := Felt.ofNat (b0.val * a0.val / 2 ^ 32))
    (ha := hb0) (hb := ha1)
    (hc := by simpa [u128MulO0, Nat.mul_comm] using hO0_u32)]
  miden_bind
  miden_dup
  simp [pure, Pure.pure, u128MulC0, u128MulO0, u128MulP1, u128MulO1a]

private theorem u128_mul_low_chunk2_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) (evts : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true) (ha2 : a2.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨b1 ::
        u128MulP1 a0 a1 b0 ::
        u128MulO1a a0 a1 b0 ::
        a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        u128MulC0 a0 b0 ::
        rest,
        mem, locs, adv, evts⟩
      u128_mul_low_chunk2 =
    some ⟨
      u128MulP2b a0 a1 a2 b0 b1 ::
      u128MulO2b a0 a1 a2 b0 b1 ::
      u128MulO2a a0 a1 a2 b0 b1 ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulO1Carry a0 a1 b0 b1 ::
      rest,
      mem, locs, adv, evts⟩ := by
  unfold execWithEnv u128_mul_low_chunk2
  simp only [List.foldlM]
  have hO0_u32 : (u128MulO0 a0 b0).isU32 = true := by
    unfold u128MulO0
    simpa [Nat.mul_comm] using u32_prod_div_isU32 b0 a0 hb0 ha0
  have hP1_u32 : (u128MulP1 a0 a1 b0).isU32 = true := by
    unfold u128MulP1
    exact u32_mod_isU32 _
  have hO1a_u32 : (u128MulO1a a0 a1 b0).isU32 = true := by
    unfold u128MulO1a
    simpa [Nat.mul_comm] using u32_madd_div_isU32 b0 a1 (u128MulO0 a0 b0) hb0 ha1 hO0_u32
  have hO1b_u32 : (u128MulO1b a0 a1 b0 b1).isU32 = true := by
    unfold u128MulO1b
    simpa [Nat.mul_comm] using u32_madd_div_isU32 b1 a0 (u128MulP1 a0 a1 b0) hb1 ha0 hP1_u32
  have hO1Sum_u32 : (u128MulO1Sum a0 a1 b0 b1).isU32 = true := by
    unfold u128MulO1Sum
    exact u32_mod_isU32 _
  have hP2a_u32 : (u128MulP2a a0 a1 a2 b0 b1).isU32 = true := by
    unfold u128MulP2a
    exact u32_mod_isU32 _
  miden_dup
  rw [stepU32WidenMadd (ha := hb1) (hb := ha0) (hc := hP1_u32)]
  miden_bind
  miden_movdn
  rw [stepU32WidenAdd
    (a := u128MulO1a a0 a1 b0)
    (b := Felt.ofNat ((b1.val * a0.val + (u128MulP1 a0 a1 b0).val) / 2 ^ 32))
    (ha := hO1a_u32)
    (hb := by simpa [u128MulO1b, Nat.mul_comm] using hO1b_u32)]
  miden_bind
  miden_swap
  miden_movdn
  miden_dup
  miden_dup
  rw [stepU32WidenMadd
    (a := b0) (b := a2)
    (c := Felt.ofNat
      (((u128MulO1a a0 a1 b0).val +
          (Felt.ofNat ((b1.val * a0.val + (u128MulP1 a0 a1 b0).val) / 2 ^ 32)).val) %
        2 ^ 32))
    (ha := hb0) (hb := ha2)
    (hc := u32_mod_isU32 _)]
  miden_bind
  miden_dup
  miden_dup
  rw [stepU32WidenMadd
    (a := b1) (b := a1)
    (c := Felt.ofNat
      ((b0.val * a2.val +
          (Felt.ofNat
            (((u128MulO1a a0 a1 b0).val +
                (Felt.ofNat ((b1.val * a0.val + (u128MulP1 a0 a1 b0).val) / 2 ^ 32)).val) %
              2 ^ 32)).val) %
        2 ^ 32))
    (ha := hb1) (hb := ha1)
    (hc := u32_mod_isU32 _)]
  miden_bind
  simp [pure, Pure.pure, u128MulC0, u128MulO0, u128MulP1, u128MulO1a, u128MulC1, u128MulO1b,
    u128MulO1Sum, u128MulO1Carry, u128MulP2a, u128MulO2a, u128MulP2b, u128MulO2b]

private theorem u128_mul_low_chunk3_add3_step
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) (evts : List Felt)
    (hO2a_u32 : (u128MulO2a a0 a1 a2 b0 b1).isU32 = true)
    (hO2b_u32 : (u128MulO2b a0 a1 a2 b0 b1).isU32 = true)
    (hO2c_u32 : (u128MulO2c a0 a1 a2 b0 b1 b2).isU32 = true) :
    execInstruction
      ⟨u128MulO2c a0 a1 a2 b0 b1 b2 ::
        u128MulO2b a0 a1 a2 b0 b1 ::
        u128MulO2a a0 a1 a2 b0 b1 ::
        a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        u128MulC0 a0 b0 ::
        u128MulC1 a0 a1 b0 b1 ::
        u128MulC2 a0 a1 a2 b0 b1 b2 ::
        u128MulO1Carry a0 a1 b0 b1 ::
        rest,
        mem, locs, adv, evts⟩
      .u32WidenAdd3 =
    some ⟨
      u128MulO2Partial a0 a1 a2 b0 b1 b2 ::
      u128MulO2Carry1 a0 a1 a2 b0 b1 b2 ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      u128MulO1Carry a0 a1 b0 b1 ::
      rest,
      mem, locs, adv, evts⟩ := by
  simpa [u128MulO2Partial, u128MulO2Carry1, u128MulC2] using
    (stepU32WidenAdd3 (mem := mem) (locs := locs) (adv := adv)
      (a := u128MulO2a a0 a1 a2 b0 b1)
      (b := u128MulO2b a0 a1 a2 b0 b1)
      (c := u128MulO2c a0 a1 a2 b0 b1 b2)
      (rest := a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        u128MulC0 a0 b0 :: u128MulC1 a0 a1 b0 b1 :: u128MulC2 a0 a1 a2 b0 b1 b2 ::
        u128MulO1Carry a0 a1 b0 b1 :: rest)
      (ha := hO2a_u32) (hb := hO2b_u32) (hc := hO2c_u32))

private theorem u128_mul_low_chunk3_add_step
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) (evts : List Felt)
    (hO1Carry_u32 : (u128MulO1Carry a0 a1 b0 b1).isU32 = true)
    (hO2Partial_u32 : (u128MulO2Partial a0 a1 a2 b0 b1 b2).isU32 = true) :
    execInstruction
      ⟨u128MulO1Carry a0 a1 b0 b1 ::
        u128MulO2Partial a0 a1 a2 b0 b1 b2 ::
        u128MulO2Carry1 a0 a1 a2 b0 b1 b2 ::
        a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        u128MulC0 a0 b0 ::
        u128MulC1 a0 a1 b0 b1 ::
        u128MulC2 a0 a1 a2 b0 b1 b2 ::
        rest,
        mem, locs, adv, evts⟩
      .u32WidenAdd =
    some ⟨
      u128MulO2Sum a0 a1 a2 b0 b1 b2 ::
      u128MulO2Carry2 a0 a1 a2 b0 b1 b2 ::
      u128MulO2Carry1 a0 a1 a2 b0 b1 b2 ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      rest,
      mem, locs, adv, evts⟩ := by
  simpa [u128MulO2Sum, u128MulO2Carry2, Nat.add_comm] using
    (stepU32WidenAdd (mem := mem) (locs := locs) (adv := adv)
      (a := u128MulO2Partial a0 a1 a2 b0 b1 b2)
      (b := u128MulO1Carry a0 a1 b0 b1)
      (rest := u128MulO2Carry1 a0 a1 a2 b0 b1 b2 ::
        a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        u128MulC0 a0 b0 :: u128MulC1 a0 a1 b0 b1 :: u128MulC2 a0 a1 a2 b0 b1 b2 :: rest)
      (ha := hO2Partial_u32) (hb := hO1Carry_u32))

private theorem u128_mul_low_chunk3_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) (evts : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true) (ha2 : a2.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) (hb2 : b2.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨u128MulP2b a0 a1 a2 b0 b1 ::
        u128MulO2b a0 a1 a2 b0 b1 ::
        u128MulO2a a0 a1 a2 b0 b1 ::
        a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        u128MulC0 a0 b0 ::
        u128MulC1 a0 a1 b0 b1 ::
        u128MulO1Carry a0 a1 b0 b1 ::
        rest,
        mem, locs, adv, evts⟩
      u128_mul_low_chunk3 =
    some ⟨
      u128MulO2Sum a0 a1 a2 b0 b1 b2 ::
      u128MulO2Carry a0 a1 a2 b0 b1 b2 ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      rest,
      mem, locs, adv, evts⟩ := by
  unfold execWithEnv u128_mul_low_chunk3
  simp only [List.foldlM]
  have hP2b_u32 : (u128MulP2b a0 a1 a2 b0 b1).isU32 = true := by
    unfold u128MulP2b
    exact u32_mod_isU32 _
  have hO0_u32 : (u128MulO0 a0 b0).isU32 = true := by
    unfold u128MulO0
    simpa [Nat.mul_comm] using u32_prod_div_isU32 b0 a0 hb0 ha0
  have hP1_u32 : (u128MulP1 a0 a1 b0).isU32 = true := by
    unfold u128MulP1
    exact u32_mod_isU32 _
  have hO1a_u32 : (u128MulO1a a0 a1 b0).isU32 = true := by
    unfold u128MulO1a
    simpa [Nat.mul_comm] using u32_madd_div_isU32 b0 a1 (u128MulO0 a0 b0) hb0 ha1 hO0_u32
  have hO1b_u32 : (u128MulO1b a0 a1 b0 b1).isU32 = true := by
    unfold u128MulO1b
    simpa [Nat.mul_comm] using u32_madd_div_isU32 b1 a0 (u128MulP1 a0 a1 b0) hb1 ha0 hP1_u32
  have hO1Carry_u32 : (u128MulO1Carry a0 a1 b0 b1).isU32 = true := by
    unfold u128MulO1Carry
    simpa using u32_div_2_32_isU32 (u128MulO1a a0 a1 b0) (u128MulO1b a0 a1 b0 b1) hO1a_u32 hO1b_u32
  have hO1Sum_u32 : (u128MulO1Sum a0 a1 b0 b1).isU32 = true := by
    unfold u128MulO1Sum
    exact u32_mod_isU32 _
  have hO2a_u32 : (u128MulO2a a0 a1 a2 b0 b1).isU32 = true := by
    unfold u128MulO2a
    simpa [Nat.mul_comm] using
      u32_madd_div_isU32 b0 a2 (u128MulO1Sum a0 a1 b0 b1) hb0 ha2 hO1Sum_u32
  have hP2a_u32 : (u128MulP2a a0 a1 a2 b0 b1).isU32 = true := by
    unfold u128MulP2a
    exact u32_mod_isU32 _
  have hO2b_u32 : (u128MulO2b a0 a1 a2 b0 b1).isU32 = true := by
    unfold u128MulO2b
    simpa [Nat.mul_comm] using
      u32_madd_div_isU32 b1 a1 (u128MulP2a a0 a1 a2 b0 b1) hb1 ha1 hP2a_u32
  have hO2c_u32 : (u128MulO2c a0 a1 a2 b0 b1 b2).isU32 = true := by
    unfold u128MulO2c
    simpa [Nat.mul_comm] using
      u32_madd_div_isU32 b2 a0 (u128MulP2b a0 a1 a2 b0 b1) hb2 ha0 hP2b_u32
  have hO2Partial_u32 : (u128MulO2Partial a0 a1 a2 b0 b1 b2).isU32 = true := by
    unfold u128MulO2Partial
    exact u32_mod_isU32 _
  miden_dup
  miden_dup
  rw [stepU32WidenMadd (ha := hb2) (hb := ha0) (hc := hP2b_u32)]
  miden_bind
  miden_movdn
  have hAdd3 :
      execInstruction
        ⟨Felt.ofNat ((b2.val * a0.val + (u128MulP2b a0 a1 a2 b0 b1).val) / 2 ^ 32) ::
          u128MulO2b a0 a1 a2 b0 b1 ::
          u128MulO2a a0 a1 a2 b0 b1 ::
          a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
          u128MulC0 a0 b0 ::
          u128MulC1 a0 a1 b0 b1 ::
          Felt.ofNat ((b2.val * a0.val + (u128MulP2b a0 a1 a2 b0 b1).val) % 2 ^ 32) ::
          u128MulO1Carry a0 a1 b0 b1 ::
          rest,
          mem, locs, adv, evts⟩
        .u32WidenAdd3 =
      some ⟨
        u128MulO2Partial a0 a1 a2 b0 b1 b2 ::
        u128MulO2Carry1 a0 a1 a2 b0 b1 b2 ::
        a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        u128MulC0 a0 b0 ::
        u128MulC1 a0 a1 b0 b1 ::
        u128MulC2 a0 a1 a2 b0 b1 b2 ::
        u128MulO1Carry a0 a1 b0 b1 ::
        rest,
        mem, locs, adv, evts⟩ := by
    simpa [u128MulC2, u128MulO2Partial, u128MulO2Carry1] using
      (stepU32WidenAdd3 (mem := mem) (locs := locs) (adv := adv)
        (a := u128MulO2a a0 a1 a2 b0 b1)
        (b := u128MulO2b a0 a1 a2 b0 b1)
        (c := Felt.ofNat ((b2.val * a0.val + (u128MulP2b a0 a1 a2 b0 b1).val) / 2 ^ 32))
        (rest := a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
          u128MulC0 a0 b0 :: u128MulC1 a0 a1 b0 b1 ::
          Felt.ofNat ((b2.val * a0.val + (u128MulP2b a0 a1 a2 b0 b1).val) % 2 ^ 32) ::
          u128MulO1Carry a0 a1 b0 b1 :: rest)
        (ha := hO2a_u32) (hb := hO2b_u32)
        (hc := by simpa [u128MulO2c] using hO2c_u32))
  rw [hAdd3]
  miden_bind
  miden_movup
  have hAdd2 :
      execInstruction
        ⟨u128MulO1Carry a0 a1 b0 b1 ::
          u128MulO2Partial a0 a1 a2 b0 b1 b2 ::
          u128MulO2Carry1 a0 a1 a2 b0 b1 b2 ::
          a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
          u128MulC0 a0 b0 ::
          u128MulC1 a0 a1 b0 b1 ::
          u128MulC2 a0 a1 a2 b0 b1 b2 ::
          rest,
          mem, locs, adv, evts⟩
        .u32WidenAdd =
      some ⟨
        u128MulO2Sum a0 a1 a2 b0 b1 b2 ::
        u128MulO2Carry2 a0 a1 a2 b0 b1 b2 ::
        u128MulO2Carry1 a0 a1 a2 b0 b1 b2 ::
        a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        u128MulC0 a0 b0 ::
        u128MulC1 a0 a1 b0 b1 ::
        u128MulC2 a0 a1 a2 b0 b1 b2 ::
        rest,
        mem, locs, adv, evts⟩ := by
    simpa [u128MulO2Sum, u128MulO2Carry2, Nat.add_comm] using
      (stepU32WidenAdd (mem := mem) (locs := locs) (adv := adv)
        (a := u128MulO2Partial a0 a1 a2 b0 b1 b2)
        (b := u128MulO1Carry a0 a1 b0 b1)
        (rest := u128MulO2Carry1 a0 a1 a2 b0 b1 b2 ::
          a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
          u128MulC0 a0 b0 :: u128MulC1 a0 a1 b0 b1 :: u128MulC2 a0 a1 a2 b0 b1 b2 :: rest)
        (ha := hO2Partial_u32) (hb := hO1Carry_u32))
  rw [hAdd2]
  miden_bind
  miden_swap
  miden_movup
  rw [stepAdd]
  miden_bind
  miden_swap
  simp [pure, Pure.pure, u128MulO2Carry, add_comm]

theorem u128_mul_low_chunk_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) (evts : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (_ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (_hb3 : b3.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv, evts⟩
      u128_mul_low_chunk =
    some ⟨
      u128MulO2Sum a0 a1 a2 b0 b1 b2 ::
      u128MulO2Carry a0 a1 a2 b0 b1 b2 ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      rest,
      mem, locs, adv, evts⟩ := by
  rw [u128_mul_low_chunk_decomp, execWithEnv_append]
  rw [u128_mul_low_chunk1_run env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv ha0 ha1 hb0]
  miden_bind
  rw [execWithEnv_append]
  rw [u128_mul_low_chunk2_run env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
    ha0 ha1 ha2 hb0 hb1]
  miden_bind
  rw [u128_mul_low_chunk3_run env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
    ha0 ha1 ha2 hb0 hb1 hb2]

theorem u128_overflowing_mul_c3_chunk_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) (evts : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨u128MulO2Sum a0 a1 a2 b0 b1 b2 ::
        u128MulO2Carry a0 a1 a2 b0 b1 b2 ::
        a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        u128MulC0 a0 b0 ::
        u128MulC1 a0 a1 b0 b1 ::
        u128MulC2 a0 a1 a2 b0 b1 b2 ::
        rest,
        mem, locs, adv, evts⟩
      u128_overflowing_mul_c3_chunk =
    some ⟨
      u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
      u128MulO3d a0 a1 a2 a3 b0 b1 b2 b3 ::
      u128MulO3c a0 a1 a2 a3 b0 b1 b2 ::
      u128MulO3b a0 a1 a2 a3 b0 b1 b2 ::
      u128MulO3a a0 a1 a2 a3 b0 b1 b2 ::
      u128MulO2Carry a0 a1 a2 b0 b1 b2 ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      rest,
      mem, locs, adv, evts⟩ := by
  unfold execWithEnv u128_overflowing_mul_c3_chunk
  simp only [List.foldlM]
  have hO2Sum_u32 : (u128MulO2Sum a0 a1 a2 b0 b1 b2).isU32 = true := by
    unfold u128MulO2Sum
    exact u32_mod_isU32 _
  miden_dup
  miden_dup
  rw [stepU32WidenMadd (ha := hb0) (hb := ha3) (hc := hO2Sum_u32)]
  miden_bind
  miden_dup
  miden_dup
  rw [stepU32WidenMadd
    (a := b1) (b := a2)
    (c := Felt.ofNat ((b0.val * a3.val + (u128MulO2Sum a0 a1 a2 b0 b1 b2).val) % 2 ^ 32))
    (ha := hb1) (hb := ha2) (hc := u32_mod_isU32 _)]
  miden_bind
  miden_dup
  miden_dup
  rw [stepU32WidenMadd
    (a := b2) (b := a1)
    (c := Felt.ofNat
      ((b1.val * a2.val + (Felt.ofNat ((b0.val * a3.val + (u128MulO2Sum a0 a1 a2 b0 b1 b2).val) % 2 ^ 32)).val) %
        2 ^ 32))
    (ha := hb2) (hb := ha1) (hc := u32_mod_isU32 _)]
  miden_bind
  miden_dup
  miden_dup
  rw [stepU32WidenMadd
    (a := b3) (b := a0)
    (c := Felt.ofNat
      ((b2.val * a1.val +
          (Felt.ofNat
            ((b1.val * a2.val + (Felt.ofNat ((b0.val * a3.val + (u128MulO2Sum a0 a1 a2 b0 b1 b2).val) % 2 ^ 32)).val) %
              2 ^ 32)).val) %
        2 ^ 32))
    (ha := hb3) (hb := ha0) (hc := u32_mod_isU32 _)]
  miden_bind
  simp [pure, Pure.pure, u128MulP3a, u128MulO3a, u128MulP3b, u128MulO3b, u128MulP3c, u128MulO3c,
    u128MulC3, u128MulO3d]

theorem u128_overflowing_mul_overflow_acc_chunk_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) (evts : List Felt) :
    execWithEnv env (fuel + 1)
      ⟨u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
        u128MulO3d a0 a1 a2 a3 b0 b1 b2 b3 ::
        u128MulO3c a0 a1 a2 a3 b0 b1 b2 ::
        u128MulO3b a0 a1 a2 a3 b0 b1 b2 ::
        u128MulO3a a0 a1 a2 a3 b0 b1 b2 ::
        u128MulO2Carry a0 a1 a2 b0 b1 b2 ::
        a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        u128MulC0 a0 b0 ::
        u128MulC1 a0 a1 b0 b1 ::
        u128MulC2 a0 a1 a2 b0 b1 b2 ::
        rest,
        mem, locs, adv, evts⟩
      u128_overflowing_mul_overflow_acc_chunk =
    some ⟨
      (if u128MulCarryOverflowBool a0 a1 a2 a3 b0 b1 b2 b3 then (1 : Felt) else 0) ::
      u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      rest,
      mem, locs, adv, evts⟩ := by
  unfold u128_overflowing_mul_overflow_acc_chunk execWithEnv execInstruction
    execSwap execMovup execAdd execNeqImm removeNth
  simp [MidenState.withStack, u128MulCarryOverflowBool]

private theorem u128_overflowing_mul_overflow_products_chunk1_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) (evts : List Felt)
    (_ha1 : a1.isU32 = true) (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb1 : b1.isU32 = true) (hb2 : b2.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨(if u128MulCarryOverflowBool a0 a1 a2 a3 b0 b1 b2 b3 then (1 : Felt) else 0) ::
        u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
        a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        u128MulC0 a0 b0 ::
        u128MulC1 a0 a1 b0 b1 ::
        u128MulC2 a0 a1 a2 b0 b1 b2 ::
        rest,
        mem, locs, adv, evts⟩
      u128_overflowing_mul_overflow_products_chunk1 =
    some ⟨
      (if ((u128MulCarryOverflowBool a0 a1 a2 a3 b0 b1 b2 b3 || u128MulP41Bool a1 a3 b1) ||
          u128MulP42Bool a2 b2) then (1 : Felt) else 0) ::
      u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      rest,
      mem, locs, adv, evts⟩ := by
  unfold execWithEnv u128_overflowing_mul_overflow_products_chunk1
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepU32WidenMul (ha := hb1) (hb := ha3)]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [stepNeqImm]
  miden_bind
  rw [stepOrIte]
  miden_bind
  miden_dup
  miden_dup
  rw [stepU32WidenMul (ha := hb2) (hb := ha2)]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [stepNeqImm]
  miden_bind
  rw [stepOrIte]
  miden_bind
  simp [pure, Pure.pure, u128MulCarryOverflowBool, u128MulP41Bool, u128MulP42Bool, add_comm,
    Bool.or_assoc]

private theorem u128_overflowing_mul_overflow_products_chunk2_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) (evts : List Felt)
    (ha1 : a1.isU32 = true) (ha3 : a3.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨(if ((u128MulCarryOverflowBool a0 a1 a2 a3 b0 b1 b2 b3 || u128MulP41Bool a1 a3 b1) ||
            u128MulP42Bool a2 b2) then (1 : Felt) else 0) ::
        u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
        a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        u128MulC0 a0 b0 ::
        u128MulC1 a0 a1 b0 b1 ::
        u128MulC2 a0 a1 a2 b0 b1 b2 ::
        rest,
        mem, locs, adv, evts⟩
      u128_overflowing_mul_overflow_products_chunk2 =
    some ⟨
      (if ((((u128MulCarryOverflowBool a0 a1 a2 a3 b0 b1 b2 b3 || u128MulP41Bool a1 a3 b1) ||
              u128MulP42Bool a2 b2) || u128MulP43Bool a1 b3) || u128MulP52Bool a3 b2) then
          (1 : Felt)
        else 0) ::
      u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      rest,
      mem, locs, adv, evts⟩ := by
  unfold execWithEnv u128_overflowing_mul_overflow_products_chunk2
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepU32WidenMul (ha := hb3) (hb := ha1)]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [stepNeqImm]
  miden_bind
  rw [stepOrIte]
  miden_bind
  miden_dup
  miden_dup
  rw [stepU32WidenMul (ha := hb2) (hb := ha3)]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [stepNeqImm]
  miden_bind
  rw [stepOrIte]
  miden_bind
  simp [pure, Pure.pure, u128MulCarryOverflowBool, u128MulP41Bool, u128MulP42Bool, u128MulP43Bool,
    u128MulP52Bool, add_comm, Bool.or_assoc]

private theorem u128_overflowing_mul_overflow_products_chunk3_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) (evts : List Felt)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb3 : b3.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨(if ((((u128MulCarryOverflowBool a0 a1 a2 a3 b0 b1 b2 b3 || u128MulP41Bool a1 a3 b1) ||
              u128MulP42Bool a2 b2) || u128MulP43Bool a1 b3) || u128MulP52Bool a3 b2) then
            (1 : Felt)
          else 0) ::
        u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
        a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        u128MulC0 a0 b0 ::
        u128MulC1 a0 a1 b0 b1 ::
        u128MulC2 a0 a1 a2 b0 b1 b2 ::
        rest,
        mem, locs, adv, evts⟩
      u128_overflowing_mul_overflow_products_chunk3 =
    some ⟨
      (if u128MulOverflowBool a0 a1 a2 a3 b0 b1 b2 b3 then (1 : Felt) else 0) ::
      u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      rest,
      mem, locs, adv, evts⟩ := by
  unfold execWithEnv u128_overflowing_mul_overflow_products_chunk3
  simp only [List.foldlM]
  miden_dup
  miden_dup
  rw [stepU32WidenMul (ha := hb3) (hb := ha2)]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [stepNeqImm]
  miden_bind
  rw [stepOrIte]
  miden_bind
  miden_dup
  miden_dup
  rw [stepU32WidenMul (ha := hb3) (hb := ha3)]
  miden_bind
  rw [stepAdd]
  miden_bind
  rw [stepNeqImm]
  miden_bind
  rw [stepOrIte]
  miden_bind
  simp [pure, Pure.pure, u128MulOverflowBool, u128MulCarryOverflowBool, u128MulP41Bool,
    u128MulP42Bool, u128MulP43Bool, u128MulP52Bool, u128MulP53Bool, u128MulP63Bool, add_comm,
    Bool.or_assoc]

theorem u128_overflowing_mul_overflow_products_chunk_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) (evts : List Felt)
    (_ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (_hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨(if u128MulCarryOverflowBool a0 a1 a2 a3 b0 b1 b2 b3 then (1 : Felt) else 0) ::
        u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
        a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        u128MulC0 a0 b0 ::
        u128MulC1 a0 a1 b0 b1 ::
        u128MulC2 a0 a1 a2 b0 b1 b2 ::
        rest,
        mem, locs, adv, evts⟩
      u128_overflowing_mul_overflow_products_chunk =
    some ⟨
      (if u128MulOverflowBool a0 a1 a2 a3 b0 b1 b2 b3 then (1 : Felt) else 0) ::
      u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      rest,
      mem, locs, adv, evts⟩ := by
  rw [u128_overflowing_mul_overflow_products_chunk_decomp, execWithEnv_append]
  rw [u128_overflowing_mul_overflow_products_chunk1_run env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
    ha1 ha2 ha3 hb1 hb2]
  miden_bind
  rw [execWithEnv_append]
  rw [u128_overflowing_mul_overflow_products_chunk2_run env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
    ha1 ha3 hb2 hb3]
  miden_bind
  rw [u128_overflowing_mul_overflow_products_chunk3_run env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
    ha2 ha3 hb3]

theorem u128_overflowing_mul_cleanup_chunk_run
    (env : ProcEnv) (fuel : Nat)
    (overflow c0 c1 c2 c3 a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) (evts : List Felt) :
    execWithEnv env (fuel + 1)
      ⟨overflow :: c3 :: a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: c0 :: c1 :: c2 :: rest,
        mem, locs, adv, evts⟩
      u128_overflowing_mul_cleanup_chunk =
    some ⟨overflow :: c0 :: c1 :: c2 :: c3 :: rest, mem, locs, adv, evts⟩ := by
  unfold u128_overflowing_mul_cleanup_chunk execWithEnv execInstruction
    execMovup execDrop execSwap execMovdn removeNth insertAt
  simp [MidenState.withStack]

theorem u128_overflowing_mul_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt) (evts : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv, evts⟩
      Miden.Core.U128.overflowing_mul =
    some ⟨
      (if u128MulOverflowBool a0 a1 a2 a3 b0 b1 b2 b3 then (1 : Felt) else 0) ::
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
      rest,
      mem, locs, adv, evts⟩ := by
  rw [overflowing_mul_decomp, execWithEnv_append]
  rw [u128_mul_low_chunk_run env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3]
  miden_bind
  rw [execWithEnv_append]
  rw [u128_overflowing_mul_c3_chunk_run env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3]
  miden_bind
  rw [execWithEnv_append]
  rw [u128_overflowing_mul_overflow_acc_chunk_run env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv]
  miden_bind
  rw [execWithEnv_append]
  rw [u128_overflowing_mul_overflow_products_chunk_run env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3]
  miden_bind
  rw [u128_overflowing_mul_cleanup_chunk_run env fuel]

/-- `u128::overflowing_mul` correctly computes the low 128 bits of the product and an overflow flag.
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [overflow, c0, c1, c2, c3] ++ rest
    where `c0..c3` are the low-to-high limbs of `(a * b) mod 2^128`
    and `overflow` is `1` exactly when the discarded high part is nonzero. -/
theorem u128_overflowing_mul_correct
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    exec 116 s Miden.Core.U128.overflowing_mul =
    some (s.withStack (
      (if u128MulOverflowBool a0 a1 a2 a3 b0 b1 b2 b3 then (1 : Felt) else 0) ::
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
      rest)) := by
  obtain ⟨stk, mem, locs, adv, evts⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  simpa [exec] using
    u128_overflowing_mul_run (fun _ => none) 115 a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3

end MidenLean.Proofs
