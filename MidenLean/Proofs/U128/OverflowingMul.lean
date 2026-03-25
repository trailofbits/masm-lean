import MidenLean.Proofs.U128.Common
import MidenLean.Proofs.Tactics
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

@[miden_dispatch] theorem stepNeqImm (v : Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ (.neqImm v) =
    some ⟨(if a != v then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execNeqImm
  rfl

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

set_option maxHeartbeats 12000000 in
private theorem u128_mul_low_chunk1_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (hb0 : b0.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      u128_mul_low_chunk1 =
    some ⟨
      b1 ::
      u128MulP1 a0 a1 b0 ::
      u128MulO1a a0 a1 b0 ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
      u128MulC0 a0 b0 ::
      rest,
      mem, locs, adv⟩ := by
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

set_option maxHeartbeats 12000000 in
private theorem u128_mul_low_chunk2_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true) (ha2 : a2.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨b1 ::
        u128MulP1 a0 a1 b0 ::
        u128MulO1a a0 a1 b0 ::
        a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        u128MulC0 a0 b0 ::
        rest,
        mem, locs, adv⟩
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
      mem, locs, adv⟩ := by
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

set_option maxHeartbeats 12000000 in
private theorem u128_mul_low_chunk3_add3_step
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
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
        mem, locs, adv⟩
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
      mem, locs, adv⟩ := by
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
    (mem locs : Nat → Felt) (adv : List Felt)
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
        mem, locs, adv⟩
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
      mem, locs, adv⟩ := by
  simpa [u128MulO2Sum, u128MulO2Carry2, Nat.add_comm] using
    (stepU32WidenAdd (mem := mem) (locs := locs) (adv := adv)
      (a := u128MulO2Partial a0 a1 a2 b0 b1 b2)
      (b := u128MulO1Carry a0 a1 b0 b1)
      (rest := u128MulO2Carry1 a0 a1 a2 b0 b1 b2 ::
        a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        u128MulC0 a0 b0 :: u128MulC1 a0 a1 b0 b1 :: u128MulC2 a0 a1 a2 b0 b1 b2 :: rest)
      (ha := hO2Partial_u32) (hb := hO1Carry_u32))

set_option maxHeartbeats 12000000 in
private theorem u128_mul_low_chunk3_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
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
        mem, locs, adv⟩
      u128_mul_low_chunk3 =
    some ⟨
      u128MulO2Sum a0 a1 a2 b0 b1 b2 ::
      u128MulO2Carry a0 a1 a2 b0 b1 b2 ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      rest,
      mem, locs, adv⟩ := by
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
          mem, locs, adv⟩
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
        mem, locs, adv⟩ := by
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
          mem, locs, adv⟩
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
        mem, locs, adv⟩ := by
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

set_option maxHeartbeats 12000000 in
theorem u128_mul_low_chunk_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (_ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (_hb3 : b3.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      u128_mul_low_chunk =
    some ⟨
      u128MulO2Sum a0 a1 a2 b0 b1 b2 ::
      u128MulO2Carry a0 a1 a2 b0 b1 b2 ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      rest,
      mem, locs, adv⟩ := by
  rw [u128_mul_low_chunk_decomp, execWithEnv_append]
  rw [u128_mul_low_chunk1_run env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv ha0 ha1 hb0]
  miden_bind
  rw [execWithEnv_append]
  rw [u128_mul_low_chunk2_run env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
    ha0 ha1 ha2 hb0 hb1]
  miden_bind
  rw [u128_mul_low_chunk3_run env fuel a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
    ha0 ha1 ha2 hb0 hb1 hb2]

set_option maxHeartbeats 8000000 in
theorem u128_overflowing_mul_c3_chunk_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
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
        mem, locs, adv⟩
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
      mem, locs, adv⟩ := by
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
    (mem locs : Nat → Felt) (adv : List Felt) :
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
        mem, locs, adv⟩
      u128_overflowing_mul_overflow_acc_chunk =
    some ⟨
      (if u128MulCarryOverflowBool a0 a1 a2 a3 b0 b1 b2 b3 then (1 : Felt) else 0) ::
      u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      rest,
      mem, locs, adv⟩ := by
  unfold u128_overflowing_mul_overflow_acc_chunk execWithEnv execInstruction
    execSwap execMovup execAdd execNeqImm removeNth
  simp [MidenState.withStack, u128MulCarryOverflowBool]

set_option maxHeartbeats 8000000 in
private theorem u128_overflowing_mul_overflow_products_chunk1_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
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
        mem, locs, adv⟩
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
      mem, locs, adv⟩ := by
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

set_option maxHeartbeats 8000000 in
private theorem u128_overflowing_mul_overflow_products_chunk2_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
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
        mem, locs, adv⟩
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
      mem, locs, adv⟩ := by
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

set_option maxHeartbeats 8000000 in
private theorem u128_overflowing_mul_overflow_products_chunk3_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
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
        mem, locs, adv⟩
      u128_overflowing_mul_overflow_products_chunk3 =
    some ⟨
      (if u128MulOverflowBool a0 a1 a2 a3 b0 b1 b2 b3 then (1 : Felt) else 0) ::
      u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      rest,
      mem, locs, adv⟩ := by
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

set_option maxHeartbeats 8000000 in
theorem u128_overflowing_mul_overflow_products_chunk_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
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
        mem, locs, adv⟩
      u128_overflowing_mul_overflow_products_chunk =
    some ⟨
      (if u128MulOverflowBool a0 a1 a2 a3 b0 b1 b2 b3 then (1 : Felt) else 0) ::
      u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
      a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      rest,
      mem, locs, adv⟩ := by
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
    (mem locs : Nat → Felt) (adv : List Felt) :
    execWithEnv env (fuel + 1)
      ⟨overflow :: c3 :: a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: c0 :: c1 :: c2 :: rest,
        mem, locs, adv⟩
      u128_overflowing_mul_cleanup_chunk =
    some ⟨overflow :: c0 :: c1 :: c2 :: c3 :: rest, mem, locs, adv⟩ := by
  unfold u128_overflowing_mul_cleanup_chunk execWithEnv execInstruction
    execMovup execDrop execSwap execMovdn removeNth insertAt
  simp [MidenState.withStack]

set_option maxHeartbeats 12000000 in
theorem u128_overflowing_mul_run
    (env : ProcEnv) (fuel : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt)
    (mem locs : Nat → Felt) (adv : List Felt)
    (ha0 : a0.isU32 = true) (ha1 : a1.isU32 = true)
    (ha2 : a2.isU32 = true) (ha3 : a3.isU32 = true)
    (hb0 : b0.isU32 = true) (hb1 : b1.isU32 = true)
    (hb2 : b2.isU32 = true) (hb3 : b3.isU32 = true) :
    execWithEnv env (fuel + 1)
      ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, locs, adv⟩
      Miden.Core.U128.overflowing_mul =
    some ⟨
      (if u128MulOverflowBool a0 a1 a2 a3 b0 b1 b2 b3 then (1 : Felt) else 0) ::
      u128MulC0 a0 b0 ::
      u128MulC1 a0 a1 b0 b1 ::
      u128MulC2 a0 a1 a2 b0 b1 b2 ::
      u128MulC3 a0 a1 a2 a3 b0 b1 b2 b3 ::
      rest,
      mem, locs, adv⟩ := by
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

set_option maxHeartbeats 12000000 in
/-- `u128::overflowing_mul` correctly computes the low 128 bits of the product and an overflow flag.
    Input stack:  [b0, b1, b2, b3, a0, a1, a2, a3] ++ rest
    Output stack: [overflow, c0, c1, c2, c3] ++ rest
    where `c0..c3` are the low-to-high limbs of `(a * b) mod 2^128`
    and `overflow` is `1` exactly when the discarded high part is nonzero. -/
theorem u128_overflowing_mul_raw
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
  obtain ⟨stk, mem, locs, adv⟩ := s
  simp only [MidenState.withStack] at hs ⊢
  subst hs
  simpa [exec] using
    u128_overflowing_mul_run (fun _ => none) 115 a0 a1 a2 a3 b0 b1 b2 b3 rest mem locs adv
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3

-- ============================================================================
-- Multiplication limb bridge: u128MulC0..C3 = (a * b).a0..a3.val
-- ============================================================================

/-- Helper: `(x + y % m) % m = (x + y) % m` (modular flattening). -/
private theorem add_mod_mod (x y m : Nat) : (x + y % m) % m = (x + y) % m := by
  rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl m), ← Nat.add_mod]

private theorem u128MulC0_eq (a b : U128) :
    u128MulC0 a.a0.val b.a0.val = (a * b).a0.val := by
  simp only [u128MulC0, HMul.hMul, Mul.mul, U128.ofNat_a0, U128.toNat]
  congr 1
  set a0 := a.a0.val.val; set a1 := a.a1.val.val; set a2 := a.a2.val.val; set a3 := a.a3.val.val
  set b0 := b.a0.val.val; set b1 := b.a1.val.val; set b2 := b.a2.val.val; set b3 := b.a3.val.val
  show b0 * a0 % 2^32 = (a3 * 2^96 + a2 * 2^64 + a1 * 2^32 + a0) *
    (b3 * 2^96 + b2 * 2^64 + b1 * 2^32 + b0) % 2^32
  suffices h : ∃ k, (a3 * 2^96 + a2 * 2^64 + a1 * 2^32 + a0) *
      (b3 * 2^96 + b2 * 2^64 + b1 * 2^32 + b0) = b0 * a0 + k * 2^32 by
    obtain ⟨k, hk⟩ := h; rw [hk]; omega
  exact ⟨a0*b1 + a1*b0 + (a0*b2 + a1*b1 + a2*b0)*2^32 +
      (a0*b3 + a1*b2 + a2*b1 + a3*b0)*2^64 +
      (a1*b3 + a2*b2 + a3*b1)*2^96 + (a2*b3 + a3*b2)*2^128 + a3*b3*2^160, by ring⟩

private theorem u128MulC1_eq (a b : U128) :
    u128MulC1 a.a0.val a.a1.val b.a0.val b.a1.val = (a * b).a1.val := by
  simp only [u128MulC1, u128MulP1, u128MulO0,
    HMul.hMul, Mul.mul, U128.ofNat_a1, U128.toNat]
  congr 1
  set a0 := a.a0.val.val; set a1 := a.a1.val.val; set a2 := a.a2.val.val; set a3 := a.a3.val.val
  set b0 := b.a0.val.val; set b1 := b.a1.val.val; set b2 := b.a2.val.val; set b3 := b.a3.val.val
  show (b1 * a0 + (Felt.ofNat ((b0 * a1 + (Felt.ofNat (b0 * a0 / 2 ^ 32)).val) % 2 ^ 32)).val) %
    2 ^ 32 = (a3 * 2^96 + a2 * 2^64 + a1 * 2^32 + a0) *
    (b3 * 2^96 + b2 * 2^64 + b1 * 2^32 + b0) / 2 ^ 32 % 2 ^ 32
  rw [u32_mod_val,
      felt_ofNat_val_lt _ (u32_prod_div_lt_prime b.a0.val a.a0.val b.a0.isU32 a.a0.isU32),
      add_mod_mod]
  -- Goal: (b1*a0 + b0*a1 + b0*a0/2^32) % 2^32 = P / 2^32 % 2^32
  suffices h : ∃ K, (a3 * 2 ^ 96 + a2 * 2 ^ 64 + a1 * 2 ^ 32 + a0) *
      (b3 * 2 ^ 96 + b2 * 2 ^ 64 + b1 * 2 ^ 32 + b0) =
      b0 * a0 + (b0 * a1 + b1 * a0 + K * 2 ^ 32) * 2 ^ 32 by
    obtain ⟨K, hK⟩ := h; rw [hK]
    set p := b0 * a0; set q := b0 * a1; set r := b1 * a0
    omega
  exact ⟨a0*b2 + a1*b1 + a2*b0 + (a0*b3 + a1*b2 + a2*b1 + a3*b0)*2^32 +
      (a1*b3 + a2*b2 + a3*b1)*2^64 + (a2*b3 + a3*b2)*2^96 + a3*b3*2^128, by ring⟩

/-- Carry-splitting identity: `x / m + (y + x % m) / m = (x + y) / m`. -/
private theorem div_add_mod_div (x y m : Nat) (hm : 0 < m) :
    x / m + (y + x % m) / m = (x + y) / m := by
  have hdm := Nat.div_add_mod x m
  have heq : x + y = m * (x / m) + (x % m + y) := by omega
  rw [Nat.add_comm y (x % m)]
  conv_rhs => rw [heq, Nat.mul_add_div hm]

private theorem u128MulC2_eq (a b : U128) :
    u128MulC2 a.a0.val a.a1.val a.a2.val b.a0.val b.a1.val b.a2.val = (a * b).a2.val := by
  simp only [u128MulC2, u128MulP2b, u128MulP2a, u128MulO1Sum, u128MulO1a, u128MulO1b,
    u128MulP1, u128MulO0, HMul.hMul, Mul.mul, U128.ofNat_a2, U128.toNat]
  congr 1
  simp only [Nat.mul_def]
  -- Step 1: Eliminate all mod round-trips at once: (Felt.ofNat (n % 2^32)).val = n % 2^32
  simp only [u32_mod_val]
  -- Step 2: Eliminate div round-trips, innermost first
  -- O0: (Felt.ofNat (b0*a0/2^32)).val
  rw [felt_ofNat_val_lt _ (u32_prod_div_lt_prime b.a0.val a.a0.val b.a0.isU32 a.a0.isU32)]
  -- Now establish u32 bounds for limbs
  have ha0 : a.a0.val.val < 2^32 := by
    have := a.a0.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
  have ha1 : a.a1.val.val < 2^32 := by
    have := a.a1.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
  have hb0 : b.a0.val.val < 2^32 := by
    have := b.a0.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
  have hb1 : b.a1.val.val < 2^32 := by
    have := b.a1.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
  -- O1a: (Felt.ofNat ((b0*a1 + b0*a0/2^32) / 2^32)).val
  have hO1a_bound : (b.a0.val.val * a.a1.val.val + b.a0.val.val * a.a0.val.val / 2^32) / 2^32 < GOLDILOCKS_PRIME := by
    have hprod : b.a0.val.val * a.a0.val.val / 2^32 < 2^32 := by
      calc b.a0.val.val * a.a0.val.val / 2^32
          ≤ (2^32-1)*(2^32-1) / 2^32 := Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))
        _ < 2^32 := by native_decide
    have hsum : b.a0.val.val * a.a1.val.val + b.a0.val.val * a.a0.val.val / 2^32
        ≤ (2^32-1)*(2^32-1) + (2^32-1) := by
      have := Nat.mul_le_mul (show b.a0.val.val ≤ 2^32-1 by omega) (show a.a1.val.val ≤ 2^32-1 by omega)
      omega
    calc (b.a0.val.val * a.a1.val.val + b.a0.val.val * a.a0.val.val / 2^32) / 2^32
        ≤ ((2^32-1)*(2^32-1) + (2^32-1)) / 2^32 := Nat.div_le_div_right hsum
      _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide
  rw [felt_ofNat_val_lt _ hO1a_bound]
  -- O1b: (Felt.ofNat ((b1*a0 + (b0*a1 + b0*a0/2^32) % 2^32) / 2^32)).val
  have hO1b_bound : (b.a1.val.val * a.a0.val.val +
      (b.a0.val.val * a.a1.val.val + b.a0.val.val * a.a0.val.val / 2^32) % 2^32) / 2^32 < GOLDILOCKS_PRIME := by
    have hsum : b.a1.val.val * a.a0.val.val +
        (b.a0.val.val * a.a1.val.val + b.a0.val.val * a.a0.val.val / 2^32) % 2^32
        ≤ (2^32-1)*(2^32-1) + (2^32-1) := by
      have := Nat.mul_le_mul (show b.a1.val.val ≤ 2^32-1 by omega) (show a.a0.val.val ≤ 2^32-1 by omega)
      omega
    calc (b.a1.val.val * a.a0.val.val +
        (b.a0.val.val * a.a1.val.val + b.a0.val.val * a.a0.val.val / 2^32) % 2^32) / 2^32
        ≤ ((2^32-1)*(2^32-1) + (2^32-1)) / 2^32 := Nat.div_le_div_right hsum
      _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide
  rw [felt_ofNat_val_lt _ hO1b_bound]
  -- Apply div_add_mod_div to simplify O1a + O1b carry chain
  rw [div_add_mod_div _ _ _ (by norm_num : (0 : Nat) < 2^32)]
  -- Flatten nested mods
  rw [add_mod_mod]
  -- Now set variables and use suffices
  set a0 := a.a0.val.val; set a1 := a.a1.val.val; set a2 := a.a2.val.val; set a3 := a.a3.val.val
  set b0 := b.a0.val.val; set b1 := b.a1.val.val; set b2 := b.a2.val.val; set b3 := b.a3.val.val
  -- Flatten remaining nested mods
  rw [add_mod_mod]
  -- Reassociate to expose add_mod_mod pattern
  rw [show b2 * a0 + (b1 * a1 + (b0 * a2 + (b0 * a1 + b0 * a0 / 2 ^ 32 + b1 * a0) / 2 ^ 32) % 2 ^ 32) =
    b2 * a0 + b1 * a1 + (b0 * a2 + (b0 * a1 + b0 * a0 / 2 ^ 32 + b1 * a0) / 2 ^ 32) % 2 ^ 32 from by omega]
  rw [add_mod_mod]
  -- Use suffices with existential form
  suffices h : ∃ K, (a3 * 2 ^ 96 + a2 * 2 ^ 64 + a1 * 2 ^ 32 + a0) *
      (b3 * 2 ^ 96 + b2 * 2 ^ 64 + b1 * 2 ^ 32 + b0) =
      b0 * a0 + (b0 * a1 + b1 * a0 +
        (b0 * a2 + b1 * a1 + b2 * a0 + K * 2 ^ 32) * 2 ^ 32) * 2 ^ 32 by
    obtain ⟨K, hK⟩ := h; rw [hK]
    set p := b0 * a0; set q := b0 * a1; set r := b1 * a0
    set s := b0 * a2; set t := b1 * a1; set u := b2 * a0
    omega
  exact ⟨a0*b3 + a1*b2 + a2*b1 + a3*b0 + (a1*b3 + a2*b2 + a3*b1)*2^32 +
      (a2*b3 + a3*b2)*2^64 + a3*b3*2^96, by ring⟩

private theorem u128MulC3_eq (a b : U128) :
    u128MulC3 a.a0.val a.a1.val a.a2.val a.a3.val b.a0.val b.a1.val b.a2.val b.a3.val =
    (a * b).a3.val := by
  simp only [u128MulC3, u128MulP3c, u128MulP3b, u128MulP3a, u128MulO2Sum,
    u128MulO1Carry, u128MulO2Partial, u128MulO2a, u128MulO2b, u128MulO2c,
    u128MulP2a, u128MulP2b, u128MulO1Sum, u128MulO1a, u128MulO1b,
    u128MulP1, u128MulO0, HMul.hMul, Mul.mul, U128.ofNat_a3, U128.toNat]
  congr 1
  simp only [Nat.mul_def]
  -- Step 1: Eliminate all mod round-trips
  simp only [u32_mod_val]
  -- Step 2: Eliminate div round-trips
  -- O0: (Felt.ofNat (b0*a0/2^32)).val
  rw [felt_ofNat_val_lt _ (u32_prod_div_lt_prime b.a0.val a.a0.val b.a0.isU32 a.a0.isU32)]
  -- Establish u32 bounds for limbs
  have ha0 : a.a0.val.val < 2^32 := by
    have := a.a0.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
  have ha1 : a.a1.val.val < 2^32 := by
    have := a.a1.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
  have ha2 : a.a2.val.val < 2^32 := by
    have := a.a2.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
  have hb0 : b.a0.val.val < 2^32 := by
    have := b.a0.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
  have hb1 : b.a1.val.val < 2^32 := by
    have := b.a1.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
  have hb2 : b.a2.val.val < 2^32 := by
    have := b.a2.isU32; simp only [Felt.isU32, decide_eq_true_eq] at this; exact this
  -- O1a bound
  have hO1a_bound : (b.a0.val.val * a.a1.val.val + b.a0.val.val * a.a0.val.val / 2^32) / 2^32 < GOLDILOCKS_PRIME := by
    have hprod : b.a0.val.val * a.a0.val.val / 2^32 < 2^32 := by
      calc b.a0.val.val * a.a0.val.val / 2^32
          ≤ (2^32-1)*(2^32-1) / 2^32 := Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))
        _ < 2^32 := by native_decide
    have hsum : b.a0.val.val * a.a1.val.val + b.a0.val.val * a.a0.val.val / 2^32
        ≤ (2^32-1)*(2^32-1) + (2^32-1) := by
      have := Nat.mul_le_mul (show b.a0.val.val ≤ 2^32-1 by omega) (show a.a1.val.val ≤ 2^32-1 by omega)
      omega
    calc (b.a0.val.val * a.a1.val.val + b.a0.val.val * a.a0.val.val / 2^32) / 2^32
        ≤ ((2^32-1)*(2^32-1) + (2^32-1)) / 2^32 := Nat.div_le_div_right hsum
      _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide
  rw [felt_ofNat_val_lt _ hO1a_bound]
  -- O1b bound
  have hO1b_bound : (b.a1.val.val * a.a0.val.val +
      (b.a0.val.val * a.a1.val.val + b.a0.val.val * a.a0.val.val / 2^32) % 2^32) / 2^32 < GOLDILOCKS_PRIME := by
    have hsum : b.a1.val.val * a.a0.val.val +
        (b.a0.val.val * a.a1.val.val + b.a0.val.val * a.a0.val.val / 2^32) % 2^32
        ≤ (2^32-1)*(2^32-1) + (2^32-1) := by
      have := Nat.mul_le_mul (show b.a1.val.val ≤ 2^32-1 by omega) (show a.a0.val.val ≤ 2^32-1 by omega)
      omega
    calc (b.a1.val.val * a.a0.val.val +
        (b.a0.val.val * a.a1.val.val + b.a0.val.val * a.a0.val.val / 2^32) % 2^32) / 2^32
        ≤ ((2^32-1)*(2^32-1) + (2^32-1)) / 2^32 := Nat.div_le_div_right hsum
      _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide
  rw [felt_ofNat_val_lt _ hO1b_bound]
  -- Apply div_add_mod_div for O1a + O1b
  rw [div_add_mod_div _ _ _ (by norm_num : (0 : Nat) < 2^32)]
  -- Now need to eliminate remaining div round-trips: O1Carry, O2a, O2b, O2c
  -- O1Carry: (Felt.ofNat ((...)/2^32/2^32)).val
  -- But first, note that (x/2^32)/2^32 is just x/2^64 for Nat.
  -- The O1Carry expression is now:
  --   (b0*a1 + b0*a0/2^32 + b1*a0) / 2^32 / 2^32
  -- which is a small number (< 2). Its Felt round-trip needs:
  have hO1Carry_bound :
      (b.a0.val.val * a.a1.val.val + b.a0.val.val * a.a0.val.val / 2^32 + b.a1.val.val * a.a0.val.val) / 2^32 / 2^32 < GOLDILOCKS_PRIME := by
    have hsum : b.a0.val.val * a.a1.val.val + b.a0.val.val * a.a0.val.val / 2^32 + b.a1.val.val * a.a0.val.val
        ≤ (2^32-1)*(2^32-1) + (2^32-1) + (2^32-1)*(2^32-1) := by
      have h1 := Nat.mul_le_mul (show b.a0.val.val ≤ 2^32-1 by omega) (show a.a1.val.val ≤ 2^32-1 by omega)
      have h2 := Nat.mul_le_mul (show b.a1.val.val ≤ 2^32-1 by omega) (show a.a0.val.val ≤ 2^32-1 by omega)
      have h3 : b.a0.val.val * a.a0.val.val / 2^32 ≤ (2^32-1) := by
        calc b.a0.val.val * a.a0.val.val / 2^32
            ≤ (2^32-1)*(2^32-1) / 2^32 := Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))
          _ ≤ 2^32-1 := by native_decide
      omega
    calc (b.a0.val.val * a.a1.val.val + b.a0.val.val * a.a0.val.val / 2^32 + b.a1.val.val * a.a0.val.val) / 2^32 / 2^32
        ≤ ((2^32-1)*(2^32-1) + (2^32-1) + (2^32-1)*(2^32-1)) / 2^32 / 2^32 := by
          apply Nat.div_le_div_right; apply Nat.div_le_div_right; exact hsum
      _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide
  rw [felt_ofNat_val_lt _ hO1Carry_bound]
  -- Abbreviate the carry1 sum for readability
  set C1 := (b.a0.val.val * a.a1.val.val + b.a0.val.val * a.a0.val.val / 2^32 + b.a1.val.val * a.a0.val.val) / 2^32
  -- Helper for bounding madd div round-trips: (x*y + z%2^32)/2^32 < GOLDILOCKS_PRIME
  -- when x,y < 2^32
  have madd_div_bound : ∀ x y z, x < 2^32 → y < 2^32 →
      (x * y + z % 2^32) / 2^32 < GOLDILOCKS_PRIME := by
    intro x y z hx hy
    have := Nat.mul_le_mul (show x ≤ 2^32-1 by omega) (show y ≤ 2^32-1 by omega)
    calc (x * y + z % 2^32) / 2^32
        ≤ ((2^32-1)*(2^32-1) + (2^32-1)) / 2^32 := by
          apply Nat.div_le_div_right; omega
      _ < GOLDILOCKS_PRIME := by unfold GOLDILOCKS_PRIME; native_decide
  -- O2a: (b0*a2 + C1%2^32) / 2^32
  rw [felt_ofNat_val_lt _ (madd_div_bound _ _ _ hb0 ha2)]
  -- O2b: (b1*a1 + (b0*a2 + C1%2^32) % 2^32) / 2^32
  rw [felt_ofNat_val_lt _ (madd_div_bound _ _ _ hb1 ha1)]
  -- O2c: (b2*a0 + (...) % 2^32) / 2^32
  rw [felt_ofNat_val_lt _ (madd_div_bound _ _ _ hb2 ha0)]
  -- Now simplify carry chain with div_add_mod_div
  -- First: O2a + O2b = (b0*a2 + C1%2^32)/2^32 + (b1*a1 + (b0*a2+C1%2^32)%2^32)/2^32
  --                   = (b0*a2 + C1%2^32 + b1*a1) / 2^32 (by div_add_mod_div)
  rw [div_add_mod_div _ _ _ (by norm_num : (0 : Nat) < 2^32)]
  -- Combine (O2a+O2b) with O2c:
  -- The inner mod (b1*a1 + (b0*a2 + C1%2^32)%2^32)%2^32 needs flattening first
  rw [add_mod_mod (ZMod.val b.a1.val * ZMod.val a.a1.val)
    (ZMod.val b.a0.val * ZMod.val a.a2.val + C1 % 2 ^ 32) (2 ^ 32)]
  -- Reassociate: b1*a1 + (b0*a2 + C1%2^32) = b0*a2 + C1%2^32 + b1*a1
  rw [show ZMod.val b.a1.val * ZMod.val a.a1.val +
        (ZMod.val b.a0.val * ZMod.val a.a2.val + C1 % 2 ^ 32) =
      ZMod.val b.a0.val * ZMod.val a.a2.val + C1 % 2 ^ 32 +
        ZMod.val b.a1.val * ZMod.val a.a1.val from by omega]
  -- Now apply div_add_mod_div for the combined O2 + O2c:
  rw [div_add_mod_div _ _ _ (by norm_num : (0 : Nat) < 2^32)]
  -- Now commute to put C1%2^32 at the end for div_add_mod_div with C1:
  -- Now the inner expr is: C1/2^32 + (b0*a2+C1%2^32+b1*a1+b2*a0)/2^32 % 2^32
  -- which is (C1/2^32 + ((b0*a2+C1%2^32+b1*a1+b2*a0)/2^32) % 2^32) % 2^32
  -- wrapped inside b0*a3 + ... % 2^32
  -- Use add_mod_mod without explicit args to flatten the (x + y%m) % m pattern
  rw [add_mod_mod (C1 / 2 ^ 32)]
  -- Now we have: (C1/2^32 + (b0*a2+C1%2^32+b1*a1+b2*a0)/2^32) in the inner expression
  -- Reassociate to put C1%2^32 at end for div_add_mod_div
  rw [show ZMod.val b.a0.val * ZMod.val a.a2.val + C1 % 2 ^ 32 +
        ZMod.val b.a1.val * ZMod.val a.a1.val + ZMod.val b.a2.val * ZMod.val a.a0.val =
      ZMod.val b.a0.val * ZMod.val a.a2.val + ZMod.val b.a1.val * ZMod.val a.a1.val +
        ZMod.val b.a2.val * ZMod.val a.a0.val + C1 % 2 ^ 32 from by omega]
  rw [div_add_mod_div _ _ _ (by norm_num : (0 : Nat) < 2^32)]
  -- Now set variables
  set a0 := a.a0.val.val; set a1 := a.a1.val.val; set a2 := a.a2.val.val; set a3 := a.a3.val.val
  set b0 := b.a0.val.val; set b1 := b.a1.val.val; set b2 := b.a2.val.val; set b3 := b.a3.val.val
  -- The LHS has form: (b3*a0 + (b2*a1 + (b1*a2 + (b0*a3 + (C1+S2)/2^32 % 2^32)) % 2^32)) % 2^32
  -- We need to flatten all the nested mods. Use Nat.add_mod repeatedly.
  -- Key identity: (x + y%m) % m = (x + y) % m
  -- But the nesting is (x + (y + z%m)) % m, so we need two-level flattening.
  -- Strategy: rewrite the inner (b0*a3 + (C1+S2)/2^32 % 2^32) using add_mod_mod first,
  -- but since it's not followed by % 2^32 directly, we need a different approach.
  -- Use suffices with the existing structure. The LHS still has C1 and nested divs,
  -- but C1 is a def abbreviation, so suffices + omega should work after providing
  -- the ring witness for the RHS.
  -- Use a two-level suffices decomposition.
  -- First level: factor the product at the 2^64 boundary
  suffices h : ∃ K, (a3 * 2 ^ 96 + a2 * 2 ^ 64 + a1 * 2 ^ 32 + a0) *
      (b3 * 2 ^ 96 + b2 * 2 ^ 64 + b1 * 2 ^ 32 + b0) =
      b0 * a0 + (b0 * a1 + b1 * a0) * 2 ^ 32 +
        (b0 * a2 + b1 * a1 + b2 * a0 +
          (b0 * a3 + b1 * a2 + b2 * a1 + b3 * a0 + K * 2 ^ 32) * 2 ^ 32) * 2 ^ 64 by
    obtain ⟨K, hK⟩ := h; rw [hK]
    -- Now the RHS is: (... + X*2^64) / 2^96 % 2^32 where X contains the level-3 info
    -- LHS: (b3*a0 + (b2*a1 + (b1*a2 + (b0*a3 + (C1+(b0*a2+b1*a1+b2*a0))/2^32 % 2^32)%2^32)%2^32)%2^32)%2^32
    -- After rw, the RHS has no nested div/mod, just plain division by 2^96
    -- The key: C1 = (b0*a1 + b0*a0/2^32 + b1*a0) / 2^32
    -- In terms of the structured product: the carry from limbs 0+1 is
    -- (b0*a0 + (b0*a1+b1*a0)*2^32) / 2^64 = C1 (needs proof)
    set p := b0 * a0
    set q := b0 * a1 + b1 * a0
    -- Provide Nat.div_add_mod relationships
    have hp_dm := Nat.div_add_mod p (2 ^ 32)
    -- C1 is the carry from limb 0+1: C1 = (q + p/2^32) / 2^32
    -- And: p + q*2^32 = p%2^32*1 + (q + p/2^32)%2^32 * 2^32 + C1 * 2^64
    -- Key: (p + q*2^32) / 2^64 = C1
    -- This is because (b0*a0 + (b0*a1+b1*a0)*2^32) / 2^32 / 2^32
    -- = (b0*a1+b1*a0 + b0*a0/2^32) / 2^32 = C1  (by Nat.add_mul_div_right)
    have hC1 : (p + q * 2 ^ 32) / 2 ^ 64 = C1 := by
      rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from by norm_num]
      rw [← Nat.div_div_eq_div_mul]
      rw [Nat.add_mul_div_right _ _ (show (0 : Nat) < 2 ^ 32 from by norm_num)]
      -- Now: (q + p / 2^32) / 2^32 = C1
      -- C1 = (b0*a1 + b0*a0/2^32 + b1*a0) / 2^32 = (q + p/2^32) / 2^32
      -- since q = b0*a1 + b1*a0 and p = b0*a0
      -- Need to show: (b0*a1+b1*a0 + b0*a0/2^32) / 2^32 = C1
      -- C1 is (b0*a1 + b0*a0/2^32 + b1*a0) / 2^32
      -- These differ only in addition order: q + p/2^32 vs b0*a1 + p/2^32 + b1*a0
      show (p / 2 ^ 32 + q) / 2 ^ 32 = C1
      -- q = b0*a1 + b1*a0, p = b0*a0, C1 = (b0*a1 + b0*a0/2^32 + b1*a0)/2^32
      -- = (b0*a1 + p/2^32 + b1*a0)/2^32 = (p/2^32 + q)/2^32
      -- This is definitionally equal since C1 := (b0*a1 + b0*a0/2^32 + b1*a0)/2^32
      -- and q := b0*a1 + b1*a0, p := b0*a0
      -- So (p/2^32 + q)/2^32 = (b0*a0/2^32 + b0*a1+b1*a0)/2^32
      -- which should equal C1 = (b0*a1 + b0*a0/2^32 + b1*a0)/2^32
      -- by commutativity of addition. But omega can't see this because it sees
      -- ZMod.val b.a0.val as different from b0 after unfolding.
      -- Rewrite C1 in terms of the set abbreviations, then close by congr + omega
      rw [show C1 = (b0 * a1 + b0 * a0 / 2^32 + b1 * a0) / 2^32 from by simp only [C1, b0, a0, a1, b1]]
      congr 1; omega
    -- Use hC1 to relate the structured product to C1
    -- Total = (p + q*2^32) + R*2^64 where R = b0*a2+b1*a1+b2*a0 + Z*2^32
    -- (p + q*2^32) = (p+q*2^32)%2^64 + C1*2^64 (by Nat.div_add_mod + hC1)
    -- So Total = (p+q*2^32)%2^64 + (C1 + R)*2^64
    -- Total / 2^96 = ((p+q*2^32)%2^64 + (C1+R)*2^64) / 2^96
    -- Since (p+q*2^32)%2^64 < 2^64 and (C1+R)*2^64 / 2^96 = (C1+R)/2^32:
    -- Total / 2^96 = (C1 + R) / 2^32  when (p+q*2^32)%2^64 < 2^64 (always true)
    -- + ((p+q*2^32)%2^64) / 2^96 which is 0.
    -- So Total / 2^96 = (C1 + R) / 2^32
    -- And the LHS is (b3*a0+b2*a1+b1*a2+b0*a3 + (C1+b0*a2+b1*a1+b2*a0)/2^32) % 2^32
    -- The RHS is Total/2^96 % 2^32 = (C1+R)/2^32 % 2^32
    -- where R = b0*a2+b1*a1+b2*a0 + Z*2^32, so (C1+R)/2^32 = (C1+b0*a2+b1*a1+b2*a0)/2^32 + Z
    -- And % 2^32 gives: (b0*a3+b1*a2+b2*a1+b3*a0 + (C1+b0*a2+b1*a1+b2*a0)/2^32) % 2^32
    -- Which matches the LHS!
    have hpq_dm := Nat.div_add_mod (p + q * 2 ^ 32) (2 ^ 64)
    have hpq_split : p + q * 2 ^ 32 = (p + q * 2 ^ 32) % 2 ^ 64 + C1 * 2 ^ 64 := by
      omega
    simp
    omega
  exact ⟨a1*b3 + a2*b2 + a3*b1 + (a2*b3 + a3*b2)*2^32 + a3*b3*2^64, by ring⟩

-- ============================================================================
-- List bridge: raw limb list = (a * b) limb list
-- ============================================================================

theorem u128MulResult_eq (a b : U128) (rest : List Felt) :
    u128MulC0 a.a0.val b.a0.val ::
    u128MulC1 a.a0.val a.a1.val b.a0.val b.a1.val ::
    u128MulC2 a.a0.val a.a1.val a.a2.val b.a0.val b.a1.val b.a2.val ::
    u128MulC3 a.a0.val a.a1.val a.a2.val a.a3.val b.a0.val b.a1.val b.a2.val b.a3.val ::
    rest =
    (a * b).a0.val :: (a * b).a1.val :: (a * b).a2.val :: (a * b).a3.val :: rest := by
  rw [u128MulC0_eq, u128MulC1_eq, u128MulC2_eq, u128MulC3_eq]

-- ============================================================================
-- High-level correctness theorem
-- ============================================================================

set_option maxHeartbeats 12000000 in
/-- `u128::overflowing_mul` correctly computes the low 128 bits of the product `a * b`
    and an overflow flag.
    Input stack:  [b.a0, b.a1, b.a2, b.a3, a.a0, a.a1, a.a2, a.a3] ++ rest
    Output stack: [overflow, (a*b).a0, (a*b).a1, (a*b).a2, (a*b).a3] ++ rest -/
theorem u128_overflowing_mul_correct (a b : U128) (rest : List Felt) (s : MidenState)
    (hs : s.stack = b.a0.val :: b.a1.val :: b.a2.val :: b.a3.val ::
                    a.a0.val :: a.a1.val :: a.a2.val :: a.a3.val :: rest) :
    exec 116 s Miden.Core.U128.overflowing_mul =
    some (s.withStack (
      (if u128MulOverflowBool a.a0.val a.a1.val a.a2.val a.a3.val
          b.a0.val b.a1.val b.a2.val b.a3.val then (1 : Felt) else 0) ::
      (a * b).a0.val :: (a * b).a1.val :: (a * b).a2.val :: (a * b).a3.val :: rest)) := by
  have h := u128_overflowing_mul_raw a.a0.val a.a1.val a.a2.val a.a3.val
    b.a0.val b.a1.val b.a2.val b.a3.val rest s hs
    a.a0.isU32 a.a1.isU32 a.a2.isU32 a.a3.isU32
    b.a0.isU32 b.a1.isU32 b.a2.isU32 b.a3.isU32
  rw [h]; congr 1; congr 1
  exact congrArg _ (u128MulResult_eq a b rest)

end MidenLean.Proofs
