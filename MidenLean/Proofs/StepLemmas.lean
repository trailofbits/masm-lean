import MidenLean.Proofs.Helpers

namespace MidenLean.StepLemmas

open MidenLean

-- ============================================================================
-- Stack manipulation
-- ============================================================================

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepDrop (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .drop =
    some ⟨rest, mem, frames, adv⟩ := by
  unfold execInstruction execDrop; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepDropw (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b c d : Felt) (rest : List Felt) :
    execInstruction ⟨a :: b :: c :: d :: rest, mem, frames, adv⟩ .dropw =
    some ⟨rest, mem, frames, adv⟩ := by
  unfold execInstruction execDropw; rfl

set_option maxHeartbeats 800000 in
/-- Parametric dup: copies the element at index `n` to the top of the stack. -/
@[miden_dispatch] theorem stepDup (n : Fin 16) (stk : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (v : Felt) (h : stk[n.val]? = some v) :
    execInstruction ⟨stk, mem, frames, adv⟩ (.dup n) =
    some ⟨v :: stk, mem, frames, adv⟩ := by
  unfold execInstruction execDup
  simp [h, MidenState.withStack]

set_option maxHeartbeats 4000000 in
/-- Parametric swap: swaps the top element with the element at index `n`.
    After the rewrite, the result stack contains `List.set` operations;
    use `dsimp only [List.set]` to normalize on concrete lists. -/
@[miden_dispatch] theorem stepSwap (n : Fin 16) (stk : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hn : (n.val == 0) = false)
    (top nth : Felt) (htop : stk[0]? = some top) (hnth : stk[n.val]? = some nth) :
    execInstruction ⟨stk, mem, frames, adv⟩ (.swap n) =
    some ⟨(stk.set 0 nth).set n.val top, mem, frames, adv⟩ := by
  unfold execInstruction execSwap
  simp [hn, htop, hnth, MidenState.withStack]

-- movup and movdn: parametric forms

set_option maxHeartbeats 4000000 in
/-- Parametric movup: removes element at index `n` and places it on top.
    After the rewrite, the result stack contains `List.eraseIdx`;
    use `dsimp only [List.eraseIdx]` to normalize on concrete lists. -/
@[miden_dispatch] theorem stepMovup (n : Nat) (stk : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (v : Felt) (hn : (n < 2 || n > 15) = false) (hv : stk[n]? = some v) :
    execInstruction ⟨stk, mem, frames, adv⟩ (.movup n) =
    some ⟨v :: stk.eraseIdx n, mem, frames, adv⟩ := by
  unfold execInstruction execMovup removeNth
  simp [hn, hv, MidenState.withStack]

set_option maxHeartbeats 4000000 in
/-- Parametric movdn: pops the top element and inserts it at position `n`.
    After the rewrite, the result stack contains `insertAt`;
    use `dsimp only [insertAt, List.take, List.drop, List.append]` to normalize. -/
@[miden_dispatch] theorem stepMovdn (n : Nat) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (top : Felt) (rest : List Felt) (hn : (n < 2 || n > 15) = false) :
    execInstruction ⟨top :: rest, mem, frames, adv⟩ (.movdn n) =
    some ⟨insertAt rest n top, mem, frames, adv⟩ := by
  unfold execInstruction execMovdn
  simp [hn, MidenState.withStack]

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepReversew (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b c d : Felt) (rest : List Felt) :
    execInstruction ⟨a :: b :: c :: d :: rest, mem, frames, adv⟩ .reversew =
    some ⟨d :: c :: b :: a :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execReversew; rfl

set_option maxHeartbeats 800000 in
@[miden_dispatch] theorem stepDupw0 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b c d : Felt) (rest : List Felt) :
    execInstruction ⟨a :: b :: c :: d :: rest, mem, frames, adv⟩ (.dupw 0) =
    some ⟨a :: b :: c :: d :: a :: b :: c :: d :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execDupw
  simp [MidenState.withStack]

set_option maxHeartbeats 800000 in
@[miden_dispatch] theorem stepDupw1 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) :
    execInstruction ⟨a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest, mem, frames, adv⟩ (.dupw 1) =
    some ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execDupw
  simp [MidenState.withStack]

set_option maxHeartbeats 800000 in
@[miden_dispatch] theorem stepSwapw1 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) :
    execInstruction ⟨a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest, mem, frames, adv⟩ (.swapw 1) =
    some ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execSwapw
  simp [MidenState.withStack]

-- ============================================================================
-- Assertions
-- ============================================================================

set_option maxHeartbeats 400000 in
/-- assert succeeds when top of stack is 1, pops it. -/
@[miden_dispatch] theorem stepAssert (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt) (h : a.val = 1) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .assert =
    some ⟨rest, mem, frames, adv⟩ := by
  unfold execInstruction execAssert
  simp [h, MidenState.withStack]

set_option maxHeartbeats 400000 in
/-- assertWithError behaves identically to assert (error string is for debugging). -/
@[miden_dispatch] theorem stepAssertWithError (msg : String) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt) (h : a.val = 1) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ (.assertWithError msg) =
    some ⟨rest, mem, frames, adv⟩ := by
  unfold execInstruction execAssert
  simp [h, MidenState.withStack]

set_option maxHeartbeats 400000 in
/-- assertz succeeds when top of stack is 0, pops it. -/
@[miden_dispatch] theorem stepAssertz (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.val = 0) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .assertz =
    some ⟨rest, mem, frames, adv⟩ := by
  unfold execInstruction execAssertz
  simp [ha, MidenState.withStack]

set_option maxHeartbeats 400000 in
/-- assertEq succeeds when top two elements are equal, pops both. -/
@[miden_dispatch] theorem stepAssertEq (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: a :: rest, mem, frames, adv⟩ .assertEq =
    some ⟨rest, mem, frames, adv⟩ := by
  unfold execInstruction execAssertEq
  simp [MidenState.withStack]

set_option maxHeartbeats 400000 in
/-- assertEqWithError behaves identically to assertEq. -/
@[miden_dispatch] theorem stepAssertEqWithError (msg : String) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: a :: rest, mem, frames, adv⟩ (.assertEqWithError msg) =
    some ⟨rest, mem, frames, adv⟩ := by
  unfold execInstruction execAssertEq
  simp [MidenState.withStack]

-- ============================================================================
-- Assertion failure lemmas (for forward-direction proofs)
-- ============================================================================

set_option maxHeartbeats 400000 in
/-- assertWithError returns none when the top value is not 1. -/
theorem stepAssertWithError_none (msg : String) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt) (h : a.val ≠ 1) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ (.assertWithError msg) = none := by
  unfold execInstruction execAssert
  simp [show ¬(a.val == 1) = true from by simp [h]]

set_option maxHeartbeats 400000 in
/-- assertEqWithError returns none when the top two values differ. -/
theorem stepAssertEqWithError_none (msg : String) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt) (h : a ≠ b) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ (.assertEqWithError msg) = none := by
  unfold execInstruction execAssertEq
  simp [show ¬(a == b) = true from by simp [h]]

-- ============================================================================
-- U32 assertions
-- ============================================================================

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32Assert2 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨a :: b :: rest, mem, frames, adv⟩ .u32Assert2 =
    some ⟨a :: b :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Assert2
  simp [ha, hb]

-- ============================================================================
-- Field comparison
-- ============================================================================

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepEqImm (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (v a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ (.eqImm v) =
    some ⟨(if a == v then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execEqImm; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepEq (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .eq =
    some ⟨(if a == b then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execEq; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepNeq (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .neq =
    some ⟨(if a != b then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execNeq; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepLt (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .lt =
    some ⟨(if a.val < b.val then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execLt; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepGt (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .gt =
    some ⟨(if a.val > b.val then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execGt; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepLte (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .lte =
    some ⟨(if a.val ≤ b.val then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execLte; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepGte (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .gte =
    some ⟨(if a.val ≥ b.val then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execGte; rfl

-- ============================================================================
-- Field boolean
-- ============================================================================

set_option maxHeartbeats 800000 in
@[miden_dispatch] theorem stepAndIte (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (rest : List Felt) (p q : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) :: (if q then (1 : Felt) else 0) :: rest, mem, frames, adv⟩
      Instruction.and =
    some ⟨(if q && p then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execAnd
  simp only [Felt.isBool_ite_bool, MidenState.withStack]
  cases p <;> cases q <;> simp

set_option maxHeartbeats 800000 in
@[miden_dispatch] theorem stepOrIte (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (rest : List Felt) (p q : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) :: (if q then (1 : Felt) else 0) :: rest, mem, frames, adv⟩
      Instruction.or =
    some ⟨(if q || p then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execOr
  simp only [Felt.isBool_ite_bool, MidenState.withStack]
  cases p <;> cases q <;> simp

set_option maxHeartbeats 800000 in
@[miden_dispatch] theorem stepNotIte (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (rest : List Felt) (p : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) :: rest, mem, frames, adv⟩
      Instruction.not =
    some ⟨(if !p then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execNot
  simp only [Felt.isBool_ite_bool, MidenState.withStack]
  cases p <;> simp

-- ============================================================================
-- Conditional stack manipulation
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- cswap on a boolean condition (as ite): if true, swap the two elements below. -/
@[miden_dispatch] theorem stepCswapIte (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (rest : List Felt) (a b : Felt) (p : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) :: b :: a :: rest, mem, frames, adv⟩
      .cswap =
    some ⟨(if p then a else b) :: (if p then b else a) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execCswap
  simp only [MidenState.withStack]
  cases p <;> simp

set_option maxHeartbeats 800000 in
/-- cdrop on a boolean condition (as ite): if true, keep b; if false, keep a. -/
@[miden_dispatch] theorem stepCdropIte (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (rest : List Felt) (a b : Felt) (p : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) :: b :: a :: rest, mem, frames, adv⟩
      .cdrop =
    some ⟨(if p then b else a) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execCdrop
  simp only [MidenState.withStack]
  cases p <;> simp

set_option maxHeartbeats 800000 in
/-- cdropw on a boolean condition (as ite): if true, keep the word `b`; if false, keep the word `a`. -/
@[miden_dispatch] theorem stepCdropwIte (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (rest : List Felt)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (p : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) ::
          b0 :: b1 :: b2 :: b3 ::
          a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩
      .cdropw =
    some ⟨
      (if p then b0 else a0) ::
      (if p then b1 else a1) ::
      (if p then b2 else a2) ::
      (if p then b3 else a3) ::
      rest, mem, frames, adv⟩ := by
  unfold execInstruction execCdropw
  simp only [MidenState.withStack]
  cases p <;> simp

-- ============================================================================
-- Field arithmetic
-- ============================================================================

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepAdd (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .add =
    some ⟨(a + b) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execAdd; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepAddImm (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (v a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ (.addImm v) =
    some ⟨(a + v) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execAddImm; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepSub (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .sub =
    some ⟨(a - b) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execSub; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepMul (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .mul =
    some ⟨(a * b) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execMul; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepNeg (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .neg =
    some ⟨(-a) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execNeg; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepIncr (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .incr =
    some ⟨(a + 1) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execIncr; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepPush (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (v : Felt) (stk : List Felt) :
    execInstruction ⟨stk, mem, frames, adv⟩ (.push v) =
    some ⟨v :: stk, mem, frames, adv⟩ := by
  unfold execInstruction execPush; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepPadw (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (stk : List Felt) :
    execInstruction ⟨stk, mem, frames, adv⟩ .padw =
    some ⟨(0 : Felt) :: 0 :: 0 :: 0 :: stk, mem, frames, adv⟩ := by
  unfold execInstruction execPadw; rfl

-- ============================================================================
-- Pow2
-- ============================================================================

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepPow2 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.val ≤ 63) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .pow2 =
    some ⟨Felt.ofNat (2^a.val) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execPow2
  simp [show ¬(a.val > 63) from by omega, MidenState.withStack]

-- ============================================================================
-- U32 arithmetic
-- ============================================================================

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32WidenAdd (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32WidenAdd =
    some ⟨Felt.ofNat ((a.val + b.val) % 2^32) ::
          Felt.ofNat ((a.val + b.val) / 2^32) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32WidenAdd u32WideAdd u32Max
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32OverflowAdd (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32OverflowAdd =
    some ⟨Felt.ofNat ((a.val + b.val) / 2^32) ::
          Felt.ofNat ((a.val + b.val) % 2^32) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32OverflowAdd u32WideAdd u32Max
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32WidenAdd3 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b c : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    execInstruction ⟨c :: b :: a :: rest, mem, frames, adv⟩ .u32WidenAdd3 =
    some ⟨Felt.ofNat ((a.val + b.val + c.val) % 2^32) ::
          Felt.ofNat ((a.val + b.val + c.val) / 2^32) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32WidenAdd3 u32WideAdd3 u32Max
  simp [ha, hb, hc, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32OverflowSub (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32OverflowSub =
    some ⟨Felt.ofNat (u32OverflowingSub a.val b.val).1 ::
          Felt.ofNat (u32OverflowingSub a.val b.val).2 ::
          rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32OverflowSub
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32WidenMul (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32WidenMul =
    some ⟨Felt.ofNat ((a.val * b.val) % 2^32) ::
          Felt.ofNat ((a.val * b.val) / 2^32) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32WidenMul u32WideMul u32Max
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32WidenMadd (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b c : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    execInstruction ⟨b :: a :: c :: rest, mem, frames, adv⟩ .u32WidenMadd =
    some ⟨Felt.ofNat ((a.val * b.val + c.val) % 2^32) ::
          Felt.ofNat ((a.val * b.val + c.val) / 2^32) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32WidenMadd u32WideMadd u32Max
  simp [ha, hb, hc, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32WrappingMadd (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b c : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    execInstruction ⟨b :: a :: c :: rest, mem, frames, adv⟩ .u32WrappingMadd =
    some ⟨Felt.ofNat ((a.val * b.val + c.val) % 2^32) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32WrappingMadd u32Max
  simp [ha, hb, hc, MidenState.withStack]

-- ============================================================================
-- U32 bitwise (require isU32 preconditions)
-- ============================================================================

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32And (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32And =
    some ⟨Felt.ofNat (a.val &&& b.val) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32And
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32Or (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32Or =
    some ⟨Felt.ofNat (a.val ||| b.val) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Or
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32Xor (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32Xor =
    some ⟨Felt.ofNat (a.val ^^^ b.val) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Xor
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32Not (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .u32Not =
    some ⟨Felt.ofNat (u32Max - 1 - a.val) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Not u32Max
  simp [ha, MidenState.withStack]

-- ============================================================================
-- U32 comparison (require isU32 preconditions)
-- ============================================================================

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32Lt (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32Lt =
    some ⟨(if a.val < b.val then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Lt
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32Gt (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32Gt =
    some ⟨(if a.val > b.val then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Gt
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32Lte (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32Lte =
    some ⟨(if a.val ≤ b.val then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Lte
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32Gte (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32Gte =
    some ⟨(if a.val ≥ b.val then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Gte
  simp [ha, hb, MidenState.withStack]

-- ============================================================================
-- U32 bit counting
-- ============================================================================

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32Clz (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .u32Clz =
    some ⟨Felt.ofNat (u32CountLeadingZeros a.val) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Clz
  simp [ha, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32Ctz (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .u32Ctz =
    some ⟨Felt.ofNat (u32CountTrailingZeros a.val) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Ctz
  simp [ha, MidenState.withStack]

set_option maxHeartbeats 4000000 in
/-- u32Clo: count leading ones, expressed via u32CountLeadingZeros on the bitwise complement.
    (u32CountLeadingOnes is private in Semantics.) -/
@[miden_dispatch] theorem stepU32Clo (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .u32Clo =
    some ⟨Felt.ofNat (u32CountLeadingZeros (u32Max - 1 - a.val)) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Clo u32CountLeadingOnes
  simp [ha, MidenState.withStack]

set_option maxHeartbeats 4000000 in
/-- u32Cto: count trailing ones, expressed via u32CountTrailingZeros on the XOR complement.
    (u32CountTrailingOnes is private in Semantics.) -/
@[miden_dispatch] theorem stepU32Cto (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .u32Cto =
    some ⟨Felt.ofNat (u32CountTrailingZeros (a.val ^^^ (u32Max - 1))) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Cto u32CountTrailingOnes
  simp [ha, MidenState.withStack]

-- ============================================================================
-- U32 split
-- ============================================================================

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepU32Split (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .u32Split =
    some ⟨a.lo32 :: a.hi32 :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Split; rfl

-- ============================================================================
-- Field div (requires nonzero divisor)
-- ============================================================================

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepDiv (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (hb : (b == (0 : Felt)) = false) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .div =
    some ⟨(a * b⁻¹) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execDiv
  simp [hb, MidenState.withStack]

-- ============================================================================
-- U32 divmod (requires isU32 and nonzero divisor)
-- ============================================================================

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32DivMod (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true)
    (hbnz : (b.val == 0) = false) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32DivMod =
    some ⟨Felt.ofNat (a.val % b.val) :: Felt.ofNat (a.val / b.val) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32DivMod
  simp [ha, hb, hbnz, MidenState.withStack]

-- ============================================================================
-- Emit (no-op)
-- ============================================================================

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepEmitImm (n : Nat) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (stk : List Felt) :
    execInstruction ⟨stk, mem, frames, adv⟩ (.emitImm n) =
    some ⟨stk, mem, frames, adv⟩ := by
  unfold execInstruction; rfl

-- ============================================================================
-- Advice stack
-- ============================================================================

set_option maxHeartbeats 800000 in
@[miden_dispatch] theorem stepAdvPush (n : Nat) (mem : Nat → Felt)
    (frames : List LocalFrame) (adv : List Felt) (stk : List Felt)
    (hlen : adv.length ≥ n) :
    execInstruction ⟨stk, mem, frames, adv⟩ (.advPush n) =
    some ⟨(adv.take n).reverse ++ stk, mem, frames, adv.drop n⟩ := by
  unfold execInstruction execAdvPush
  simp only [MidenState.withStack, MidenState.withAdvice]
  split
  · omega
  · rfl

set_option maxHeartbeats 800000 in
@[miden_dispatch] theorem stepAdvPush1 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (v : Felt) (stk : List Felt) (adv' : List Felt)
    (hadv : adv = v :: adv') :
    execInstruction ⟨stk, mem, frames, adv⟩ (.advPush 1) =
    some ⟨v :: stk, mem, frames, adv'⟩ := by
  unfold execInstruction execAdvPush
  subst hadv
  simp [MidenState.withStack, MidenState.withAdvice]

set_option maxHeartbeats 800000 in
@[miden_dispatch] theorem stepAdvPush2 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (v1 v2 : Felt) (stk : List Felt) (adv' : List Felt)
    (hadv : adv = v1 :: v2 :: adv') :
    execInstruction ⟨stk, mem, frames, adv⟩ (.advPush 2) =
    some ⟨v2 :: v1 :: stk, mem, frames, adv'⟩ := by
  unfold execInstruction execAdvPush
  subst hadv
  simp [MidenState.withStack, MidenState.withAdvice]

-- ============================================================================
-- Local memory (frame-aware)
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- locLoad: push the value of local slot `idx` onto the stack. -/
@[miden_dispatch] theorem stepLocLoad (idx : Nat) (frame : LocalFrame) (frames_rest : List LocalFrame)
    (mem : Nat → Felt) (adv : List Felt)
    (stk : List Felt) (hidx : idx < frame.numLocals) :
    execInstruction ⟨stk, mem, frame :: frames_rest, adv⟩ (.locLoad idx) =
    some ⟨mem (frame.localAddr idx) :: stk, mem, frame :: frames_rest, adv⟩ := by
  unfold execInstruction execLocLoad
  simp [MidenState.readLocal?, MidenState.localAddr?, hidx, MidenState.withStack]

set_option maxHeartbeats 800000 in
/-- locStore: pop the top of the stack and write it to local slot `idx`. -/
@[miden_dispatch] theorem stepLocStore (idx : Nat) (frame : LocalFrame) (frames_rest : List LocalFrame)
    (mem : Nat → Felt) (adv : List Felt)
    (v : Felt) (rest : List Felt) (hidx : idx < frame.numLocals) :
    execInstruction ⟨v :: rest, mem, frame :: frames_rest, adv⟩ (.locStore idx) =
    some ⟨rest, fun i => if i = frame.localAddr idx then v else mem i, frame :: frames_rest, adv⟩ := by
  unfold execInstruction execLocStore
  simp [MidenState.writeLocal?, MidenState.localAddr?, hidx, MidenState.writeMemory, MidenState.withStack]

set_option maxHeartbeats 1600000 in
/-- locStorewBe: store the top word to local memory at `idx` in big-endian order.
    The word remains on the stack. The resulting memory function is a nested
    if-then-else chain reflecting the four writes. -/
@[miden_dispatch] theorem stepLocStorewBe (idx : Nat) (frame : LocalFrame) (frames_rest : List LocalFrame)
    (mem : Nat → Felt) (adv : List Felt)
    (e0 e1 e2 e3 : Felt) (rest : List Felt)
    (halign : idx % 4 = 0) (hbound : idx + 4 ≤ frame.numLocals) :
    let baseAddr := frame.localAddr idx
    execInstruction ⟨e0 :: e1 :: e2 :: e3 :: rest, mem, frame :: frames_rest, adv⟩ (.locStorewBe idx) =
    some ⟨e0 :: e1 :: e2 :: e3 :: rest,
      fun i => if i = baseAddr + 3 then e0
               else if i = baseAddr + 2 then e1
               else if i = baseAddr + 1 then e2
               else if i = baseAddr then e3
               else mem i,
      frame :: frames_rest, adv⟩ := by
  unfold execInstruction execLocStorewBe currentFrame
  simp [halign, Nat.not_lt_of_le hbound, MidenState.writeMemory, MidenState.withStack]

set_option maxHeartbeats 1600000 in
/-- locStorewLe: store the top word to local memory at `idx` in little-endian order.
    The word remains on the stack. The resulting memory function is a nested
    if-then-else chain reflecting the four writes. -/
@[miden_dispatch] theorem stepLocStorewLe (idx : Nat) (frame : LocalFrame) (frames_rest : List LocalFrame)
    (mem : Nat → Felt) (adv : List Felt)
    (e0 e1 e2 e3 : Felt) (rest : List Felt)
    (halign : idx % 4 = 0) (hbound : idx + 4 ≤ frame.numLocals) :
    let baseAddr := frame.localAddr idx
    execInstruction ⟨e0 :: e1 :: e2 :: e3 :: rest, mem, frame :: frames_rest, adv⟩ (.locStorewLe idx) =
    some ⟨e0 :: e1 :: e2 :: e3 :: rest,
      fun i => if i = baseAddr + 3 then e3
               else if i = baseAddr + 2 then e2
               else if i = baseAddr + 1 then e1
               else if i = baseAddr then e0
               else mem i,
      frame :: frames_rest, adv⟩ := by
  unfold execInstruction execLocStorewLe currentFrame
  simp [halign, Nat.not_lt_of_le hbound, MidenState.writeMemory, MidenState.withStack]

set_option maxHeartbeats 800000 in
/-- locLoadwBe: load a word from local memory at `idx` in big-endian order,
    replacing the top four stack elements. -/
@[miden_dispatch] theorem stepLocLoadwBe (idx : Nat) (frame : LocalFrame) (frames_rest : List LocalFrame)
    (mem : Nat → Felt) (adv : List Felt)
    (s0 s1 s2 s3 : Felt) (rest : List Felt)
    (halign : idx % 4 = 0) (hbound : idx + 4 ≤ frame.numLocals) :
    let baseAddr := frame.localAddr idx
    execInstruction ⟨s0 :: s1 :: s2 :: s3 :: rest, mem, frame :: frames_rest, adv⟩ (.locLoadwBe idx) =
    some ⟨mem (baseAddr + 3) :: mem (baseAddr + 2) :: mem (baseAddr + 1) :: mem baseAddr :: rest,
      mem, frame :: frames_rest, adv⟩ := by
  unfold execInstruction execLocLoadwBe currentFrame
  simp [halign, Nat.not_lt_of_le hbound, MidenState.withStack]

set_option maxHeartbeats 800000 in
/-- locLoadwLe: load a word from local memory at `idx` in little-endian order,
    replacing the top four stack elements. -/
@[miden_dispatch] theorem stepLocLoadwLe (idx : Nat) (frame : LocalFrame) (frames_rest : List LocalFrame)
    (mem : Nat → Felt) (adv : List Felt)
    (s0 s1 s2 s3 : Felt) (rest : List Felt)
    (halign : idx % 4 = 0) (hbound : idx + 4 ≤ frame.numLocals) :
    let baseAddr := frame.localAddr idx
    execInstruction ⟨s0 :: s1 :: s2 :: s3 :: rest, mem, frame :: frames_rest, adv⟩ (.locLoadwLe idx) =
    some ⟨mem baseAddr :: mem (baseAddr + 1) :: mem (baseAddr + 2) :: mem (baseAddr + 3) :: rest,
      mem, frame :: frames_rest, adv⟩ := by
  unfold execInstruction execLocLoadwLe currentFrame
  simp [halign, Nat.not_lt_of_le hbound, MidenState.withStack]

set_option maxHeartbeats 800000 in
/-- locaddr: push the absolute address of local slot `idx` onto the stack. -/
@[miden_dispatch] theorem stepLocAddr (idx : Nat) (frame : LocalFrame) (frames_rest : List LocalFrame)
    (mem : Nat → Felt) (adv : List Felt)
    (stk : List Felt) (hidx : idx < frame.numLocals) :
    execInstruction ⟨stk, mem, frame :: frames_rest, adv⟩ (.locaddr idx) =
    some ⟨Felt.ofNat (frame.localAddr idx) :: stk, mem, frame :: frames_rest, adv⟩ := by
  unfold execInstruction execLocAddr
  simp [MidenState.localAddr?, hidx, MidenState.withStack]

end MidenLean.StepLemmas
