import MidenLean.Proofs.Helpers

namespace MidenLean.StepLemmas

open MidenLean

-- ============================================================================
-- Stack manipulation
-- ============================================================================

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepDrop (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .drop =
    some ⟨rest, mem, locs, adv⟩ := by
  unfold execInstruction execDrop; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepDropw (mem locs : Nat → Felt) (adv : List Felt)
    (a b c d : Felt) (rest : List Felt) :
    execInstruction ⟨a :: b :: c :: d :: rest, mem, locs, adv⟩ .dropw =
    some ⟨rest, mem, locs, adv⟩ := by
  unfold execInstruction execDropw; rfl

set_option maxHeartbeats 800000 in
/-- Parametric dup: copies the element at index `n` to the top of the stack. -/
@[miden_dispatch] theorem stepDup (n : Fin 16) (stk : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (v : Felt) (h : stk[n.val]? = some v) :
    execInstruction ⟨stk, mem, locs, adv⟩ (.dup n) =
    some ⟨v :: stk, mem, locs, adv⟩ := by
  unfold execInstruction execDup
  simp [h, MidenState.withStack]

set_option maxHeartbeats 4000000 in
/-- Parametric swap: swaps the top element with the element at index `n`.
    After the rewrite, the result stack contains `List.set` operations;
    use `dsimp only [List.set]` to normalize on concrete lists. -/
@[miden_dispatch] theorem stepSwap (n : Fin 16) (stk : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (hn : (n.val == 0) = false)
    (top nth : Felt) (htop : stk[0]? = some top) (hnth : stk[n.val]? = some nth) :
    execInstruction ⟨stk, mem, locs, adv⟩ (.swap n) =
    some ⟨(stk.set 0 nth).set n.val top, mem, locs, adv⟩ := by
  unfold execInstruction execSwap
  simp [hn, htop, hnth, MidenState.withStack]

-- movup and movdn: parametric forms

set_option maxHeartbeats 4000000 in
/-- Parametric movup: removes element at index `n` and places it on top.
    After the rewrite, the result stack contains `List.eraseIdx`;
    use `dsimp only [List.eraseIdx]` to normalize on concrete lists. -/
@[miden_dispatch] theorem stepMovup (n : Nat) (stk : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (v : Felt) (hn : (n < 2 || n > 15) = false) (hv : stk[n]? = some v) :
    execInstruction ⟨stk, mem, locs, adv⟩ (.movup n) =
    some ⟨v :: stk.eraseIdx n, mem, locs, adv⟩ := by
  unfold execInstruction execMovup removeNth
  simp [hn, hv, MidenState.withStack]

set_option maxHeartbeats 4000000 in
/-- Parametric movdn: pops the top element and inserts it at position `n`.
    After the rewrite, the result stack contains `insertAt`;
    use `dsimp only [insertAt, List.take, List.drop, List.append]` to normalize. -/
@[miden_dispatch] theorem stepMovdn (n : Nat) (mem locs : Nat → Felt) (adv : List Felt)
    (top : Felt) (rest : List Felt) (hn : (n < 2 || n > 15) = false) :
    execInstruction ⟨top :: rest, mem, locs, adv⟩ (.movdn n) =
    some ⟨insertAt rest n top, mem, locs, adv⟩ := by
  unfold execInstruction execMovdn
  simp [hn, MidenState.withStack]

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepReversew (mem locs : Nat → Felt) (adv : List Felt)
    (a b c d : Felt) (rest : List Felt) :
    execInstruction ⟨a :: b :: c :: d :: rest, mem, locs, adv⟩ .reversew =
    some ⟨d :: c :: b :: a :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execReversew; rfl

set_option maxHeartbeats 800000 in
@[miden_dispatch] theorem stepDupw0 (mem locs : Nat → Felt) (adv : List Felt)
    (a b c d : Felt) (rest : List Felt) :
    execInstruction ⟨a :: b :: c :: d :: rest, mem, locs, adv⟩ (.dupw 0) =
    some ⟨a :: b :: c :: d :: a :: b :: c :: d :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execDupw
  simp [MidenState.withStack]

-- ============================================================================
-- Assertions
-- ============================================================================

set_option maxHeartbeats 400000 in
/-- assert succeeds when top of stack is 1, pops it. -/
@[miden_dispatch] theorem stepAssert (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt) (h : a.val = 1) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .assert =
    some ⟨rest, mem, locs, adv⟩ := by
  unfold execInstruction execAssert
  simp [h, MidenState.withStack]

set_option maxHeartbeats 400000 in
/-- assertWithError behaves identically to assert (error string is for debugging). -/
@[miden_dispatch] theorem stepAssertWithError (msg : String) (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt) (h : a.val = 1) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ (.assertWithError msg) =
    some ⟨rest, mem, locs, adv⟩ := by
  unfold execInstruction execAssert
  simp [h, MidenState.withStack]

set_option maxHeartbeats 400000 in
/-- assertz succeeds when top of stack is 0, pops it. -/
@[miden_dispatch] theorem stepAssertz (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.val = 0) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .assertz =
    some ⟨rest, mem, locs, adv⟩ := by
  unfold execInstruction execAssertz
  simp [ha, MidenState.withStack]

set_option maxHeartbeats 400000 in
/-- assertEq succeeds when top two elements are equal, pops both. -/
@[miden_dispatch] theorem stepAssertEq (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: a :: rest, mem, locs, adv⟩ .assertEq =
    some ⟨rest, mem, locs, adv⟩ := by
  unfold execInstruction execAssertEq
  simp [MidenState.withStack]

set_option maxHeartbeats 400000 in
/-- assertEqWithError behaves identically to assertEq. -/
@[miden_dispatch] theorem stepAssertEqWithError (msg : String) (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: a :: rest, mem, locs, adv⟩ (.assertEqWithError msg) =
    some ⟨rest, mem, locs, adv⟩ := by
  unfold execInstruction execAssertEq
  simp [MidenState.withStack]

-- ============================================================================
-- U32 assertions
-- ============================================================================

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32Assert2 (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨a :: b :: rest, mem, locs, adv⟩ .u32Assert2 =
    some ⟨a :: b :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32Assert2
  simp [ha, hb]

-- ============================================================================
-- Field comparison
-- ============================================================================

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepEqImm (mem locs : Nat → Felt) (adv : List Felt)
    (v a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ (.eqImm v) =
    some ⟨(if a == v then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execEqImm; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepEq (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .eq =
    some ⟨(if a == b then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execEq; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepNeq (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .neq =
    some ⟨(if a != b then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execNeq; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepLt (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .lt =
    some ⟨(if a.val < b.val then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execLt; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepGt (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .gt =
    some ⟨(if a.val > b.val then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execGt; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepLte (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .lte =
    some ⟨(if a.val ≤ b.val then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execLte; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepGte (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .gte =
    some ⟨(if a.val ≥ b.val then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execGte; rfl

-- ============================================================================
-- Field boolean
-- ============================================================================

set_option maxHeartbeats 800000 in
@[miden_dispatch] theorem stepAndIte (mem locs : Nat → Felt) (adv : List Felt)
    (rest : List Felt) (p q : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) :: (if q then (1 : Felt) else 0) :: rest, mem, locs, adv⟩
      Instruction.and =
    some ⟨(if q && p then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execAnd
  simp only [Felt.isBool_ite_bool, MidenState.withStack]
  cases p <;> cases q <;> simp

set_option maxHeartbeats 800000 in
@[miden_dispatch] theorem stepOrIte (mem locs : Nat → Felt) (adv : List Felt)
    (rest : List Felt) (p q : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) :: (if q then (1 : Felt) else 0) :: rest, mem, locs, adv⟩
      Instruction.or =
    some ⟨(if q || p then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execOr
  simp only [Felt.isBool_ite_bool, MidenState.withStack]
  cases p <;> cases q <;> simp

set_option maxHeartbeats 800000 in
@[miden_dispatch] theorem stepNotIte (mem locs : Nat → Felt) (adv : List Felt)
    (rest : List Felt) (p : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) :: rest, mem, locs, adv⟩
      Instruction.not =
    some ⟨(if !p then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execNot
  simp only [Felt.isBool_ite_bool, MidenState.withStack]
  cases p <;> simp

-- ============================================================================
-- Conditional stack manipulation
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- cswap on a boolean condition (as ite): if true, swap the two elements below. -/
@[miden_dispatch] theorem stepCswapIte (mem locs : Nat → Felt) (adv : List Felt)
    (rest : List Felt) (a b : Felt) (p : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) :: b :: a :: rest, mem, locs, adv⟩
      .cswap =
    some ⟨(if p then a else b) :: (if p then b else a) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execCswap
  simp only [MidenState.withStack]
  cases p <;> simp

set_option maxHeartbeats 800000 in
/-- cdrop on a boolean condition (as ite): if true, keep b; if false, keep a. -/
@[miden_dispatch] theorem stepCdropIte (mem locs : Nat → Felt) (adv : List Felt)
    (rest : List Felt) (a b : Felt) (p : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) :: b :: a :: rest, mem, locs, adv⟩
      .cdrop =
    some ⟨(if p then b else a) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execCdrop
  simp only [MidenState.withStack]
  cases p <;> simp

-- ============================================================================
-- Field arithmetic
-- ============================================================================

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepAdd (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .add =
    some ⟨(a + b) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execAdd; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepAddImm (mem locs : Nat → Felt) (adv : List Felt)
    (v a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ (.addImm v) =
    some ⟨(a + v) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execAddImm; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepSub (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .sub =
    some ⟨(a - b) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execSub; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepMul (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .mul =
    some ⟨(a * b) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execMul; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepNeg (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .neg =
    some ⟨(-a) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execNeg; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepIncr (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .incr =
    some ⟨(a + 1) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execIncr; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepPush (mem locs : Nat → Felt) (adv : List Felt)
    (v : Felt) (stk : List Felt) :
    execInstruction ⟨stk, mem, locs, adv⟩ (.push v) =
    some ⟨v :: stk, mem, locs, adv⟩ := by
  unfold execInstruction execPush; rfl

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepPadw (mem locs : Nat → Felt) (adv : List Felt)
    (stk : List Felt) :
    execInstruction ⟨stk, mem, locs, adv⟩ .padw =
    some ⟨(0 : Felt) :: 0 :: 0 :: 0 :: stk, mem, locs, adv⟩ := by
  unfold execInstruction execPadw; rfl

-- ============================================================================
-- Pow2
-- ============================================================================

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepPow2 (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.val ≤ 63) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .pow2 =
    some ⟨Felt.ofNat (2^a.val) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execPow2
  simp [show ¬(a.val > 63) from by omega, MidenState.withStack]

-- ============================================================================
-- U32 arithmetic
-- ============================================================================

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32WidenAdd (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32WidenAdd =
    some ⟨Felt.ofNat ((a.val + b.val) % 2^32) ::
          Felt.ofNat ((a.val + b.val) / 2^32) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32WidenAdd u32WideAdd u32Max
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32WidenAdd3 (mem locs : Nat → Felt) (adv : List Felt)
    (a b c : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    execInstruction ⟨c :: b :: a :: rest, mem, locs, adv⟩ .u32WidenAdd3 =
    some ⟨Felt.ofNat ((a.val + b.val + c.val) % 2^32) ::
          Felt.ofNat ((a.val + b.val + c.val) / 2^32) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32WidenAdd3 u32WideAdd3 u32Max
  simp [ha, hb, hc, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32OverflowSub (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32OverflowSub =
    some ⟨Felt.ofNat (u32OverflowingSub a.val b.val).1 ::
          Felt.ofNat (u32OverflowingSub a.val b.val).2 ::
          rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32OverflowSub
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32WidenMul (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32WidenMul =
    some ⟨Felt.ofNat ((a.val * b.val) % 2^32) ::
          Felt.ofNat ((a.val * b.val) / 2^32) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32WidenMul u32WideMul u32Max
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32WidenMadd (mem locs : Nat → Felt) (adv : List Felt)
    (a b c : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    execInstruction ⟨b :: a :: c :: rest, mem, locs, adv⟩ .u32WidenMadd =
    some ⟨Felt.ofNat ((a.val * b.val + c.val) % 2^32) ::
          Felt.ofNat ((a.val * b.val + c.val) / 2^32) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32WidenMadd u32WideMadd u32Max
  simp [ha, hb, hc, MidenState.withStack]

-- ============================================================================
-- U32 bitwise (require isU32 preconditions)
-- ============================================================================

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32And (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32And =
    some ⟨Felt.ofNat (a.val &&& b.val) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32And
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32Or (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32Or =
    some ⟨Felt.ofNat (a.val ||| b.val) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32Or
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32Xor (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32Xor =
    some ⟨Felt.ofNat (a.val ^^^ b.val) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32Xor
  simp [ha, hb, MidenState.withStack]

-- ============================================================================
-- U32 comparison (require isU32 preconditions)
-- ============================================================================

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32Lt (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32Lt =
    some ⟨(if a.val < b.val then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32Lt
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32Gt (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32Gt =
    some ⟨(if a.val > b.val then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32Gt
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32Lte (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32Lte =
    some ⟨(if a.val ≤ b.val then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32Lte
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32Gte (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32Gte =
    some ⟨(if a.val ≥ b.val then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32Gte
  simp [ha, hb, MidenState.withStack]

-- ============================================================================
-- U32 bit counting
-- ============================================================================

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32Clz (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .u32Clz =
    some ⟨Felt.ofNat (u32CountLeadingZeros a.val) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32Clz
  simp [ha, MidenState.withStack]

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32Ctz (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .u32Ctz =
    some ⟨Felt.ofNat (u32CountTrailingZeros a.val) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32Ctz
  simp [ha, MidenState.withStack]

set_option maxHeartbeats 4000000 in
/-- u32Clo: count leading ones, expressed via u32CountLeadingZeros on the bitwise complement.
    (u32CountLeadingOnes is private in Semantics.) -/
@[miden_dispatch] theorem stepU32Clo (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .u32Clo =
    some ⟨Felt.ofNat (u32CountLeadingZeros (u32Max - 1 - a.val)) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32Clo u32CountLeadingOnes
  simp [ha, MidenState.withStack]

set_option maxHeartbeats 4000000 in
/-- u32Cto: count trailing ones, expressed via u32CountTrailingZeros on the XOR complement.
    (u32CountTrailingOnes is private in Semantics.) -/
@[miden_dispatch] theorem stepU32Cto (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .u32Cto =
    some ⟨Felt.ofNat (u32CountTrailingZeros (a.val ^^^ (u32Max - 1))) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32Cto u32CountTrailingOnes
  simp [ha, MidenState.withStack]

-- ============================================================================
-- U32 split
-- ============================================================================

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepU32Split (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .u32Split =
    some ⟨a.lo32 :: a.hi32 :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32Split; rfl

-- ============================================================================
-- Field div (requires nonzero divisor)
-- ============================================================================

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepDiv (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (hb : (b == (0 : Felt)) = false) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .div =
    some ⟨(a * b⁻¹) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execDiv
  simp [hb, MidenState.withStack]

-- ============================================================================
-- U32 divmod (requires isU32 and nonzero divisor)
-- ============================================================================

set_option maxHeartbeats 4000000 in
@[miden_dispatch] theorem stepU32DivMod (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true)
    (hbnz : (b.val == 0) = false) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32DivMod =
    some ⟨Felt.ofNat (a.val % b.val) :: Felt.ofNat (a.val / b.val) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32DivMod
  simp [ha, hb, hbnz, MidenState.withStack]

-- ============================================================================
-- Emit (no-op)
-- ============================================================================

set_option maxHeartbeats 400000 in
@[miden_dispatch] theorem stepEmitImm (n : Nat) (mem locs : Nat → Felt) (adv : List Felt)
    (stk : List Felt) :
    execInstruction ⟨stk, mem, locs, adv⟩ (.emitImm n) =
    some ⟨stk, mem, locs, adv⟩ := by
  unfold execInstruction; rfl

-- ============================================================================
-- Advice stack
-- ============================================================================

set_option maxHeartbeats 800000 in
@[miden_dispatch] theorem stepAdvPush (n : Nat) (mem locs : Nat → Felt)
    (adv : List Felt) (stk : List Felt)
    (hlen : adv.length ≥ n) :
    execInstruction ⟨stk, mem, locs, adv⟩ (.advPush n) =
    some ⟨(adv.take n).reverse ++ stk, mem, locs, adv.drop n⟩ := by
  unfold execInstruction execAdvPush
  simp only [MidenState.withStack, MidenState.withAdvice]
  split
  · omega
  · rfl

set_option maxHeartbeats 800000 in
@[miden_dispatch] theorem stepAdvPush1 (mem locs : Nat → Felt) (adv : List Felt)
    (v : Felt) (stk : List Felt) (adv' : List Felt)
    (hadv : adv = v :: adv') :
    execInstruction ⟨stk, mem, locs, adv⟩ (.advPush 1) =
    some ⟨v :: stk, mem, locs, adv'⟩ := by
  unfold execInstruction execAdvPush
  subst hadv
  simp [MidenState.withStack, MidenState.withAdvice]

set_option maxHeartbeats 800000 in
@[miden_dispatch] theorem stepAdvPush2 (mem locs : Nat → Felt) (adv : List Felt)
    (v1 v2 : Felt) (stk : List Felt) (adv' : List Felt)
    (hadv : adv = v1 :: v2 :: adv') :
    execInstruction ⟨stk, mem, locs, adv⟩ (.advPush 2) =
    some ⟨v2 :: v1 :: stk, mem, locs, adv'⟩ := by
  unfold execInstruction execAdvPush
  subst hadv
  simp [MidenState.withStack, MidenState.withAdvice]

end MidenLean.StepLemmas
