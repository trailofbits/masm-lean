import MidenLean.Proofs.Helpers
import MidenLean.Proofs.EquationLemmas

namespace MidenLean.StepLemmas

open MidenLean

-- ============================================================================
-- Stack manipulation
-- ============================================================================

theorem stepDrop (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .drop =
    some ⟨rest, mem, locs, adv⟩ := by
  simp only [execInstruction_drop, execDrop,
    MidenState.withStack]

/-- Parametric dup: copies the element at index `n` to the top of the stack. -/
theorem stepDup (n : Fin 16) (stk : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (v : Felt) (h : stk[n.val]? = some v) :
    execInstruction ⟨stk, mem, locs, adv⟩ (.dup n) =
    some ⟨v :: stk, mem, locs, adv⟩ := by
  simp only [execInstruction_dup]
  unfold execDup
  simp [h, MidenState.withStack]

/-- Parametric swap: swaps the top element with the element at index `n`.
    After the rewrite, the result stack contains `List.set` operations;
    use `dsimp only [List.set]` to normalize on concrete lists. -/
theorem stepSwap (n : Fin 16) (stk : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (hn : (n.val == 0) = false)
    (top nth : Felt) (htop : stk[0]? = some top) (hnth : stk[n.val]? = some nth) :
    execInstruction ⟨stk, mem, locs, adv⟩ (.swap n) =
    some ⟨(stk.set 0 nth).set n.val top, mem, locs, adv⟩ := by
  simp only [execInstruction_swap]
  unfold execSwap
  simp [hn, htop, hnth, MidenState.withStack]

-- movup and movdn: parametric forms

/-- Parametric movup: removes element at index `n` and places it on top.
    After the rewrite, the result stack contains `List.eraseIdx`;
    use `dsimp only [List.eraseIdx]` to normalize on concrete lists. -/
theorem stepMovup (n : Nat) (stk : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (v : Felt) (hn : (n < 2 || n > 15) = false) (hv : stk[n]? = some v) :
    execInstruction ⟨stk, mem, locs, adv⟩ (.movup n) =
    some ⟨v :: stk.eraseIdx n, mem, locs, adv⟩ := by
  simp only [execInstruction_movup]
  unfold execMovup removeNth
  simp [hn, hv, MidenState.withStack]

/-- Parametric movdn: pops the top element and inserts it at position `n`.
    After the rewrite, the result stack contains `insertAt`;
    use `dsimp only [insertAt, List.take, List.drop, List.append]` to normalize. -/
theorem stepMovdn (n : Nat) (mem locs : Nat → Felt) (adv : List Felt)
    (top : Felt) (rest : List Felt) (hn : (n < 2 || n > 15) = false) :
    execInstruction ⟨top :: rest, mem, locs, adv⟩ (.movdn n) =
    some ⟨insertAt rest n top, mem, locs, adv⟩ := by
  simp only [execInstruction_movdn]
  unfold execMovdn
  simp [hn, MidenState.withStack]

-- ============================================================================
-- U32 assertions
-- ============================================================================

theorem stepU32Assert2 (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨a :: b :: rest, mem, locs, adv⟩ .u32Assert2 =
    some ⟨a :: b :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_u32Assert2]
  unfold execU32Assert2
  simp [ha, hb]

-- ============================================================================
-- Field comparison
-- ============================================================================

theorem stepEqImm (mem locs : Nat → Felt) (adv : List Felt)
    (v a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ (.eqImm v) =
    some ⟨(if a == v then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_eqImm, execEqImm, MidenState.withStack]

theorem stepEq (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .eq =
    some ⟨(if a == b then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_eq', execEq, MidenState.withStack]

theorem stepNeq (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .neq =
    some ⟨(if a != b then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_neq, execNeq, MidenState.withStack]

-- ============================================================================
-- Field boolean
-- ============================================================================

theorem stepAndIte (mem locs : Nat → Felt) (adv : List Felt)
    (rest : List Felt) (p q : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) :: (if q then (1 : Felt) else 0) :: rest, mem, locs, adv⟩
      Instruction.and =
    some ⟨(if q && p then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_and]
  unfold execAnd
  simp only [Felt.isBool_ite_bool, MidenState.withStack]
  cases p <;> cases q <;> simp

theorem stepOrIte (mem locs : Nat → Felt) (adv : List Felt)
    (rest : List Felt) (p q : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) :: (if q then (1 : Felt) else 0) :: rest, mem, locs, adv⟩
      Instruction.or =
    some ⟨(if q || p then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_or]
  unfold execOr
  simp only [Felt.isBool_ite_bool, MidenState.withStack]
  cases p <;> cases q <;> simp

theorem stepNotIte (mem locs : Nat → Felt) (adv : List Felt)
    (rest : List Felt) (p : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) :: rest, mem, locs, adv⟩
      Instruction.not =
    some ⟨(if !p then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_not]
  unfold execNot
  simp only [Felt.isBool_ite_bool, MidenState.withStack]
  cases p <;> simp

-- ============================================================================
-- Field arithmetic
-- ============================================================================

theorem stepAddImm (mem locs : Nat → Felt) (adv : List Felt)
    (v a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ (.addImm v) =
    some ⟨(a + v) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_addImm, execAddImm, MidenState.withStack]

-- ============================================================================
-- U32 arithmetic
-- ============================================================================

theorem stepU32WidenAdd (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32WidenAdd =
    some ⟨Felt.ofNat ((a.val + b.val) % 2^32) ::
          Felt.ofNat ((a.val + b.val) / 2^32) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_u32WidenAdd]
  unfold execU32WidenAdd u32WideAdd u32Max
  simp [ha, hb, MidenState.withStack]

theorem stepU32WidenAdd3 (mem locs : Nat → Felt) (adv : List Felt)
    (a b c : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    execInstruction ⟨c :: b :: a :: rest, mem, locs, adv⟩ .u32WidenAdd3 =
    some ⟨Felt.ofNat ((a.val + b.val + c.val) % 2^32) ::
          Felt.ofNat ((a.val + b.val + c.val) / 2^32) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_u32WidenAdd3]
  unfold execU32WidenAdd3 u32WideAdd3 u32Max
  simp [ha, hb, hc, MidenState.withStack]

theorem stepU32OverflowSub (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32OverflowSub =
    some ⟨Felt.ofNat (u32OverflowingSub a.val b.val).1 ::
          Felt.ofNat (u32OverflowingSub a.val b.val).2 ::
          rest, mem, locs, adv⟩ := by
  simp only [execInstruction_u32OverflowSub]
  unfold execU32OverflowSub
  simp [ha, hb, MidenState.withStack]

theorem stepU32WidenMul (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32WidenMul =
    some ⟨Felt.ofNat ((a.val * b.val) % 2^32) ::
          Felt.ofNat ((a.val * b.val) / 2^32) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_u32WidenMul]
  unfold execU32WidenMul u32WideMul u32Max
  simp [ha, hb, MidenState.withStack]

theorem stepU32WidenMadd (mem locs : Nat → Felt) (adv : List Felt)
    (a b c : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    execInstruction ⟨b :: a :: c :: rest, mem, locs, adv⟩ .u32WidenMadd =
    some ⟨Felt.ofNat ((a.val * b.val + c.val) % 2^32) ::
          Felt.ofNat ((a.val * b.val + c.val) / 2^32) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_u32WidenMadd]
  unfold execU32WidenMadd u32WideMadd u32Max
  simp [ha, hb, hc, MidenState.withStack]

-- U32 bitwise (require isU32 preconditions)

theorem stepU32And (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32And =
    some ⟨Felt.ofNat (a.val &&& b.val) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_u32And]
  unfold execU32And
  simp [ha, hb, MidenState.withStack]

theorem stepU32Or (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32Or =
    some ⟨Felt.ofNat (a.val ||| b.val) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_u32Or]
  unfold execU32Or
  simp [ha, hb, MidenState.withStack]

theorem stepU32Xor (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32Xor =
    some ⟨Felt.ofNat (a.val ^^^ b.val) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_u32Xor]
  unfold execU32Xor
  simp [ha, hb, MidenState.withStack]

-- U32 bit counting

theorem stepU32Clz (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .u32Clz =
    some ⟨Felt.ofNat (u32CountLeadingZeros a.val) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_u32Clz]
  unfold execU32Clz
  simp [ha, MidenState.withStack]

theorem stepU32Ctz (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .u32Ctz =
    some ⟨Felt.ofNat (u32CountTrailingZeros a.val) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_u32Ctz]
  unfold execU32Ctz
  simp [ha, MidenState.withStack]

/-- u32Clo: count leading ones, expressed via u32CountLeadingZeros on the bitwise complement.
    (u32CountLeadingOnes is private in Semantics.) -/
theorem stepU32Clo (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .u32Clo =
    some ⟨Felt.ofNat (u32CountLeadingZeros (a.val ^^^ (u32Max - 1))) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_u32Clo]
  unfold execU32Clo u32CountLeadingOnes
  simp [ha, MidenState.withStack]

/-- u32Cto: count trailing ones, expressed via u32CountTrailingZeros on the XOR complement.
    (u32CountTrailingOnes is private in Semantics.) -/
theorem stepU32Cto (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .u32Cto =
    some ⟨Felt.ofNat (u32CountTrailingZeros (a.val ^^^ (u32Max - 1))) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_u32Cto]
  unfold execU32Cto u32CountTrailingOnes
  simp [ha, MidenState.withStack]

-- ============================================================================
-- Additional stack and arithmetic operations
-- ============================================================================

theorem stepReversew (mem locs : Nat → Felt) (adv : List Felt)
    (a b c d : Felt) (rest : List Felt) :
    execInstruction ⟨a :: b :: c :: d :: rest, mem, locs, adv⟩ .reversew =
    some ⟨d :: c :: b :: a :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_reversew, execReversew, MidenState.withStack]

theorem stepDropw (mem locs : Nat → Felt) (adv : List Felt)
    (a b c d : Felt) (rest : List Felt) :
    execInstruction ⟨a :: b :: c :: d :: rest, mem, locs, adv⟩ .dropw =
    some ⟨rest, mem, locs, adv⟩ := by
  simp only [execInstruction_dropw, execDropw, MidenState.withStack]

theorem stepPush (v : Felt) (mem locs : Nat → Felt) (adv : List Felt) (stk : List Felt) :
    execInstruction ⟨stk, mem, locs, adv⟩ (.push v) =
    some ⟨v :: stk, mem, locs, adv⟩ := by
  simp only [execInstruction_push, execPush, MidenState.withStack]

theorem stepAdd (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .add =
    some ⟨(a + b) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_add, execAdd, MidenState.withStack]

theorem stepMul (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .mul =
    some ⟨(a * b) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_mul, execMul, MidenState.withStack]

theorem stepCdropIte (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) (p : Bool) :
    execInstruction ⟨(if p then (1:Felt) else 0) :: a :: b :: rest, mem, locs, adv⟩ .cdrop =
    some ⟨(if p then a else b) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_cdrop]
  unfold execCdrop
  cases p <;> simp [MidenState.withStack]

theorem stepCswapIte (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) (p : Bool) :
    execInstruction ⟨(if p then (1:Felt) else 0) :: b :: a :: rest, mem, locs, adv⟩ .cswap =
    some ⟨(if p then a else b) :: (if p then b else a) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_cswap]
  unfold execCswap
  cases p <;> simp [MidenState.withStack]

theorem stepPow2 (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt) (ha : a.val ≤ 63) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .pow2 =
    some ⟨Felt.ofNat (2^a.val) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_pow2]
  unfold execPow2
  simp [ha, MidenState.withStack]

theorem stepU32Split (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .u32Split =
    some ⟨a.lo32 :: a.hi32 :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_u32Split, execU32Split, MidenState.withStack]

theorem stepU32WrappingSub (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32WrappingSub =
    some ⟨Felt.ofNat (u32OverflowingSub a.val b.val).2 :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_u32WrappingSub]
  unfold execU32WrappingSub
  simp [ha, hb, MidenState.withStack]

theorem stepU32Lt (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32Lt =
    some ⟨(if a.val < b.val then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_u32Lt]
  unfold execU32Lt
  simp [ha, hb, MidenState.withStack]

theorem stepU32DivMod (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hbz : b.val ≠ 0) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32DivMod =
    some ⟨Felt.ofNat (a.val % b.val) :: Felt.ofNat (a.val / b.val) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_u32DivMod]
  unfold execU32DivMod
  simp [ha, hb, hbz, MidenState.withStack]

theorem stepLt (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .lt =
    some ⟨(if a.val < b.val then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_lt, execLt, MidenState.withStack]

theorem stepGt (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .gt =
    some ⟨(if a.val > b.val then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_gt, execGt, MidenState.withStack]

/-- Parametric dupw: duplicates a word (4 elements) from position `n` to the top.
    For n=0, duplicates the top word. -/
theorem stepDupw (n : Fin 4) (stk : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (a b c d : Felt)
    (h0 : stk[n.val * 4]? = some a) (h1 : stk[n.val * 4 + 1]? = some b)
    (h2 : stk[n.val * 4 + 2]? = some c) (h3 : stk[n.val * 4 + 3]? = some d) :
    execInstruction ⟨stk, mem, locs, adv⟩ (.dupw n) =
    some ⟨a :: b :: c :: d :: stk, mem, locs, adv⟩ := by
  simp only [execInstruction_dupw]
  unfold execDupw
  simp [h0, h1, h2, h3, MidenState.withStack]

theorem stepDiv (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (hb : (b == (0 : Felt)) = false) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .div =
    some ⟨(a * b⁻¹) :: rest, mem, locs, adv⟩ := by
  simp only [execInstruction_div']
  unfold execDiv
  simp [hb, MidenState.withStack]

-- ============================================================================
-- Assertion, advice, and emit step lemmas
-- ============================================================================

theorem stepEmitImm (v : Felt) (stk : List Felt) (mem locs : Nat → Felt) (adv : List Felt) :
    execInstruction ⟨stk, mem, locs, adv⟩ (.emitImm v) =
    some ⟨stk, mem, locs, adv⟩ := by
  rw [execInstruction_emitImm']

theorem stepAssert (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt) (ha : a.val == 1) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .assert =
    some ⟨rest, mem, locs, adv⟩ := by
  simp only [execInstruction_assert]
  unfold execAssert
  simp [ha, MidenState.withStack]

theorem stepAssertWithError (msg : String) (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt) (ha : a.val == 1) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ (.assertWithError msg) =
    some ⟨rest, mem, locs, adv⟩ := by
  simp only [execInstruction_assertWithError]
  unfold execAssert
  simp [ha, MidenState.withStack]

theorem stepAssertEq (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) (hab : a == b) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .assertEq =
    some ⟨rest, mem, locs, adv⟩ := by
  simp only [execInstruction_assertEq]
  unfold execAssertEq
  simp [hab, MidenState.withStack]

theorem stepAssertEqWithError (msg : String) (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) (hab : a == b) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ (.assertEqWithError msg) =
    some ⟨rest, mem, locs, adv⟩ := by
  simp only [execInstruction_assertEqWithError]
  unfold execAssertEq
  simp [hab, MidenState.withStack]

theorem stepAdvPush2 (stk : List Felt) (mem locs : Nat → Felt)
    (v0 v1 : Felt) (adv_rest : List Felt) :
    execInstruction ⟨stk, mem, locs, v0 :: v1 :: adv_rest⟩ (.advPush 2) =
    some ⟨v1 :: v0 :: stk, mem, locs, adv_rest⟩ := by
  rw [execInstruction_advPush']
  unfold execAdvPush
  dsimp only [MidenState.withStack, MidenState.withAdvice,
    MidenState.advice, MidenState.stack, MidenState.memory,
    MidenState.locals,
    List.take, List.drop, List.reverse, List.length,
    List.reverseAux, List.append]
  rfl

-- ============================================================================
-- Memory
-- ============================================================================

/-- memStorewLe: pops address, stores top 4 elements
    to memory at addr..addr+3 in LE order.
    Requires addr < u32Max and addr % 4 = 0. -/
theorem stepMemStorewLe (locs : Nat → Felt) (adv : List Felt)
    (a e0 e1 e2 e3 : Felt) (rest : List Felt)
    (mem : Nat → Felt)
    (ha_lt : a.val < u32Max)
    (ha_align : a.val % 4 = 0) :
    execInstruction ⟨a :: e0 :: e1 :: e2 :: e3 :: rest,
      mem, locs, adv⟩ .memStorewLe =
    some ⟨e0 :: e1 :: e2 :: e3 :: rest,
      fun addr => if addr = a.val + 3 then e3
        else if addr = a.val + 2 then e2
        else if addr = a.val + 1 then e1
        else if addr = a.val then e0
        else mem addr,
      locs, adv⟩ := by
  rw [execInstruction_memStorewLe']
  unfold execMemStorewLe
  dsimp only [MidenState.stack]
  have h1 : decide (a.val ≥ u32Max) = false := by
    simp only [decide_eq_false_iff_not, not_le]; exact ha_lt
  have h2 : (a.val % 4 != 0) = false := by
    simp only [bne_self_eq_false, ha_align]
  simp only [h1, h2, Bool.false_or, Bool.false_eq_true,
    ite_false, MidenState.withStack, MidenState.writeMemory]

end MidenLean.StepLemmas
