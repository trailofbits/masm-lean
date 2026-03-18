import MidenLean.Proofs.Helpers

namespace MidenLean.StepLemmas

open MidenLean

-- ============================================================================
-- Stack manipulation
-- ============================================================================

set_option maxHeartbeats 400000 in
theorem stepDrop (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .drop =
    some ⟨rest, mem, locs, adv⟩ := by
  unfold execInstruction execDrop; rfl

set_option maxHeartbeats 800000 in
/-- Parametric dup: copies the element at index `n` to the top of the stack. -/
theorem stepDup (n : Fin 16) (stk : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (v : Felt) (h : stk[n.val]? = some v) :
    execInstruction ⟨stk, mem, locs, adv⟩ (.dup n) =
    some ⟨v :: stk, mem, locs, adv⟩ := by
  unfold execInstruction execDup
  simp [h, MidenState.withStack]

set_option maxHeartbeats 4000000 in
/-- Parametric swap: swaps the top element with the element at index `n`.
    After the rewrite, the result stack contains `List.set` operations;
    use `dsimp only [List.set]` to normalize on concrete lists. -/
theorem stepSwap (n : Fin 16) (stk : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
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
theorem stepMovup (n : Nat) (stk : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (v : Felt) (hn : (n < 2 || n > 15) = false) (hv : stk[n]? = some v) :
    execInstruction ⟨stk, mem, locs, adv⟩ (.movup n) =
    some ⟨v :: stk.eraseIdx n, mem, locs, adv⟩ := by
  unfold execInstruction execMovup removeNth
  simp [hn, hv, MidenState.withStack]

set_option maxHeartbeats 4000000 in
/-- Parametric movdn: pops the top element and inserts it at position `n`.
    After the rewrite, the result stack contains `insertAt`;
    use `dsimp only [insertAt, List.take, List.drop, List.append]` to normalize. -/
theorem stepMovdn (n : Nat) (mem locs : Nat → Felt) (adv : List Felt)
    (top : Felt) (rest : List Felt) (hn : (n < 2 || n > 15) = false) :
    execInstruction ⟨top :: rest, mem, locs, adv⟩ (.movdn n) =
    some ⟨insertAt rest n top, mem, locs, adv⟩ := by
  unfold execInstruction execMovdn
  simp [hn, MidenState.withStack]

-- ============================================================================
-- U32 assertions
-- ============================================================================

set_option maxHeartbeats 4000000 in
theorem stepU32Assert2 (mem locs : Nat → Felt) (adv : List Felt)
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
theorem stepEqImm (mem locs : Nat → Felt) (adv : List Felt)
    (v a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ (.eqImm v) =
    some ⟨(if a == v then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execEqImm; rfl

set_option maxHeartbeats 400000 in
theorem stepEq (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .eq =
    some ⟨(if a == b then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execEq; rfl

set_option maxHeartbeats 400000 in
theorem stepNeq (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .neq =
    some ⟨(if a != b then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execNeq; rfl

-- ============================================================================
-- Field boolean
-- ============================================================================

set_option maxHeartbeats 800000 in
theorem stepAndIte (mem locs : Nat → Felt) (adv : List Felt)
    (rest : List Felt) (p q : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) :: (if q then (1 : Felt) else 0) :: rest, mem, locs, adv⟩
      Instruction.and =
    some ⟨(if q && p then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execAnd
  simp only [Felt.isBool_ite_bool, MidenState.withStack]
  cases p <;> cases q <;> simp

set_option maxHeartbeats 800000 in
theorem stepOrIte (mem locs : Nat → Felt) (adv : List Felt)
    (rest : List Felt) (p q : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) :: (if q then (1 : Felt) else 0) :: rest, mem, locs, adv⟩
      Instruction.or =
    some ⟨(if q || p then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execOr
  simp only [Felt.isBool_ite_bool, MidenState.withStack]
  cases p <;> cases q <;> simp

set_option maxHeartbeats 800000 in
theorem stepNotIte (mem locs : Nat → Felt) (adv : List Felt)
    (rest : List Felt) (p : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) :: rest, mem, locs, adv⟩
      Instruction.not =
    some ⟨(if !p then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execNot
  simp only [Felt.isBool_ite_bool, MidenState.withStack]
  cases p <;> simp

-- ============================================================================
-- Field arithmetic
-- ============================================================================

set_option maxHeartbeats 400000 in
theorem stepAddImm (mem locs : Nat → Felt) (adv : List Felt)
    (v a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ (.addImm v) =
    some ⟨(a + v) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execAddImm; rfl

-- ============================================================================
-- U32 arithmetic
-- ============================================================================

set_option maxHeartbeats 4000000 in
theorem stepU32WidenAdd (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32WidenAdd =
    some ⟨Felt.ofNat ((a.val + b.val) % 2^32) ::
          Felt.ofNat ((a.val + b.val) / 2^32) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32WidenAdd u32WideAdd u32Max
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
theorem stepU32WidenAdd3 (mem locs : Nat → Felt) (adv : List Felt)
    (a b c : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    execInstruction ⟨c :: b :: a :: rest, mem, locs, adv⟩ .u32WidenAdd3 =
    some ⟨Felt.ofNat ((a.val + b.val + c.val) % 2^32) ::
          Felt.ofNat ((a.val + b.val + c.val) / 2^32) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32WidenAdd3 u32WideAdd3 u32Max
  simp [ha, hb, hc, MidenState.withStack]

set_option maxHeartbeats 4000000 in
theorem stepU32OverflowSub (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32OverflowSub =
    some ⟨Felt.ofNat (u32OverflowingSub a.val b.val).1 ::
          Felt.ofNat (u32OverflowingSub a.val b.val).2 ::
          rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32OverflowSub
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
theorem stepU32WidenMul (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32WidenMul =
    some ⟨Felt.ofNat ((a.val * b.val) % 2^32) ::
          Felt.ofNat ((a.val * b.val) / 2^32) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32WidenMul u32WideMul u32Max
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
theorem stepU32WidenMadd (mem locs : Nat → Felt) (adv : List Felt)
    (a b c : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    execInstruction ⟨b :: a :: c :: rest, mem, locs, adv⟩ .u32WidenMadd =
    some ⟨Felt.ofNat ((a.val * b.val + c.val) % 2^32) ::
          Felt.ofNat ((a.val * b.val + c.val) / 2^32) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32WidenMadd u32WideMadd u32Max
  simp [ha, hb, hc, MidenState.withStack]

-- U32 bitwise (require isU32 preconditions)

set_option maxHeartbeats 4000000 in
theorem stepU32And (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32And =
    some ⟨Felt.ofNat (a.val &&& b.val) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32And
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
theorem stepU32Or (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32Or =
    some ⟨Felt.ofNat (a.val ||| b.val) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32Or
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
theorem stepU32Xor (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32Xor =
    some ⟨Felt.ofNat (a.val ^^^ b.val) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32Xor
  simp [ha, hb, MidenState.withStack]

-- U32 bit counting

set_option maxHeartbeats 4000000 in
theorem stepU32Clz (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .u32Clz =
    some ⟨Felt.ofNat (u32CountLeadingZeros a.val) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32Clz
  simp [ha, MidenState.withStack]

set_option maxHeartbeats 4000000 in
theorem stepU32Ctz (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .u32Ctz =
    some ⟨Felt.ofNat (u32CountTrailingZeros a.val) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32Ctz
  simp [ha, MidenState.withStack]

set_option maxHeartbeats 4000000 in
/-- u32Clo: count leading ones, expressed via u32CountLeadingZeros on the bitwise complement.
    (u32CountLeadingOnes is private in Semantics.) -/
theorem stepU32Clo (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .u32Clo =
    some ⟨Felt.ofNat (u32CountLeadingZeros (u32Max - 1 - a.val)) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32Clo u32CountLeadingOnes
  simp [ha, MidenState.withStack]

set_option maxHeartbeats 4000000 in
/-- u32Cto: count trailing ones, expressed via u32CountTrailingZeros on the XOR complement.
    (u32CountTrailingOnes is private in Semantics.) -/
theorem stepU32Cto (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, locs, adv⟩ .u32Cto =
    some ⟨Felt.ofNat (u32CountTrailingZeros (a.val ^^^ (u32Max - 1))) :: rest, mem, locs, adv⟩ := by
  unfold execInstruction execU32Cto u32CountTrailingOnes
  simp [ha, MidenState.withStack]

end MidenLean.StepLemmas
