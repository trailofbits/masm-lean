import MidenLean.Proofs.Helpers

namespace MidenLean.StepLemmas

open MidenLean

-- ============================================================================
-- Stack manipulation
-- ============================================================================

set_option maxHeartbeats 400000 in
theorem stepDrop (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    stepInstruction ⟨a :: rest, mem, locs, adv⟩ .drop =
    some ⟨rest, mem, locs, adv⟩ := by
  unfold stepInstruction; rfl

set_option maxHeartbeats 800000 in
/-- Parametric dup: copies the element at index `n` to the top of the stack. -/
theorem stepDup (n : Fin 16) (stk : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (v : Felt) (h : stk[n.val]? = some v) :
    stepInstruction ⟨stk, mem, locs, adv⟩ (.dup n) =
    some ⟨v :: stk, mem, locs, adv⟩ := by
  unfold stepInstruction
  simp [h, MidenState.withStack]

set_option maxHeartbeats 4000000 in
/-- Parametric swap: swaps the top element with the element at index `n`.
    After the rewrite, the result stack contains `List.set` operations;
    use `dsimp only [List.set]` to normalize on concrete lists. -/
theorem stepSwap (n : Fin 16) (stk : List Felt) (mem locs : Nat → Felt) (adv : List Felt)
    (hn : (n.val == 0) = false)
    (top nth : Felt) (htop : stk[0]? = some top) (hnth : stk[n.val]? = some nth) :
    stepInstruction ⟨stk, mem, locs, adv⟩ (.swap n) =
    some ⟨(stk.set 0 nth).set n.val top, mem, locs, adv⟩ := by
  unfold stepInstruction
  simp [hn, htop, hnth, MidenState.withStack]

-- movup and movdn: concrete forms since removeNth/insertAt are private to Semantics

set_option maxHeartbeats 4000000 in
theorem stepMovup2 (mem locs : Nat → Felt) (adv : List Felt)
    (a b c : Felt) (rest : List Felt) :
    stepInstruction ⟨a :: b :: c :: rest, mem, locs, adv⟩ (.movup 2) =
    some ⟨c :: a :: b :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction; rfl

set_option maxHeartbeats 4000000 in
theorem stepMovup3 (mem locs : Nat → Felt) (adv : List Felt)
    (a b c d : Felt) (rest : List Felt) :
    stepInstruction ⟨a :: b :: c :: d :: rest, mem, locs, adv⟩ (.movup 3) =
    some ⟨d :: a :: b :: c :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction; rfl

set_option maxHeartbeats 4000000 in
theorem stepMovdn2 (mem locs : Nat → Felt) (adv : List Felt)
    (a b c : Felt) (rest : List Felt) :
    stepInstruction ⟨a :: b :: c :: rest, mem, locs, adv⟩ (.movdn 2) =
    some ⟨b :: c :: a :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction; rfl

set_option maxHeartbeats 4000000 in
theorem stepMovdn3 (mem locs : Nat → Felt) (adv : List Felt)
    (a b c d : Felt) (rest : List Felt) :
    stepInstruction ⟨a :: b :: c :: d :: rest, mem, locs, adv⟩ (.movdn 3) =
    some ⟨b :: c :: d :: a :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction; rfl

-- ============================================================================
-- Field comparison
-- ============================================================================

set_option maxHeartbeats 400000 in
theorem stepEqImm (mem locs : Nat → Felt) (adv : List Felt)
    (v a : Felt) (rest : List Felt) :
    stepInstruction ⟨a :: rest, mem, locs, adv⟩ (.eqImm v) =
    some ⟨(if a == v then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction; rfl

set_option maxHeartbeats 400000 in
theorem stepEq (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    stepInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .eq =
    some ⟨(if a == b then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction; rfl

set_option maxHeartbeats 400000 in
theorem stepNeq (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    stepInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .neq =
    some ⟨(if a != b then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction; rfl

-- ============================================================================
-- Field boolean
-- ============================================================================

set_option maxHeartbeats 800000 in
theorem stepAndIte (mem locs : Nat → Felt) (adv : List Felt)
    (rest : List Felt) (p q : Bool) :
    stepInstruction
      ⟨(if p then (1 : Felt) else 0) :: (if q then (1 : Felt) else 0) :: rest, mem, locs, adv⟩
      Instruction.and =
    some ⟨(if q && p then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction
  simp only [Felt.isBool_ite_bool, MidenState.withStack]
  cases p <;> cases q <;> simp

set_option maxHeartbeats 800000 in
theorem stepOrIte (mem locs : Nat → Felt) (adv : List Felt)
    (rest : List Felt) (p q : Bool) :
    stepInstruction
      ⟨(if p then (1 : Felt) else 0) :: (if q then (1 : Felt) else 0) :: rest, mem, locs, adv⟩
      Instruction.or =
    some ⟨(if q || p then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction
  simp only [Felt.isBool_ite_bool, MidenState.withStack]
  cases p <;> cases q <;> simp

set_option maxHeartbeats 800000 in
theorem stepNotIte (mem locs : Nat → Felt) (adv : List Felt)
    (rest : List Felt) (p : Bool) :
    stepInstruction
      ⟨(if p then (1 : Felt) else 0) :: rest, mem, locs, adv⟩
      Instruction.not =
    some ⟨(if !p then (1 : Felt) else 0) :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction
  simp only [Felt.isBool_ite_bool, MidenState.withStack]
  cases p <;> simp

-- ============================================================================
-- Field arithmetic
-- ============================================================================

set_option maxHeartbeats 400000 in
theorem stepAddImm (mem locs : Nat → Felt) (adv : List Felt)
    (v a : Felt) (rest : List Felt) :
    stepInstruction ⟨a :: rest, mem, locs, adv⟩ (.addImm v) =
    some ⟨(a + v) :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction; rfl

-- ============================================================================
-- U32 arithmetic
-- ============================================================================

set_option maxHeartbeats 4000000 in
theorem stepU32WidenAdd (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    stepInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32WidenAdd =
    some ⟨Felt.ofNat ((a.val + b.val) % 2^32) ::
          Felt.ofNat ((a.val + b.val) / 2^32) :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction; rfl

set_option maxHeartbeats 4000000 in
theorem stepU32WidenAdd3 (mem locs : Nat → Felt) (adv : List Felt)
    (a b c : Felt) (rest : List Felt) :
    stepInstruction ⟨c :: b :: a :: rest, mem, locs, adv⟩ .u32WidenAdd3 =
    some ⟨Felt.ofNat ((a.val + b.val + c.val) % 2^32) ::
          Felt.ofNat ((a.val + b.val + c.val) / 2^32) :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction; rfl

set_option maxHeartbeats 4000000 in
theorem stepU32OverflowSub (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    stepInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32OverflowSub =
    some ⟨Felt.ofNat (u32OverflowingSub a.val b.val).1 ::
          Felt.ofNat (u32OverflowingSub a.val b.val).2 ::
          rest, mem, locs, adv⟩ := by
  unfold stepInstruction; rfl

-- U32 bitwise (require isU32 preconditions)

set_option maxHeartbeats 4000000 in
theorem stepU32And (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    stepInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32And =
    some ⟨Felt.ofNat (a.val &&& b.val) :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
theorem stepU32Or (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    stepInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32Or =
    some ⟨Felt.ofNat (a.val ||| b.val) :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction
  simp [ha, hb, MidenState.withStack]

set_option maxHeartbeats 4000000 in
theorem stepU32Xor (mem locs : Nat → Felt) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    stepInstruction ⟨b :: a :: rest, mem, locs, adv⟩ .u32Xor =
    some ⟨Felt.ofNat (a.val ^^^ b.val) :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction
  simp [ha, hb, MidenState.withStack]

-- U32 bit counting

set_option maxHeartbeats 4000000 in
theorem stepU32Clz (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    stepInstruction ⟨a :: rest, mem, locs, adv⟩ .u32Clz =
    some ⟨Felt.ofNat (u32CountLeadingZeros a.val) :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction; rfl

set_option maxHeartbeats 4000000 in
theorem stepU32Ctz (mem locs : Nat → Felt) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    stepInstruction ⟨a :: rest, mem, locs, adv⟩ .u32Ctz =
    some ⟨Felt.ofNat (u32CountTrailingZeros a.val) :: rest, mem, locs, adv⟩ := by
  unfold stepInstruction; rfl

end MidenLean.StepLemmas
