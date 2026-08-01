import MidenLean.Proofs.Helpers

/-!
# Step Lemmas

One lemma per instruction pre-computing the effect of a single
`execInstruction` call (`stepDrop`, `stepDup`, ...), parametric where
possible with explicit range hypotheses for `movup`/`movdn`. These are the
building blocks of the manual proof style; `miden_vcg`-style proofs go
through the symbolic executor instead and do not use them.
-/

namespace MidenLean.StepLemmas

/- One file-level heartbeat budget instead of a copy-pasted per-lemma
   override on all 82 lemmas: at that density the annotations carried no
   information about which lemma is actually expensive. The word-width step
   lemmas (dupw/swapw/movupw) are the reason for the size. -/
set_option maxHeartbeats 4000000

open MidenLean

-- Stack manipulation

theorem stepDrop (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .drop =
    some ⟨rest, mem, frames, adv⟩ := by
  unfold execInstruction execDrop; rfl

theorem stepDropw (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b c d : Felt) (rest : List Felt) :
    execInstruction ⟨a :: b :: c :: d :: rest, mem, frames, adv⟩ .dropw =
    some ⟨rest, mem, frames, adv⟩ := by
  unfold execInstruction execDropw; rfl

/-- Parametric dup: copies the element at index `n` to the top of the stack. -/
theorem stepDup (n : Fin 16) (stk : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (v : Felt) (h : stk[n.val]? = some v) :
    execInstruction ⟨stk, mem, frames, adv⟩ (.dup n) =
    some ⟨v :: stk, mem, frames, adv⟩ := by
  unfold execInstruction execDup
  simp [h, Concrete.State.withStack]

/-- Parametric swap: swaps the top element with the element at index `n`.
    After the rewrite, the result stack contains `List.set` operations;
    use `dsimp only [List.set]` to normalize on concrete lists. -/
theorem stepSwap (n : Fin 16) (stk : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (hn : (n.val == 0) = false)
    (top nth : Felt) (htop : stk[0]? = some top) (hnth : stk[n.val]? = some nth) :
    execInstruction ⟨stk, mem, frames, adv⟩ (.swap n) =
    some ⟨(stk.set 0 nth).set n.val top, mem, frames, adv⟩ := by
  unfold execInstruction execSwap
  simp [hn, htop, hnth, Concrete.State.withStack]

-- movup and movdn: parametric forms

/-- Parametric movup: removes element at index `n` and places it on top.
    After the rewrite, the result stack contains `List.eraseIdx`;
    use `dsimp only [List.eraseIdx]` to normalize on concrete lists. -/
theorem stepMovup (n : Nat) (stk : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (v : Felt) (hn : (n < 2 || n > 15) = false) (hv : stk[n]? = some v) :
    execInstruction ⟨stk, mem, frames, adv⟩ (.movup n) =
    some ⟨v :: stk.eraseIdx n, mem, frames, adv⟩ := by
  unfold execInstruction execMovup removeNth
  simp [hn, hv, Concrete.State.withStack]

/-- Parametric movdn: pops the top element and inserts it at position `n`.
    After the rewrite, the result stack contains `insertAt`;
    use `dsimp only [insertAt, List.take, List.drop, List.append]` to normalize. -/
theorem stepMovdn (n : Nat) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (top : Felt) (rest : List Felt) (hn : (n < 2 || n > 15) = false) :
    execInstruction ⟨top :: rest, mem, frames, adv⟩ (.movdn n) =
    some ⟨insertAt rest n top, mem, frames, adv⟩ := by
  unfold execInstruction execMovdn
  simp [hn, Concrete.State.withStack]

theorem stepReversew (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b c d : Felt) (rest : List Felt) :
    execInstruction ⟨a :: b :: c :: d :: rest, mem, frames, adv⟩ .reversew =
    some ⟨d :: c :: b :: a :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execReversew; rfl

theorem stepDupw0 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b c d : Felt) (rest : List Felt) :
    execInstruction ⟨a :: b :: c :: d :: rest, mem, frames, adv⟩ (.dupw 0) =
    some ⟨a :: b :: c :: d :: a :: b :: c :: d :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execDupw
  simp [Concrete.State.withStack]

theorem stepDupw1 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) :
    execInstruction ⟨a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest, mem, frames, adv⟩ (.dupw 1) =
    some ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execDupw
  simp [Concrete.State.withStack]

theorem stepSwapw1 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Felt) (rest : List Felt) :
    execInstruction ⟨a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest, mem, frames, adv⟩ (.swapw 1) =
    some ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execSwapw
  simp [Concrete.State.withStack]

theorem stepSwapw2 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 : Felt) (rest : List Felt) :
    execInstruction ⟨a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        c0 :: c1 :: c2 :: c3 :: rest, mem, frames, adv⟩ (.swapw 2) =
      some ⟨c0 :: c1 :: c2 :: c3 :: b0 :: b1 :: b2 :: b3 ::
        a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execSwapw; simp [Concrete.State.withStack]

theorem stepSwapw3 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 : Felt) (rest : List Felt) :
    execInstruction ⟨a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
        c0 :: c1 :: c2 :: c3 :: d0 :: d1 :: d2 :: d3 :: rest, mem, frames, adv⟩ (.swapw 3) =
      some ⟨d0 :: d1 :: d2 :: d3 :: b0 :: b1 :: b2 :: b3 ::
        c0 :: c1 :: c2 :: c3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execSwapw; simp [Concrete.State.withStack]

/-- movdnw 2: move the top word down by 2 word positions.
    Stack: [a0..a3, b0..b3, c0..c3, rest] → [b0..b3, c0..c3, a0..a3, rest] -/
theorem stepMovdnw2 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 : Felt) (rest : List Felt) :
    execInstruction ⟨a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
                     c0 :: c1 :: c2 :: c3 :: rest, mem, frames, adv⟩ (.movdnw 2) =
    some ⟨b0 :: b1 :: b2 :: b3 :: c0 :: c1 :: c2 :: c3 ::
          a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execMovdnw
  simp [Concrete.State.withStack]

/-- movdnw 3: move the top word down by 3 word positions.
    Stack: [a0..a3, b0..b3, c0..c3, d0..d3, rest] → [b0..b3, c0..c3, d0..d3, a0..a3, rest] -/
theorem stepMovdnw3 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 : Felt) (rest : List Felt) :
    execInstruction ⟨a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
                     c0 :: c1 :: c2 :: c3 :: d0 :: d1 :: d2 :: d3 :: rest, mem, frames, adv⟩ (.movdnw 3) =
    some ⟨b0 :: b1 :: b2 :: b3 :: c0 :: c1 :: c2 :: c3 ::
          d0 :: d1 :: d2 :: d3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execMovdnw
  simp [Concrete.State.withStack]

/-- swapdw: swap the first two words with the second two words.
    Stack: [a0..a3, b0..b3, c0..c3, d0..d3, rest] → [c0..c3, d0..d3, a0..a3, b0..b3, rest] -/
theorem stepSwapdw (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 : Felt) (rest : List Felt) :
    execInstruction ⟨a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
                     c0 :: c1 :: c2 :: c3 :: d0 :: d1 :: d2 :: d3 :: rest, mem, frames, adv⟩ .swapdw =
    some ⟨c0 :: c1 :: c2 :: c3 :: d0 :: d1 :: d2 :: d3 ::
          a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execSwapdw
  simp [Concrete.State.withStack]

/-- movdn 8: move the top element down by 8 positions.
    Stack: [a0, a1..a8, rest] → [a1..a8, a0, rest] -/
theorem stepMovdn8 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Felt) (rest : List Felt) :
    execInstruction ⟨a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: rest, mem, frames, adv⟩
      (.movdn 8) =
    some ⟨a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a0 :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execMovdn; simp [Concrete.State.withStack]; rfl

/-- movup 8: move element at position 8 to the top.
    Stack: [a0..a7, a8, rest] → [a8, a0..a7, rest] -/
theorem stepMovup8 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Felt) (rest : List Felt) :
    execInstruction ⟨a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: rest, mem, frames, adv⟩
      (.movup 8) =
    some ⟨a8 :: a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execMovup; simp [Concrete.State.withStack]; rfl

-- Assertions

/-- assert succeeds when top of stack is 1, pops it. -/
theorem stepAssert (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt) (h : a.val = 1) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .assert =
    some ⟨rest, mem, frames, adv⟩ := by
  unfold execInstruction execAssert
  simp [h, Concrete.State.withStack]

/-- assertWithError behaves identically to assert (error string is for debugging). -/
theorem stepAssertWithError (msg : String) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt) (h : a.val = 1) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ (.assertWithError msg) =
    some ⟨rest, mem, frames, adv⟩ := by
  unfold execInstruction execAssert
  simp [h, Concrete.State.withStack]

/-- assertz succeeds when top of stack is 0, pops it. -/
theorem stepAssertz (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.val = 0) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .assertz =
    some ⟨rest, mem, frames, adv⟩ := by
  unfold execInstruction execAssertz
  simp [ha, Concrete.State.withStack]

/-- assertEq succeeds when top two elements are equal, pops both. -/
theorem stepAssertEq (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: a :: rest, mem, frames, adv⟩ .assertEq =
    some ⟨rest, mem, frames, adv⟩ := by
  unfold execInstruction execAssertEq
  simp [Concrete.State.withStack]

/-- assertEqWithError behaves identically to assertEq. -/
theorem stepAssertEqWithError (msg : String) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: a :: rest, mem, frames, adv⟩ (.assertEqWithError msg) =
    some ⟨rest, mem, frames, adv⟩ := by
  unfold execInstruction execAssertEq
  simp [Concrete.State.withStack]

-- Assertion failure lemmas (for forward-direction proofs)

/-- assertWithError returns none when the top value is not 1. -/
theorem stepAssertWithError_none (msg : String) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt) (h : a.val ≠ 1) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ (.assertWithError msg) = none := by
  unfold execInstruction execAssert
  simp [show ¬(a.val == 1) = true from by simp [h]]

/-- assertEqWithError returns none when the top two values differ. -/
theorem stepAssertEqWithError_none (msg : String) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt) (h : a ≠ b) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ (.assertEqWithError msg) = none := by
  unfold execInstruction execAssertEq
  simp [show ¬(a == b) = true from by simp [h]]

-- U32 assertions

theorem stepU32Assert2 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨a :: b :: rest, mem, frames, adv⟩ .u32Assert2 =
    some ⟨a :: b :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Assert2
  simp [ha, hb]

-- Field comparison

theorem stepEqImm (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (v a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ (.eqImm v) =
    some ⟨(if a == v then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execEqImm; rfl

theorem stepEq (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .eq =
    some ⟨(if a == b then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execEq; rfl

theorem stepNeq (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .neq =
    some ⟨(if a != b then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execNeq; rfl

theorem stepNeqImm (v : Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ (.neqImm v) =
    some ⟨(if a != v then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execNeqImm; rfl

/-- eqw: compare two words element-wise, push 1 if all equal, 0 otherwise.
    Stack: [b0..b3, a0..a3, rest] → [result, b0..b3, a0..a3, rest] -/
theorem stepEqw (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (b0 b1 b2 b3 a0 a1 a2 a3 : Felt) (rest : List Felt) :
    execInstruction ⟨b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩ .eqw =
      some ⟨(if (a0 == b0) && (a1 == b1) && (a2 == b2) && (a3 == b3) then (1 : Felt) else 0) ::
        b0 :: b1 :: b2 :: b3 :: a0 :: a1 :: a2 :: a3 :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execEqw; simp [Concrete.State.withStack]

theorem stepLt (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .lt =
    some ⟨(if a.val < b.val then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execLt; rfl

theorem stepGt (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .gt =
    some ⟨(if a.val > b.val then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execGt; rfl

theorem stepLte (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .lte =
    some ⟨(if a.val ≤ b.val then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execLte; rfl

theorem stepGte (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .gte =
    some ⟨(if a.val ≥ b.val then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execGte; rfl

-- Field boolean

theorem stepAndIte (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (rest : List Felt) (p q : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) :: (if q then (1 : Felt) else 0) :: rest, mem, frames, adv⟩
      Instruction.and =
    some ⟨(if q && p then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execAnd
  simp only [Felt.isBool_ite_bool, Concrete.State.withStack]
  cases p <;> cases q <;> simp

theorem stepOrIte (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (rest : List Felt) (p q : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) :: (if q then (1 : Felt) else 0) :: rest, mem, frames, adv⟩
      Instruction.or =
    some ⟨(if q || p then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execOr
  simp only [Felt.isBool_ite_bool, Concrete.State.withStack]
  cases p <;> cases q <;> simp

theorem stepNotIte (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (rest : List Felt) (p : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) :: rest, mem, frames, adv⟩
      Instruction.not =
    some ⟨(if !p then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execNot
  simp only [Felt.isBool_ite_bool, Concrete.State.withStack]
  cases p <;> simp

-- Conditional stack manipulation

/-- cswap on a boolean condition (as ite): if true, swap the two elements below. -/
theorem stepCswapIte (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (rest : List Felt) (a b : Felt) (p : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) :: b :: a :: rest, mem, frames, adv⟩
      .cswap =
    some ⟨(if p then a else b) :: (if p then b else a) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execCswap
  simp only [Concrete.State.withStack]
  cases p <;> simp

/-- cdrop on a boolean condition (as ite): if true, keep b; if false, keep a. -/
theorem stepCdropIte (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (rest : List Felt) (a b : Felt) (p : Bool) :
    execInstruction
      ⟨(if p then (1 : Felt) else 0) :: b :: a :: rest, mem, frames, adv⟩
      .cdrop =
    some ⟨(if p then b else a) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execCdrop
  simp only [Concrete.State.withStack]
  cases p <;> simp

/-- cdropw on a boolean condition (as ite): if true, keep the word `b`; if false, keep the word `a`. -/
theorem stepCdropwIte (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
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
  simp only [Concrete.State.withStack]
  cases p <;> simp

-- Field arithmetic

theorem stepAdd (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .add =
    some ⟨(a + b) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execAdd; rfl

theorem stepAddImm (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (v a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ (.addImm v) =
    some ⟨(a + v) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execAddImm; rfl

theorem stepSub (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .sub =
    some ⟨(a - b) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execSub; rfl

theorem stepMul (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .mul =
    some ⟨(a * b) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execMul; rfl

theorem stepNeg (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .neg =
    some ⟨(-a) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execNeg; rfl

theorem stepIncr (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .incr =
    some ⟨(a + 1) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execIncr; rfl

theorem stepPush (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (v : Felt) (stk : List Felt) :
    execInstruction ⟨stk, mem, frames, adv⟩ (.push v) =
    some ⟨v :: stk, mem, frames, adv⟩ := by
  unfold execInstruction execPush; rfl

theorem stepPadw (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (stk : List Felt) :
    execInstruction ⟨stk, mem, frames, adv⟩ .padw =
    some ⟨(0 : Felt) :: 0 :: 0 :: 0 :: stk, mem, frames, adv⟩ := by
  unfold execInstruction execPadw; rfl

-- Pow2

theorem stepPow2 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.val ≤ 63) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .pow2 =
    some ⟨Felt.ofNat (2^a.val) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execPow2
  simp [show ¬(a.val > 63) from by omega, Concrete.State.withStack]

-- U32 arithmetic

theorem stepU32WidenAdd (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32WidenAdd =
    some ⟨Felt.ofNat ((a.val + b.val) % 2^32) ::
          Felt.ofNat ((a.val + b.val) / 2^32) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32WidenAdd u32WideAdd u32Max
  simp [ha, hb, Concrete.State.withStack]

theorem stepU32OverflowAdd (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32OverflowAdd =
    some ⟨Felt.ofNat ((a.val + b.val) / 2^32) ::
          Felt.ofNat ((a.val + b.val) % 2^32) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32OverflowAdd u32WideAdd u32Max
  simp [ha, hb, Concrete.State.withStack]

theorem stepU32WidenAdd3 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b c : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    execInstruction ⟨c :: b :: a :: rest, mem, frames, adv⟩ .u32WidenAdd3 =
    some ⟨Felt.ofNat ((a.val + b.val + c.val) % 2^32) ::
          Felt.ofNat ((a.val + b.val + c.val) / 2^32) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32WidenAdd3 u32WideAdd3 u32Max
  simp [ha, hb, hc, Concrete.State.withStack]

theorem stepU32OverflowSub (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32OverflowSub =
    some ⟨Felt.ofNat (u32OverflowingSub a.val b.val).1 ::
          Felt.ofNat (u32OverflowingSub a.val b.val).2 ::
          rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32OverflowSub
  simp [ha, hb, Concrete.State.withStack]

theorem stepU32WidenMul (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32WidenMul =
    some ⟨Felt.ofNat ((a.val * b.val) % 2^32) ::
          Felt.ofNat ((a.val * b.val) / 2^32) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32WidenMul u32WideMul u32Max
  simp [ha, hb, Concrete.State.withStack]

theorem stepU32WidenMadd (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b c : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    execInstruction ⟨b :: a :: c :: rest, mem, frames, adv⟩ .u32WidenMadd =
    some ⟨Felt.ofNat ((a.val * b.val + c.val) % 2^32) ::
          Felt.ofNat ((a.val * b.val + c.val) / 2^32) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32WidenMadd u32WideMadd u32Max
  simp [ha, hb, hc, Concrete.State.withStack]

theorem stepU32WrappingMadd (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b c : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) (hc : c.isU32 = true) :
    execInstruction ⟨b :: a :: c :: rest, mem, frames, adv⟩ .u32WrappingMadd =
    some ⟨Felt.ofNat ((a.val * b.val + c.val) % 2^32) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32WrappingMadd u32Max
  simp [ha, hb, hc, Concrete.State.withStack]

-- U32 bitwise (require isU32 preconditions)

theorem stepU32And (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32And =
    some ⟨Felt.ofNat (a.val &&& b.val) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32And
  simp [ha, hb, Concrete.State.withStack]

theorem stepU32Or (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32Or =
    some ⟨Felt.ofNat (a.val ||| b.val) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Or
  simp [ha, hb, Concrete.State.withStack]

theorem stepU32Xor (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32Xor =
    some ⟨Felt.ofNat (a.val ^^^ b.val) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Xor
  simp [ha, hb, Concrete.State.withStack]

theorem stepU32Not (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .u32Not =
    some ⟨Felt.ofNat (u32Max - 1 - a.val) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Not u32Max
  simp [ha, Concrete.State.withStack]

-- U32 comparison (require isU32 preconditions)

theorem stepU32Lt (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32Lt =
    some ⟨(if a.val < b.val then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Lt
  simp [ha, hb, Concrete.State.withStack]

theorem stepU32Gt (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32Gt =
    some ⟨(if a.val > b.val then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Gt
  simp [ha, hb, Concrete.State.withStack]

theorem stepU32Lte (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32Lte =
    some ⟨(if a.val ≤ b.val then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Lte
  simp [ha, hb, Concrete.State.withStack]

theorem stepU32Gte (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32Gte =
    some ⟨(if a.val ≥ b.val then (1 : Felt) else 0) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Gte
  simp [ha, hb, Concrete.State.withStack]

-- U32 bit counting

theorem stepU32Clz (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .u32Clz =
    some ⟨Felt.ofNat (u32CountLeadingZeros a.val) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Clz
  simp [ha, Concrete.State.withStack]

theorem stepU32Ctz (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .u32Ctz =
    some ⟨Felt.ofNat (u32CountTrailingZeros a.val) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Ctz
  simp [ha, Concrete.State.withStack]

/-- u32Clo: count leading ones, expressed via u32CountLeadingZeros on the bitwise complement.
    (u32CountLeadingOnes is private in Semantics.) -/
theorem stepU32Clo (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .u32Clo =
    some ⟨Felt.ofNat (u32CountLeadingZeros (u32Max - 1 - a.val)) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Clo u32CountLeadingOnes
  simp [ha, Concrete.State.withStack]

/-- u32Cto: count trailing ones, expressed via u32CountTrailingZeros on the XOR complement.
    (u32CountTrailingOnes is private in Semantics.) -/
theorem stepU32Cto (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt)
    (ha : a.isU32 = true) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .u32Cto =
    some ⟨Felt.ofNat (u32CountTrailingZeros (a.val ^^^ (u32Max - 1))) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Cto u32CountTrailingOnes
  simp [ha, Concrete.State.withStack]

-- U32 split

theorem stepU32Split (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a : Felt) (rest : List Felt) :
    execInstruction ⟨a :: rest, mem, frames, adv⟩ .u32Split =
    some ⟨a.lo32 :: a.hi32 :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32Split; rfl

-- Field div (requires nonzero divisor)

theorem stepDiv (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (hb : (b == (0 : Felt)) = false) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .div =
    some ⟨(a * b⁻¹) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execDiv
  simp [hb, Concrete.State.withStack]

-- U32 divmod (requires isU32 and nonzero divisor)

theorem stepU32DivMod (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (a b : Felt) (rest : List Felt)
    (ha : a.isU32 = true) (hb : b.isU32 = true)
    (hbnz : (b.val == 0) = false) :
    execInstruction ⟨b :: a :: rest, mem, frames, adv⟩ .u32DivMod =
    some ⟨Felt.ofNat (a.val % b.val) :: Felt.ofNat (a.val / b.val) :: rest, mem, frames, adv⟩ := by
  unfold execInstruction execU32DivMod
  simp [ha, hb, hbnz, Concrete.State.withStack]

-- Emit (no-op)

theorem stepEmitImm (n : Nat) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (stk : List Felt) :
    execInstruction ⟨stk, mem, frames, adv⟩ (.emitImm n) =
    some ⟨stk, mem, frames, adv⟩ := by
  unfold execInstruction; rfl

-- Advice stack

theorem stepAdvPush (n : Nat) (mem : Nat → Felt)
    (frames : List LocalFrame) (adv : List Felt) (stk : List Felt)
    (hlen : adv.length ≥ n) :
    execInstruction ⟨stk, mem, frames, adv⟩ (.advPush n) =
    some ⟨(adv.take n).reverse ++ stk, mem, frames, adv.drop n⟩ := by
  unfold execInstruction execAdvPush
  simp only [Concrete.State.withStack, Concrete.State.withAdvice]
  split
  · omega
  · rfl

theorem stepAdvPush1 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (v : Felt) (stk : List Felt) (adv' : List Felt)
    (hadv : adv = v :: adv') :
    execInstruction ⟨stk, mem, frames, adv⟩ (.advPush 1) =
    some ⟨v :: stk, mem, frames, adv'⟩ := by
  unfold execInstruction execAdvPush
  subst hadv
  simp [Concrete.State.withStack, Concrete.State.withAdvice]

theorem stepAdvPush2 (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (v1 v2 : Felt) (stk : List Felt) (adv' : List Felt)
    (hadv : adv = v1 :: v2 :: adv') :
    execInstruction ⟨stk, mem, frames, adv⟩ (.advPush 2) =
    some ⟨v2 :: v1 :: stk, mem, frames, adv'⟩ := by
  unfold execInstruction execAdvPush
  subst hadv
  simp [Concrete.State.withStack, Concrete.State.withAdvice]

-- Local memory (frame-aware)

/-- locLoad: push the value of local slot `idx` onto the stack. -/
theorem stepLocLoad (idx : Nat) (frame : LocalFrame) (frames_rest : List LocalFrame)
    (mem : Nat → Felt) (adv : List Felt)
    (stk : List Felt) (hidx : idx < frame.numLocals) :
    execInstruction ⟨stk, mem, frame :: frames_rest, adv⟩ (.locLoad idx) =
    some ⟨mem (frame.localAddr idx) :: stk, mem, frame :: frames_rest, adv⟩ := by
  unfold execInstruction execLocLoad
  simp [Concrete.State.readLocal?, Concrete.State.localAddr?, hidx, Concrete.State.withStack]

/-- locStore: pop the top of the stack and write it to local slot `idx`. -/
theorem stepLocStore (idx : Nat) (frame : LocalFrame) (frames_rest : List LocalFrame)
    (mem : Nat → Felt) (adv : List Felt)
    (v : Felt) (rest : List Felt) (hidx : idx < frame.numLocals) :
    execInstruction ⟨v :: rest, mem, frame :: frames_rest, adv⟩ (.locStore idx) =
    some ⟨rest, fun i => if i = frame.localAddr idx then v else mem i, frame :: frames_rest, adv⟩ := by
  unfold execInstruction execLocStore
  simp [Concrete.State.writeLocal?, Concrete.State.localAddr?, hidx, Concrete.State.writeMemory, Concrete.State.withStack]

/-- locStorewBe: store the top word to local memory at `idx` in big-endian order.
    The word remains on the stack. The resulting memory function is a nested
    if-then-else chain reflecting the four writes. -/
theorem stepLocStorewBe (idx : Nat) (frame : LocalFrame) (frames_rest : List LocalFrame)
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
  simp [halign, Nat.not_lt_of_le hbound, Concrete.State.writeMemory, Concrete.State.withStack]

/-- locStorewLe: store the top word to local memory at `idx` in little-endian order.
    The word remains on the stack. The resulting memory function is a nested
    if-then-else chain reflecting the four writes. -/
theorem stepLocStorewLe (idx : Nat) (frame : LocalFrame) (frames_rest : List LocalFrame)
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
  simp [halign, Nat.not_lt_of_le hbound, Concrete.State.writeMemory, Concrete.State.withStack]

/-- locLoadwBe: load a word from local memory at `idx` in big-endian order,
    replacing the top four stack elements. -/
theorem stepLocLoadwBe (idx : Nat) (frame : LocalFrame) (frames_rest : List LocalFrame)
    (mem : Nat → Felt) (adv : List Felt)
    (s0 s1 s2 s3 : Felt) (rest : List Felt)
    (halign : idx % 4 = 0) (hbound : idx + 4 ≤ frame.numLocals) :
    let baseAddr := frame.localAddr idx
    execInstruction ⟨s0 :: s1 :: s2 :: s3 :: rest, mem, frame :: frames_rest, adv⟩ (.locLoadwBe idx) =
    some ⟨mem (baseAddr + 3) :: mem (baseAddr + 2) :: mem (baseAddr + 1) :: mem baseAddr :: rest,
      mem, frame :: frames_rest, adv⟩ := by
  unfold execInstruction execLocLoadwBe currentFrame
  simp [halign, Nat.not_lt_of_le hbound, Concrete.State.withStack]

/-- locLoadwLe: load a word from local memory at `idx` in little-endian order,
    replacing the top four stack elements. -/
theorem stepLocLoadwLe (idx : Nat) (frame : LocalFrame) (frames_rest : List LocalFrame)
    (mem : Nat → Felt) (adv : List Felt)
    (s0 s1 s2 s3 : Felt) (rest : List Felt)
    (halign : idx % 4 = 0) (hbound : idx + 4 ≤ frame.numLocals) :
    let baseAddr := frame.localAddr idx
    execInstruction ⟨s0 :: s1 :: s2 :: s3 :: rest, mem, frame :: frames_rest, adv⟩ (.locLoadwLe idx) =
    some ⟨mem baseAddr :: mem (baseAddr + 1) :: mem (baseAddr + 2) :: mem (baseAddr + 3) :: rest,
      mem, frame :: frames_rest, adv⟩ := by
  unfold execInstruction execLocLoadwLe currentFrame
  simp [halign, Nat.not_lt_of_le hbound, Concrete.State.withStack]

/-- locaddr: push the absolute address of local slot `idx` onto the stack. -/
theorem stepLocAddr (idx : Nat) (frame : LocalFrame) (frames_rest : List LocalFrame)
    (mem : Nat → Felt) (adv : List Felt)
    (stk : List Felt) (hidx : idx < frame.numLocals) :
    execInstruction ⟨stk, mem, frame :: frames_rest, adv⟩ (.locaddr idx) =
    some ⟨Felt.ofNat (frame.localAddr idx) :: stk, mem, frame :: frames_rest, adv⟩ := by
  unfold execInstruction execLocAddr
  simp [Concrete.State.localAddr?, hidx, Concrete.State.withStack]

end MidenLean.StepLemmas
