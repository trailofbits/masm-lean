import MidenLean.Symbolic.Soundness
import MidenLean.Generated.U64

/-!
# Symbolic Reflection

Demonstrates end-to-end use of the symbolic block executor to prove
correctness of real MASM procedures. The key components:
1. `exec_basic_block` bridge (exec → concreteExecBlock)
2. `execBlock_sound` soundness theorem
3. `reflect_basic_block` combined theorem
-/

/-- Strip leading ∧ conjuncts from `hexec`, subst the trailing equation, close with rfl.
    Works for both the old `hconc` name and the current `hexec` name. -/
syntax "extract_and_close" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| extract_and_close) => `(tactic|
    first
    | (obtain ⟨_, _, _, _, _, hexec⟩ := hexec; subst hexec; exact ⟨rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, _, _, hexec⟩ := hexec; subst hexec; exact ⟨rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, _, hexec⟩ := hexec; subst hexec; exact ⟨rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, hexec⟩ := hexec; subst hexec; exact ⟨rfl, rfl, rfl⟩)
    | (obtain ⟨_, hexec⟩ := hexec; subst hexec; exact ⟨rfl, rfl, rfl⟩)
    | (subst hexec; exact ⟨rfl, rfl, rfl⟩))

namespace MidenLean

/-- Stack-pure instructions don't read or write memory, frames, or advice. -/
def Instruction.isStackPure : Instruction → Bool
  | .cswap | .cswapw | .cdrop | .cdropw => false
  | .u32Test | .u32TestW => false
  | .memLoad | .memLoadImm _ | .memStore | .memStoreImm _ => false
  | .memLoadwBe | .memLoadwBeImm _ | .memStorewBe | .memStorewBeImm _ => false
  | .memLoadwLe | .memLoadwLeImm _ | .memStorewLe | .memStorewLeImm _ => false
  | .locLoad _ | .locStore _ | .locLoadwBe _ | .locLoadwLe _ => false
  | .locStorewBe _ | .locStorewLe _ | .locaddr _ => false
  | .advPush _ | .advLoadW => false
  | .exec _ => false
  | _ => true

end MidenLean

namespace MidenLean.Symbolic.Reflect

open MidenLean
open MidenLean.Symbolic

-- ============================================================================
-- Stack-pure instruction: combined preservation and transfer
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- For a stack-pure instruction, if execution succeeds on one state, it
    succeeds on any other state with the same stack, producing the same
    output stack and preserving the second state's non-stack components. -/
private theorem concreteExecInstruction_stackPure
    (i : Instruction) (stk : List Felt)
    (m₁ m₂ : Nat → Felt) (f₁ f₂ : List LocalFrame) (a₁ a₂ : List Felt)
    (cs₁' : MidenState)
    (hpure : i.isStackPure)
    (hexec₁ : MidenLean.execInstruction ⟨stk, m₁, f₁, a₁⟩ i = some cs₁') :
    ∃ cs₂', MidenLean.execInstruction ⟨stk, m₂, f₂, a₂⟩ i = some cs₂' ∧
             cs₂'.stack = cs₁'.stack ∧
             cs₂'.memory = m₂ ∧ cs₂'.frames = f₂ ∧ cs₂'.advice = a₂ := by
  -- Phase 1: prove preservation (cs₁' keeps m₁, f₁, a₁)
  have hpres : cs₁'.memory = m₁ ∧ cs₁'.frames = f₁ ∧ cs₁'.advice = a₁ := by
    revert hexec₁; intro hexec
    cases i with
    | cswap | cswapw | cdrop | cdropw | u32Test | u32TestW
    | memLoad | memStore | memLoadwBe | memStorewBe | memLoadwLe | memStorewLe
    | advLoadW =>
      simp [Instruction.isStackPure] at hpure
    | memLoadImm | memStoreImm | memLoadwBeImm | memStorewBeImm
    | memLoadwLeImm | memStorewLeImm
    | locLoad | locStore | locLoadwBe | locLoadwLe | locStorewBe | locStorewLe | locaddr
    | advPush | exec =>
      simp [Instruction.isStackPure] at hpure
    | nop => simp [MidenLean.execInstruction] at hexec; subst hexec; exact ⟨rfl, rfl, rfl⟩
    | emitImm => simp [MidenLean.execInstruction] at hexec; subst hexec; exact ⟨rfl, rfl, rfl⟩
    | emit =>
      simp only [MidenLean.execInstruction] at hexec; unfold execEmit at hexec
      revert hexec; cases stk <;> simp; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | drop =>
      simp only [MidenLean.execInstruction] at hexec; unfold execDrop at hexec
      revert hexec; cases stk <;> simp [MidenState.withStack]
      intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | dropw =>
      simp only [MidenLean.execInstruction] at hexec; unfold execDropw at hexec
      revert hexec; match stk with
      | [] | [_] | [_,_] | [_,_,_] => simp
      | _::_::_::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | padw =>
      simp only [MidenLean.execInstruction] at hexec; unfold execPadw at hexec
      simp [MidenState.withStack] at hexec; subst hexec; exact ⟨rfl, rfl, rfl⟩
    | push =>
      simp only [MidenLean.execInstruction] at hexec; unfold execPush at hexec
      simp [MidenState.withStack] at hexec; subst hexec; exact ⟨rfl, rfl, rfl⟩
    | pushList =>
      simp only [MidenLean.execInstruction] at hexec; unfold execPushList at hexec
      simp [MidenState.withStack] at hexec; subst hexec; exact ⟨rfl, rfl, rfl⟩
    | dup =>
      simp only [MidenLean.execInstruction] at hexec; unfold execDup at hexec
      split at hexec <;> simp [MidenState.withStack] at hexec
      subst hexec; exact ⟨rfl, rfl, rfl⟩
    | dupw n =>
      simp only [MidenLean.execInstruction] at hexec; unfold execDupw at hexec
      fin_cases n <;> (
        simp only [] at hexec
        split at hexec
        · simp only [MidenState.withStack, Option.some.injEq] at hexec
          subst hexec; exact ⟨rfl, rfl, rfl⟩
        · simp at hexec)
    | swap =>
      simp only [MidenLean.execInstruction] at hexec; unfold execSwap at hexec
      split at hexec
      · simp at hexec; subst hexec; exact ⟨rfl, rfl, rfl⟩
      · split at hexec <;> simp [MidenState.withStack] at hexec
        subst hexec; exact ⟨rfl, rfl, rfl⟩
    | swapw n =>
      simp only [MidenLean.execInstruction] at hexec; unfold execSwapw at hexec
      fin_cases n <;> simp only [] at hexec <;> simp at hexec <;> (
        first
        | (subst hexec; exact ⟨rfl, rfl, rfl⟩)
        | (split at hexec
           · simp only [MidenState.withStack, Option.some.injEq] at hexec
             subst hexec; exact ⟨rfl, rfl, rfl⟩
           · simp at hexec))
    | swapdw =>
      simp only [MidenLean.execInstruction] at hexec; unfold execSwapdw at hexec
      revert hexec; match stk with
      | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_]
      | [_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_]
      | [_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_]
      | [_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => simp
      | _::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_ =>
        simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | movup =>
      simp only [MidenLean.execInstruction] at hexec; unfold execMovup removeNth at hexec
      split at hexec
      · simp at hexec
      · split at hexec <;> simp [MidenState.withStack] at hexec
        subst hexec; exact ⟨rfl, rfl, rfl⟩
    | movdn =>
      simp only [MidenLean.execInstruction] at hexec; unfold execMovdn at hexec
      split at hexec
      · simp at hexec
      · revert hexec; cases stk with
        | nil => simp
        | cons top rest =>
          simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | movupw =>
      simp only [MidenLean.execInstruction] at hexec; unfold execMovupw at hexec
      simp [MidenState.withStack] at hexec; extract_and_close
    | movdnw =>
      simp only [MidenLean.execInstruction] at hexec; unfold execMovdnw at hexec
      simp [MidenState.withStack] at hexec; extract_and_close
    | reversew =>
      simp only [MidenLean.execInstruction] at hexec; unfold execReversew at hexec
      revert hexec; match stk with
      | [] | [_] | [_,_] | [_,_,_] => simp
      | _::_::_::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | eqw =>
      simp only [MidenLean.execInstruction] at hexec; unfold execEqw at hexec
      revert hexec; match stk with
      | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] | [_,_,_,_,_,_,_] => simp
      | _::_::_::_::_::_::_::_::_ =>
        simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | add =>
      simp only [MidenLean.execInstruction] at hexec; unfold execAdd at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | sub =>
      simp only [MidenLean.execInstruction] at hexec; unfold execSub at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | mul =>
      simp only [MidenLean.execInstruction] at hexec; unfold execMul at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | eq =>
      simp only [MidenLean.execInstruction] at hexec; unfold execEq at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | neq =>
      simp only [MidenLean.execInstruction] at hexec; unfold execNeq at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | lt =>
      simp only [MidenLean.execInstruction] at hexec; unfold execLt at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | lte =>
      simp only [MidenLean.execInstruction] at hexec; unfold execLte at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | gt =>
      simp only [MidenLean.execInstruction] at hexec; unfold execGt at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | gte =>
      simp only [MidenLean.execInstruction] at hexec; unfold execGte at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | neg =>
      simp only [MidenLean.execInstruction] at hexec; unfold execNeg at hexec
      revert hexec; cases stk <;> simp [MidenState.withStack]
      intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | incr =>
      simp only [MidenLean.execInstruction] at hexec; unfold execIncr at hexec
      revert hexec; cases stk <;> simp [MidenState.withStack]
      intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | isOdd =>
      simp only [MidenLean.execInstruction] at hexec; unfold execIsOdd at hexec
      revert hexec; cases stk <;> simp [MidenState.withStack]
      intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | addImm =>
      simp only [MidenLean.execInstruction] at hexec; unfold execAddImm at hexec
      revert hexec; cases stk <;> simp [MidenState.withStack]
      intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | subImm =>
      simp only [MidenLean.execInstruction] at hexec; unfold execSubImm at hexec
      revert hexec; cases stk <;> simp [MidenState.withStack]
      intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | mulImm =>
      simp only [MidenLean.execInstruction] at hexec; unfold execMulImm at hexec
      revert hexec; cases stk <;> simp [MidenState.withStack]
      intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | eqImm =>
      simp only [MidenLean.execInstruction] at hexec; unfold execEqImm at hexec
      revert hexec; cases stk <;> simp [MidenState.withStack]
      intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | neqImm =>
      simp only [MidenLean.execInstruction] at hexec; unfold execNeqImm at hexec
      revert hexec; cases stk <;> simp [MidenState.withStack]
      intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | assert =>
      simp only [MidenLean.execInstruction] at hexec; unfold execAssert at hexec
      revert hexec; cases stk with
      | nil => simp
      | cons a rest =>
        intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | assertWithError =>
      simp only [MidenLean.execInstruction] at hexec; unfold execAssert at hexec
      revert hexec; cases stk with
      | nil => simp
      | cons a rest =>
        intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | assertz =>
      simp only [MidenLean.execInstruction] at hexec; unfold execAssertz at hexec
      revert hexec; cases stk with
      | nil => simp
      | cons a rest =>
        intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | assertzWithError =>
      simp only [MidenLean.execInstruction] at hexec; unfold execAssertz at hexec
      revert hexec; cases stk with
      | nil => simp
      | cons a rest =>
        intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | assertEq =>
      simp only [MidenLean.execInstruction] at hexec; unfold execAssertEq at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _ :: _ :: _ =>
        intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | assertEqWithError =>
      simp only [MidenLean.execInstruction] at hexec; unfold execAssertEq at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _ :: _ :: _ =>
        intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | assertEqw =>
      simp only [MidenLean.execInstruction] at hexec; unfold execAssertEqw at hexec
      revert hexec; match stk with
      | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] | [_,_,_,_,_,_,_] => simp
      | _::_::_::_::_::_::_::_::_ =>
        intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | div =>
      simp only [MidenLean.execInstruction] at hexec; unfold execDiv at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ =>
        intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | divImm =>
      simp only [MidenLean.execInstruction] at hexec; unfold execDivImm at hexec
      revert hexec; cases stk with
      | nil => simp
      | cons a rest =>
        intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | inv =>
      simp only [MidenLean.execInstruction] at hexec; unfold execInv at hexec
      revert hexec; cases stk with
      | nil => simp
      | cons a rest =>
        intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | pow2 =>
      simp only [MidenLean.execInstruction] at hexec; unfold execPow2 at hexec
      revert hexec; cases stk with
      | nil => simp
      | cons a rest =>
        intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | and =>
      simp only [MidenLean.execInstruction] at hexec; unfold execAnd at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | or =>
      simp only [MidenLean.execInstruction] at hexec; unfold execOr at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | xor =>
      simp only [MidenLean.execInstruction] at hexec; unfold execXor at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | not =>
      simp only [MidenLean.execInstruction] at hexec; unfold execNot at hexec
      revert hexec; cases stk with
      | nil => simp
      | cons a rest => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32Assert =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Assert at hexec
      revert hexec; cases stk with
      | nil => simp
      | cons a rest => intro hexec; simp at hexec; extract_and_close
    | u32Assert2 =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Assert2 at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp at hexec; extract_and_close
    | u32AssertW =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32AssertW at hexec
      revert hexec; match stk with
      | [] | [_] | [_,_] | [_,_,_] => simp
      | _::_::_::_::_ => intro hexec; simp at hexec; extract_and_close
    | u32Cast =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Cast at hexec
      revert hexec; cases stk <;> simp [MidenState.withStack]
      intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | u32Split =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Split at hexec
      revert hexec; cases stk <;> simp [MidenState.withStack]
      intro h; subst h; exact ⟨rfl, rfl, rfl⟩
    | u32WidenAdd =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32WidenAdd at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32OverflowAdd =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32OverflowAdd at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32WrappingAdd =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32WrappingAdd at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32OverflowSub =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32OverflowSub at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32WrappingSub =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32WrappingSub at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32WidenMul =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32WidenMul at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32WrappingMul =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32WrappingMul at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32And =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32And at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32Or =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Or at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32Xor =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Xor at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32Lt =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Lt at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32Lte =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Lte at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32Gt =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Gt at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32Gte =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Gte at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32Min =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Min at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32Max =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Max at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32WidenAdd3 =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32WidenAdd3 at hexec
      revert hexec; match stk with
      | [] | [_] | [_,_] => simp
      | _::_::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32OverflowAdd3 =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32OverflowAdd3 at hexec
      revert hexec; match stk with
      | [] | [_] | [_,_] => simp
      | _::_::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32WrappingAdd3 =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32WrappingAdd3 at hexec
      revert hexec; match stk with
      | [] | [_] | [_,_] => simp
      | _::_::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32WidenMadd =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32WidenMadd at hexec
      revert hexec; match stk with
      | [] | [_] | [_,_] => simp
      | _::_::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32WrappingMadd =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32WrappingMadd at hexec
      revert hexec; match stk with
      | [] | [_] | [_,_] => simp
      | _::_::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32DivMod =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32DivMod at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32Div =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Div at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32Mod =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Mod at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32Not =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Not at hexec
      revert hexec; cases stk with
      | nil => simp
      | cons a rest => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32Popcnt =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Popcnt at hexec
      revert hexec; cases stk with
      | nil => simp
      | cons a rest => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32Clz =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Clz at hexec
      revert hexec; cases stk with
      | nil => simp
      | cons a rest => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32Ctz =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Ctz at hexec
      revert hexec; cases stk with
      | nil => simp
      | cons a rest => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32Clo =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Clo at hexec
      revert hexec; cases stk with
      | nil => simp
      | cons a rest => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32Cto =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Cto at hexec
      revert hexec; cases stk with
      | nil => simp
      | cons a rest => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32Shl =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Shl at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32Shr =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Shr at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32Rotl =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Rotl at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32Rotr =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32Rotr at hexec
      revert hexec; match stk with
      | [] | [_] => simp
      | _::_::_ => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32ShlImm =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32ShlImm at hexec
      revert hexec; cases stk with
      | nil => simp
      | cons a rest => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32ShrImm =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32ShrImm at hexec
      revert hexec; cases stk with
      | nil => simp
      | cons a rest => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32RotlImm =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32RotlImm at hexec
      revert hexec; cases stk with
      | nil => simp
      | cons a rest => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
    | u32RotrImm =>
      simp only [MidenLean.execInstruction] at hexec; unfold execU32RotrImm at hexec
      revert hexec; cases stk with
      | nil => simp
      | cons a rest => intro hexec; simp [MidenState.withStack] at hexec; extract_and_close
  -- Phase 2: use preservation to rewrite cs₁', then build transfer witness
  have hcs₁ : cs₁' = ⟨cs₁'.stack, m₁, f₁, a₁⟩ := by cases cs₁'; simp_all
  rw [hcs₁] at hexec₁ ⊢
  refine ⟨⟨cs₁'.stack, m₂, f₂, a₂⟩, ?_, rfl, rfl, rfl, rfl⟩
  cases i with
  | cswap | cswapw | cdrop | cdropw | u32Test | u32TestW
  | memLoad | memStore | memLoadwBe | memStorewBe | memLoadwLe | memStorewLe
  | advLoadW =>
    simp [Instruction.isStackPure] at hpure
  | memLoadImm | memStoreImm | memLoadwBeImm | memStorewBeImm
  | memLoadwLeImm | memStorewLeImm
  | locLoad | locStore | locLoadwBe | locLoadwLe | locStorewBe | locStorewLe | locaddr
  | advPush | exec =>
    simp [Instruction.isStackPure] at hpure
  | nop | emitImm =>
    simp [MidenLean.execInstruction] at hexec₁ ⊢; exact hexec₁
  | emit =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execEmit at hexec₁ ⊢
    revert hexec₁; cases stk <;> simp
  | drop =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execDrop at hexec₁ ⊢
    revert hexec₁; cases stk <;> simp [MidenState.withStack]
  | dropw =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execDropw at hexec₁ ⊢
    revert hexec₁; match stk with
    | [] | [_] | [_,_] | [_,_,_] => simp
    | _::_::_::_::_ => simp [MidenState.withStack]
  | padw =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execPadw at hexec₁ ⊢
    revert hexec₁; simp [MidenState.withStack]
  | push =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execPush at hexec₁ ⊢
    revert hexec₁; simp [MidenState.withStack]
  | pushList =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execPushList at hexec₁ ⊢
    revert hexec₁; simp [MidenState.withStack]
  | dup =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execDup at hexec₁ ⊢
    revert hexec₁; cases stk with
    | nil => simp
    | cons head tail =>
      simp only [MidenState.withStack]
      intro h; split at h
      · simp only [Option.some.injEq, MidenState.mk.injEq] at h; rw [h.1]
      · simp at h
  | dupw n =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execDupw at hexec₁ ⊢
    revert hexec₁
    fin_cases n <;> simp only [] <;> (
      intro h; split at h
      · simp only [MidenState.withStack, Option.some.injEq, MidenState.mk.injEq] at h
        simp only [MidenState.withStack]; rw [h.1]
      · simp at h)
  | swap =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execSwap at hexec₁ ⊢
    revert hexec₁; cases stk with
    | nil => simp
    | cons a rest =>
      simp only [MidenState.withStack]
      intro h; split at h
      · split
        · simp only [Option.some.injEq, MidenState.mk.injEq] at h ⊢
          exact ⟨by rw [h.1], trivial, trivial, trivial⟩
        · contradiction
      · split
        · contradiction
        · split at h
          · simp only [Option.some.injEq, MidenState.mk.injEq] at h ⊢
            exact ⟨h.1, trivial, trivial, trivial⟩
          · simp at h
  | swapw n =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execSwapw at hexec₁ ⊢
    revert hexec₁; intro h
    split at h
    · split
      · simp only [Option.some.injEq, MidenState.mk.injEq] at h ⊢
        exact ⟨by rw [h.1], trivial, trivial, trivial⟩
      · contradiction
    · split
      · contradiction
      · set_option linter.unusedSimpArgs false in
        simp only [MidenState.stack] at h ⊢
        split at h
        · simp only [MidenState.withStack, Option.some.injEq, MidenState.mk.injEq] at h ⊢
          exact ⟨by rw [h.1], trivial, trivial, trivial⟩
        · simp at h
  | swapdw =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execSwapdw at hexec₁ ⊢
    revert hexec₁; match stk with
    | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_]
    | [_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_]
    | [_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_]
    | [_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => simp
    | _::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_ => simp [MidenState.withStack]
  | movup =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execMovup removeNth at hexec₁ ⊢
    simp only [MidenState.withStack] at *
    revert hexec₁; intro h
    split at h
    · simp at h
    · split
      · contradiction
      · split at h
        · simp only [Option.some.injEq, MidenState.mk.injEq] at h ⊢
          exact ⟨h.1, trivial, trivial, trivial⟩
        · simp at h
  | movdn =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execMovdn at hexec₁ ⊢
    simp only [MidenState.withStack] at *
    revert hexec₁; intro h
    split at h
    · simp at h
    · split
      · contradiction
      · cases stk with
        | nil => simp at h
        | cons top rest =>
          simp only [Option.some.injEq, MidenState.mk.injEq] at h ⊢
          exact ⟨by rw [h.1], trivial, trivial, trivial⟩
  | movupw =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execMovupw at hexec₁ ⊢
    revert hexec₁; simp [MidenState.withStack]
  | movdnw =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execMovdnw at hexec₁ ⊢
    revert hexec₁; simp [MidenState.withStack]
  | reversew =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execReversew at hexec₁ ⊢
    revert hexec₁; match stk with
    | [] | [_] | [_,_] | [_,_,_] => simp
    | _::_::_::_::_ => simp [MidenState.withStack]
  | eqw =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execEqw at hexec₁ ⊢
    revert hexec₁; match stk with
    | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] | [_,_,_,_,_,_,_] => simp
    | _::_::_::_::_::_::_::_::_ => simp [MidenState.withStack]
  | add =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execAdd at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | sub =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execSub at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | mul =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execMul at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | eq =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execEq at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | neq =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execNeq at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | lt =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execLt at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | lte =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execLte at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | gt =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execGt at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | gte =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execGte at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | neg =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execNeg at hexec₁ ⊢
    revert hexec₁; cases stk <;> simp [MidenState.withStack]
  | incr =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execIncr at hexec₁ ⊢
    revert hexec₁; cases stk <;> simp [MidenState.withStack]
  | isOdd =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execIsOdd at hexec₁ ⊢
    revert hexec₁; cases stk <;> simp [MidenState.withStack]
  | addImm =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execAddImm at hexec₁ ⊢
    revert hexec₁; cases stk <;> simp [MidenState.withStack]
  | subImm =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execSubImm at hexec₁ ⊢
    revert hexec₁; cases stk <;> simp [MidenState.withStack]
  | mulImm =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execMulImm at hexec₁ ⊢
    revert hexec₁; cases stk <;> simp [MidenState.withStack]
  | eqImm =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execEqImm at hexec₁ ⊢
    revert hexec₁; cases stk <;> simp [MidenState.withStack]
  | neqImm =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execNeqImm at hexec₁ ⊢
    revert hexec₁; cases stk <;> simp [MidenState.withStack]
  | assert =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execAssert at hexec₁ ⊢
    revert hexec₁; cases stk with | nil => simp | cons a rest => simp [MidenState.withStack]
  | assertWithError =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execAssert at hexec₁ ⊢
    revert hexec₁; cases stk with | nil => simp | cons a rest => simp [MidenState.withStack]
  | assertz =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execAssertz at hexec₁ ⊢
    revert hexec₁; cases stk with | nil => simp | cons a rest => simp [MidenState.withStack]
  | assertzWithError =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execAssertz at hexec₁ ⊢
    revert hexec₁; cases stk with | nil => simp | cons a rest => simp [MidenState.withStack]
  | assertEq | assertEqWithError =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execAssertEq at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | assertEqw =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execAssertEqw at hexec₁ ⊢
    revert hexec₁; match stk with
    | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] | [_,_,_,_,_,_,_] => simp
    | _::_::_::_::_::_::_::_::_ => simp [MidenState.withStack]
  | div =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execDiv at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | divImm =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execDivImm at hexec₁ ⊢
    revert hexec₁; cases stk with | nil => simp | cons a rest => simp [MidenState.withStack]
  | inv =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execInv at hexec₁ ⊢
    revert hexec₁; cases stk with | nil => simp | cons a rest => simp [MidenState.withStack]
  | pow2 =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execPow2 at hexec₁ ⊢
    revert hexec₁; cases stk with | nil => simp | cons a rest => simp [MidenState.withStack]
  | and =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execAnd at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | or =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execOr at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | xor =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execXor at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | not =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execNot at hexec₁ ⊢
    revert hexec₁; cases stk with | nil => simp | cons a rest => simp [MidenState.withStack]
  | u32Assert =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Assert at hexec₁ ⊢
    revert hexec₁; cases stk with | nil => simp | cons a rest => simp
  | u32Assert2 =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Assert2 at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp
  | u32AssertW =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32AssertW at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] | [_,_] | [_,_,_] => simp | _::_::_::_::_ => simp
  | u32Cast =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Cast at hexec₁ ⊢
    revert hexec₁; cases stk <;> simp [MidenState.withStack]
  | u32Split =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Split at hexec₁ ⊢
    revert hexec₁; cases stk <;> simp [MidenState.withStack]
  | u32WidenAdd =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32WidenAdd at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32OverflowAdd =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32OverflowAdd at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32WrappingAdd =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32WrappingAdd at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32OverflowSub =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32OverflowSub at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32WrappingSub =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32WrappingSub at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32WidenMul =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32WidenMul at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32WrappingMul =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32WrappingMul at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32And =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32And at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32Or =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Or at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32Xor =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Xor at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32Lt =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Lt at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32Lte =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Lte at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32Gt =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Gt at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32Gte =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Gte at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32Min =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Min at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32Max =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Max at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32WidenAdd3 =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32WidenAdd3 at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] | [_,_] => simp | _::_::_::_ => simp [MidenState.withStack]
  | u32OverflowAdd3 =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32OverflowAdd3 at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] | [_,_] => simp | _::_::_::_ => simp [MidenState.withStack]
  | u32WrappingAdd3 =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32WrappingAdd3 at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] | [_,_] => simp | _::_::_::_ => simp [MidenState.withStack]
  | u32WidenMadd =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32WidenMadd at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] | [_,_] => simp | _::_::_::_ => simp [MidenState.withStack]
  | u32WrappingMadd =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32WrappingMadd at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] | [_,_] => simp | _::_::_::_ => simp [MidenState.withStack]
  | u32DivMod =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32DivMod at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32Div =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Div at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32Mod =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Mod at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32Not =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Not at hexec₁ ⊢
    revert hexec₁; cases stk with | nil => simp | cons a rest => simp [MidenState.withStack]
  | u32Popcnt =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Popcnt at hexec₁ ⊢
    revert hexec₁; cases stk with | nil => simp | cons a rest => simp [MidenState.withStack]
  | u32Clz =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Clz at hexec₁ ⊢
    revert hexec₁; cases stk with | nil => simp | cons a rest => simp [MidenState.withStack]
  | u32Ctz =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Ctz at hexec₁ ⊢
    revert hexec₁; cases stk with | nil => simp | cons a rest => simp [MidenState.withStack]
  | u32Clo =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Clo at hexec₁ ⊢
    revert hexec₁; cases stk with | nil => simp | cons a rest => simp [MidenState.withStack]
  | u32Cto =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Cto at hexec₁ ⊢
    revert hexec₁; cases stk with | nil => simp | cons a rest => simp [MidenState.withStack]
  | u32Shl =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Shl at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32Shr =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Shr at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32Rotl =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Rotl at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32Rotr =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32Rotr at hexec₁ ⊢
    revert hexec₁; match stk with | [] | [_] => simp | _::_::_ => simp [MidenState.withStack]
  | u32ShlImm =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32ShlImm at hexec₁ ⊢
    revert hexec₁; cases stk with | nil => simp | cons a rest => simp [MidenState.withStack]
  | u32ShrImm =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32ShrImm at hexec₁ ⊢
    revert hexec₁; cases stk with | nil => simp | cons a rest => simp [MidenState.withStack]
  | u32RotlImm =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32RotlImm at hexec₁ ⊢
    revert hexec₁; cases stk with | nil => simp | cons a rest => simp [MidenState.withStack]
  | u32RotrImm =>
    simp only [MidenLean.execInstruction] at hexec₁ ⊢; unfold execU32RotrImm at hexec₁ ⊢
    revert hexec₁; cases stk with | nil => simp | cons a rest => simp [MidenState.withStack]

-- ============================================================================
-- Block-level independence + preservation
-- ============================================================================

set_option maxHeartbeats 800000 in
/-- For a block of stack-pure instructions, concrete execution from any state
    with the same stack gives a result with the same output stack, preserving
    the other state's memory, frames, and advice. -/
private theorem concreteExecBlock_stackPure
    (insts : List Instruction) (stk : List Felt)
    (m₁ m₂ : Nat → Felt) (f₁ f₂ : List LocalFrame) (a₁ a₂ : List Felt)
    (cs₁' : MidenState)
    (hpure : ∀ i ∈ insts, i.isStackPure)
    (hexec₁ : concreteExecBlock insts ⟨stk, m₁, f₁, a₁⟩ = some cs₁') :
    ∃ cs₂', concreteExecBlock insts ⟨stk, m₂, f₂, a₂⟩ = some cs₂' ∧
             cs₂'.stack = cs₁'.stack ∧
             cs₂'.memory = m₂ ∧ cs₂'.frames = f₂ ∧ cs₂'.advice = a₂ := by
  induction insts generalizing stk m₁ m₂ f₁ f₂ a₁ a₂ cs₁' with
  | nil =>
    simp [concreteExecBlock, List.foldlM] at hexec₁
    subst hexec₁
    exact ⟨⟨stk, m₂, f₂, a₂⟩, rfl, rfl, rfl, rfl, rfl⟩
  | cons i rest ih =>
    unfold concreteExecBlock at hexec₁ ⊢
    simp only [List.foldlM, bind, Bind.bind, Option.bind] at hexec₁ ⊢
    have hipure : i.isStackPure := hpure i (List.mem_cons_self ..)
    have hrestpure : ∀ j ∈ rest, j.isStackPure :=
      fun j hj => hpure j (List.mem_cons_of_mem _ hj)
    match hstep₁ : MidenLean.execInstruction ⟨stk, m₁, f₁, a₁⟩ i with
    | none => simp [hstep₁] at hexec₁
    | some cs₁_mid =>
      simp only [hstep₁] at hexec₁
      -- Get transfer to second state
      obtain ⟨cs₂_mid, hstep₂, hstk_eq, hm₂, hf₂, ha₂⟩ :=
        concreteExecInstruction_stackPure i stk m₁ m₂ f₁ f₂ a₁ a₂ cs₁_mid hipure hstep₁
      simp only [hstep₂]
      -- Get preservation on first state (apply with m₂=m₁ etc.)
      obtain ⟨cs₁_self, hstep_self, _, hm₁_eq, hf₁_eq, ha₁_eq⟩ :=
        concreteExecInstruction_stackPure i stk m₁ m₁ f₁ f₁ a₁ a₁ cs₁_mid hipure hstep₁
      -- cs₁_mid preserves non-stack state
      have heq : some cs₁_self = some cs₁_mid := by rw [← hstep_self, ← hstep₁]
      have : cs₁_mid = cs₁_self := by simpa using heq.symm
      rw [this] at hexec₁ hstk_eq
      have hcs₁ : cs₁_self = ⟨cs₁_self.stack, m₁, f₁, a₁⟩ := by
        cases cs₁_self; simp_all
      have hcs₂ : cs₂_mid = ⟨cs₁_self.stack, m₂, f₂, a₂⟩ := by
        cases cs₂_mid; simp only [MidenState.mk.injEq] at hstk_eq hm₂ hf₂ ha₂ ⊢
        exact ⟨hstk_eq, hm₂, hf₂, ha₂⟩
      rw [hcs₁] at hexec₁
      rw [hcs₂]
      exact ih cs₁_self.stack m₁ m₂ f₁ f₂ a₁ a₂ cs₁' hrestpure hexec₁

/-- Combined reflection for basic blocks. If the symbolic executor succeeds,
    all preconditions hold, and every instruction is stack-pure, then `exec`
    produces the expected stack result with preserved non-stack state. -/
theorem reflect_basic_block
    (insts : List Instruction) (proc : Procedure) (fuel : Nat)
    (stack : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) (adv : List Felt)
    (n : Nat) (rest : List Felt)
    (σ : Assignment)
    (result : BlockResult)
    (hbody : proc.body = insts.map Op.inst)
    (hlocals : proc.numLocals = 0)
    (hfuel : fuel > 0)
    (hstack : stack = (State.ofInputs n).stack.map (Expr.eval σ) ++ rest)
    (hresult : execBlock insts (State.ofInputs n) = some result)
    (hpreconds : ∀ p ∈ result.preconditions, p.holds σ)
    (hpure : ∀ i ∈ insts, i.isStackPure) :
    MidenLean.exec fuel ⟨stack, mem, frames, adv⟩ proc =
    some ⟨result.state.stack.map (Expr.eval σ) ++ rest, mem, frames, adv⟩ := by
  rw [exec_basic_block fuel ⟨stack, mem, frames, adv⟩ insts proc hbody hlocals hfuel]
  have hmodels : (State.ofInputs n).models ⟨stack, fun _ => 0, [], []⟩ σ rest := by
    unfold State.models State.ofInputs
    exact ⟨hstack, fun addr => by simp [Expr.eval], rfl, by simp⟩
  obtain ⟨cs_d', hconc_d, hmod_d⟩ :=
    execBlock_sound insts (State.ofInputs n) ⟨stack, fun _ => 0, [], []⟩ σ rest result
      hmodels hresult hpreconds
  obtain ⟨cs_r', hconc_r, hstk_r, hmem_r, hframes_r, hadv_r⟩ :=
    concreteExecBlock_stackPure insts stack (fun _ => 0) mem [] frames [] adv cs_d'
      hpure hconc_d
  rw [hconc_r]
  unfold State.models at hmod_d
  obtain ⟨hstk_d, _, _, _⟩ := hmod_d
  congr 1
  cases cs_r'
  simp only [MidenState.mk.injEq] at hstk_r hmem_r hframes_r hadv_r ⊢
  exact ⟨by rw [hstk_r, hstk_d], hmem_r, hframes_r, hadv_r⟩

end MidenLean.Symbolic.Reflect
