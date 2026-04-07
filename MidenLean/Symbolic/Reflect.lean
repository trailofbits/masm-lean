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

/-- Strip leading ∧ conjuncts from `hconc`, subst the trailing equation, close with rfl. -/
syntax "extract_and_close" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| extract_and_close) => `(tactic|
    first
    | (obtain ⟨_, _, _, _, _, hconc⟩ := hconc; subst hconc; exact ⟨rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, _, _, hconc⟩ := hconc; subst hconc; exact ⟨rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, _, hconc⟩ := hconc; subst hconc; exact ⟨rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, hconc⟩ := hconc; subst hconc; exact ⟨rfl, rfl, rfl⟩)
    | (obtain ⟨_, hconc⟩ := hconc; subst hconc; exact ⟨rfl, rfl, rfl⟩)
    | (subst hconc; exact ⟨rfl, rfl, rfl⟩))

namespace MidenLean.Symbolic.Reflect

open MidenLean
open MidenLean.Symbolic

-- Helpers

/-- Felt equality comparison is boolean: the result is 0 or 1. -/
private theorem felt_eq_isBool (a b : Felt) :
    (if a == b then (1 : Felt) else 0) = 0 ∨
    (if a == b then (1 : Felt) else 0) = 1 := by
  by_cases h : a == b <;> simp [h]

/-- Helper: extracting preservation from a withStack result. -/
private theorem withStack_preserves (cs : MidenState) (stk : List Felt) :
    (cs.withStack stk).memory = cs.memory ∧
    (cs.withStack stk).frames = cs.frames ∧
    (cs.withStack stk).advice = cs.advice :=
  ⟨rfl, rfl, rfl⟩

set_option maxHeartbeats 6400000 in
/-- Every instruction for which `execInstruction` succeeds is stack-only:
    `execInstruction` preserves memory, frames, and advice. -/
private theorem execInstruction_preserves_of_symbolic
    (i : Instruction) (cs cs' : MidenState) (ss : State)
    (hconc : MidenLean.execInstruction cs i = some cs')
    (hsymb : ∃ ss' pc, execInstruction ss i = some (ss', pc)) :
    cs'.memory = cs.memory ∧ cs'.frames = cs.frames ∧ cs'.advice = cs.advice := by
  obtain ⟨ss', pc, hsymb'⟩ := hsymb
  cases i with
  -- Instructions where execInstruction returns none: contradiction with hsymb'
  | cswap | cswapw | cdrop | cdropw | u32Test | u32TestW
  | memLoad | memLoadImm | memStore | memStoreImm
  | memLoadwBe | memLoadwBeImm | memStorewBe | memStorewBeImm
  | memLoadwLe | memLoadwLeImm | memStorewLe | memStorewLeImm
  | locLoad | locStore | locLoadwBe | locLoadwLe | locStorewBe | locStorewLe | locaddr
  | advPush | advLoadW | emit | emitImm | exec =>
    simp [execInstruction] at hsymb'
  -- nop: identity
  | nop => simp [MidenLean.execInstruction] at hconc; subst hconc; exact ⟨rfl, rfl, rfl⟩
  -- Unguarded stack ops that directly return some (cs.withStack ...)
  | drop =>
    simp only [MidenLean.execInstruction] at hconc; unfold execDrop at hconc
    revert hconc; cases cs.stack <;> simp [MidenState.withStack]
    intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | dropw =>
    simp only [MidenLean.execInstruction] at hconc; unfold execDropw at hconc
    revert hconc; match cs.stack with
    | [] | [_] | [_,_] | [_,_,_] => simp
    | _::_::_::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | padw =>
    simp only [MidenLean.execInstruction] at hconc; unfold execPadw at hconc
    simp [MidenState.withStack] at hconc; subst hconc; exact ⟨rfl, rfl, rfl⟩
  | push =>
    simp only [MidenLean.execInstruction] at hconc; unfold execPush at hconc
    simp [MidenState.withStack] at hconc; subst hconc; exact ⟨rfl, rfl, rfl⟩
  | pushList =>
    simp only [MidenLean.execInstruction] at hconc; unfold execPushList at hconc
    simp [MidenState.withStack] at hconc; subst hconc; exact ⟨rfl, rfl, rfl⟩
  | dup =>
    simp only [MidenLean.execInstruction] at hconc; unfold execDup at hconc
    split at hconc <;> simp [MidenState.withStack] at hconc
    subst hconc; exact ⟨rfl, rfl, rfl⟩
  | dupw n =>
    simp only [MidenLean.execInstruction] at hconc; unfold execDupw at hconc
    fin_cases n <;> (
      simp only [] at hconc
      split at hconc
      · simp only [MidenState.withStack, Option.some.injEq] at hconc
        subst hconc; exact ⟨rfl, rfl, rfl⟩
      · simp at hconc)
  | swap =>
    simp only [MidenLean.execInstruction] at hconc; unfold execSwap at hconc
    split at hconc
    · simp at hconc; subst hconc; exact ⟨rfl, rfl, rfl⟩
    · split at hconc <;> simp [MidenState.withStack] at hconc
      subst hconc; exact ⟨rfl, rfl, rfl⟩
  | swapw n =>
    simp only [MidenLean.execInstruction] at hconc; unfold execSwapw at hconc
    fin_cases n <;> simp only [] at hconc <;> simp at hconc <;> (
      first
      | (subst hconc; exact ⟨rfl, rfl, rfl⟩)
      | (split at hconc
         · simp only [MidenState.withStack, Option.some.injEq] at hconc
           subst hconc; exact ⟨rfl, rfl, rfl⟩
         · simp at hconc))
  | swapdw =>
    simp only [MidenLean.execInstruction] at hconc; unfold execSwapdw at hconc
    revert hconc; match cs.stack with
    | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_]
    | [_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_]
    | [_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_]
    | [_,_,_,_,_,_,_,_,_,_,_,_,_,_] | [_,_,_,_,_,_,_,_,_,_,_,_,_,_,_] => simp
    | _::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_::_ =>
      simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | movup =>
    simp only [MidenLean.execInstruction] at hconc; unfold execMovup removeNth at hconc
    split at hconc
    · simp at hconc
    · split at hconc <;> simp [MidenState.withStack] at hconc
      subst hconc; exact ⟨rfl, rfl, rfl⟩
  | movdn =>
    simp only [MidenLean.execInstruction] at hconc; unfold execMovdn at hconc
    split at hconc
    · simp at hconc
    · revert hconc; cases cs.stack with
      | nil => simp
      | cons top rest =>
        simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | movupw =>
    simp only [MidenLean.execInstruction] at hconc; unfold execMovupw at hconc
    simp [MidenState.withStack] at hconc; extract_and_close
  | movdnw =>
    simp only [MidenLean.execInstruction] at hconc; unfold execMovdnw at hconc
    simp [MidenState.withStack] at hconc; extract_and_close
  | reversew =>
    simp only [MidenLean.execInstruction] at hconc; unfold execReversew at hconc
    revert hconc; match cs.stack with
    | [] | [_] | [_,_] | [_,_,_] => simp
    | _::_::_::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | eqw =>
    simp only [MidenLean.execInstruction] at hconc; unfold execEqw at hconc
    revert hconc; match cs.stack with
    | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] | [_,_,_,_,_,_,_] => simp
    | _::_::_::_::_::_::_::_::_ =>
      simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  -- Binary field ops (no guards, direct withStack)
  | add =>
    simp only [MidenLean.execInstruction] at hconc; unfold execAdd at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | sub =>
    simp only [MidenLean.execInstruction] at hconc; unfold execSub at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | mul =>
    simp only [MidenLean.execInstruction] at hconc; unfold execMul at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | eq =>
    simp only [MidenLean.execInstruction] at hconc; unfold execEq at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | neq =>
    simp only [MidenLean.execInstruction] at hconc; unfold execNeq at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | lt =>
    simp only [MidenLean.execInstruction] at hconc; unfold execLt at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | lte =>
    simp only [MidenLean.execInstruction] at hconc; unfold execLte at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | gt =>
    simp only [MidenLean.execInstruction] at hconc; unfold execGt at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | gte =>
    simp only [MidenLean.execInstruction] at hconc; unfold execGte at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ => simp [MidenState.withStack]; intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  -- Unary field ops (no guards)
  | neg =>
    simp only [MidenLean.execInstruction] at hconc; unfold execNeg at hconc
    revert hconc; cases cs.stack <;> simp [MidenState.withStack]
    intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | incr =>
    simp only [MidenLean.execInstruction] at hconc; unfold execIncr at hconc
    revert hconc; cases cs.stack <;> simp [MidenState.withStack]
    intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | isOdd =>
    simp only [MidenLean.execInstruction] at hconc; unfold execIsOdd at hconc
    revert hconc; cases cs.stack <;> simp [MidenState.withStack]
    intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  -- Imm variants (unary, no guards)
  | addImm =>
    simp only [MidenLean.execInstruction] at hconc; unfold execAddImm at hconc
    revert hconc; cases cs.stack <;> simp [MidenState.withStack]
    intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | subImm =>
    simp only [MidenLean.execInstruction] at hconc; unfold execSubImm at hconc
    revert hconc; cases cs.stack <;> simp [MidenState.withStack]
    intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | mulImm =>
    simp only [MidenLean.execInstruction] at hconc; unfold execMulImm at hconc
    revert hconc; cases cs.stack <;> simp [MidenState.withStack]
    intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | eqImm =>
    simp only [MidenLean.execInstruction] at hconc; unfold execEqImm at hconc
    revert hconc; cases cs.stack <;> simp [MidenState.withStack]
    intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | neqImm =>
    simp only [MidenLean.execInstruction] at hconc; unfold execNeqImm at hconc
    revert hconc; cases cs.stack <;> simp [MidenState.withStack]
    intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  -- Guarded field ops (if guard then some ... else none)
  -- After simp, hconc becomes a conjunction: guard_prop ∧ expr = cs'
  -- We destructure the last conjunct to get the equation for cs'.
  | assert =>
    simp only [MidenLean.execInstruction] at hconc; unfold execAssert at hconc
    revert hconc; cases cs.stack with
    | nil => simp
    | cons a rest =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | assertWithError =>
    simp only [MidenLean.execInstruction] at hconc; unfold execAssert at hconc
    revert hconc; cases cs.stack with
    | nil => simp
    | cons a rest =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | assertz =>
    simp only [MidenLean.execInstruction] at hconc; unfold execAssertz at hconc
    revert hconc; cases cs.stack with
    | nil => simp
    | cons a rest =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | assertzWithError =>
    simp only [MidenLean.execInstruction] at hconc; unfold execAssertz at hconc
    revert hconc; cases cs.stack with
    | nil => simp
    | cons a rest =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | assertEq =>
    simp only [MidenLean.execInstruction] at hconc; unfold execAssertEq at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _ :: _ :: _ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | assertEqWithError =>
    simp only [MidenLean.execInstruction] at hconc; unfold execAssertEq at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _ :: _ :: _ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | assertEqw =>
    simp only [MidenLean.execInstruction] at hconc; unfold execAssertEqw at hconc
    revert hconc; match cs.stack with
    | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] | [_,_,_,_,_,_,_] => simp
    | _::_::_::_::_::_::_::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | div =>
    simp only [MidenLean.execInstruction] at hconc; unfold execDiv at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | divImm =>
    simp only [MidenLean.execInstruction] at hconc; unfold execDivImm at hconc
    revert hconc; cases cs.stack with
    | nil => simp
    | cons a rest =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | inv =>
    simp only [MidenLean.execInstruction] at hconc; unfold execInv at hconc
    revert hconc; cases cs.stack with
    | nil => simp
    | cons a rest =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | pow2 =>
    simp only [MidenLean.execInstruction] at hconc; unfold execPow2 at hconc
    revert hconc; cases cs.stack with
    | nil => simp
    | cons a rest =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  -- Boolean ops (guarded)
  | and =>
    simp only [MidenLean.execInstruction] at hconc; unfold execAnd at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | or =>
    simp only [MidenLean.execInstruction] at hconc; unfold execOr at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | xor =>
    simp only [MidenLean.execInstruction] at hconc; unfold execXor at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | not =>
    simp only [MidenLean.execInstruction] at hconc; unfold execNot at hconc
    revert hconc; cases cs.stack with
    | nil => simp
    | cons a rest =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  -- U32 assertions (guarded, identity on stack - return `some cs` not `some (cs.withStack ...)`)
  | u32Assert =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Assert at hconc
    revert hconc; cases cs.stack with
    | nil => simp
    | cons a rest =>
      intro hconc; simp at hconc; extract_and_close
  | u32Assert2 =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Assert2 at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp at hconc; extract_and_close
  | u32AssertW =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32AssertW at hconc
    revert hconc; match cs.stack with
    | [] | [_] | [_,_] | [_,_,_] => simp
    | _::_::_::_::_ =>
      intro hconc; simp at hconc; extract_and_close
  -- U32 conversions (no guard)
  | u32Cast =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Cast at hconc
    revert hconc; cases cs.stack <;> simp [MidenState.withStack]
    intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  | u32Split =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Split at hconc
    revert hconc; cases cs.stack <;> simp [MidenState.withStack]
    intro h; subst h; exact ⟨rfl, rfl, rfl⟩
  -- U32 binary arithmetic/bitwise/comparison ops (isU32 guard)
  | u32WidenAdd =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32WidenAdd at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32OverflowAdd =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32OverflowAdd at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32WrappingAdd =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32WrappingAdd at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32OverflowSub =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32OverflowSub at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32WrappingSub =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32WrappingSub at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32WidenMul =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32WidenMul at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32WrappingMul =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32WrappingMul at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32And =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32And at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32Or =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Or at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32Xor =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Xor at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32Lt =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Lt at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32Lte =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Lte at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32Gt =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Gt at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32Gte =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Gte at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32Min =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Min at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32Max =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Max at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  -- u32 3-ary ops
  | u32WidenAdd3 =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32WidenAdd3 at hconc
    revert hconc; match cs.stack with
    | [] | [_] | [_,_] => simp
    | _::_::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32OverflowAdd3 =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32OverflowAdd3 at hconc
    revert hconc; match cs.stack with
    | [] | [_] | [_,_] => simp
    | _::_::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32WrappingAdd3 =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32WrappingAdd3 at hconc
    revert hconc; match cs.stack with
    | [] | [_] | [_,_] => simp
    | _::_::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32WidenMadd =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32WidenMadd at hconc
    revert hconc; match cs.stack with
    | [] | [_] | [_,_] => simp
    | _::_::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32WrappingMadd =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32WrappingMadd at hconc
    revert hconc; match cs.stack with
    | [] | [_] | [_,_] => simp
    | _::_::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  -- u32 div (two guards: isU32 + nonzero)
  | u32DivMod =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32DivMod at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32Div =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Div at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32Mod =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Mod at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  -- u32 unary ops (with isU32 guard)
  | u32Not =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Not at hconc
    revert hconc; cases cs.stack with
    | nil => simp
    | cons a rest =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32Popcnt =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Popcnt at hconc
    revert hconc; cases cs.stack with
    | nil => simp
    | cons a rest =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32Clz =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Clz at hconc
    revert hconc; cases cs.stack with
    | nil => simp
    | cons a rest =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32Ctz =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Ctz at hconc
    revert hconc; cases cs.stack with
    | nil => simp
    | cons a rest =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32Clo =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Clo at hconc
    revert hconc; cases cs.stack with
    | nil => simp
    | cons a rest =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32Cto =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Cto at hconc
    revert hconc; cases cs.stack with
    | nil => simp
    | cons a rest =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  -- u32 shift/rotate (binary with two guards: isU32 + valLeq)
  | u32Shl =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Shl at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32Shr =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Shr at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32Rotl =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Rotl at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32Rotr =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32Rotr at hconc
    revert hconc; match cs.stack with
    | [] | [_] => simp
    | _::_::_ =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  -- u32 shift/rotate imm (one guard: isU32)
  | u32ShlImm =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32ShlImm at hconc
    revert hconc; cases cs.stack with
    | nil => simp
    | cons a rest =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32ShrImm =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32ShrImm at hconc
    revert hconc; cases cs.stack with
    | nil => simp
    | cons a rest =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32RotlImm =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32RotlImm at hconc
    revert hconc; cases cs.stack with
    | nil => simp
    | cons a rest =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close
  | u32RotrImm =>
    simp only [MidenLean.execInstruction] at hconc; unfold execU32RotrImm at hconc
    revert hconc; cases cs.stack with
    | nil => simp
    | cons a rest =>
      intro hconc; simp [MidenState.withStack] at hconc; extract_and_close

/-- If `execBlockStep` succeeds for an instruction where `execInstruction` also
    succeeds symbolically, the concrete result preserves memory/frames/advice. -/
private theorem foldlM_preserves
    (insts : List Instruction) (cs cs' : MidenState)
    (ss : State) (acc : List Precondition)
    (hconc : insts.foldlM (fun s i => MidenLean.execInstruction s i) cs = some cs')
    (hsymb : ∃ ss' acc', insts.foldlM execBlockStep (ss, acc) = some (ss', acc')) :
    cs'.memory = cs.memory ∧ cs'.frames = cs.frames ∧ cs'.advice = cs.advice := by
  induction insts generalizing cs ss acc with
  | nil =>
    simp [List.foldlM] at hconc; subst hconc; exact ⟨rfl, rfl, rfl⟩
  | cons i rest ih =>
    simp only [List.foldlM, bind, Bind.bind, Option.bind] at hconc hsymb
    obtain ⟨ss_final, acc_final, hsymb_fold⟩ := hsymb
    unfold execBlockStep at hsymb_fold
    match hsi : execInstruction ss i with
    | none => simp [hsi] at hsymb_fold
    | some (ss1, pc1) =>
      simp only [hsi] at hsymb_fold
      match hci : MidenLean.execInstruction cs i with
      | none => simp [hci] at hconc
      | some cs1 =>
        simp only [hci] at hconc
        have hpres := execInstruction_preserves_of_symbolic i cs cs1 ss hci ⟨ss1, pc1, hsi⟩
        have hrest := ih cs1 ss1 (pc1.reverse ++ acc) hconc ⟨ss_final, acc_final, hsymb_fold⟩
        exact ⟨hrest.1.trans hpres.1, hrest.2.1.trans hpres.2.1, hrest.2.2.trans hpres.2.2⟩

/-- concreteExecBlock preserves memory, frames, and advice when the symbolic
    executor succeeds (guaranteeing all instructions are stack-only). -/
theorem concreteExecBlock_preserves
    (insts : List Instruction) (cs cs' : MidenState) (ss : State)
    (hconc : concreteExecBlock insts cs = some cs')
    (hsymb : ∃ r, execBlock insts ss = some r) :
    cs'.memory = cs.memory ∧ cs'.frames = cs.frames ∧ cs'.advice = cs.advice := by
  obtain ⟨r, hr⟩ := hsymb
  unfold execBlock at hr
  match hfold : insts.foldlM execBlockStep (ss, []) with
  | none => simp [hfold] at hr
  | some (final_ss, final_preconds) =>
    unfold concreteExecBlock at hconc
    exact foldlM_preserves insts cs cs' ss [] hconc ⟨final_ss, final_preconds, hfold⟩

/-- Combined reflection for basic blocks. If the symbolic executor succeeds
    and all preconditions hold, then `exec` produces the expected stack result
    with preserved non-stack state. -/
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
    (hpreconds : ∀ p ∈ result.preconditions, p.holds σ) :
    MidenLean.exec fuel ⟨stack, mem, frames, adv⟩ proc =
    some ⟨result.state.stack.map (Expr.eval σ) ++ rest, mem, frames, adv⟩ := by
  rw [exec_basic_block fuel ⟨stack, mem, frames, adv⟩ insts proc hbody hlocals hfuel]
  obtain ⟨cs', hconc, hmod⟩ := execBlock_sound insts (State.ofInputs n)
    ⟨stack, mem, frames, adv⟩ σ rest result hstack hresult hpreconds
  rw [hconc]
  obtain ⟨hm, hf, ha⟩ := concreteExecBlock_preserves insts
    ⟨stack, mem, frames, adv⟩ cs' (State.ofInputs n) hconc ⟨result, hresult⟩
  unfold State.models at hmod
  congr 1; cases cs'; simp_all

end MidenLean.Symbolic.Reflect
