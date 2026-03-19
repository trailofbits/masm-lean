import MidenLean.Semantics

/-! # Equation lemmas for execInstruction

Each lemma reduces `execInstruction s .foo` to `execFoo s`
in O(1) heartbeats, avoiding the O(n) cost of unfolding
the full ~100-arm pattern match. Step lemmas in
StepLemmas.lean should `rw [execInstruction_foo]` instead
of `unfold execInstruction`. -/

namespace MidenLean

-- Stack manipulation
theorem execInstruction_drop (s : MidenState) :
    execInstruction s .drop = execDrop s := rfl
theorem execInstruction_dup (s : MidenState)
    (n : Fin 16) :
    execInstruction s (.dup n) = execDup n s := rfl
theorem execInstruction_swap (s : MidenState)
    (n : Fin 16) :
    execInstruction s (.swap n) = execSwap n s := rfl
theorem execInstruction_movup (s : MidenState)
    (n : Nat) :
    execInstruction s (.movup n) = execMovup n s := rfl
theorem execInstruction_movdn (s : MidenState)
    (n : Nat) :
    execInstruction s (.movdn n) = execMovdn n s := rfl
theorem execInstruction_padw (s : MidenState) :
    execInstruction s .padw = execPadw s := rfl
theorem execInstruction_dupw (s : MidenState)
    (n : Fin 4) :
    execInstruction s (.dupw n) = execDupw n s := rfl
theorem execInstruction_swapw (s : MidenState)
    (n : Fin 4) :
    execInstruction s (.swapw n) = execSwapw n s := rfl
theorem execInstruction_swapdw
    (s : MidenState) :
    execInstruction s .swapdw = execSwapdw s := rfl
theorem execInstruction_movupw (s : MidenState)
    (n : Fin 4) :
    execInstruction s (.movupw n) = execMovupw n s :=
  rfl
theorem execInstruction_movdnw (s : MidenState)
    (n : Fin 4) :
    execInstruction s (.movdnw n) = execMovdnw n s :=
  rfl
theorem execInstruction_reversew
    (s : MidenState) :
    execInstruction s .reversew = execReversew s := rfl
theorem execInstruction_cswap
    (s : MidenState) :
    execInstruction s .cswap = execCswap s := rfl
theorem execInstruction_cswapw
    (s : MidenState) :
    execInstruction s .cswapw = execCswapw s := rfl
theorem execInstruction_cdrop
    (s : MidenState) :
    execInstruction s .cdrop = execCdrop s := rfl
theorem execInstruction_cdropw
    (s : MidenState) :
    execInstruction s .cdropw = execCdropw s := rfl
theorem execInstruction_dropw
    (s : MidenState) :
    execInstruction s .dropw = execDropw s := rfl

-- Constants
theorem execInstruction_push (s : MidenState)
    (v : Felt) :
    execInstruction s (.push v) = execPush v s := rfl
theorem execInstruction_pushList (s : MidenState)
    (vs : List Felt) :
    execInstruction s (.pushList vs) =
      execPushList vs s := rfl

-- Field arithmetic
theorem execInstruction_add (s : MidenState) :
    execInstruction s .add = execAdd s := rfl
theorem execInstruction_addImm (s : MidenState)
    (v : Felt) :
    execInstruction s (.addImm v) = execAddImm v s :=
  rfl
theorem execInstruction_sub (s : MidenState) :
    execInstruction s .sub = execSub s := rfl
theorem execInstruction_subImm (s : MidenState)
    (v : Felt) :
    execInstruction s (.subImm v) = execSubImm v s :=
  rfl
theorem execInstruction_mul (s : MidenState) :
    execInstruction s .mul = execMul s := rfl
theorem execInstruction_mulImm (s : MidenState)
    (v : Felt) :
    execInstruction s (.mulImm v) = execMulImm v s :=
  rfl
theorem execInstruction_div' (s : MidenState) :
    execInstruction s .div = execDiv s := rfl
theorem execInstruction_divImm (s : MidenState)
    (v : Felt) :
    execInstruction s (.divImm v) = execDivImm v s :=
  rfl
theorem execInstruction_neg (s : MidenState) :
    execInstruction s .neg = execNeg s := rfl
theorem execInstruction_inv (s : MidenState) :
    execInstruction s .inv = execInv s := rfl
theorem execInstruction_pow2 (s : MidenState) :
    execInstruction s .pow2 = execPow2 s := rfl
theorem execInstruction_incr (s : MidenState) :
    execInstruction s .incr = execIncr s := rfl

-- Field comparison
theorem execInstruction_eq' (s : MidenState) :
    execInstruction s .eq = execEq s := rfl
theorem execInstruction_eqImm (s : MidenState)
    (v : Felt) :
    execInstruction s (.eqImm v) = execEqImm v s := rfl
theorem execInstruction_neq (s : MidenState) :
    execInstruction s .neq = execNeq s := rfl
theorem execInstruction_neqImm (s : MidenState)
    (v : Felt) :
    execInstruction s (.neqImm v) =
      execNeqImm v s := rfl
theorem execInstruction_lt (s : MidenState) :
    execInstruction s .lt = execLt s := rfl
theorem execInstruction_lte (s : MidenState) :
    execInstruction s .lte = execLte s := rfl
theorem execInstruction_gt (s : MidenState) :
    execInstruction s .gt = execGt s := rfl
theorem execInstruction_gte (s : MidenState) :
    execInstruction s .gte = execGte s := rfl
theorem execInstruction_isOdd
    (s : MidenState) :
    execInstruction s .isOdd = execIsOdd s := rfl

-- Boolean
theorem execInstruction_and (s : MidenState) :
    execInstruction s .and = execAnd s := rfl
theorem execInstruction_or (s : MidenState) :
    execInstruction s .or = execOr s := rfl
theorem execInstruction_xor' (s : MidenState) :
    execInstruction s .xor = execXor s := rfl
theorem execInstruction_not (s : MidenState) :
    execInstruction s .not = execNot s := rfl

-- U32 assertions
theorem execInstruction_u32Assert
    (s : MidenState) :
    execInstruction s .u32Assert = execU32Assert s :=
  rfl
theorem execInstruction_u32Assert2
    (s : MidenState) :
    execInstruction s .u32Assert2 =
      execU32Assert2 s := rfl
theorem execInstruction_u32Test
    (s : MidenState) :
    execInstruction s .u32Test = execU32Test s := rfl
theorem execInstruction_u32Cast
    (s : MidenState) :
    execInstruction s .u32Cast = execU32Cast s := rfl
theorem execInstruction_u32Split
    (s : MidenState) :
    execInstruction s .u32Split = execU32Split s := rfl

-- U32 arithmetic
theorem execInstruction_u32WidenAdd
    (s : MidenState) :
    execInstruction s .u32WidenAdd =
      execU32WidenAdd s := rfl
theorem execInstruction_u32OverflowAdd
    (s : MidenState) :
    execInstruction s .u32OverflowAdd =
      execU32OverflowAdd s := rfl
theorem execInstruction_u32WrappingAdd
    (s : MidenState) :
    execInstruction s .u32WrappingAdd =
      execU32WrappingAdd s := rfl
theorem execInstruction_u32OverflowSub'
    (s : MidenState) :
    execInstruction s .u32OverflowSub =
      execU32OverflowSub s := rfl
theorem execInstruction_u32WrappingSub'
    (s : MidenState) :
    execInstruction s .u32WrappingSub =
      execU32WrappingSub s := rfl
theorem execInstruction_u32WidenMul'
    (s : MidenState) :
    execInstruction s .u32WidenMul =
      execU32WidenMul s := rfl
theorem execInstruction_u32WrappingMul
    (s : MidenState) :
    execInstruction s .u32WrappingMul =
      execU32WrappingMul s := rfl
theorem execInstruction_u32WidenMadd'
    (s : MidenState) :
    execInstruction s .u32WidenMadd =
      execU32WidenMadd s := rfl
theorem execInstruction_u32DivMod
    (s : MidenState) :
    execInstruction s .u32DivMod =
      execU32DivMod s := rfl
theorem execInstruction_u32Div
    (s : MidenState) :
    execInstruction s .u32Div = execU32Div s := rfl
theorem execInstruction_u32Mod
    (s : MidenState) :
    execInstruction s .u32Mod = execU32Mod s := rfl

-- U32 bitwise
theorem execInstruction_u32And
    (s : MidenState) :
    execInstruction s .u32And = execU32And s := rfl
theorem execInstruction_u32Or
    (s : MidenState) :
    execInstruction s .u32Or = execU32Or s := rfl
theorem execInstruction_u32Xor
    (s : MidenState) :
    execInstruction s .u32Xor = execU32Xor s := rfl
theorem execInstruction_u32Not
    (s : MidenState) :
    execInstruction s .u32Not = execU32Not s := rfl
theorem execInstruction_u32Shl
    (s : MidenState) :
    execInstruction s .u32Shl = execU32Shl s := rfl
theorem execInstruction_u32Shr
    (s : MidenState) :
    execInstruction s .u32Shr = execU32Shr s := rfl
theorem execInstruction_u32Rotl
    (s : MidenState) :
    execInstruction s .u32Rotl = execU32Rotl s := rfl
theorem execInstruction_u32Rotr
    (s : MidenState) :
    execInstruction s .u32Rotr = execU32Rotr s := rfl
theorem execInstruction_u32Popcnt
    (s : MidenState) :
    execInstruction s .u32Popcnt = execU32Popcnt s :=
  rfl
theorem execInstruction_u32Clz
    (s : MidenState) :
    execInstruction s .u32Clz = execU32Clz s := rfl
theorem execInstruction_u32Ctz
    (s : MidenState) :
    execInstruction s .u32Ctz = execU32Ctz s := rfl
theorem execInstruction_u32Clo
    (s : MidenState) :
    execInstruction s .u32Clo = execU32Clo s := rfl
theorem execInstruction_u32Cto
    (s : MidenState) :
    execInstruction s .u32Cto = execU32Cto s := rfl

-- U32 comparison
theorem execInstruction_u32Lt
    (s : MidenState) :
    execInstruction s .u32Lt = execU32Lt s := rfl
theorem execInstruction_u32Lte
    (s : MidenState) :
    execInstruction s .u32Lte = execU32Lte s := rfl
theorem execInstruction_u32Gt
    (s : MidenState) :
    execInstruction s .u32Gt = execU32Gt s := rfl
theorem execInstruction_u32Gte
    (s : MidenState) :
    execInstruction s .u32Gte = execU32Gte s := rfl
theorem execInstruction_u32Min
    (s : MidenState) :
    execInstruction s .u32Min = execU32Min s := rfl
theorem execInstruction_u32Max
    (s : MidenState) :
    execInstruction s .u32Max = execU32Max s := rfl

-- Memory
theorem execInstruction_memLoad
    (s : MidenState) :
    execInstruction s .memLoad = execMemLoad s := rfl
theorem execInstruction_memLoadImm
    (s : MidenState) (addr : Nat) :
    execInstruction s (.memLoadImm addr) =
      execMemLoadImm addr s := rfl
theorem execInstruction_memStore
    (s : MidenState) :
    execInstruction s .memStore = execMemStore s := rfl
theorem execInstruction_memStoreImm
    (s : MidenState) (addr : Nat) :
    execInstruction s (.memStoreImm addr) =
      execMemStoreImm addr s := rfl
theorem execInstruction_memStorewBe
    (s : MidenState) :
    execInstruction s .memStorewBe =
      execMemStorewBe s := rfl
theorem execInstruction_memStorewBeImm
    (s : MidenState) (addr : Nat) :
    execInstruction s (.memStorewBeImm addr) =
      execMemStorewBeImm addr s := rfl
theorem execInstruction_memStorewLe'
    (s : MidenState) :
    execInstruction s .memStorewLe =
      execMemStorewLe s := rfl
theorem execInstruction_memStorewLeImm
    (s : MidenState) (addr : Nat) :
    execInstruction s (.memStorewLeImm addr) =
      execMemStorewLeImm addr s := rfl
theorem execInstruction_memLoadwBe
    (s : MidenState) :
    execInstruction s .memLoadwBe =
      execMemLoadwBe s := rfl
theorem execInstruction_memLoadwBeImm
    (s : MidenState) (addr : Nat) :
    execInstruction s (.memLoadwBeImm addr) =
      execMemLoadwBeImm addr s := rfl
theorem execInstruction_memLoadwLe
    (s : MidenState) :
    execInstruction s .memLoadwLe =
      execMemLoadwLe s := rfl
theorem execInstruction_memLoadwLeImm
    (s : MidenState) (addr : Nat) :
    execInstruction s (.memLoadwLeImm addr) =
      execMemLoadwLeImm addr s := rfl

-- Locals
theorem execInstruction_locLoad
    (s : MidenState) (idx : Nat) :
    execInstruction s (.locLoad idx) =
      execLocLoad idx s := rfl
theorem execInstruction_locStore
    (s : MidenState) (idx : Nat) :
    execInstruction s (.locStore idx) =
      execLocStore idx s := rfl

-- Advice
theorem execInstruction_advPush'
    (n : Nat) (s : MidenState) :
    execInstruction s (.advPush n) =
      execAdvPush n s := rfl
theorem execInstruction_advLoadW
    (s : MidenState) :
    execInstruction s .advLoadW = execAdvLoadW s := rfl

-- Events
theorem execInstruction_emit
    (s : MidenState) :
    execInstruction s .emit = execEmit s := rfl
theorem execInstruction_emitImm'
    (v : Felt) (s : MidenState) :
    execInstruction s (.emitImm v) =
      some { s with events := v :: s.events } := rfl

-- Assert
theorem execInstruction_assert
    (s : MidenState) :
    execInstruction s .assert = execAssert s := rfl
theorem execInstruction_assertz
    (s : MidenState) :
    execInstruction s .assertz = execAssertz s := rfl
theorem execInstruction_assertEq
    (s : MidenState) :
    execInstruction s .assertEq = execAssertEq s := rfl
theorem execInstruction_nop (s : MidenState) :
    execInstruction s .nop = some s := rfl
theorem execInstruction_assertWithError
    (s : MidenState) (msg : String) :
    execInstruction s (.assertWithError msg) =
      execAssert s := rfl
theorem execInstruction_assertEqWithError
    (s : MidenState) (msg : String) :
    execInstruction s (.assertEqWithError msg) =
      execAssertEq s := rfl

-- U32 3-operand arithmetic
theorem execInstruction_u32WidenAdd3
    (s : MidenState) :
    execInstruction s .u32WidenAdd3 =
      execU32WidenAdd3 s := rfl
theorem execInstruction_u32WrappingMadd
    (s : MidenState) :
    execInstruction s .u32WrappingMadd =
      execU32WrappingMadd s := rfl

end MidenLean
