import MidenLean.Felt

namespace MidenLean

/-- Miden VM instructions. This covers the subset needed for word.masm and math/u64.masm.
    Additional instructions will be added as coverage expands. -/
inductive Instruction where
  -- No-op
  | nop

  -- Assertions
  | assert
  | assertWithError (msg : String)
  | assertz
  | assertzWithError (msg : String)
  | assertEq
  | assertEqWithError (msg : String)
  | assertEqw

  -- Stack: drop
  | drop
  | dropw

  -- Stack: pad
  | padw

  -- Stack: dup
  | dup (n : Fin 16)
  | dupw (n : Fin 4)

  -- Stack: swap
  | swap (n : Fin 16)  -- swap.0 is nop, swap.1 is the standard swap
  | swapw (n : Fin 4)
  | swapdw

  -- Stack: move (movup/movdn valid for n in {2, ..., 15}, movupw/movdnw valid for n in {2, 3})
  | movup (n : Nat)
  | movdn (n : Nat)
  | movupw (n : Nat)
  | movdnw (n : Nat)

  -- Stack: reverse
  | reversew

  -- Stack: conditional
  | cswap
  | cswapw
  | cdrop
  | cdropw

  -- Constants
  | push (v : Felt)
  | pushList (vs : List Felt)

  -- Field arithmetic
  | add
  | addImm (v : Felt)
  | sub
  | subImm (v : Felt)
  | mul
  | mulImm (v : Felt)
  | div
  | divImm (v : Felt)
  | neg
  | inv
  | pow2
  | incr

  -- Field comparison
  | eq
  | eqImm (v : Felt)
  | neq
  | neqImm (v : Felt)
  | lt
  | lte
  | gt
  | gte
  | isOdd

  -- Field boolean
  | and
  | or
  | xor
  | not

  -- U32 conversions
  | u32Test
  | u32TestW
  | u32Assert
  | u32Assert2
  | u32AssertW
  | u32Cast
  | u32Split

  -- U32 arithmetic
  | u32WidenAdd        -- [b, a] -> [sum_lo, carry]
  | u32OverflowAdd     -- [b, a] -> [carry, sum_lo]
  | u32WrappingAdd
  | u32WidenAdd3       -- [c, b, a] -> [sum_lo, carry]
  | u32OverflowAdd3    -- [c, b, a] -> [carry, sum_lo]
  | u32WrappingAdd3
  | u32OverflowSub     -- [b, a] -> [borrow, diff]
  | u32WrappingSub
  | u32WidenMul        -- [b, a] -> [lo, hi]
  | u32WrappingMul
  | u32WidenMadd       -- [b, a, c] -> [lo, hi] where result = a*b + c
  | u32WrappingMadd
  | u32Div             -- [b, a] -> [quot]  (upstream: u32divmod + drop)
  | u32Mod             -- [b, a] -> [rem]   (upstream: u32divmod + swap + drop)
  | u32DivMod          -- [b, a] -> [rem, quot]

  -- U32 bitwise
  | u32And
  | u32Or
  | u32Xor
  | u32Not
  | u32Shl
  | u32ShlImm (n : Nat)
  | u32Shr
  | u32ShrImm (n : Nat)
  | u32Rotl
  | u32RotlImm (n : Nat)
  | u32Rotr
  | u32RotrImm (n : Nat)
  | u32Popcnt
  | u32Clz
  | u32Ctz
  | u32Clo
  | u32Cto

  -- U32 comparison
  | u32Lt
  | u32Lte
  | u32Gt
  | u32Gte
  | u32Min
  | u32Max

  -- Memory
  | memLoad
  | memLoadImm (addr : Nat)
  | memStore
  | memStoreImm (addr : Nat)
  | memLoadwBe
  | memLoadwBeImm (addr : Nat)
  | memStorewBe
  | memStorewBeImm (addr : Nat)
  | memLoadwLe
  | memLoadwLeImm (addr : Nat)
  | memStorewLe
  | memStorewLeImm (addr : Nat)

  -- Procedure locals
  | locLoad (idx : Nat)
  | locStore (idx : Nat)
  | locLoadwBe (idx : Nat)
  | locStorewBe (idx : Nat)
  | locLoadwLe (idx : Nat)
  | locStorewLe (idx : Nat)
  | locaddr (idx : Nat)

  -- Advice stack
  | advPush (n : Nat)
  | advLoadW

  -- Events
  | emit
  | emitImm (eventId : Felt)

  -- Procedure calls (resolved by name)
  | exec (target : String)

  deriving Repr, BEq

end MidenLean
