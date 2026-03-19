-- MASM source repo commit: a6e57e8e303ff4ab24d0551332fa8f669b058cc1
import MidenLean.Semantics

open MidenLean

namespace Miden.Core.U128

def overflowing_add : List Op := [
  .inst (.movup 4),
  .inst (.u32WidenAdd),
  .inst (.movdn 7),
  .inst (.movup 4),
  .inst (.movup 2),
  .inst (.u32WidenAdd3),
  .inst (.movdn 6),
  .inst (.movup 3),
  .inst (.movup 2),
  .inst (.u32WidenAdd3),
  .inst (.movdn 5),
  .inst (.movup 2),
  .inst (.movup 2),
  .inst (.u32WidenAdd3),
  .inst (.movdn 4)
]

def widening_add : List Op := [
  .inst (.exec "overflowing_add"),
  .inst (.movdn 4)
]

def wrapping_add : List Op := [
  .inst (.exec "overflowing_add"),
  .inst (.drop)
]

def overflowing_sub : List Op := [
  .inst (.movup 7),
  .inst (.movup 7),
  .inst (.movup 7),
  .inst (.movup 7),
  .inst (.movup 4),
  .inst (.u32OverflowSub),
  .inst (.movdn 7),
  .inst (.movup 4),
  .inst (.movup 2),
  .inst (.swap 1),
  .inst (.u32OverflowSub),
  .inst (.movup 7),
  .inst (.movup 2),
  .inst (.swap 1),
  .inst (.u32OverflowSub),
  .inst (.movup 2),
  .inst (.or),
  .inst (.movdn 6),
  .inst (.movup 4),
  .inst (.movup 3),
  .inst (.swap 1),
  .inst (.u32OverflowSub),
  .inst (.movup 6),
  .inst (.movup 2),
  .inst (.swap 1),
  .inst (.u32OverflowSub),
  .inst (.movup 2),
  .inst (.or),
  .inst (.movdn 5),
  .inst (.movup 4),
  .inst (.movup 4),
  .inst (.swap 1),
  .inst (.u32OverflowSub),
  .inst (.movup 5),
  .inst (.movup 2),
  .inst (.swap 1),
  .inst (.u32OverflowSub),
  .inst (.movup 2),
  .inst (.or),
  .inst (.movdn 4),
  .inst (.movdn 3),
  .inst (.movdn 2),
  .inst (.swap 1),
  .inst (.movup 4)
]

def wrapping_sub : List Op := [
  .inst (.exec "overflowing_sub"),
  .inst (.drop)
]

def overflowing_mul : List Op := [
  .inst (.movup 7),
  .inst (.movup 7),
  .inst (.movup 7),
  .inst (.movup 7),
  .inst (.dup 4),
  .inst (.dup 1),
  .inst (.u32WidenMul),
  .inst (.movdn 9),
  .inst (.dup 5),
  .inst (.dup 3),
  .inst (.u32WidenMadd),
  .inst (.dup 7),
  .inst (.dup 3),
  .inst (.u32WidenMadd),
  .inst (.movdn 11),
  .inst (.u32WidenAdd),
  .inst (.swap 1),
  .inst (.movdn 11),
  .inst (.dup 5),
  .inst (.dup 4),
  .inst (.u32WidenMadd),
  .inst (.dup 7),
  .inst (.dup 4),
  .inst (.u32WidenMadd),
  .inst (.dup 9),
  .inst (.dup 4),
  .inst (.u32WidenMadd),
  .inst (.movdn 13),
  .inst (.u32WidenAdd3),
  .inst (.movup 13),
  .inst (.u32WidenAdd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.add),
  .inst (.swap 1),
  .inst (.dup 6),
  .inst (.dup 6),
  .inst (.u32WidenMadd),
  .inst (.dup 8),
  .inst (.dup 6),
  .inst (.u32WidenMadd),
  .inst (.dup 10),
  .inst (.dup 6),
  .inst (.u32WidenMadd),
  .inst (.dup 12),
  .inst (.dup 6),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.add),
  .inst (.movup 2),
  .inst (.add),
  .inst (.movup 2),
  .inst (.add),
  .inst (.movup 2),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.dup 7),
  .inst (.dup 6),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 8),
  .inst (.dup 5),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 9),
  .inst (.dup 4),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 8),
  .inst (.dup 6),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 9),
  .inst (.dup 5),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 9),
  .inst (.dup 6),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.movup 2),
  .inst (.drop),
  .inst (.movup 2),
  .inst (.drop),
  .inst (.movup 2),
  .inst (.drop),
  .inst (.movup 2),
  .inst (.drop),
  .inst (.movup 2),
  .inst (.drop),
  .inst (.movup 2),
  .inst (.drop),
  .inst (.movup 2),
  .inst (.drop),
  .inst (.movup 2),
  .inst (.drop),
  .inst (.swap 1),
  .inst (.movdn 4)
]

def widening_mul : List Op := [
  .inst (.exec "overflowing_mul"),
  .inst (.movdn 4)
]

def wrapping_mul : List Op := [
  .inst (.movup 7),
  .inst (.movup 7),
  .inst (.movup 7),
  .inst (.movup 7),
  .inst (.dup 4),
  .inst (.dup 1),
  .inst (.u32WidenMul),
  .inst (.movdn 9),
  .inst (.dup 5),
  .inst (.dup 3),
  .inst (.u32WidenMadd),
  .inst (.dup 7),
  .inst (.dup 3),
  .inst (.u32WidenMadd),
  .inst (.movdn 11),
  .inst (.u32WidenAdd),
  .inst (.swap 1),
  .inst (.movdn 11),
  .inst (.dup 5),
  .inst (.dup 4),
  .inst (.u32WidenMadd),
  .inst (.dup 7),
  .inst (.dup 4),
  .inst (.u32WidenMadd),
  .inst (.dup 9),
  .inst (.dup 4),
  .inst (.u32WidenMadd),
  .inst (.movdn 13),
  .inst (.u32WidenAdd3),
  .inst (.movup 13),
  .inst (.u32WidenAdd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.add),
  .inst (.swap 1),
  .inst (.swap 1),
  .inst (.drop),
  .inst (.dup 5),
  .inst (.dup 5),
  .inst (.u32WrappingMadd),
  .inst (.dup 6),
  .inst (.dup 4),
  .inst (.u32WrappingMadd),
  .inst (.dup 7),
  .inst (.dup 3),
  .inst (.u32WrappingMadd),
  .inst (.dup 8),
  .inst (.dup 2),
  .inst (.u32WrappingMadd),
  .inst (.movup 9),
  .inst (.movup 10),
  .inst (.movup 11),
  .inst (.movup 3),
  .inst (.swapw 1),
  .inst (.dropw),
  .inst (.swapw 1),
  .inst (.dropw),
  .inst (.movdn 3),
  .inst (.movdn 2),
  .inst (.swap 1)
]

def eq : List Op := [
  .inst (.movup 4),
  .inst (.eq),
  .inst (.movup 4),
  .inst (.movup 2),
  .inst (.eq),
  .inst (.and),
  .inst (.movup 3),
  .inst (.movup 2),
  .inst (.eq),
  .inst (.and),
  .inst (.movup 2),
  .inst (.movup 2),
  .inst (.eq),
  .inst (.and)
]

def neq : List Op := [
  .inst (.movup 4),
  .inst (.neq),
  .inst (.movup 4),
  .inst (.movup 2),
  .inst (.neq),
  .inst (.or),
  .inst (.movup 3),
  .inst (.movup 2),
  .inst (.neq),
  .inst (.or),
  .inst (.movup 2),
  .inst (.movup 2),
  .inst (.neq),
  .inst (.or)
]

def eqz : List Op := [
  .inst (.eqImm 0),
  .inst (.swap 1),
  .inst (.eqImm 0),
  .inst (.and),
  .inst (.swap 1),
  .inst (.eqImm 0),
  .inst (.and),
  .inst (.swap 1),
  .inst (.eqImm 0),
  .inst (.and)
]

def lt : List Op := [
  .inst (.exec "overflowing_sub"),
  .inst (.movdn 4),
  .inst (.drop),
  .inst (.drop),
  .inst (.drop),
  .inst (.drop)
]

def gt : List Op := [
  .inst (.swapw 1),
  .inst (.exec "overflowing_sub"),
  .inst (.movdn 4),
  .inst (.drop),
  .inst (.drop),
  .inst (.drop),
  .inst (.drop)
]

def lte : List Op := [
  .inst (.exec "gt"),
  .inst (.not)
]

def gte : List Op := [
  .inst (.exec "lt"),
  .inst (.not)
]

def min : List Op := [
  .inst (.dupw 1),
  .inst (.dupw 1),
  .inst (.exec "gt"),
  .inst (.cdropw)
]

def max : List Op := [
  .inst (.dupw 1),
  .inst (.dupw 1),
  .inst (.exec "lt"),
  .inst (.cdropw)
]

def and : List Op := [
  .inst (.movup 4),
  .inst (.u32And),
  .inst (.movup 4),
  .inst (.movup 2),
  .inst (.u32And),
  .inst (.movup 4),
  .inst (.movup 3),
  .inst (.u32And),
  .inst (.movup 4),
  .inst (.movup 4),
  .inst (.u32And),
  .inst (.reversew)
]

def or : List Op := [
  .inst (.movup 4),
  .inst (.u32Or),
  .inst (.movup 4),
  .inst (.movup 2),
  .inst (.u32Or),
  .inst (.movup 4),
  .inst (.movup 3),
  .inst (.u32Or),
  .inst (.movup 4),
  .inst (.movup 4),
  .inst (.u32Or),
  .inst (.reversew)
]

def xor : List Op := [
  .inst (.movup 4),
  .inst (.u32Xor),
  .inst (.movup 4),
  .inst (.movup 2),
  .inst (.u32Xor),
  .inst (.movup 4),
  .inst (.movup 3),
  .inst (.u32Xor),
  .inst (.movup 4),
  .inst (.movup 4),
  .inst (.u32Xor),
  .inst (.reversew)
]

def not : List Op := [
  .inst (.movup 3),
  .inst (.u32Not),
  .inst (.movup 3),
  .inst (.u32Not),
  .inst (.movup 3),
  .inst (.u32Not),
  .inst (.movup 3),
  .inst (.u32Not)
]

def clz : List Op := [
  .inst (.movup 3),
  .inst (.dup 0),
  .inst (.eqImm 0),
  .ifElse [
    .inst (.drop),
    .inst (.movup 2),
    .inst (.dup 0),
    .inst (.eqImm 0),
    .ifElse [
      .inst (.drop),
      .inst (.swap 1),
      .inst (.dup 0),
      .inst (.eqImm 0),
      .ifElse [
        .inst (.drop),
        .inst (.u32Clz),
        .inst (.addImm 96)
] [
        .inst (.swap 1),
        .inst (.drop),
        .inst (.u32Clz),
        .inst (.addImm 64)
]
] [
      .inst (.movdn 2),
      .inst (.drop),
      .inst (.drop),
      .inst (.u32Clz),
      .inst (.addImm 32)
]
] [
    .inst (.movdn 3),
    .inst (.drop),
    .inst (.drop),
    .inst (.drop),
    .inst (.u32Clz)
]
]

def ctz : List Op := [
  .inst (.dup 0),
  .inst (.eqImm 0),
  .ifElse [
    .inst (.drop),
    .inst (.dup 0),
    .inst (.eqImm 0),
    .ifElse [
      .inst (.drop),
      .inst (.dup 0),
      .inst (.eqImm 0),
      .ifElse [
        .inst (.drop),
        .inst (.u32Ctz),
        .inst (.addImm 96)
] [
        .inst (.swap 1),
        .inst (.drop),
        .inst (.u32Ctz),
        .inst (.addImm 64)
]
] [
      .inst (.movdn 2),
      .inst (.drop),
      .inst (.drop),
      .inst (.u32Ctz),
      .inst (.addImm 32)
]
] [
    .inst (.movdn 3),
    .inst (.drop),
    .inst (.drop),
    .inst (.drop),
    .inst (.u32Ctz)
]
]

def clo : List Op := [
  .inst (.movup 3),
  .inst (.dup 0),
  .inst (.eqImm 4294967295),
  .ifElse [
    .inst (.drop),
    .inst (.movup 2),
    .inst (.dup 0),
    .inst (.eqImm 4294967295),
    .ifElse [
      .inst (.drop),
      .inst (.swap 1),
      .inst (.dup 0),
      .inst (.eqImm 4294967295),
      .ifElse [
        .inst (.drop),
        .inst (.u32Clo),
        .inst (.addImm 96)
] [
        .inst (.swap 1),
        .inst (.drop),
        .inst (.u32Clo),
        .inst (.addImm 64)
]
] [
      .inst (.movdn 2),
      .inst (.drop),
      .inst (.drop),
      .inst (.u32Clo),
      .inst (.addImm 32)
]
] [
    .inst (.movdn 3),
    .inst (.drop),
    .inst (.drop),
    .inst (.drop),
    .inst (.u32Clo)
]
]

def cto : List Op := [
  .inst (.dup 0),
  .inst (.eqImm 4294967295),
  .ifElse [
    .inst (.drop),
    .inst (.dup 0),
    .inst (.eqImm 4294967295),
    .ifElse [
      .inst (.drop),
      .inst (.dup 0),
      .inst (.eqImm 4294967295),
      .ifElse [
        .inst (.drop),
        .inst (.u32Cto),
        .inst (.addImm 96)
] [
        .inst (.swap 1),
        .inst (.drop),
        .inst (.u32Cto),
        .inst (.addImm 64)
]
] [
      .inst (.movdn 2),
      .inst (.drop),
      .inst (.drop),
      .inst (.u32Cto),
      .inst (.addImm 32)
]
] [
    .inst (.movdn 3),
    .inst (.drop),
    .inst (.drop),
    .inst (.drop),
    .inst (.u32Cto)
]
]

def shl : List Op := [
  .inst (.dup 0),
  .inst (.push 128),
  .inst (.u32Lt),
  .inst (.assertWithError "shift amount must be in the range [0, 128)"),
  .inst (.dup 0),
  .inst (.push 64),
  .inst (.u32Lt),
  .ifElse [
    .inst (.pow2),
    .inst (.u32Split),
    .inst (.push 0),
    .inst (.push 0),
    .inst (.movup 3),
    .inst (.movup 3),
    .inst (.exec "wrapping_mul")
] [
    .inst (.push 64),
    .inst (.u32WrappingSub),
    .inst (.pow2),
    .inst (.u32Split),
    .inst (.push 0),
    .inst (.push 0),
    .inst (.exec "wrapping_mul")
]
]

def shr : List Op := [
  .inst (.dup 0),
  .inst (.push 128),
  .inst (.u32Lt),
  .inst (.assertWithError "shift amount must be in the range [0, 128)"),
  .inst (.dup 0),
  .inst (.eqImm 0),
  .ifElse [
    .inst (.drop)
] [
    .inst (.dup 0),
    .inst (.push 31),
    .inst (.u32And),
    .inst (.swap 1),
    .inst (.push 5),
    .inst (.u32Shr),
    .inst (.dup 0),
    .inst (.eqImm 0),
    .ifElse [
      .inst (.drop),
      .inst (.exec "shr_k0")
] [
      .inst (.dup 0),
      .inst (.eqImm 1),
      .ifElse [
        .inst (.drop),
        .inst (.push 0),
        .inst (.movdn 5),
        .inst (.exec "shr_k1")
] [
        .inst (.dup 0),
        .inst (.eqImm 2),
        .ifElse [
          .inst (.drop),
          .inst (.push 0),
          .inst (.movdn 5),
          .inst (.push 0),
          .inst (.movdn 5),
          .inst (.exec "shr_k2")
] [
          .inst (.drop),
          .inst (.push 0),
          .inst (.movdn 5),
          .inst (.push 0),
          .inst (.movdn 5),
          .inst (.push 0),
          .inst (.movdn 5),
          .inst (.exec "shr_k3")
]
]
]
]
]

def shr_k0 : List Op := [
  .inst (.push 32),
  .inst (.dup 1),
  .inst (.u32WrappingSub),
  .inst (.pow2),
  .inst (.dup 5),
  .inst (.dup 2),
  .inst (.u32Shr),
  .inst (.dup 5),
  .inst (.dup 3),
  .inst (.u32Shr),
  .inst (.dup 7),
  .inst (.dup 3),
  .inst (.u32WidenMul),
  .inst (.swap 1),
  .inst (.drop),
  .inst (.u32Or),
  .inst (.dup 5),
  .inst (.dup 4),
  .inst (.u32Shr),
  .inst (.dup 7),
  .inst (.dup 4),
  .inst (.u32WidenMul),
  .inst (.swap 1),
  .inst (.drop),
  .inst (.u32Or),
  .inst (.dup 5),
  .inst (.dup 5),
  .inst (.u32Shr),
  .inst (.dup 7),
  .inst (.dup 5),
  .inst (.u32WidenMul),
  .inst (.swap 1),
  .inst (.drop),
  .inst (.u32Or),
  .inst (.movup 4),
  .inst (.drop),
  .inst (.movup 4),
  .inst (.drop),
  .inst (.movup 4),
  .inst (.drop),
  .inst (.movup 4),
  .inst (.drop),
  .inst (.movup 4),
  .inst (.drop),
  .inst (.movup 4),
  .inst (.drop)
]

def shr_k1 : List Op := [
  .inst (.dup 0),
  .inst (.eqImm 0),
  .ifElse [
    .inst (.drop),
    .inst (.drop)
] [
    .inst (.push 32),
    .inst (.dup 1),
    .inst (.u32WrappingSub),
    .inst (.pow2),
    .inst (.dup 5),
    .inst (.dup 2),
    .inst (.u32Shr),
    .inst (.dup 5),
    .inst (.dup 3),
    .inst (.u32Shr),
    .inst (.dup 7),
    .inst (.dup 3),
    .inst (.u32WidenMul),
    .inst (.swap 1),
    .inst (.drop),
    .inst (.u32Or),
    .inst (.dup 5),
    .inst (.dup 4),
    .inst (.u32Shr),
    .inst (.dup 7),
    .inst (.dup 4),
    .inst (.u32WidenMul),
    .inst (.swap 1),
    .inst (.drop),
    .inst (.u32Or),
    .inst (.movdn 8),
    .inst (.movdn 8),
    .inst (.movdn 8),
    .inst (.drop),
    .inst (.drop),
    .inst (.drop),
    .inst (.drop),
    .inst (.drop),
    .inst (.drop)
]
]

def shr_k2 : List Op := [
  .inst (.dup 0),
  .inst (.eqImm 0),
  .ifElse [
    .inst (.drop),
    .inst (.drop),
    .inst (.drop)
] [
    .inst (.push 32),
    .inst (.dup 1),
    .inst (.u32WrappingSub),
    .inst (.pow2),
    .inst (.dup 5),
    .inst (.dup 2),
    .inst (.u32Shr),
    .inst (.dup 5),
    .inst (.dup 3),
    .inst (.u32Shr),
    .inst (.dup 7),
    .inst (.dup 3),
    .inst (.u32WidenMul),
    .inst (.swap 1),
    .inst (.drop),
    .inst (.u32Or),
    .inst (.movdn 7),
    .inst (.movdn 7),
    .inst (.drop),
    .inst (.drop),
    .inst (.drop),
    .inst (.drop),
    .inst (.drop),
    .inst (.drop)
]
]

def shr_k3 : List Op := [
  .inst (.movup 4),
  .inst (.swap 1),
  .inst (.u32Shr),
  .inst (.movdn 3),
  .inst (.drop),
  .inst (.drop),
  .inst (.drop)
]

def rotl : List Op := [
  .inst (.dup 0),
  .inst (.eqImm 0),
  .ifElse [
    .inst (.drop)
] [
    .inst (.dup 0),
    .inst (.dup 5),
    .inst (.dup 5),
    .inst (.dup 5),
    .inst (.dup 5),
    .inst (.movup 4),
    .inst (.exec "shl"),
    .inst (.movdn 8),
    .inst (.movdn 8),
    .inst (.movdn 8),
    .inst (.movdn 8),
    .inst (.push 128),
    .inst (.swap 1),
    .inst (.u32WrappingSub),
    .inst (.exec "shr"),
    .inst (.movup 4),
    .inst (.u32Or),
    .inst (.swap 1),
    .inst (.movup 4),
    .inst (.u32Or),
    .inst (.swap 1),
    .inst (.movup 2),
    .inst (.movup 4),
    .inst (.u32Or),
    .inst (.movdn 2),
    .inst (.movup 3),
    .inst (.movup 4),
    .inst (.u32Or),
    .inst (.movdn 3)
]
]

def rotr : List Op := [
  .inst (.dup 0),
  .inst (.eqImm 0),
  .ifElse [
    .inst (.drop)
] [
    .inst (.dup 0),
    .inst (.dup 5),
    .inst (.dup 5),
    .inst (.dup 5),
    .inst (.dup 5),
    .inst (.movup 4),
    .inst (.exec "shr"),
    .inst (.movdn 8),
    .inst (.movdn 8),
    .inst (.movdn 8),
    .inst (.movdn 8),
    .inst (.push 128),
    .inst (.swap 1),
    .inst (.u32WrappingSub),
    .inst (.exec "shl"),
    .inst (.movup 4),
    .inst (.u32Or),
    .inst (.swap 1),
    .inst (.movup 4),
    .inst (.u32Or),
    .inst (.swap 1),
    .inst (.movup 2),
    .inst (.movup 4),
    .inst (.u32Or),
    .inst (.movdn 2),
    .inst (.movup 3),
    .inst (.movup 4),
    .inst (.u32Or),
    .inst (.movdn 3)
]
]

def div : List Op := [
  .inst (.exec "divmod"),
  .inst (.dropw)
]

def mod : List Op := [
  .inst (.exec "divmod"),
  .inst (.swapw 1),
  .inst (.dropw)
]

def divmod : List Op := [
  .inst (.emitImm 15463989275656898604),
  .inst (.padw),
  .inst (.advLoadW),
  .inst (.u32AssertW),
  .inst (.padw),
  .inst (.advLoadW),
  .inst (.u32AssertW),
  .inst (.dup 8),
  .inst (.dup 1),
  .inst (.u32WidenMul),
  .inst (.dup 6),
  .inst (.u32WidenAdd),
  .inst (.movup 15),
  .inst (.assertEqWithError "u128 divmod: col 0"),
  .inst (.add),
  .inst (.dup 9),
  .inst (.dup 3),
  .inst (.u32WidenMadd),
  .inst (.dup 11),
  .inst (.dup 3),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.add),
  .inst (.swap 1),
  .inst (.dup 7),
  .inst (.u32WidenAdd),
  .inst (.movup 15),
  .inst (.assertEqWithError "u128 divmod: col 1"),
  .inst (.add),
  .inst (.u32Split),
  .inst (.dup 10),
  .inst (.dup 5),
  .inst (.u32WidenMadd),
  .inst (.dup 12),
  .inst (.dup 5),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.movup 3),
  .inst (.add),
  .inst (.add),
  .inst (.swap 1),
  .inst (.dup 12),
  .inst (.dup 3),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.add),
  .inst (.swap 1),
  .inst (.dup 8),
  .inst (.u32WidenAdd),
  .inst (.movup 15),
  .inst (.assertEqWithError "u128 divmod: col 2"),
  .inst (.add),
  .inst (.u32Split),
  .inst (.dup 10),
  .inst (.dup 6),
  .inst (.u32WidenMadd),
  .inst (.dup 12),
  .inst (.dup 6),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.movup 3),
  .inst (.add),
  .inst (.add),
  .inst (.swap 1),
  .inst (.dup 12),
  .inst (.dup 4),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.add),
  .inst (.swap 1),
  .inst (.dup 13),
  .inst (.dup 3),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.add),
  .inst (.swap 1),
  .inst (.dup 9),
  .inst (.u32WidenAdd),
  .inst (.movup 15),
  .inst (.assertEqWithError "u128 divmod: col 3"),
  .inst (.add),
  .inst (.assertzWithError "u128 divmod: carry overflow"),
  .inst (.push 0),
  .inst (.dup 10),
  .inst (.dup 5),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 11),
  .inst (.dup 4),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 12),
  .inst (.dup 3),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 11),
  .inst (.dup 5),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 12),
  .inst (.dup 4),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.dup 12),
  .inst (.dup 5),
  .inst (.u32WidenMul),
  .inst (.add),
  .inst (.neqImm 0),
  .inst (.or),
  .inst (.assertzWithError "u128 divmod: q*b overflow"),
  .inst (.dup 4),
  .inst (.dup 9),
  .inst (.u32OverflowSub),
  .inst (.swap 1),
  .inst (.drop),
  .inst (.dup 6),
  .inst (.dup 11),
  .inst (.u32OverflowSub),
  .inst (.swap 1),
  .inst (.eqImm 0),
  .inst (.movup 2),
  .inst (.and),
  .inst (.or),
  .inst (.dup 7),
  .inst (.dup 12),
  .inst (.u32OverflowSub),
  .inst (.swap 1),
  .inst (.eqImm 0),
  .inst (.movup 2),
  .inst (.and),
  .inst (.or),
  .inst (.dup 8),
  .inst (.dup 13),
  .inst (.u32OverflowSub),
  .inst (.swap 1),
  .inst (.eqImm 0),
  .inst (.movup 2),
  .inst (.and),
  .inst (.or),
  .inst (.assertWithError "u128 divmod: remainder >= divisor"),
  .inst (.swapw 2),
  .inst (.dropw)
]

end Miden.Core.U128
