import MidenLean.Semantics

open MidenLean

namespace Miden.Core.Math.U64

def u32assert4 : List Op := [
  .inst (.u32Assert2),
  .inst (.movup 3),
  .inst (.movup 3),
  .inst (.u32Assert2),
  .inst (.movup 3),
  .inst (.movup 3)
]

def overflowing_add : List Op := [
  .inst (.movup 2),
  .inst (.u32WidenAdd),
  .inst (.movdn 3),
  .inst (.u32WidenAdd3),
  .inst (.movdn 2)
]

def widening_add : List Op := [
  .inst (.exec "overflowing_add"),
  .inst (.movdn 2)
]

def wrapping_add : List Op := [
  .inst (.exec "overflowing_add"),
  .inst (.drop)
]

def wrapping_sub : List Op := [
  .inst (.movup 3),
  .inst (.movup 3),
  .inst (.movup 2),
  .inst (.u32OverflowSub),
  .inst (.movup 2),
  .inst (.movup 3),
  .inst (.u32OverflowSub),
  .inst (.drop),
  .inst (.swap 1),
  .inst (.u32OverflowSub),
  .inst (.drop),
  .inst (.swap 1)
]

def overflowing_sub : List Op := [
  .inst (.movup 3),
  .inst (.movup 3),
  .inst (.movup 2),
  .inst (.u32OverflowSub),
  .inst (.movup 2),
  .inst (.movup 3),
  .inst (.u32OverflowSub),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.u32OverflowSub),
  .inst (.movup 2),
  .inst (.or),
  .inst (.movup 2),
  .inst (.swap 1)
]

def wrapping_mul : List Op := [
  .inst (.dup 2),
  .inst (.dup 1),
  .inst (.u32WidenMul),
  .inst (.swap 1),
  .inst (.movup 3),
  .inst (.movup 4),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.drop),
  .inst (.movup 2),
  .inst (.movup 3),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.drop),
  .inst (.swap 1)
]

def widening_mul : List Op := [
  .inst (.reversew),
  .inst (.dup 3),
  .inst (.dup 2),
  .inst (.u32WidenMul),
  .inst (.swap 1),
  .inst (.dup 4),
  .inst (.movup 4),
  .inst (.u32WidenMadd),
  .inst (.movup 5),
  .inst (.dup 4),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.movup 5),
  .inst (.movup 5),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.movup 3),
  .inst (.movup 2),
  .inst (.u32WidenAdd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.add),
  .inst (.reversew)
]

def lt : List Op := [
  .inst (.movup 3),
  .inst (.movup 3),
  .inst (.movup 2),
  .inst (.u32OverflowSub),
  .inst (.movdn 3),
  .inst (.drop),
  .inst (.swap 1),
  .inst (.u32OverflowSub),
  .inst (.swap 1),
  .inst (.eqImm 0),
  .inst (.movup 2),
  .inst (.and),
  .inst (.or)
]

def gt : List Op := [
  .inst (.movup 3),
  .inst (.movup 3),
  .inst (.movup 2),
  .inst (.swap 1),
  .inst (.u32OverflowSub),
  .inst (.movdn 3),
  .inst (.drop),
  .inst (.u32OverflowSub),
  .inst (.swap 1),
  .inst (.eqImm 0),
  .inst (.movup 2),
  .inst (.and),
  .inst (.or)
]

def lte : List Op := [
  .inst (.exec "gt"),
  .inst (.not)
]

def gte : List Op := [
  .inst (.exec "lt"),
  .inst (.not)
]

def eq : List Op := [
  .inst (.movup 2),
  .inst (.eq),
  .inst (.swap 2),
  .inst (.eq),
  .inst (.and)
]

def neq : List Op := [
  .inst (.movup 2),
  .inst (.neq),
  .inst (.swap 2),
  .inst (.neq),
  .inst (.or)
]

def eqz : List Op := [
  .inst (.eqImm 0),
  .inst (.swap 1),
  .inst (.eqImm 0),
  .inst (.and)
]

def min : List Op := [
  .inst (.movup 3),
  .inst (.movup 3),
  .inst (.dupw 0),
  .inst (.exec "gt"),
  .inst (.movup 4),
  .inst (.movup 3),
  .inst (.dup 2),
  .inst (.cdrop),
  .inst (.movdn 3),
  .inst (.cdrop)
]

def max : List Op := [
  .inst (.movup 3),
  .inst (.movup 3),
  .inst (.dupw 0),
  .inst (.exec "lt"),
  .inst (.movup 4),
  .inst (.movup 3),
  .inst (.dup 2),
  .inst (.cdrop),
  .inst (.movdn 3),
  .inst (.cdrop)
]

def div : List Op := [
  .inst (.exec "divmod"),
  .inst (.drop),
  .inst (.drop)
]

def mod : List Op := [
  .inst (.exec "divmod"),
  .inst (.movup 2),
  .inst (.drop),
  .inst (.movup 2),
  .inst (.drop)
]

def divmod : List Op := [
  .inst (.emitImm 14153021663962350784),
  .inst (.advPush 2),
  .inst (.u32Assert2),
  .inst (.dup 2),
  .inst (.dup 1),
  .inst (.u32WidenMul),
  .inst (.swap 1),
  .inst (.dup 5),
  .inst (.dup 3),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.eqImm 0),
  .inst (.assertWithError "comparison failed: divmod"),
  .inst (.dup 4),
  .inst (.dup 4),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.eqImm 0),
  .inst (.assertWithError "comparison failed: divmod"),
  .inst (.dup 5),
  .inst (.dup 4),
  .inst (.mul),
  .inst (.eqImm 0),
  .inst (.assertWithError "comparison failed: divmod"),
  .inst (.advPush 2),
  .inst (.u32Assert2),
  .inst (.movup 6),
  .inst (.movup 7),
  .inst (.swap 1),
  .inst (.dup 3),
  .inst (.dup 3),
  .inst (.movup 3),
  .inst (.movup 3),
  .inst (.exec "lt"),
  .inst (.assertWithError "comparison failed: divmod"),
  .inst (.dup 0),
  .inst (.movup 4),
  .inst (.u32WidenAdd),
  .inst (.swap 1),
  .inst (.dup 3),
  .inst (.movup 5),
  .inst (.movup 2),
  .inst (.u32WidenAdd3),
  .inst (.swap 1),
  .inst (.eqImm 0),
  .inst (.assertWithError "comparison failed: divmod"),
  .inst (.movup 7),
  .inst (.assertEqWithError "comparison failed: divmod"),
  .inst (.movup 5),
  .inst (.assertEqWithError "comparison failed: divmod")
]

def and : List Op := [
  .inst (.movup 2),
  .inst (.u32And),
  .inst (.swap 2),
  .inst (.u32And),
  .inst (.swap 1)
]

def or : List Op := [
  .inst (.movup 2),
  .inst (.u32Or),
  .inst (.swap 2),
  .inst (.u32Or),
  .inst (.swap 1)
]

def xor : List Op := [
  .inst (.movup 2),
  .inst (.u32Xor),
  .inst (.swap 2),
  .inst (.u32Xor),
  .inst (.swap 1)
]

def shl : List Op := [
  .inst (.pow2),
  .inst (.u32Split),
  .inst (.movup 2),
  .inst (.movup 3),
  .inst (.swap 1),
  .inst (.exec "wrapping_mul")
]

def shr : List Op := [
  .inst (.movup 2),
  .inst (.swap 1),
  .inst (.pow2),
  .inst (.u32Split),
  .inst (.swap 1),
  .inst (.dup 1),
  .inst (.add),
  .inst (.movup 2),
  .inst (.swap 1),
  .inst (.u32DivMod),
  .inst (.swap 1),
  .inst (.movup 3),
  .inst (.movup 3),
  .inst (.dup 0),
  .inst (.eqImm 0),
  .inst (.u32OverflowSub),
  .inst (.not),
  .inst (.movdn 4),
  .inst (.dup 0),
  .inst (.movdn 4),
  .inst (.u32DivMod),
  .inst (.swap 1),
  .inst (.swap 1),
  .inst (.drop),
  .inst (.push 4294967296),
  .inst (.dup 5),
  .inst (.mul),
  .inst (.movup 4),
  .inst (.div),
  .inst (.movup 3),
  .inst (.mul),
  .inst (.add),
  .inst (.movup 2),
  .inst (.cswap),
  .inst (.swap 1)
]

def rotl : List Op := [
  .inst (.movup 2),
  .inst (.swap 1),
  .inst (.push 31),
  .inst (.dup 1),
  .inst (.u32OverflowSub),
  .inst (.swap 1),
  .inst (.drop),
  .inst (.movdn 3),
  .inst (.push 31),
  .inst (.u32And),
  .inst (.pow2),
  .inst (.dup 0),
  .inst (.movup 3),
  .inst (.u32WidenMul),
  .inst (.swap 1),
  .inst (.movup 3),
  .inst (.movup 3),
  .inst (.u32WidenMadd),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.add),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.cswap),
  .inst (.swap 1)
]

def rotr : List Op := [
  .inst (.movup 2),
  .inst (.swap 1),
  .inst (.push 31),
  .inst (.dup 1),
  .inst (.u32Lt),
  .inst (.movdn 3),
  .inst (.push 31),
  .inst (.u32And),
  .inst (.push 32),
  .inst (.swap 1),
  .inst (.u32WrappingSub),
  .inst (.pow2),
  .inst (.dup 0),
  .inst (.movup 3),
  .inst (.mul),
  .inst (.u32Split),
  .inst (.swap 1),
  .inst (.movup 3),
  .inst (.movup 3),
  .inst (.mul),
  .inst (.add),
  .inst (.u32Split),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.add),
  .inst (.swap 1),
  .inst (.movup 2),
  .inst (.not),
  .inst (.cswap),
  .inst (.swap 1)
]

def clz : List Op := [
  .inst (.swap 1),
  .inst (.dup 0),
  .inst (.eqImm 0),
  .ifElse [
    .inst (.drop),
    .inst (.u32Clz),
    .inst (.addImm 32)
] [
    .inst (.swap 1),
    .inst (.drop),
    .inst (.u32Clz)
]
]

def ctz : List Op := [
  .inst (.dup 0),
  .inst (.eqImm 0),
  .ifElse [
    .inst (.drop),
    .inst (.u32Ctz),
    .inst (.addImm 32)
] [
    .inst (.swap 1),
    .inst (.drop),
    .inst (.u32Ctz)
]
]

def clo : List Op := [
  .inst (.swap 1),
  .inst (.dup 0),
  .inst (.eqImm 4294967295),
  .ifElse [
    .inst (.drop),
    .inst (.u32Clo),
    .inst (.addImm 32)
] [
    .inst (.swap 1),
    .inst (.drop),
    .inst (.u32Clo)
]
]

def cto : List Op := [
  .inst (.dup 0),
  .inst (.eqImm 4294967295),
  .ifElse [
    .inst (.drop),
    .inst (.u32Cto),
    .inst (.addImm 32)
] [
    .inst (.swap 1),
    .inst (.drop),
    .inst (.u32Cto)
]
]

end Miden.Core.Math.U64
