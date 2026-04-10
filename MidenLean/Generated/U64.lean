-- MASM source repo commit: a6e57e8e303ff4ab24d0551332fa8f669b058cc1
import MidenLean.Concrete.Exec

open MidenLean

namespace Miden.Core.U64

def u32assert4 : Procedure := {
  name := "u32assert4",
  numLocals := 0,
  body := [
  .inst (.u32Assert2),
  .inst (.movup 3),
  .inst (.movup 3),
  .inst (.u32Assert2),
  .inst (.movup 3),
  .inst (.movup 3)
] }

def overflowing_add : Procedure := {
  name := "overflowing_add",
  numLocals := 0,
  body := [
  .inst (.movup 2),
  .inst (.u32WidenAdd),
  .inst (.movdn 3),
  .inst (.u32WidenAdd3),
  .inst (.movdn 2)
] }

def widening_add : Procedure := {
  name := "widening_add",
  numLocals := 0,
  body := [
  .inst (.exec "overflowing_add"),
  .inst (.movdn 2)
] }

def wrapping_add : Procedure := {
  name := "wrapping_add",
  numLocals := 0,
  body := [
  .inst (.exec "overflowing_add"),
  .inst (.drop)
] }

def wrapping_sub : Procedure := {
  name := "wrapping_sub",
  numLocals := 0,
  body := [
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
] }

def overflowing_sub : Procedure := {
  name := "overflowing_sub",
  numLocals := 0,
  body := [
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
] }

def wrapping_mul : Procedure := {
  name := "wrapping_mul",
  numLocals := 0,
  body := [
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
] }

def widening_mul : Procedure := {
  name := "widening_mul",
  numLocals := 0,
  body := [
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
] }

def lt : Procedure := {
  name := "lt",
  numLocals := 0,
  body := [
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
] }

def gt : Procedure := {
  name := "gt",
  numLocals := 0,
  body := [
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
] }

def lte : Procedure := {
  name := "lte",
  numLocals := 0,
  body := [
  .inst (.exec "gt"),
  .inst (.not)
] }

def gte : Procedure := {
  name := "gte",
  numLocals := 0,
  body := [
  .inst (.exec "lt"),
  .inst (.not)
] }

def eq : Procedure := {
  name := "eq",
  numLocals := 0,
  body := [
  .inst (.movup 2),
  .inst (.eq),
  .inst (.swap 2),
  .inst (.eq),
  .inst (.and)
] }

def neq : Procedure := {
  name := "neq",
  numLocals := 0,
  body := [
  .inst (.movup 2),
  .inst (.neq),
  .inst (.swap 2),
  .inst (.neq),
  .inst (.or)
] }

def eqz : Procedure := {
  name := "eqz",
  numLocals := 0,
  body := [
  .inst (.eqImm 0),
  .inst (.swap 1),
  .inst (.eqImm 0),
  .inst (.and)
] }

def min : Procedure := {
  name := "min",
  numLocals := 0,
  body := [
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
] }

def max : Procedure := {
  name := "max",
  numLocals := 0,
  body := [
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
] }

def div : Procedure := {
  name := "div",
  numLocals := 0,
  body := [
  .inst (.exec "divmod"),
  .inst (.drop),
  .inst (.drop)
] }

def mod : Procedure := {
  name := "mod",
  numLocals := 0,
  body := [
  .inst (.exec "divmod"),
  .inst (.movup 2),
  .inst (.drop),
  .inst (.movup 2),
  .inst (.drop)
] }

def divmod : Procedure := {
  name := "divmod",
  numLocals := 0,
  body := [
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
] }

def and : Procedure := {
  name := "and",
  numLocals := 0,
  body := [
  .inst (.movup 2),
  .inst (.u32And),
  .inst (.swap 2),
  .inst (.u32And),
  .inst (.swap 1)
] }

def or : Procedure := {
  name := "or",
  numLocals := 0,
  body := [
  .inst (.movup 2),
  .inst (.u32Or),
  .inst (.swap 2),
  .inst (.u32Or),
  .inst (.swap 1)
] }

def xor : Procedure := {
  name := "xor",
  numLocals := 0,
  body := [
  .inst (.movup 2),
  .inst (.u32Xor),
  .inst (.swap 2),
  .inst (.u32Xor),
  .inst (.swap 1)
] }

def shl : Procedure := {
  name := "shl",
  numLocals := 0,
  body := [
  .inst (.pow2),
  .inst (.u32Split),
  .inst (.movup 2),
  .inst (.movup 3),
  .inst (.swap 1),
  .inst (.exec "wrapping_mul")
] }

def shr : Procedure := {
  name := "shr",
  numLocals := 0,
  body := [
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
  .inst (.dup 2),
  .inst (.cswap),
  .inst (.movup 2),
  .inst (.mul),
  .inst (.swap 1)
] }

def rotl : Procedure := {
  name := "rotl",
  numLocals := 0,
  body := [
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
] }

def rotr : Procedure := {
  name := "rotr",
  numLocals := 0,
  body := [
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
] }

def clz : Procedure := {
  name := "clz",
  numLocals := 0,
  body := [
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
] }

def ctz : Procedure := {
  name := "ctz",
  numLocals := 0,
  body := [
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
] }

def clo : Procedure := {
  name := "clo",
  numLocals := 0,
  body := [
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
] }

def cto : Procedure := {
  name := "cto",
  numLocals := 0,
  body := [
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
] }

end Miden.Core.U64
