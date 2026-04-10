-- MASM source repo commit: a6e57e8e303ff4ab24d0551332fa8f669b058cc1
import MidenLean.Concrete.Exec

open MidenLean

namespace Miden.Core.Word

def reverse : Procedure := {
  name := "reverse",
  numLocals := 0,
  body := [
  .inst (.reversew)
] }

def store_word_u32s_le : Procedure := {
  name := "store_word_u32s_le",
  numLocals := 0,
  body := [
  .inst (.swap 1),
  .inst (.u32Split),
  .inst (.movup 2),
  .inst (.u32Split),
  .inst (.dup 6),
  .inst (.memStorewLe),
  .inst (.dropw),
  .inst (.swap 1),
  .inst (.u32Split),
  .inst (.movup 2),
  .inst (.u32Split),
  .inst (.movup 4),
  .inst (.addImm 4),
  .inst (.memStorewLe),
  .inst (.dropw)
] }

def eqz : Procedure := {
  name := "eqz",
  numLocals := 0,
  body := [
  .inst (.eqImm 0),
  .repeat 3 [
    .inst (.swap 1),
    .inst (.eqImm 0),
    .inst (.and)
]
] }

def testz : Procedure := {
  name := "testz",
  numLocals := 0,
  body := [
  .repeat 4 [
    .inst (.dup 3),
    .inst (.eqImm 0)
],
  .inst (.and),
  .inst (.and),
  .inst (.and)
] }

def gt : Procedure := {
  name := "gt",
  numLocals := 0,
  body := [
  .inst (.exec "arrange_words_adjacent_le"),
  .inst (.push 1),
  .inst (.push 0),
  .repeat 4 [
    .inst (.movup 3),
    .inst (.movup 3),
    .inst (.dup 0),
    .inst (.dup 2),
    .inst (.eq),
    .inst (.movdn 3),
    .inst (.lt),
    .inst (.dup 3),
    .inst (.and),
    .inst (.or),
    .inst (.movdn 2),
    .inst (.and),
    .inst (.swap 1)
],
  .inst (.swap 1),
  .inst (.drop)
] }

def gte : Procedure := {
  name := "gte",
  numLocals := 0,
  body := [
  .inst (.exec "lt"),
  .inst (.not)
] }

def lt : Procedure := {
  name := "lt",
  numLocals := 0,
  body := [
  .inst (.exec "arrange_words_adjacent_le"),
  .inst (.push 1),
  .inst (.push 0),
  .repeat 4 [
    .inst (.movup 3),
    .inst (.movup 3),
    .inst (.dup 0),
    .inst (.dup 2),
    .inst (.eq),
    .inst (.movdn 3),
    .inst (.gt),
    .inst (.dup 3),
    .inst (.and),
    .inst (.or),
    .inst (.movdn 2),
    .inst (.and),
    .inst (.swap 1)
],
  .inst (.swap 1),
  .inst (.drop)
] }

def lte : Procedure := {
  name := "lte",
  numLocals := 0,
  body := [
  .inst (.exec "gt"),
  .inst (.not)
] }

def eq : Procedure := {
  name := "eq",
  numLocals := 0,
  body := [
  .inst (.movup 4),
  .inst (.eq),
  .inst (.swap 1),
  .inst (.movup 4),
  .inst (.eq),
  .inst (.and),
  .inst (.swap 1),
  .inst (.movup 3),
  .inst (.eq),
  .inst (.and),
  .inst (.movdn 2),
  .inst (.eq),
  .inst (.and)
] }

def test_eq : Procedure := {
  name := "test_eq",
  numLocals := 0,
  body := [
  .inst (.dup 7),
  .inst (.dup 4),
  .inst (.eq),
  .inst (.dup 7),
  .inst (.dup 4),
  .inst (.eq),
  .inst (.and),
  .inst (.dup 6),
  .inst (.dup 3),
  .inst (.eq),
  .inst (.and),
  .inst (.dup 5),
  .inst (.dup 2),
  .inst (.eq),
  .inst (.and)
] }

def arrange_words_adjacent_le : Procedure := {
  name := "arrange_words_adjacent_le",
  numLocals := 0,
  body := [
  .inst (.movup 7),
  .inst (.movup 4),
  .inst (.swap 1),
  .inst (.movup 7),
  .inst (.movdn 2),
  .inst (.movup 5),
  .inst (.movdn 3),
  .inst (.movup 7),
  .inst (.movdn 4),
  .inst (.movup 6),
  .inst (.movdn 5),
  .inst (.movup 7),
  .inst (.movdn 6)
] }

end Miden.Core.Word
