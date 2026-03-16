import MidenLean.Semantics

open MidenLean

namespace Miden.Core.Word

def reverse : List Op := [
  .inst (.reversew)
]

def store_word_u32s_le : List Op := [
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
]

def eqz : List Op := [
  .inst (.eqImm 0),
  .repeat 3 [
    .inst (.swap 1),
    .inst (.eqImm 0),
    .inst (.and)
]
]

def testz : List Op := [
  .repeat 4 [
    .inst (.dup 3),
    .inst (.eqImm 0)
],
  .inst (.and),
  .inst (.and),
  .inst (.and)
]

def gt : List Op := [
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
]

def gte : List Op := [
  .inst (.exec "lt"),
  .inst (.not)
]

def lt : List Op := [
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
]

def lte : List Op := [
  .inst (.exec "gt"),
  .inst (.not)
]

def eq : List Op := [
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
]

def test_eq : List Op := [
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
]

def arrange_words_adjacent_le : List Op := [
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
]

end Miden.Core.Word
