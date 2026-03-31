-- Generated from collections/mmr.masm
import MidenLean.Semantics

open MidenLean

namespace Miden.Core.Collections.Mmr

def num_leaves_to_num_peaks : List Op := [
  .inst (.u32Split),
  .inst (.u32Popcnt),
  .inst (.swap 1),
  .inst (.u32Popcnt),
  .inst (.add)
]

def num_peaks_to_message_size : List Op := [
  .inst (.push 16),
  .inst (.u32Max),
  .inst (.dup 0),
  .inst (.isOdd),
  .inst (.add),
  .inst (.mulImm 4)
]

end Miden.Core.Collections.Mmr
