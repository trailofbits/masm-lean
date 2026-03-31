import MidenLean.AIR.Frame
/-!
# General Stack Transition Constraints

Hand-translated from `audit-miden-vm/air/src/constraints/stack/general/mod.rs`.

For each stack position i, the constraint enforces:
  next[i] * flag_sum = no_shift[i]*current[i] + left_shift[i+1]*current[i+1] + right_shift[i-1]*current[i-1]

Since shift flags are composite (computed from op bits), we parameterize
constraints on abstract flag values rather than trying to decompose them.
-/

namespace MidenLean.AIR.Constraints.General

open MidenLean MidenLean.AIR

/-- A general stack transition constraint at position i.
    `ns` = no_shift flag, `ls` = left_shift flag, `rs` = right_shift flag.
    `curr_i` = current[i], `curr_left` = current[i+1], `curr_right` = current[i-1]. -/
def stack_transition (next_i ns ls rs curr_i curr_left curr_right : Felt) : Felt :=
  next_i * (ns + ls + rs) - (ns * curr_i + ls * curr_left + rs * curr_right)

/-- Position 0: no right shift (new value pushed instead).
    next[0] * (ns[0] + ls[1]) = ns[0]*s[0] + ls[1]*s[1] -/
def pos0 (f : Frame) (ns0 ls1 : Felt) : Felt :=
  f.s' 0 * (ns0 + ls1) - (ns0 * f.s 0 + ls1 * f.s 1)

/-- Position 15: no left shift (overflow handles it).
    next[15] * (ns[15] + rs[14]) = ns[15]*s[15] + rs[14]*s[14] -/
def pos15 (f : Frame) (ns15 rs14 : Felt) : Felt :=
  f.s' 15 * (ns15 + rs14) - (ns15 * f.s 15 + rs14 * f.s 14)

/-- Position i (1 ≤ i ≤ 14): all three shifts possible.
    Parameterized on the position index and flag values. -/
def posN (f : Frame) (i : Fin 16) (ns ls rs : Felt)
    (curr_left curr_right : Felt) : Felt :=
  f.s' i * (ns + ls + rs) - (ns * f.s i + ls * curr_left + rs * curr_right)

end MidenLean.AIR.Constraints.General
