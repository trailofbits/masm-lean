import MidenLean.AIR.Constraints.StackArith
/-!
# Differential Tests: Stack Arithmetic AIR Constraints

Test vectors generated from the Miden VM (audit-miden-vm).
Each test constructs a Frame from an actual execution trace row
and checks that our Lean constraint definitions evaluate to zero.

Regenerate with: `cd air-test-vectors && cargo run > test_vectors.json`
-/

namespace MidenLean.AIR.Tests.StackArith

open MidenLean MidenLean.AIR MidenLean.AIR.Constraints

-- Vector 0: add  s=[3, 5, 0, 0]  s'=[8, 0, 0, 0]  h=[0, 0, 0, 0, 0, 0]
#eval (Frame.ofLists
  [3, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [0, 0, 0, 0, 0, 0]).check Constraints.add  -- true

-- Vector 1: neg  s=[7, 0, 0, 0]  s'=[18446744069414584314, 0, 0, 0]  h=[0, 0, 0, 0, 0, 0]
#eval (Frame.ofLists
  [7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [18446744069414584314, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [0, 0, 0, 0, 0, 0]).check Constraints.neg  -- true

-- Vector 2: mul  s=[3, 7, 0, 0]  s'=[21, 0, 0, 0]  h=[0, 0, 0, 0, 0, 0]
#eval (Frame.ofLists
  [3, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [0, 0, 0, 0, 0, 0]).check Constraints.mul  -- true

-- Vector 3: inv  s=[2, 0, 0, 0]  s'=[9223372034707292161, 0, 0, 0]  h=[0, 0, 0, 0, 0, 0]
#eval (Frame.ofLists
  [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [9223372034707292161, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [0, 0, 0, 0, 0, 0]).check Constraints.inv  -- true

-- Vector 4: incr  s=[41, 0, 0, 0]  s'=[42, 0, 0, 0]  h=[0, 0, 0, 0, 0, 0]
#eval (Frame.ofLists
  [41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [0, 0, 0, 0, 0, 0]).check Constraints.incr  -- true

-- Vector 5: not  s=[1, 0, 0, 0]  s'=[0, 0, 0, 0]  h=[0, 0, 0, 0, 0, 0]
#eval (Frame.ofLists
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [0, 0, 0, 0, 0, 0]).check Constraints.not  -- true

-- Vector 6: and  s=[1, 1, 0, 0]  s'=[1, 0, 0, 0]  h=[0, 0, 0, 0, 0, 0]
#eval (Frame.ofLists
  [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [0, 0, 0, 0, 0, 0]).check Constraints.and  -- true

-- Vector 7: or  s=[1, 0, 0, 0]  s'=[1, 0, 0, 0]  h=[0, 0, 0, 0, 0, 0]
#eval (Frame.ofLists
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [0, 0, 0, 0, 0, 0]).check Constraints.or  -- true

-- Vector 8: eq  s=[5, 5, 0, 0]  s'=[1, 0, 0, 0]  h=[0, 0, 0, 0, 0, 0]
#eval (Frame.ofLists
  [5, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [0, 0, 0, 0, 0, 0]).check Constraints.eq  -- true

-- Vector 9: eq  s=[3, 7, 0, 0]  s'=[0, 0, 0, 0]  h=[4611686017353646080, 0, 0, 0, 0, 0]
#eval (Frame.ofLists
  [3, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [4611686017353646080, 0, 0, 0, 0, 0]).check Constraints.eq  -- true

-- Vector 10: eqz  s=[0, 0, 0, 0]  s'=[1, 0, 0, 0]  h=[0, 0, 0, 0, 0, 0]
#eval (Frame.ofLists
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [0, 0, 0, 0, 0, 0]).check Constraints.eqz  -- true

-- Vector 11: eqz  s=[5, 0, 0, 0]  s'=[0, 0, 0, 0]  h=[14757395255531667457, 0, 0, 0, 0, 0]
#eval (Frame.ofLists
  [5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [14757395255531667457, 0, 0, 0, 0, 0]).check Constraints.eqz  -- true

-- Vector 12: expacc  s=[1, 3, 1, 7]  s'=[1, 9, 3, 3]  h=[3, 0, 0, 0, 0, 0]
#eval (Frame.ofLists
  [1, 3, 1, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [1, 9, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [3, 0, 0, 0, 0, 0]).check Constraints.expacc  -- true

-- Vector 13: expacc  s=[0, 2, 5, 4]  s'=[0, 4, 5, 2]  h=[1, 0, 0, 0, 0, 0]
#eval (Frame.ofLists
  [0, 2, 5, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [0, 4, 5, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [1, 0, 0, 0, 0, 0]).check Constraints.expacc  -- true

-- Vector 14: ext2mul  s=[2, 3, 5, 7]  s'=[2, 3, 157, 29]  h=[0, 0, 0, 0, 0, 0]
#eval (Frame.ofLists
  [2, 3, 5, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [2, 3, 157, 29, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [0, 0, 0, 0, 0, 0]).check Constraints.ext2mul  -- true

-- Vector 15: u32split  s=[4294967297, 0, 0, 0]  s'=[1, 1, 0, 0]  h=[1, 0, 1, 0, 12297829378178067115, 0]
#eval (Frame.ofLists
  [4294967297, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [1, 0, 1, 0, 12297829378178067115, 0]).check Constraints.u32split  -- true

-- Vector 16: u32add  s=[3, 5, 0, 0]  s'=[8, 0, 0, 0]  h=[8, 0, 0, 0, 0, 0]
#eval (Frame.ofLists
  [3, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [8, 0, 0, 0, 0, 0]).check Constraints.u32add  -- true

-- Vector 17: u32add  s=[4294967295, 1, 0, 0]  s'=[0, 1, 0, 0]  h=[0, 0, 1, 0, 0, 0]
#eval (Frame.ofLists
  [4294967295, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [0, 0, 1, 0, 0, 0]).check Constraints.u32add  -- true

-- Vector 18: u32add3  s=[100, 200, 300, 0]  s'=[600, 0, 0, 0]  h=[600, 0, 0, 0, 0, 0]
#eval (Frame.ofLists
  [100, 200, 300, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [600, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [600, 0, 0, 0, 0, 0]).check Constraints.u32add3  -- true

-- Vector 19: u32sub  s=[3, 10, 0, 0]  s'=[0, 7, 0, 0]  h=[7, 0, 0, 0, 0, 0]
#eval (Frame.ofLists
  [3, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [7, 0, 0, 0, 0, 0]).check Constraints.u32sub  -- true

-- Vector 20: u32sub  s=[10, 3, 0, 0]  s'=[1, 4294967289, 0, 0]  h=[65529, 65535, 0, 0, 0, 0]
#eval (Frame.ofLists
  [10, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [1, 4294967289, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [65529, 65535, 0, 0, 0, 0]).check Constraints.u32sub  -- true

-- Vector 21: u32mul  s=[65536, 65536, 0, 0]  s'=[0, 1, 0, 0]  h=[0, 0, 1, 0, 12297829378178067115, 0]
#eval (Frame.ofLists
  [65536, 65536, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [0, 0, 1, 0, 12297829378178067115, 0]).check Constraints.u32mul  -- true

-- Vector 22: u32mul  s=[7, 11, 0, 0]  s'=[77, 0, 0, 0]  h=[77, 0, 0, 0, 18446744065119617025, 0]
#eval (Frame.ofLists
  [7, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [77, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [77, 0, 0, 0, 18446744065119617025, 0]).check Constraints.u32mul  -- true

-- Vector 23: u32madd  s=[3, 5, 10, 0]  s'=[25, 0, 0, 0]  h=[25, 0, 0, 0, 18446744065119617025, 0]
#eval (Frame.ofLists
  [3, 5, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [25, 0, 0, 0, 18446744065119617025, 0]).check Constraints.u32madd  -- true

-- Vector 24: u32div  s=[3, 10, 0, 0]  s'=[1, 3, 0, 0]  h=[7, 0, 1, 0, 0, 0]
#eval (Frame.ofLists
  [3, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [7, 0, 1, 0, 0, 0]).check Constraints.u32div  -- true

-- Vector 25: u32assert2  s=[100, 200, 0, 0]  s'=[100, 200, 0, 0]  h=[200, 0, 100, 0, 0, 0]
#eval (Frame.ofLists
  [100, 200, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [100, 200, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  [200, 0, 100, 0, 0, 0]).check Constraints.u32assert2  -- true

end MidenLean.AIR.Tests.StackArith
