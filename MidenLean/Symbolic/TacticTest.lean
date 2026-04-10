import MidenLean.Proofs.Tactics
import MidenLean.Symbolic.Tactic
import MidenLean.Generated.U64

/-!
# Tactic Validation (Phase 2, Deliverable 2.7)

Tests the `miden_reflect` tactic on real procedures.
After `miden_reflect`, either only semantic precondition obligations remain
or the whole theorem closes if the block has no residual side conditions.
-/

namespace MidenLean.Symbolic.TacticTest

open MidenLean

set_option maxHeartbeats 800000 in
/-- u64::eq proved via `miden_reflect` tactic.
    Compare with the manual 20-line proof in Reflect.lean. -/
theorem u64_eq_via_tactic (b_lo b_hi a_lo a_hi : Felt) (rest : List Felt)
    (frames : List LocalFrame) :
    MidenLean.exec 10 ⟨b_lo :: b_hi :: a_lo :: a_hi :: rest, fun _ => (0 : Felt), frames, []⟩
      Miden.Core.U64.eq =
    some ⟨((if b_lo == a_lo then (1 : Felt) else 0) *
           (if b_hi == a_hi then (1 : Felt) else 0)) :: rest,
          fun _ => (0 : Felt), frames, []⟩ := by
  miden_reflect
  all_goals miden_finish_reflection

set_option maxHeartbeats 800000 in
/-- Test `miden_reflect` with `cdrop` (condition = 1). -/
theorem cdrop_test (a b : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) :
    MidenLean.exec 10
      ⟨(1 : Felt) :: b :: a :: rest, mem, frames, []⟩
      ⟨"test_cdrop", 0, [.inst .cdrop]⟩ =
    some ⟨b :: rest, mem, frames, []⟩ := by
  miden_reflect

set_option maxHeartbeats 800000 in
/-- Test `miden_reflect` with `cswap` (condition = 1). -/
theorem cswap_test (a b : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) :
    MidenLean.exec 10
      ⟨(1 : Felt) :: b :: a :: rest, mem, frames, []⟩
      ⟨"test_cswap", 0, [.inst .cswap]⟩ =
    some ⟨a :: b :: rest, mem, frames, []⟩ := by
  miden_reflect

set_option maxHeartbeats 800000 in
/-- Test `miden_reflect` with `u32Test`. -/
theorem u32Test_test (a : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) :
    MidenLean.exec 10
      ⟨a :: rest, mem, frames, []⟩
      ⟨"test_u32test", 0, [.inst .u32Test]⟩ =
    some ⟨(if a.isU32 then (1 : Felt) else 0) :: a :: rest, mem, frames, []⟩ := by
  miden_reflect

set_option maxHeartbeats 800000 in
/-- Test `miden_reflect` with `advPush`. -/
theorem advPush_test (a : Felt) (v0 v1 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) :
    MidenLean.exec 10
      ⟨a :: rest, mem, frames, [v0, v1]⟩
      ⟨"test_advpush", 0, [.inst (.advPush 2)]⟩ =
    some ⟨v1 :: v0 :: a :: rest, mem, frames, []⟩ := by
  miden_reflect

set_option maxHeartbeats 800000 in
/-- Test `miden_reflect` on a zero-input block. -/
theorem emitImm_empty_stack_test
    (mem : Nat → Felt) (frames : List LocalFrame) :
    MidenLean.exec 10
      ⟨[], mem, frames, []⟩
      ⟨"test_emitimm", 0, [.inst (.emitImm 42)]⟩ =
    some ⟨[], mem, frames, []⟩ := by
  miden_reflect

set_option maxHeartbeats 800000 in
/-- Test `miden_reflect` with `advLoadW`. -/
theorem advLoadW_test (s0 s1 s2 s3 tail : Felt) (v0 v1 v2 v3 : Felt) (rest : List Felt)
    (mem : Nat → Felt) (frames : List LocalFrame) :
    MidenLean.exec 10
      ⟨s0 :: s1 :: s2 :: s3 :: tail :: rest, mem, frames, [v0, v1, v2, v3]⟩
      ⟨"test_advloadw", 0, [.inst .advLoadW]⟩ =
    some ⟨v0 :: v1 :: v2 :: v3 :: tail :: rest, mem, frames, []⟩ := by
  miden_reflect

set_option maxHeartbeats 800000 in
/-- Test `miden_reflect` with `memStoreImm` + `memLoadImm`. -/
theorem memStoreLoad_test (a : Felt) (rest : List Felt)
    (frames : List LocalFrame) :
    MidenLean.exec 10
      ⟨a :: rest, fun _ => (0 : Felt), frames, []⟩
      ⟨"test_memstoreload", 0, [.inst (.memStoreImm 100), .inst (.memLoadImm 100)]⟩ =
    some ⟨a :: rest, fun addr => if addr = 100 then a else (0 : Felt), frames, []⟩ := by
  miden_reflect

set_option maxHeartbeats 800000 in
/-- Test `miden_reflect` with `locaddr`. -/
theorem locaddr_test (rest : List Felt)
    (mem : Nat → Felt) :
    MidenLean.exec 10
      ⟨rest, mem, [], []⟩
      ⟨"test_locaddr", 4, [.inst (.locaddr 0)]⟩ =
    some ⟨Felt.ofNat
      (({ base := 0, numLocals := 4, alignedNumLocals := MidenLean.alignLocals 4 } : LocalFrame).localAddr 0) ::
      rest, mem, [], []⟩ := by
  miden_reflect

set_option maxHeartbeats 1600000 in
/-- Test `miden_reflect` with `locStorewBe` + `locLoadwBe`. -/
theorem locStorewBeLoadwBe_test (w0 w1 w2 w3 tail : Felt) (rest : List Felt)
    :
    MidenLean.exec 10
      ⟨w0 :: w1 :: w2 :: w3 :: tail :: rest, fun _ => (0 : Felt), [], []⟩
      ⟨"test_locstorewbeloadwbe", 4, [.inst (.locStorewBe 0), .inst (.locLoadwBe 0)]⟩ =
    some ⟨w0 :: w1 :: w2 :: w3 :: tail :: rest,
          fun addr =>
            if addr = MidenLean.LOCAL_MEM_BASE then w3
            else if addr = MidenLean.LOCAL_MEM_BASE + 1 then w2
            else if addr = MidenLean.LOCAL_MEM_BASE + 2 then w1
            else if addr = MidenLean.LOCAL_MEM_BASE + 3 then w0
            else (0 : Felt),
          [],
          []⟩ := by
  miden_reflect

set_option maxHeartbeats 800000 in
/-- Test `miden_reflect` on the `numLocals > 0` path with `locStore` + `locLoad`. -/
theorem locStoreLoad_test (a b : Felt) (rest : List Felt)
    :
    MidenLean.exec 10
      ⟨a :: b :: rest, fun _ => (0 : Felt), [], []⟩
      ⟨"test_locstoreload", 2, [.inst (.locStore 0), .inst (.locLoad 0)]⟩ =
    some ⟨a :: b :: rest,
          fun addr => if addr = MidenLean.LOCAL_MEM_BASE then a else (0 : Felt),
          [],
          []⟩ := by
  miden_reflect

/--
error: miden_reflect: `.exec` target "lt" is missing from the concrete `ProcEnv`. Use `execProcedure` with a reducible environment or pass `using Γ`.
-/
#guard_msgs in
example (x : Felt) (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) :
    MidenLean.exec 10
      ⟨x :: rest, mem, frames, []⟩
      ⟨"test_bad_exec", 0, [.inst (.exec "lt")]⟩ =
    some ⟨x :: rest, mem, frames, []⟩ := by
  miden_reflect

/--
error: miden_reflect: op Op.ifElse [Op.inst Instruction.add]
  [Op.inst
      Instruction.sub] at position 0 is outside the supported straight-line fragment: control-flow op `ifElse` is unsupported. Use `miden_vcg` or manual chunking.
-/
#guard_msgs in
example (x y : Felt) (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) :
    MidenLean.exec 10
      ⟨x :: y :: rest, mem, frames, []⟩
      ⟨"test_bad_ifelse", 0, [Op.ifElse [Op.inst .add] [Op.inst .sub]]⟩ =
    some ⟨x :: y :: rest, mem, frames, []⟩ := by
  miden_reflect

/--
error: miden_reflect: op Op.inst
  Instruction.memLoad at position 0 is outside the supported straight-line fragment: dynamic-address memory instruction `memLoad` is unsupported. Use manual chunking or extend the symbolic executor first.
-/
#guard_msgs in
example (addr : Felt) (rest : List Felt) (mem : Nat → Felt) (frames : List LocalFrame) :
    MidenLean.exec 10
      ⟨addr :: rest, mem, frames, []⟩
      ⟨"test_bad_memload", 0, [.inst .memLoad]⟩ =
    some ⟨addr :: rest, mem, frames, []⟩ := by
  miden_reflect

end MidenLean.Symbolic.TacticTest
