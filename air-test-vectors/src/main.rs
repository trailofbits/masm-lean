//! Generates AIR constraint test vectors from the Miden VM.
//!
//! For each stack_arith operation, executes it in the VM, captures the
//! transition frame (current row + next row), and outputs JSON that can
//! be compared against the Lean constraint evaluator.

use miden_air::trace::RowIndex;
use miden_core::advice::AdviceInputs;
use miden_core::mast::{BasicBlockNodeBuilder, MastForest, MastForestContributor};
use miden_core::operations::Operation;
use miden_core::program::Program;
use miden_core::Felt;
use miden_processor::trace::{ExecutionTrace, build_trace};
use miden_processor::{DefaultHost, ExecutionOptions, FastProcessor, StackInputs};
use serde::Serialize;

/// A transition frame extracted from the VM trace.
#[derive(Serialize, Debug)]
struct TestVector {
    /// Operation name (matches Lean constraint set name).
    op: String,
    /// Stack columns s0..s15 in the current row.
    s: Vec<u64>,
    /// Stack columns s0'..s15' in the next row.
    s_next: Vec<u64>,
    /// Helper registers h0..h5 in the current row.
    h: Vec<u64>,
    /// Stack depth (b0) in the current row.
    b0: u64,
    /// Stack depth (b0') in the next row.
    b0_next: u64,
    /// Whether constraints should be satisfied (true for positive vectors).
    expect_satisfied: bool,
}

/// Execute a list of operations with the given initial stack and return the trace.
/// Uses the same approach as the Miden processor tests.
fn execute_ops(operations: Vec<Operation>, stack: &[u64]) -> ExecutionTrace {
    let mut mast_forest = MastForest::new();
    let basic_block_id = BasicBlockNodeBuilder::new(operations, Vec::new())
        .add_to_forest(&mut mast_forest)
        .unwrap();
    mast_forest.make_root(basic_block_id);
    let program = Program::new(mast_forest.into(), basic_block_id);

    let felts: Vec<Felt> = stack.iter().map(|&v| Felt::new(v)).collect();
    let stack_inputs = StackInputs::new(&felts).unwrap();
    let mut host = DefaultHost::default();
    let processor = FastProcessor::new_with_options(
        stack_inputs,
        AdviceInputs::default(),
        ExecutionOptions::default(),
    );
    let (execution_output, trace_generation_context) =
        processor.execute_for_trace_sync(&program, &mut host).unwrap();

    build_trace(execution_output, trace_generation_context, program.to_info()).unwrap()
}

/// Extracted frame data: (s, s_next, h, b0, b0_next).
struct FrameData {
    s: Vec<u64>,
    s_next: Vec<u64>,
    h: Vec<u64>,
    b0: u64,
    b0_next: u64,
}

/// Extract a transition frame (row i → row i+1) from the trace.
fn extract_frame(trace: &ExecutionTrace, row: usize) -> FrameData {
    let main = trace.main_trace();
    let curr = RowIndex::from(row);
    let next = RowIndex::from(row + 1);

    let s: Vec<u64> = (0..16)
        .map(|i| main.stack_element(i, curr).as_canonical_u64())
        .collect();
    let s_next: Vec<u64> = (0..16)
        .map(|i| main.stack_element(i, next).as_canonical_u64())
        .collect();
    let h: Vec<u64> = (0..6)
        .map(|i| main.helper_register(i, curr).as_canonical_u64())
        .collect();
    let b0 = main.stack_depth(curr).as_canonical_u64();
    let b0_next = main.stack_depth(next).as_canonical_u64();

    FrameData { s, s_next, h, b0, b0_next }
}

/// Generate a positive test vector for an operation.
/// The operation executes at row 1 (row 0 is SPAN setup).
/// `balance_ops` are appended after the target op to balance the stack depth
/// so the program doesn't trigger OutputStackOverflow.
fn gen_vector(
    op_name: &str,
    operation: Operation,
    stack: &[u64],
    balance_ops: &[Operation],
) -> TestVector {
    let mut ops = vec![operation];
    ops.extend_from_slice(balance_ops);
    let trace = execute_ops(ops, stack);
    // Target op is always at row 1 (row 0 = SPAN)
    let fd = extract_frame(&trace, 1);
    TestVector {
        op: op_name.to_string(),
        s: fd.s,
        s_next: fd.s_next,
        h: fd.h,
        b0: fd.b0,
        b0_next: fd.b0_next,
        expect_satisfied: true,
    }
}

fn main() {
    let mut vectors: Vec<TestVector> = Vec::new();

    let no_balance: &[Operation] = &[];
    let drop1: &[Operation] = &[Operation::Drop]; // for ops that push +1

    // Field arithmetic (stack depth unchanged: pop 2 push 1 → -1, or pop 1 push 1 → 0)
    // ADD pops 2, pushes 1 → net -1. Need to start with ≥2 elements.
    vectors.push(gen_vector("add", Operation::Add, &[3, 5], no_balance));
    vectors.push(gen_vector("neg", Operation::Neg, &[7], no_balance));
    vectors.push(gen_vector("mul", Operation::Mul, &[3, 7], no_balance));
    vectors.push(gen_vector("inv", Operation::Inv, &[2], no_balance));
    vectors.push(gen_vector("incr", Operation::Incr, &[41], no_balance));
    vectors.push(gen_vector("not", Operation::Not, &[1], no_balance));
    vectors.push(gen_vector("and", Operation::And, &[1, 1], no_balance));
    vectors.push(gen_vector("or", Operation::Or, &[1, 0], no_balance));

    // EQ: equal case (5 == 5)
    vectors.push(gen_vector("eq", Operation::Eq, &[5, 5], no_balance));
    // EQ: unequal case (3 != 7)
    vectors.push(gen_vector("eq", Operation::Eq, &[3, 7], no_balance));

    // EQZ
    vectors.push(gen_vector("eqz", Operation::Eqz, &[0], no_balance));
    vectors.push(gen_vector("eqz", Operation::Eqz, &[5], no_balance));

    // EXPACC: stack = [exp_bit, exp, acc, exp_b, ...]
    vectors.push(gen_vector("expacc", Operation::Expacc, &[1, 3, 1, 7], no_balance));
    vectors.push(gen_vector("expacc", Operation::Expacc, &[0, 2, 5, 4], no_balance));

    // EXT2MUL: stack = [b0, b1, a0, a1, ...]
    vectors.push(gen_vector("ext2mul", Operation::Ext2Mul, &[2, 3, 5, 7], no_balance));

    // U32 operations
    // u32split: pops 1, pushes 2 → net +1 → need drop to balance
    vectors.push(gen_vector("u32split", Operation::U32split, &[4294967297], drop1));
    // u32add: pops 2, pushes 2 → net 0
    vectors.push(gen_vector("u32add", Operation::U32add, &[3, 5], no_balance));
    vectors.push(gen_vector("u32add", Operation::U32add, &[4294967295, 1], no_balance));
    // u32add3: pops 3, pushes 2 → net -1
    vectors.push(gen_vector("u32add3", Operation::U32add3, &[100, 200, 300], no_balance));
    // u32sub: pops 2, pushes 2 → net 0
    vectors.push(gen_vector("u32sub", Operation::U32sub, &[3, 10], no_balance));
    vectors.push(gen_vector("u32sub", Operation::U32sub, &[10, 3], no_balance));
    // u32mul: pops 2, pushes 2 → net 0
    vectors.push(gen_vector("u32mul", Operation::U32mul, &[65536, 65536], no_balance));
    vectors.push(gen_vector("u32mul", Operation::U32mul, &[7, 11], no_balance));
    // u32madd: pops 3, pushes 2 → net -1
    vectors.push(gen_vector("u32madd", Operation::U32madd, &[3, 5, 10], no_balance));
    // u32div: pops 2, pushes 2 → net 0
    vectors.push(gen_vector("u32div", Operation::U32div, &[3, 10], no_balance));
    // u32assert2: pops 0, pushes 0 (checks in-place)
    vectors.push(gen_vector(
        "u32assert2",
        Operation::U32assert2(Felt::ZERO),
        &[100, 200],
        no_balance,
    ));

    // ======================================================================
    // Stack manipulation operations (ops module)
    // ======================================================================

    // PAD: pushes 0 → net +1 → need drop to balance
    vectors.push(gen_vector("pad", Operation::Pad, &[10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 120, 130, 140, 150, 160], drop1));

    // DUP variants: all push +1 → need drop to balance
    vectors.push(gen_vector("dup", Operation::Dup0, &[42, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], drop1));
    vectors.push(gen_vector("dup1", Operation::Dup1, &[1, 42, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], drop1));
    vectors.push(gen_vector("dup2", Operation::Dup2, &[1, 2, 42, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], drop1));
    vectors.push(gen_vector("dup3", Operation::Dup3, &[1, 2, 3, 42, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], drop1));
    vectors.push(gen_vector("dup4", Operation::Dup4, &[1, 2, 3, 4, 42, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], drop1));
    vectors.push(gen_vector("dup5", Operation::Dup5, &[1, 2, 3, 4, 5, 42, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], drop1));
    vectors.push(gen_vector("dup6", Operation::Dup6, &[1, 2, 3, 4, 5, 6, 42, 8, 9, 10, 11, 12, 13, 14, 15, 16], drop1));
    vectors.push(gen_vector("dup7", Operation::Dup7, &[1, 2, 3, 4, 5, 6, 7, 42, 9, 10, 11, 12, 13, 14, 15, 16], drop1));
    vectors.push(gen_vector("dup9", Operation::Dup9, &[1, 2, 3, 4, 5, 6, 7, 8, 9, 42, 11, 12, 13, 14, 15, 16], drop1));
    vectors.push(gen_vector("dup11", Operation::Dup11, &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 42, 13, 14, 15, 16], drop1));
    vectors.push(gen_vector("dup13", Operation::Dup13, &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 42, 15, 16], drop1));
    vectors.push(gen_vector("dup15", Operation::Dup15, &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 42], drop1));

    // SWAP: net 0
    vectors.push(gen_vector("swap", Operation::Swap, &[10, 20, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], no_balance));

    // MOVUP variants: net 0
    vectors.push(gen_vector("movup2", Operation::MovUp2, &[1, 2, 42, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], no_balance));
    vectors.push(gen_vector("movup3", Operation::MovUp3, &[1, 2, 3, 42, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], no_balance));
    vectors.push(gen_vector("movup4", Operation::MovUp4, &[1, 2, 3, 4, 42, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], no_balance));
    vectors.push(gen_vector("movup5", Operation::MovUp5, &[1, 2, 3, 4, 5, 42, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], no_balance));
    vectors.push(gen_vector("movup6", Operation::MovUp6, &[1, 2, 3, 4, 5, 6, 42, 8, 9, 10, 11, 12, 13, 14, 15, 16], no_balance));
    vectors.push(gen_vector("movup7", Operation::MovUp7, &[1, 2, 3, 4, 5, 6, 7, 42, 9, 10, 11, 12, 13, 14, 15, 16], no_balance));
    vectors.push(gen_vector("movup8", Operation::MovUp8, &[1, 2, 3, 4, 5, 6, 7, 8, 42, 10, 11, 12, 13, 14, 15, 16], no_balance));

    // MOVDN variants: net 0
    vectors.push(gen_vector("movdn2", Operation::MovDn2, &[42, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], no_balance));
    vectors.push(gen_vector("movdn3", Operation::MovDn3, &[42, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], no_balance));
    vectors.push(gen_vector("movdn4", Operation::MovDn4, &[42, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], no_balance));
    vectors.push(gen_vector("movdn5", Operation::MovDn5, &[42, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], no_balance));
    vectors.push(gen_vector("movdn6", Operation::MovDn6, &[42, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], no_balance));
    vectors.push(gen_vector("movdn7", Operation::MovDn7, &[42, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], no_balance));
    vectors.push(gen_vector("movdn8", Operation::MovDn8, &[42, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], no_balance));

    // SWAPW: net 0
    vectors.push(gen_vector("swapw", Operation::SwapW, &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], no_balance));
    // SWAPW2: net 0
    vectors.push(gen_vector("swapw2", Operation::SwapW2, &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], no_balance));
    // SWAPW3: net 0
    vectors.push(gen_vector("swapw3", Operation::SwapW3, &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], no_balance));
    // SWAPDW: net 0
    vectors.push(gen_vector("swapdw", Operation::SwapDW, &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], no_balance));

    // CSWAP with condition=1: pops condition, swaps top 2 → net -1
    vectors.push(gen_vector("cswap", Operation::CSwap, &[1, 10, 20, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], no_balance));
    // CSWAP with condition=0: no swap
    vectors.push(gen_vector("cswap", Operation::CSwap, &[0, 10, 20, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], no_balance));
    // CSWAPW with condition=1: pops condition, swaps top 2 words → net -1
    vectors.push(gen_vector("cswapw", Operation::CSwapW, &[1, 10, 20, 30, 40, 50, 60, 70, 80, 9, 10, 11, 12, 13, 14, 15], no_balance));

    // ASSERT: pops 1 if s0=1 → net -1
    vectors.push(gen_vector("assert_op", Operation::Assert(Felt::ZERO), &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], no_balance));

    // SDEPTH: pushes stack depth → net +1 → need drop to balance
    vectors.push(gen_vector("sdepth", Operation::SDepth, &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16], drop1));

    // Output JSON
    let json = serde_json::to_string_pretty(&vectors).unwrap();
    println!("{json}");
}
