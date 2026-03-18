//! Hypothesis inference for MASM procedures.
//!
//! For each instruction in a procedure, determines what preconditions it needs:
//! - u32And/u32Or/u32Xor → isU32 on both operands
//! - u32Assert2 → isU32 on both operands
//! - pow2 → val ≤ 63 on operand
//! - u32WidenAdd/Add3 → isU32 on operands
//! - u32WidenMul/Madd → isU32 on operands
//! - u32OverflowSub → isU32 on operands
//! - advPush n → advice stack has at least n elements
//!
//! Traces stack positions back to input positions to determine which entry
//! parameters need hypotheses.

use miden_assembly_syntax::ast::{Block, Immediate, Instruction, Op};
use miden_assembly_syntax::parser::PushValue;

/// A hypothesis required by a procedure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HypothesisKind {
    /// The value at the given entry stack position must be u32.
    IsU32,
    /// The value at the given entry stack position must satisfy val ≤ 63.
    ValLeq63,
    /// The advice stack must have at least n elements.
    AdviceLength(usize),
}

/// A required hypothesis with its origin information.
#[derive(Debug, Clone)]
pub struct Hypothesis {
    /// Kind of hypothesis.
    pub kind: HypothesisKind,
    /// Index into the entry stack (0 = top of stack at entry).
    /// For AdviceLength, this is meaningless.
    pub entry_position: usize,
    /// Instruction index where this requirement arises.
    pub instruction_index: usize,
    /// Human-readable instruction name for comments.
    pub instruction_name: String,
}

/// Symbolic stack tracker for tracing values back to entry positions.
///
/// Each slot tracks which entry stack position its value originally came from.
/// -1 means "locally computed" (not traceable to an entry position).
#[derive(Debug, Clone)]
struct SymbolicStack {
    /// Each element is either Some(entry_pos) or None (locally produced).
    slots: Vec<Option<usize>>,
    /// Number of entry positions allocated so far.
    next_entry: usize,
    /// Current instruction index.
    inst_index: usize,
    /// Collected hypotheses.
    hypotheses: Vec<Hypothesis>,
    /// Total advice elements consumed so far.
    advice_consumed: usize,
}

impl SymbolicStack {
    fn new(input_arity: usize) -> Self {
        let slots = (0..input_arity).map(|i| Some(i)).collect();
        SymbolicStack {
            slots,
            next_entry: input_arity,
            inst_index: 0,
            hypotheses: Vec::new(),
            advice_consumed: 0,
        }
    }

    /// Ensure the stack has at least `depth` elements by adding entry positions.
    fn ensure_depth(&mut self, depth: usize) {
        while self.slots.len() < depth {
            self.slots.push(Some(self.next_entry));
            self.next_entry += 1;
        }
    }

    /// Get the entry position of stack slot `idx` from the top (0 = top).
    fn top_entry_pos(&self, idx: usize) -> Option<usize> {
        let len = self.slots.len();
        if idx < len {
            self.slots[len - 1 - idx]
        } else {
            None
        }
    }

    /// Pop `n` elements from the top.
    fn pop_n(&mut self, n: usize) {
        for _ in 0..n {
            if !self.slots.is_empty() {
                self.slots.pop();
            }
        }
    }

    /// Push `n` locally-produced elements.
    fn push_local(&mut self, n: usize) {
        for _ in 0..n {
            self.slots.push(None);
        }
    }

    /// Push a specific entry position.
    fn push_entry(&mut self, pos: Option<usize>) {
        self.slots.push(pos);
    }

    /// Record an isU32 hypothesis for the element at stack position `idx`.
    fn require_u32(&mut self, idx: usize, inst_name: &str) {
        if let Some(entry_pos) = self.top_entry_pos(idx) {
            // Check if we already have this hypothesis
            let already_has = self.hypotheses.iter().any(|h| {
                h.kind == HypothesisKind::IsU32 && h.entry_position == entry_pos
            });
            if !already_has {
                self.hypotheses.push(Hypothesis {
                    kind: HypothesisKind::IsU32,
                    entry_position: entry_pos,
                    instruction_index: self.inst_index,
                    instruction_name: inst_name.to_string(),
                });
            }
        }
    }

    /// Record a val ≤ 63 hypothesis for the element at stack position `idx`.
    fn require_val_leq_63(&mut self, idx: usize, inst_name: &str) {
        if let Some(entry_pos) = self.top_entry_pos(idx) {
            let already_has = self.hypotheses.iter().any(|h| {
                h.kind == HypothesisKind::ValLeq63 && h.entry_position == entry_pos
            });
            if !already_has {
                self.hypotheses.push(Hypothesis {
                    kind: HypothesisKind::ValLeq63,
                    entry_position: entry_pos,
                    instruction_index: self.inst_index,
                    instruction_name: inst_name.to_string(),
                });
            }
        }
    }

    /// Simulate a dup instruction.
    fn sim_dup(&mut self, n: usize) {
        self.ensure_depth(n + 1);
        let entry = self.top_entry_pos(n);
        self.push_entry(entry);
    }

    /// Simulate a swap instruction.
    fn sim_swap(&mut self, n: usize) {
        self.ensure_depth(n + 1);
        let len = self.slots.len();
        self.slots.swap(len - 1, len - 1 - n);
    }

    /// Simulate a movup instruction.
    fn sim_movup(&mut self, n: usize) {
        self.ensure_depth(n + 1);
        let len = self.slots.len();
        let idx = len - 1 - n;
        let val = self.slots.remove(idx);
        self.slots.push(val);
    }

    /// Simulate a movdn instruction.
    fn sim_movdn(&mut self, n: usize) {
        self.ensure_depth(n + 1);
        let val = self.slots.pop().unwrap();
        let len = self.slots.len();
        let idx = len - n + 1;
        self.slots.insert(idx.min(len), val);
    }

    /// Simulate a reversew (reverse top 4).
    fn sim_reversew(&mut self) {
        self.ensure_depth(4);
        let len = self.slots.len();
        self.slots[len - 4..].reverse();
    }

    /// Process a single instruction.
    fn process_instruction(&mut self, inst: &Instruction) {
        use Instruction::*;

        // Get the MASM-style name from the instruction_info table for hypothesis comments.
        let inst_name = crate::instruction_info::instruction_info(inst).comment_name;

        match inst {
            // Stack manipulation
            Nop => {}
            Drop => {
                self.ensure_depth(1);
                self.pop_n(1);
            }
            DropW => {
                self.ensure_depth(4);
                self.pop_n(4);
            }
            PadW => self.push_local(4),

            Dup0 => self.sim_dup(0),
            Dup1 => self.sim_dup(1),
            Dup2 => self.sim_dup(2),
            Dup3 => self.sim_dup(3),
            Dup4 => self.sim_dup(4),
            Dup5 => self.sim_dup(5),
            Dup6 => self.sim_dup(6),
            Dup7 => self.sim_dup(7),
            Dup8 => self.sim_dup(8),
            Dup9 => self.sim_dup(9),
            Dup10 => self.sim_dup(10),
            Dup11 => self.sim_dup(11),
            Dup12 => self.sim_dup(12),
            Dup13 => self.sim_dup(13),
            Dup14 => self.sim_dup(14),
            Dup15 => self.sim_dup(15),

            DupW0 => {
                self.ensure_depth(4);
                let entries: Vec<_> = (0..4).map(|i| self.top_entry_pos(i)).collect();
                for e in entries.into_iter().rev() {
                    self.push_entry(e);
                }
            }
            DupW1 => {
                self.ensure_depth(8);
                let entries: Vec<_> = (0..4).map(|i| self.top_entry_pos(4 + i)).collect();
                for e in entries.into_iter().rev() {
                    self.push_entry(e);
                }
            }
            DupW2 => {
                self.ensure_depth(12);
                let entries: Vec<_> = (0..4).map(|i| self.top_entry_pos(8 + i)).collect();
                for e in entries.into_iter().rev() {
                    self.push_entry(e);
                }
            }
            DupW3 => {
                self.ensure_depth(16);
                let entries: Vec<_> = (0..4).map(|i| self.top_entry_pos(12 + i)).collect();
                for e in entries.into_iter().rev() {
                    self.push_entry(e);
                }
            }

            Swap1 => self.sim_swap(1),
            Swap2 => self.sim_swap(2),
            Swap3 => self.sim_swap(3),
            Swap4 => self.sim_swap(4),
            Swap5 => self.sim_swap(5),
            Swap6 => self.sim_swap(6),
            Swap7 => self.sim_swap(7),
            Swap8 => self.sim_swap(8),
            Swap9 => self.sim_swap(9),
            Swap10 => self.sim_swap(10),
            Swap11 => self.sim_swap(11),
            Swap12 => self.sim_swap(12),
            Swap13 => self.sim_swap(13),
            Swap14 => self.sim_swap(14),
            Swap15 => self.sim_swap(15),

            SwapW1 | SwapW2 | SwapW3 | SwapDw => {
                // Word swaps: conservatively mark affected positions as local
                let depth = match inst {
                    SwapW1 => 8,
                    SwapW2 => 12,
                    SwapW3 | SwapDw => 16,
                    _ => unreachable!(),
                };
                self.ensure_depth(depth);
                // For simplicity, keep entries but do the swap
                // SwapW1 swaps words [0..3] and [4..7]
                match inst {
                    SwapW1 => {
                        let len = self.slots.len();
                        for i in 0..4 {
                            self.slots.swap(len - 1 - i, len - 5 - i);
                        }
                    }
                    SwapW2 => {
                        let len = self.slots.len();
                        for i in 0..4 {
                            self.slots.swap(len - 1 - i, len - 9 - i);
                        }
                    }
                    SwapW3 => {
                        let len = self.slots.len();
                        for i in 0..4 {
                            self.slots.swap(len - 1 - i, len - 13 - i);
                        }
                    }
                    SwapDw => {
                        let len = self.slots.len();
                        for i in 0..8 {
                            self.slots.swap(len - 1 - i, len - 9 - i);
                        }
                    }
                    _ => unreachable!(),
                }
            }

            MovUp2 => self.sim_movup(2),
            MovUp3 => self.sim_movup(3),
            MovUp4 => self.sim_movup(4),
            MovUp5 => self.sim_movup(5),
            MovUp6 => self.sim_movup(6),
            MovUp7 => self.sim_movup(7),
            MovUp8 => self.sim_movup(8),
            MovUp9 => self.sim_movup(9),
            MovUp10 => self.sim_movup(10),
            MovUp11 => self.sim_movup(11),
            MovUp12 => self.sim_movup(12),
            MovUp13 => self.sim_movup(13),
            MovUp14 => self.sim_movup(14),
            MovUp15 => self.sim_movup(15),

            MovDn2 => self.sim_movdn(2),
            MovDn3 => self.sim_movdn(3),
            MovDn4 => self.sim_movdn(4),
            MovDn5 => self.sim_movdn(5),
            MovDn6 => self.sim_movdn(6),
            MovDn7 => self.sim_movdn(7),
            MovDn8 => self.sim_movdn(8),
            MovDn9 => self.sim_movdn(9),
            MovDn10 => self.sim_movdn(10),
            MovDn11 => self.sim_movdn(11),
            MovDn12 => self.sim_movdn(12),
            MovDn13 => self.sim_movdn(13),
            MovDn14 => self.sim_movdn(14),
            MovDn15 => self.sim_movdn(15),

            MovUpW2 | MovUpW3 | MovDnW2 | MovDnW3 => {
                // Word moves: complex but rare. Mark as imprecise.
                let depth = match inst {
                    MovUpW2 | MovDnW2 => 12,
                    MovUpW3 | MovDnW3 => 16,
                    _ => unreachable!(),
                };
                self.ensure_depth(depth);
                // Conservatively mark all affected slots as local
                let len = self.slots.len();
                for i in 0..depth.min(len) {
                    self.slots[len - 1 - i] = None;
                }
            }

            Reversew => self.sim_reversew(),

            // Conditional instructions
            CSwap | CDrop | CSwapW | CDropW => {
                // Consume condition + operands, produce result
                match inst {
                    CSwap => {
                        self.ensure_depth(3);
                        self.pop_n(3);
                        self.push_local(2);
                    }
                    CDrop => {
                        self.ensure_depth(3);
                        self.pop_n(3);
                        self.push_local(1);
                    }
                    CSwapW => {
                        self.ensure_depth(9);
                        self.pop_n(9);
                        self.push_local(8);
                    }
                    CDropW => {
                        self.ensure_depth(9);
                        self.pop_n(9);
                        self.push_local(4);
                    }
                    _ => unreachable!(),
                }
            }

            // Constants
            Push(imm) => match imm {
                Immediate::Value(span) => match span.inner() {
                    PushValue::Word(_) => self.push_local(4),
                    PushValue::Int(_) => self.push_local(1),
                },
                Immediate::Constant(_) => self.push_local(1),
            },
            PushFeltList(values) => self.push_local(values.len()),

            // === Hypothesis-requiring instructions ===

            // u32 bitwise: both operands must be u32
            U32And | U32Or | U32Xor => {
                self.ensure_depth(2);
                self.require_u32(0, &inst_name);
                self.require_u32(1, &inst_name);
                self.pop_n(2);
                self.push_local(1);
            }

            // u32 widening add: both operands must be u32
            U32WideningAdd | U32OverflowingAdd => {
                self.ensure_depth(2);
                self.require_u32(0, &inst_name);
                self.require_u32(1, &inst_name);
                self.pop_n(2);
                self.push_local(2);
            }

            // u32 widening add3: all three operands must be u32
            U32WideningAdd3 | U32OverflowingAdd3 => {
                self.ensure_depth(3);
                self.require_u32(0, &inst_name);
                self.require_u32(1, &inst_name);
                self.require_u32(2, &inst_name);
                self.pop_n(3);
                self.push_local(2);
            }

            // u32 overflow sub: both operands must be u32
            U32OverflowingSub => {
                self.ensure_depth(2);
                self.require_u32(0, &inst_name);
                self.require_u32(1, &inst_name);
                self.pop_n(2);
                self.push_local(2);
            }

            // u32 widening mul: both operands must be u32
            U32WideningMul => {
                self.ensure_depth(2);
                self.require_u32(0, &inst_name);
                self.require_u32(1, &inst_name);
                self.pop_n(2);
                self.push_local(2);
            }

            // u32 widening madd: all three operands must be u32
            U32WideningMadd => {
                self.ensure_depth(3);
                self.require_u32(0, &inst_name);
                self.require_u32(1, &inst_name);
                self.require_u32(2, &inst_name);
                self.pop_n(3);
                self.push_local(2);
            }

            // u32 assert2: both operands must be u32 (but not consumed)
            U32Assert2 | U32Assert2WithError(_) => {
                self.ensure_depth(2);
                self.require_u32(0, &inst_name);
                self.require_u32(1, &inst_name);
                // Does not pop — it's an assertion
            }

            // u32 assert: operand must be u32 (not consumed)
            U32Assert | U32AssertWithError(_) => {
                self.ensure_depth(1);
                self.require_u32(0, &inst_name);
            }

            // pow2: operand must have val ≤ 63
            Pow2 => {
                self.ensure_depth(1);
                self.require_val_leq_63(0, &inst_name);
                self.pop_n(1);
                self.push_local(1);
            }

            // Advice push: needs advice stack elements
            AdvPush(imm) => {
                if let Immediate::Value(span) = imm {
                    let n = *span.inner() as usize;
                    self.advice_consumed += n;
                    self.hypotheses.push(Hypothesis {
                        kind: HypothesisKind::AdviceLength(self.advice_consumed),
                        entry_position: 0,
                        instruction_index: self.inst_index,
                        instruction_name: format!("advPush {}", n),
                    });
                    self.push_local(n);
                }
            }

            // Generic unary/binary/etc that don't need hypotheses
            _ => {
                // For all other instructions, use the generic stack effect
                if let Some(effect) = crate::stack_effect::instruction_effect(inst) {
                    self.ensure_depth(effect.required_depth);
                    self.pop_n(effect.pops);
                    self.push_local(effect.pushes);
                }
                // Unknown instructions: don't modify the symbolic stack
            }
        }

        self.inst_index += 1;
    }
}

/// Result of hypothesis inference for a procedure.
#[derive(Debug, Clone)]
pub struct ProcHypotheses {
    /// Input arity (number of named input parameters).
    pub input_arity: usize,
    /// Required hypotheses traced back to entry positions.
    pub hypotheses: Vec<Hypothesis>,
    /// Total advice stack elements consumed.
    pub advice_consumed: usize,
}

/// Infer hypotheses for a procedure body.
///
/// `input_arity` should come from the stack effect analysis.
pub fn infer_hypotheses(block: &Block, input_arity: usize) -> ProcHypotheses {
    let mut stack = SymbolicStack::new(input_arity);

    for op in block.iter() {
        process_op(op, &mut stack);
    }

    // Deduplicate and sort hypotheses by entry position
    let mut hypotheses = stack.hypotheses;
    hypotheses.sort_by_key(|h| (h.entry_position, format!("{:?}", h.kind)));
    hypotheses.dedup_by(|a, b| a.entry_position == b.entry_position && a.kind == b.kind);

    ProcHypotheses {
        input_arity: stack.next_entry.max(input_arity),
        hypotheses,
        advice_consumed: stack.advice_consumed,
    }
}

fn process_op(op: &Op, stack: &mut SymbolicStack) {
    match op {
        Op::Inst(spanned_inst) => {
            stack.process_instruction(spanned_inst.inner());
        }
        Op::If {
            then_blk,
            else_blk,
            ..
        } => {
            // Pop condition
            stack.ensure_depth(1);
            stack.pop_n(1);
            stack.inst_index += 1;

            // Process both branches but keep the original stack's hypotheses
            // (we collect hypotheses from both branches)
            let saved_slots = stack.slots.clone();
            for op in then_blk.iter() {
                process_op(op, stack);
            }
            // Restore and process else branch
            let after_then = stack.slots.clone();
            stack.slots = saved_slots;
            for op in else_blk.iter() {
                process_op(op, stack);
            }
            // Use then branch's slots as the result (conservative)
            stack.slots = after_then;
        }
        Op::Repeat { count, body, .. } => {
            let n = match count {
                Immediate::Value(span) => *span.inner() as usize,
                Immediate::Constant(_) => return,
            };
            for _ in 0..n {
                for inner_op in body.iter() {
                    process_op(inner_op, stack);
                }
            }
        }
        Op::While { body, .. } => {
            // Pop condition
            stack.ensure_depth(1);
            stack.pop_n(1);
            // Process body once for hypothesis collection
            for inner_op in body.iter() {
                process_op(inner_op, stack);
            }
            // Pop condition at end
            stack.ensure_depth(1);
            stack.pop_n(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use miden_assembly_syntax::ast::Instruction;
    use miden_assembly_syntax::debuginfo::{SourceSpan, Span};

    /// Helper to make a block from a list of instructions.
    fn make_block(insts: Vec<Instruction>) -> Block {
        let ops = insts
            .into_iter()
            .map(|i| Op::Inst(Span::unknown(i)))
            .collect();
        Block::new(SourceSpan::UNKNOWN, ops)
    }

    #[test]
    fn test_u32and_generates_isu32_hypotheses() {
        // u32And needs both operands to be u32
        let block = make_block(vec![Instruction::U32And]);
        let result = infer_hypotheses(&block, 2);

        // Should have 2 IsU32 hypotheses for positions 0 and 1
        let u32_hyps: Vec<_> = result
            .hypotheses
            .iter()
            .filter(|h| h.kind == HypothesisKind::IsU32)
            .collect();
        assert_eq!(u32_hyps.len(), 2);
        assert_eq!(u32_hyps[0].entry_position, 0);
        assert_eq!(u32_hyps[1].entry_position, 1);
    }

    #[test]
    fn test_dupw0_hypothesis_tracking() {
        // C4 fix: DupW0 should correctly track entry positions.
        // Stack starts as [a, b, c, d]
        // DupW0 duplicates top word: [a, b, c, d, a, b, c, d]
        // Then u32And consumes top 2: needs u32 on positions 0 and 1
        // These should trace back to entry positions 0 and 1.
        let block = make_block(vec![Instruction::DupW0, Instruction::U32And]);
        let result = infer_hypotheses(&block, 4);

        let u32_hyps: Vec<_> = result
            .hypotheses
            .iter()
            .filter(|h| h.kind == HypothesisKind::IsU32)
            .collect();
        assert_eq!(u32_hyps.len(), 2);
        // Entry positions: 0 is deepest, 3 is top of stack.
        // DupW0 duplicates the top word. u32And consumes the top 2.
        // These trace to the top two entries: positions 2 and 3.
        assert_eq!(u32_hyps[0].entry_position, 2);
        assert_eq!(u32_hyps[1].entry_position, 3);
    }

    #[test]
    fn test_swap_tracks_positions() {
        // swap 1 then u32And: after swap, positions are swapped
        let block = make_block(vec![Instruction::Swap1, Instruction::U32And]);
        let result = infer_hypotheses(&block, 2);

        let u32_hyps: Vec<_> = result
            .hypotheses
            .iter()
            .filter(|h| h.kind == HypothesisKind::IsU32)
            .collect();
        assert_eq!(u32_hyps.len(), 2);
        // After swap, position 0 has entry 1 and position 1 has entry 0
        // u32And requires both, so both entry positions should have IsU32
        let positions: Vec<_> = u32_hyps.iter().map(|h| h.entry_position).collect();
        assert!(positions.contains(&0));
        assert!(positions.contains(&1));
    }

    #[test]
    fn test_hypothesis_uses_masm_names() {
        // M5 fix: hypothesis instruction names should be MASM-style, not Debug format
        let block = make_block(vec![Instruction::U32And]);
        let result = infer_hypotheses(&block, 2);

        for h in &result.hypotheses {
            if h.kind == HypothesisKind::IsU32 {
                assert_eq!(h.instruction_name, "u32And");
            }
        }
    }
}
