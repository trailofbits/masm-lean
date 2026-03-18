//! Stack effect analysis for MASM procedures.
//!
//! For each MASM instruction, computes:
//! - Input stack depth required
//! - Output stack depth change
//! - Which stack positions are consumed/produced
//!
//! For a List Op (procedure body), computes:
//! - Total input arity (minimum stack depth at entry)
//! - Output arity (stack depth at exit)
//! - Maximum stack depth during execution
//!
//! This is a simplified version of the decompiler's signature analysis,
//! tailored for proof skeleton generation.

use std::collections::HashMap;

use miden_assembly_syntax::ast::{Block, Immediate, Instruction, InvocationTarget, Op};

/// Stack effect of a single instruction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StackEffect {
    /// Number of elements consumed from the stack.
    pub pops: usize,
    /// Number of elements produced onto the stack.
    pub pushes: usize,
    /// Minimum stack depth required before execution.
    pub required_depth: usize,
}

impl StackEffect {
    pub const fn new(pops: usize, pushes: usize) -> Self {
        StackEffect {
            pops,
            pushes,
            required_depth: pops,
        }
    }

    pub const fn with_depth(pops: usize, pushes: usize, required_depth: usize) -> Self {
        StackEffect {
            pops,
            pushes,
            required_depth,
        }
    }

    /// Net change in stack depth.
    #[allow(dead_code)]
    pub fn net(&self) -> isize {
        self.pushes as isize - self.pops as isize
    }
}

/// Aggregate stack effect of a procedure or block.
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct ProcStackEffect {
    /// Number of input arguments consumed from the entry stack.
    pub input_arity: usize,
    /// Number of output values produced (above the remaining inputs).
    pub output_arity: usize,
    /// Net stack depth change (output_arity - consumed inputs).
    pub net_effect: isize,
    /// Total number of instructions in straight-line code (for fuel calculation).
    pub instruction_count: usize,
    /// Whether the procedure contains branches (if.true).
    pub has_branches: bool,
    /// Whether the procedure contains loops (while.true).
    pub has_loops: bool,
    /// Whether the procedure contains repeat blocks.
    pub has_repeats: bool,
    /// Whether the procedure makes procedure calls (exec).
    pub has_calls: bool,
    /// Whether the procedure uses advice stack (advPush).
    pub has_advice: bool,
    /// Whether the analysis was successful or fell back to conservative estimates.
    pub is_precise: bool,
}

/// Compute the stack effect of a single instruction.
/// Delegates to the consolidated `instruction_info` table.
pub fn instruction_effect(inst: &Instruction) -> Option<StackEffect> {
    crate::instruction_info::instruction_info(inst).stack_effect
}

/// Symbolic stack simulator for computing aggregate procedure stack effects.
struct StackSimulator<'a> {
    /// Current stack depth relative to entry (positive means deeper).
    current_depth: isize,
    /// Maximum required depth below the entry point.
    max_required: usize,
    /// Total instruction count for fuel calculation.
    instruction_count: usize,
    /// Feature flags.
    has_branches: bool,
    has_loops: bool,
    has_repeats: bool,
    has_calls: bool,
    has_advice: bool,
    /// Whether analysis was fully precise.
    is_precise: bool,
    /// Optional map of already-analyzed callee effects for inter-procedural analysis.
    callee_effects: Option<&'a HashMap<String, ProcStackEffect>>,
}

impl<'a> StackSimulator<'a> {
    fn new() -> Self {
        StackSimulator {
            current_depth: 0,
            max_required: 0,
            instruction_count: 0,
            has_branches: false,
            has_loops: false,
            has_repeats: false,
            has_calls: false,
            has_advice: false,
            is_precise: true,
            callee_effects: None,
        }
    }

    fn with_callee_effects(callee_effects: &'a HashMap<String, ProcStackEffect>) -> Self {
        StackSimulator {
            current_depth: 0,
            max_required: 0,
            instruction_count: 0,
            has_branches: false,
            has_loops: false,
            has_repeats: false,
            has_calls: false,
            has_advice: false,
            is_precise: true,
            callee_effects: Some(callee_effects),
        }
    }

    fn apply_effect(&mut self, effect: &StackEffect) {
        // The required depth at this point is: the instruction needs `required_depth`
        // elements. Some of those may have been pushed by prior instructions
        // (current_depth > 0), the rest come from the original stack.
        let needed_from_original = if self.current_depth >= 0 {
            effect
                .required_depth
                .saturating_sub(self.current_depth as usize)
        } else {
            effect.required_depth + (-self.current_depth) as usize
        };
        self.max_required = self.max_required.max(needed_from_original);

        self.current_depth -= effect.pops as isize;
        self.current_depth += effect.pushes as isize;
    }

    fn simulate_block(&mut self, block: &Block) -> bool {
        for op in block.iter() {
            if !self.simulate_op(op) {
                return false;
            }
        }
        true
    }

    fn simulate_op(&mut self, op: &Op) -> bool {
        match op {
            Op::Inst(spanned_inst) => {
                let inst = spanned_inst.inner();
                self.instruction_count += 1;

                // Track advice usage
                if matches!(inst, Instruction::AdvPush(_) | Instruction::AdvLoadW) {
                    self.has_advice = true;
                }

                // Track exec calls
                if matches!(
                    inst,
                    Instruction::Exec(_) | Instruction::Call(_) | Instruction::SysCall(_)
                ) {
                    self.has_calls = true;
                }

                // Multi-instruction expansions (imm variants that translate to push + op)
                // count as 2 instructions
                if matches!(
                    inst,
                    Instruction::U32WideningAddImm(_)
                        | Instruction::U32OverflowingAddImm(_)
                        | Instruction::U32WrappingAddImm(_)
                        | Instruction::U32OverflowingSubImm(_)
                        | Instruction::U32WrappingSubImm(_)
                        | Instruction::U32WideningMulImm(_)
                        | Instruction::U32WrappingMulImm(_)
                        | Instruction::U32DivModImm(_)
                        | Instruction::U32ModImm(_)
                ) {
                    self.instruction_count += 1; // extra for the push
                }

                // Try inter-procedural analysis for exec calls
                let callee_effect = match inst {
                    Instruction::Exec(target)
                    | Instruction::Call(target)
                    | Instruction::SysCall(target) => {
                        if let Some(callee_map) = self.callee_effects {
                            let name = match target {
                                InvocationTarget::Symbol(id) => Some(id.as_str().to_string()),
                                InvocationTarget::Path(p) => Some(p.to_string()),
                                _ => None,
                            };
                            name.and_then(|n| callee_map.get(&n)).map(|effect| {
                                // The callee consumes `input_arity` items and produces
                                // `input_arity + net_effect` items.
                                let pushes = (effect.input_arity as isize + effect.net_effect)
                                    .max(0) as usize;
                                StackEffect::new(effect.input_arity, pushes)
                            })
                        } else {
                            None
                        }
                    }
                    _ => None,
                };

                let effect = callee_effect.or_else(|| instruction_effect(inst));

                match effect {
                    Some(effect) => {
                        self.apply_effect(&effect);
                        true
                    }
                    None => {
                        // Unknown instruction — mark as imprecise but continue
                        self.is_precise = false;
                        true
                    }
                }
            }
            Op::If {
                then_blk, else_blk, ..
            } => {
                self.has_branches = true;
                // Pop the condition
                self.apply_effect(&StackEffect::new(1, 0));

                let saved_depth = self.current_depth;
                let saved_required = self.max_required;

                // Simulate then branch
                let mut then_sim = StackSimulator {
                    current_depth: self.current_depth,
                    max_required: self.max_required,
                    instruction_count: 0,
                    has_branches: false,
                    has_loops: false,
                    has_repeats: false,
                    has_calls: false,
                    has_advice: false,
                    is_precise: self.is_precise,
                    callee_effects: self.callee_effects,
                };
                let then_ok = then_sim.simulate_block(then_blk);

                // Simulate else branch
                let mut else_sim = StackSimulator {
                    current_depth: saved_depth,
                    max_required: saved_required,
                    instruction_count: 0,
                    has_branches: false,
                    has_loops: false,
                    has_repeats: false,
                    has_calls: false,
                    has_advice: false,
                    is_precise: self.is_precise,
                    callee_effects: self.callee_effects,
                };
                let else_ok = else_sim.simulate_block(else_blk);

                if !then_ok || !else_ok {
                    self.is_precise = false;
                }

                // Merge: take max required depth, check equal exit depths
                self.max_required = then_sim.max_required.max(else_sim.max_required);
                self.instruction_count += then_sim.instruction_count + else_sim.instruction_count;
                self.has_calls |= then_sim.has_calls || else_sim.has_calls;
                self.has_advice |= then_sim.has_advice || else_sim.has_advice;
                self.has_branches |= then_sim.has_branches || else_sim.has_branches;

                if then_sim.current_depth != else_sim.current_depth {
                    // Branches have different stack effects — imprecise
                    self.is_precise = false;
                    // Use the then branch's depth as a best effort
                    self.current_depth = then_sim.current_depth;
                } else {
                    self.current_depth = then_sim.current_depth;
                }

                true
            }
            Op::Repeat { count, body, .. } => {
                self.has_repeats = true;
                let n = match count {
                    Immediate::Value(span) => *span.inner() as usize,
                    Immediate::Constant(_) => {
                        self.is_precise = false;
                        return true;
                    }
                };
                for _ in 0..n {
                    if !self.simulate_block(body) {
                        self.is_precise = false;
                        return true;
                    }
                }
                true
            }
            Op::While { body, .. } => {
                self.has_loops = true;
                // Pop condition
                self.apply_effect(&StackEffect::new(1, 0));
                // Simulate body once for stack effect estimation
                let saved_depth = self.current_depth;
                if !self.simulate_block(body) {
                    self.is_precise = false;
                }
                // Pop condition again at end of body
                self.apply_effect(&StackEffect::new(1, 0));
                // Assume loop is stack-neutral; restore depth
                self.current_depth = saved_depth;
                self.is_precise = false; // while loops make fuel calculation imprecise
                true
            }
        }
    }
}

/// Analyze a procedure body (Block) and return its aggregate stack effect.
/// This is the simple single-pass version without inter-procedural analysis.
pub fn analyze_block(block: &Block) -> ProcStackEffect {
    analyze_block_with_callees(block, None)
}

/// Analyze a procedure body with optional inter-procedural callee information.
pub fn analyze_block_with_callees(
    block: &Block,
    callee_effects: Option<&HashMap<String, ProcStackEffect>>,
) -> ProcStackEffect {
    let mut sim = match callee_effects {
        Some(effects) => StackSimulator::with_callee_effects(effects),
        None => StackSimulator::new(),
    };
    sim.simulate_block(block);

    let input_arity = sim.max_required;
    let net_effect = sim.current_depth;

    // Output arity: how many values are above the remaining original stack
    let output_arity = if net_effect >= 0 {
        // Some original values may still be on the stack, plus new values
        net_effect as usize
    } else {
        // Consumed more than produced; output_arity is 0 in the simplest model
        // but for proof generation we care about what's on top
        0
    };

    ProcStackEffect {
        input_arity,
        output_arity,
        net_effect,
        instruction_count: sim.instruction_count,
        has_branches: sim.has_branches,
        has_loops: sim.has_loops,
        has_repeats: sim.has_repeats,
        has_calls: sim.has_calls,
        has_advice: sim.has_advice,
        is_precise: sim.is_precise,
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
    fn test_instruction_effect_drop() {
        let effect = instruction_effect(&Instruction::Drop).unwrap();
        assert_eq!(effect.pops, 1);
        assert_eq!(effect.pushes, 0);
    }

    #[test]
    fn test_instruction_effect_dup0() {
        let effect = instruction_effect(&Instruction::Dup0).unwrap();
        assert_eq!(effect.pops, 0);
        assert_eq!(effect.pushes, 1);
        assert_eq!(effect.required_depth, 1);
    }

    #[test]
    fn test_instruction_effect_u32_wrapping_add() {
        let effect = instruction_effect(&Instruction::U32WrappingAdd).unwrap();
        assert_eq!(effect.pops, 2);
        assert_eq!(effect.pushes, 1);
    }

    #[test]
    fn test_instruction_effect_u32_cast() {
        // C1 fix: U32Cast should be in the unary list
        let effect = instruction_effect(&Instruction::U32Cast).unwrap();
        assert_eq!(effect.pops, 1);
        assert_eq!(effect.pushes, 1);
    }

    #[test]
    fn test_instruction_effect_imm_variants() {
        // C2 fix: Imm variants should have known effects
        use miden_assembly_syntax::ast::ImmU32;
        let imm = ImmU32::Value(Span::unknown(42u32));

        let effect = instruction_effect(&Instruction::U32WrappingAddImm(imm.clone())).unwrap();
        assert_eq!(effect.pops, 1);
        assert_eq!(effect.pushes, 1);

        let effect = instruction_effect(&Instruction::U32WrappingSubImm(imm.clone())).unwrap();
        assert_eq!(effect.pops, 1);
        assert_eq!(effect.pushes, 1);

        let effect = instruction_effect(&Instruction::U32WrappingMulImm(imm.clone())).unwrap();
        assert_eq!(effect.pops, 1);
        assert_eq!(effect.pushes, 1);

        let effect = instruction_effect(&Instruction::U32ModImm(imm)).unwrap();
        assert_eq!(effect.pops, 1);
        assert_eq!(effect.pushes, 1);
    }

    #[test]
    fn test_analyze_simple_block() {
        // Block: dup 0, drop  =>  needs 1 input, net effect = 0
        let block = make_block(vec![Instruction::Dup0, Instruction::Drop]);
        let effect = analyze_block(&block);
        assert_eq!(effect.input_arity, 1);
        assert_eq!(effect.instruction_count, 2);
        assert!(effect.is_precise);
    }

    #[test]
    fn test_analyze_swap_drop() {
        // Block: swap 1, drop  =>  needs 2 inputs, produces 1 output (net = -1)
        let block = make_block(vec![Instruction::Swap1, Instruction::Drop]);
        let effect = analyze_block(&block);
        assert_eq!(effect.input_arity, 2);
        assert_eq!(effect.net_effect, -1);
    }

    #[test]
    fn test_analyze_block_with_callees() {
        // Block with exec that calls a known procedure
        use miden_assembly_syntax::ast::InvocationTarget;
        let ident = miden_assembly_syntax::ast::Ident::new("callee").unwrap();
        let block = make_block(vec![Instruction::Exec(InvocationTarget::Symbol(ident))]);

        // Without callee info: imprecise
        let effect = analyze_block(&block);
        assert!(!effect.is_precise);

        // With callee info: precise
        let mut callee_map = HashMap::new();
        callee_map.insert(
            "callee".to_string(),
            ProcStackEffect {
                input_arity: 2,
                output_arity: 1,
                net_effect: -1,
                instruction_count: 5,
                has_branches: false,
                has_loops: false,
                has_repeats: false,
                has_calls: false,
                has_advice: false,
                is_precise: true,
            },
        );
        let effect = analyze_block_with_callees(&block, Some(&callee_map));
        assert_eq!(effect.input_arity, 2);
        assert!(effect.is_precise);
    }
}
