//! Complexity classifier for MASM procedures.
//!
//! Classifies each procedure as:
//! - AUTO: Straight-line, all instructions have step lemmas, no value recovery needed
//! - SEMI: Has step lemmas but needs Felt.ofNat value recovery or isU32 propagation
//! - MANUAL: Has branches (if.true), advice stack usage (advPush), deeply nested
//!           arithmetic, or unsupported instructions

use miden_assembly_syntax::ast::{Block, Instruction, Op};

use crate::hypothesis::ProcHypotheses;
use crate::instruction_info::BarrierKind;
use crate::stack_effect::ProcStackEffect;

/// Complexity classification for a procedure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Classification {
    /// Straight-line, all instructions have step lemmas, no value recovery.
    Auto,
    /// Has step lemmas but needs Felt.ofNat value recovery or isU32 propagation.
    Semi,
    /// Has branches, advice stack, deeply nested arithmetic, or unsupported instructions.
    Manual,
}

/// How the scaffold generator should shape the emitted proof.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScaffoldStyle {
    /// Very small straight-line proofs can still use the flatter style.
    FlatAuto,
    /// Prefer explicit instruction-specific steps over generic search.
    FlatExplicit,
    /// Long straight-line proofs should be grouped into chunks.
    Chunked,
    /// Branching, advice-backed, or otherwise unsupported procedures.
    Manual,
}

impl std::fmt::Display for Classification {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Classification::Auto => write!(f, "AUTO"),
            Classification::Semi => write!(f, "SEMI"),
            Classification::Manual => write!(f, "MANUAL"),
        }
    }
}

impl std::fmt::Display for ScaffoldStyle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ScaffoldStyle::FlatAuto => write!(f, "FLAT_AUTO"),
            ScaffoldStyle::FlatExplicit => write!(f, "FLAT_EXPLICIT"),
            ScaffoldStyle::Chunked => write!(f, "CHUNKED"),
            ScaffoldStyle::Manual => write!(f, "MANUAL"),
        }
    }
}

/// Instructions that produce values needing Felt.ofNat recovery.
/// Delegates to the consolidated instruction_info table.
fn needs_value_recovery(inst: &Instruction) -> bool {
    crate::instruction_info::instruction_info(inst).needs_value_recovery
}

/// Check if a block contains any unsupported instructions.
/// Uses the consolidated instruction_info table: an instruction is unsupported
/// if it is NOT marked as `is_known` in the table.
fn has_unsupported_instructions(block: &Block) -> bool {
    for op in block.iter() {
        match op {
            Op::Inst(spanned) => {
                let inst = spanned.inner();
                let info = crate::instruction_info::instruction_info(inst);
                if !info.is_known {
                    return true;
                }
            }
            Op::If {
                then_blk, else_blk, ..
            } => {
                if has_unsupported_instructions(then_blk) || has_unsupported_instructions(else_blk)
                {
                    return true;
                }
            }
            Op::Repeat { body, .. } => {
                if has_unsupported_instructions(body) {
                    return true;
                }
            }
            Op::While { body, .. } => {
                if has_unsupported_instructions(body) {
                    return true;
                }
            }
        }
    }
    false
}

/// Count how many value-recovery-needing instructions are in a block.
fn count_value_recovery_instructions(block: &Block) -> usize {
    let mut count = 0;
    for op in block.iter() {
        match op {
            Op::Inst(spanned) => {
                if needs_value_recovery(spanned.inner()) {
                    count += 1;
                }
            }
            Op::If {
                then_blk, else_blk, ..
            } => {
                count += count_value_recovery_instructions(then_blk);
                count += count_value_recovery_instructions(else_blk);
            }
            Op::Repeat { body, .. } | Op::While { body, .. } => {
                count += count_value_recovery_instructions(body);
            }
        }
    }
    count
}

fn is_hard_barrier(inst: &Instruction) -> bool {
    matches!(
        crate::instruction_info::barrier_kind(inst),
        Some(
            BarrierKind::Pow2
                | BarrierKind::U32DivMod
                | BarrierKind::U32OverflowSub
                | BarrierKind::Div
                | BarrierKind::Cswap
        )
    )
}

fn count_hard_barrier_instructions(block: &Block) -> usize {
    let mut count = 0;
    for op in block.iter() {
        match op {
            Op::Inst(spanned) => {
                if is_hard_barrier(spanned.inner()) {
                    count += 1;
                }
            }
            Op::If {
                then_blk, else_blk, ..
            } => {
                count += count_hard_barrier_instructions(then_blk);
                count += count_hard_barrier_instructions(else_blk);
            }
            Op::Repeat { body, .. } | Op::While { body, .. } => {
                count += count_hard_barrier_instructions(body);
            }
        }
    }
    count
}

/// Choose how the proof skeleton should be shaped.
pub fn choose_scaffold_style(
    block: &Block,
    stack_effect: &ProcStackEffect,
    hypotheses: &ProcHypotheses,
) -> ScaffoldStyle {
    if stack_effect.has_branches || stack_effect.has_loops {
        return ScaffoldStyle::Manual;
    }
    if stack_effect.has_advice || hypotheses.advice_consumed > 0 {
        return ScaffoldStyle::Manual;
    }
    if has_unsupported_instructions(block) {
        return ScaffoldStyle::Manual;
    }

    let barrier_count = count_hard_barrier_instructions(block);

    if !stack_effect.has_calls
        && !stack_effect.has_repeats
        && stack_effect.instruction_count <= 10
        && barrier_count == 0
    {
        return ScaffoldStyle::FlatAuto;
    }

    if stack_effect.instruction_count <= 20 && barrier_count <= 1 {
        return ScaffoldStyle::FlatExplicit;
    }

    ScaffoldStyle::Chunked
}

/// Classify a procedure based on its body, stack effects, and hypotheses.
pub fn classify(
    block: &Block,
    stack_effect: &ProcStackEffect,
    hypotheses: &ProcHypotheses,
) -> Classification {
    // MANUAL triggers:
    // 1. Has branches (if.true)
    if stack_effect.has_branches {
        return Classification::Manual;
    }
    // 2. Has while loops
    if stack_effect.has_loops {
        return Classification::Manual;
    }
    // 3. Uses advice stack
    if stack_effect.has_advice || hypotheses.advice_consumed > 0 {
        return Classification::Manual;
    }
    // 4. Has unsupported instructions
    if has_unsupported_instructions(block) {
        return Classification::Manual;
    }

    // SEMI triggers:
    // 1. Has procedure calls
    if stack_effect.has_calls {
        return Classification::Semi;
    }
    // 2. Needs value recovery (any u32 widening arithmetic)
    if count_value_recovery_instructions(block) > 0 {
        return Classification::Semi;
    }
    // 3. Has isU32 hypotheses that need propagation through intermediate values
    if !hypotheses.hypotheses.is_empty() {
        // Check if any hypothesis traces to a locally-computed value
        // (meaning isU32 propagation is needed)
        for h in &hypotheses.hypotheses {
            if h.entry_position >= hypotheses.input_arity {
                return Classification::Semi;
            }
        }
        // Even with entry-traced hypotheses, if there are u32 operations
        // the proof will need some manual work
        return Classification::Semi;
    }

    // AUTO: everything else (straight-line, all step lemmas available, no special needs)
    Classification::Auto
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hypothesis::infer_hypotheses;
    use crate::stack_effect::analyze_block;
    use miden_assembly_syntax::ast::{Ident, Instruction, InvocationTarget, Op};
    use miden_assembly_syntax::debuginfo::{SourceSpan, Span};

    /// Helper to make a block from a list of instructions.
    fn make_block(insts: Vec<Instruction>) -> Block {
        let ops = insts
            .into_iter()
            .map(|i| Op::Inst(Span::unknown(i)))
            .collect();
        Block::new(SourceSpan::UNKNOWN, ops)
    }

    fn classify_block(block: &Block) -> Classification {
        let effect = analyze_block(block);
        let hyps = infer_hypotheses(block, effect.input_arity);
        classify(block, &effect, &hyps)
    }

    fn scaffold_style(block: &Block) -> ScaffoldStyle {
        let effect = analyze_block(block);
        let hyps = infer_hypotheses(block, effect.input_arity);
        choose_scaffold_style(block, &effect, &hyps)
    }

    #[test]
    fn test_auto_classification_simple() {
        // Straight-line, all step lemmas, no value recovery
        let block = make_block(vec![Instruction::Dup0, Instruction::Drop]);
        assert_eq!(classify_block(&block), Classification::Auto);
    }

    #[test]
    fn test_semi_classification_u32_ops() {
        // Has u32 widening add => SEMI (needs value recovery)
        let block = make_block(vec![Instruction::U32WideningAdd]);
        assert_eq!(classify_block(&block), Classification::Semi);
    }

    #[test]
    fn test_manual_classification_branches() {
        // Has branches => MANUAL
        let then_blk = make_block(vec![Instruction::Nop]);
        let else_blk = make_block(vec![Instruction::Nop]);
        let ops = vec![Op::If {
            span: SourceSpan::UNKNOWN,
            then_blk,
            else_blk,
        }];
        let block = Block::new(SourceSpan::UNKNOWN, ops);
        assert_eq!(classify_block(&block), Classification::Manual);
    }

    #[test]
    fn test_manual_classification_advloadw() {
        let block = make_block(vec![Instruction::AdvLoadW]);
        assert_eq!(classify_block(&block), Classification::Manual);
    }

    #[test]
    fn test_scaffold_style_flat_auto_for_dup_drop() {
        let block = make_block(vec![Instruction::Dup0, Instruction::Drop]);
        assert_eq!(scaffold_style(&block), ScaffoldStyle::FlatAuto);
    }

    #[test]
    fn test_scaffold_style_flat_explicit_for_min_shape() {
        let block = make_block(vec![
            Instruction::Pow2,
            Instruction::Swap1,
            Instruction::Drop,
        ]);
        assert_eq!(scaffold_style(&block), ScaffoldStyle::FlatExplicit);
    }

    #[test]
    fn test_scaffold_style_chunked_for_shr_shape() {
        let block = make_block(vec![
            Instruction::MovUp2,
            Instruction::Swap1,
            Instruction::Pow2,
            Instruction::U32Split,
            Instruction::Swap1,
            Instruction::Dup1,
            Instruction::Add,
            Instruction::MovUp2,
            Instruction::Swap1,
            Instruction::U32DivMod,
            Instruction::Swap1,
            Instruction::MovUp3,
            Instruction::Dup0,
            Instruction::Add,
            Instruction::U32OverflowingSub,
            Instruction::Not,
            Instruction::U32DivMod,
            Instruction::Div,
            Instruction::CSwap,
        ]);
        assert_eq!(scaffold_style(&block), ScaffoldStyle::Chunked);
    }

    #[test]
    fn test_scaffold_style_flat_explicit_for_min_max_shape() {
        let ident = Ident::new("gt").unwrap();
        let block = make_block(vec![
            Instruction::MovUp3,
            Instruction::MovUp3,
            Instruction::DupW0,
            Instruction::Exec(InvocationTarget::Symbol(ident)),
            Instruction::MovUp4,
            Instruction::MovUp3,
            Instruction::Dup2,
            Instruction::CDrop,
            Instruction::MovDn3,
            Instruction::CDrop,
        ]);
        assert_eq!(scaffold_style(&block), ScaffoldStyle::FlatExplicit);
    }

    #[test]
    fn test_scaffold_style_manual_for_branch() {
        let then_blk = make_block(vec![Instruction::Nop]);
        let else_blk = make_block(vec![Instruction::Nop]);
        let ops = vec![Op::If {
            span: SourceSpan::UNKNOWN,
            then_blk,
            else_blk,
        }];
        let block = Block::new(SourceSpan::UNKNOWN, ops);
        assert_eq!(scaffold_style(&block), ScaffoldStyle::Manual);
    }

    #[test]
    fn test_scaffold_style_manual_for_advloadw() {
        let block = make_block(vec![Instruction::AdvLoadW]);
        assert_eq!(scaffold_style(&block), ScaffoldStyle::Manual);
    }

    #[test]
    fn test_display_classification() {
        assert_eq!(format!("{}", Classification::Auto), "AUTO");
        assert_eq!(format!("{}", Classification::Semi), "SEMI");
        assert_eq!(format!("{}", Classification::Manual), "MANUAL");
    }

    #[test]
    fn test_display_scaffold_style() {
        assert_eq!(format!("{}", ScaffoldStyle::FlatAuto), "FLAT_AUTO");
        assert_eq!(format!("{}", ScaffoldStyle::FlatExplicit), "FLAT_EXPLICIT");
        assert_eq!(format!("{}", ScaffoldStyle::Chunked), "CHUNKED");
        assert_eq!(format!("{}", ScaffoldStyle::Manual), "MANUAL");
    }
}
