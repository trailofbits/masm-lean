//! Consolidated instruction metadata.
//!
//! Single source of truth for per-instruction information used across
//! stack effect analysis, classification, hypothesis inference, and skeleton generation.

use miden_assembly_syntax::ast::{Immediate, Instruction, InvocationTarget};
use miden_assembly_syntax::parser::PushValue;

use crate::stack_effect::StackEffect;

/// Metadata about a single MASM instruction.
#[derive(Debug, Clone)]
pub struct InstructionInfo {
    /// Stack effect (None means unknown / imprecise).
    pub stack_effect: Option<StackEffect>,
    /// Whether the instruction has a step lemma in the tactic suite.
    pub has_step_lemma: bool,
    /// Whether the instruction requires hypotheses (e.g., isU32 on operands).
    pub needs_hypothesis: bool,
    /// Human-readable MASM-style name for comments.
    pub comment_name: String,
    /// Whether the instruction is known/supported (not a reason to flag as unsupported).
    pub is_known: bool,
    /// Whether the instruction produces values needing Felt.ofNat recovery.
    pub needs_value_recovery: bool,
}

/// Get consolidated metadata for an instruction.
pub fn instruction_info(inst: &Instruction) -> InstructionInfo {
    use Instruction::*;

    // Default: unknown instruction
    let mut info = InstructionInfo {
        stack_effect: None,
        has_step_lemma: false,
        needs_hypothesis: false,
        comment_name: format!("{:?}", inst),
        is_known: false,
        needs_value_recovery: false,
    };

    match inst {
        // === No-op ===
        Nop => {
            info.stack_effect = Some(StackEffect::new(0, 0));
            info.comment_name = "nop".into();
            info.is_known = true;
        }

        // === Assertions ===
        Assert => {
            info.stack_effect = Some(StackEffect::with_depth(1, 0, 1));
            info.comment_name = "assert".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.is_known = true;
        }
        AssertWithError(_) => {
            info.stack_effect = Some(StackEffect::with_depth(1, 0, 1));
            info.comment_name = "assertWithError".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.is_known = true;
        }
        Assertz => {
            info.stack_effect = Some(StackEffect::with_depth(1, 0, 1));
            info.comment_name = "assertz".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.is_known = true;
        }
        AssertzWithError(_) => {
            info.stack_effect = Some(StackEffect::with_depth(1, 0, 1));
            info.comment_name = "assertzWithError".into();
            info.is_known = true;
        }
        AssertEq => {
            info.stack_effect = Some(StackEffect::with_depth(2, 0, 2));
            info.comment_name = "assertEq".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        AssertEqWithError(_) => {
            info.stack_effect = Some(StackEffect::with_depth(2, 0, 2));
            info.comment_name = "assertEqWithError".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        AssertEqw => {
            info.stack_effect = Some(StackEffect::with_depth(8, 0, 8));
            info.comment_name = "assertEqw".into();
            info.is_known = true;
        }
        AssertEqwWithError(_) => {
            info.stack_effect = Some(StackEffect::with_depth(8, 0, 8));
            info.comment_name = "assertEqw".into();
            info.is_known = true;
        }

        // === Stack: drop ===
        Drop => {
            info.stack_effect = Some(StackEffect::new(1, 0));
            info.comment_name = "drop".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        DropW => {
            info.stack_effect = Some(StackEffect::new(4, 0));
            info.comment_name = "dropw".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }

        // === Stack: pad ===
        PadW => {
            info.stack_effect = Some(StackEffect::new(0, 4));
            info.comment_name = "padw".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }

        // === Stack: dup ===
        Dup0 => {
            info.stack_effect = Some(StackEffect::with_depth(0, 1, 1));
            info.comment_name = "dup 0".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Dup1 => {
            info.stack_effect = Some(StackEffect::with_depth(0, 1, 2));
            info.comment_name = "dup 1".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Dup2 => {
            info.stack_effect = Some(StackEffect::with_depth(0, 1, 3));
            info.comment_name = "dup 2".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Dup3 => {
            info.stack_effect = Some(StackEffect::with_depth(0, 1, 4));
            info.comment_name = "dup 3".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Dup4 => {
            info.stack_effect = Some(StackEffect::with_depth(0, 1, 5));
            info.comment_name = "dup 4".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Dup5 => {
            info.stack_effect = Some(StackEffect::with_depth(0, 1, 6));
            info.comment_name = "dup 5".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Dup6 => {
            info.stack_effect = Some(StackEffect::with_depth(0, 1, 7));
            info.comment_name = "dup 6".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Dup7 => {
            info.stack_effect = Some(StackEffect::with_depth(0, 1, 8));
            info.comment_name = "dup 7".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Dup8 => {
            info.stack_effect = Some(StackEffect::with_depth(0, 1, 9));
            info.comment_name = "dup 8".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Dup9 => {
            info.stack_effect = Some(StackEffect::with_depth(0, 1, 10));
            info.comment_name = "dup 9".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Dup10 => {
            info.stack_effect = Some(StackEffect::with_depth(0, 1, 11));
            info.comment_name = "dup 10".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Dup11 => {
            info.stack_effect = Some(StackEffect::with_depth(0, 1, 12));
            info.comment_name = "dup 11".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Dup12 => {
            info.stack_effect = Some(StackEffect::with_depth(0, 1, 13));
            info.comment_name = "dup 12".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Dup13 => {
            info.stack_effect = Some(StackEffect::with_depth(0, 1, 14));
            info.comment_name = "dup 13".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Dup14 => {
            info.stack_effect = Some(StackEffect::with_depth(0, 1, 15));
            info.comment_name = "dup 14".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Dup15 => {
            info.stack_effect = Some(StackEffect::with_depth(0, 1, 16));
            info.comment_name = "dup 15".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }

        // === Stack: dupw ===
        DupW0 => {
            info.stack_effect = Some(StackEffect::with_depth(0, 4, 4));
            info.comment_name = "dupw 0".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        DupW1 => {
            info.stack_effect = Some(StackEffect::with_depth(0, 4, 8));
            info.comment_name = "dupw 1".into();
            info.is_known = true;
        }
        DupW2 => {
            info.stack_effect = Some(StackEffect::with_depth(0, 4, 12));
            info.comment_name = "dupw 2".into();
            info.is_known = true;
        }
        DupW3 => {
            info.stack_effect = Some(StackEffect::with_depth(0, 4, 16));
            info.comment_name = "dupw 3".into();
            info.is_known = true;
        }

        // === Stack: swap ===
        Swap1 => {
            info.stack_effect = Some(StackEffect::with_depth(2, 2, 2));
            info.comment_name = "swap 1".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Swap2 => {
            info.stack_effect = Some(StackEffect::with_depth(3, 3, 3));
            info.comment_name = "swap 2".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Swap3 => {
            info.stack_effect = Some(StackEffect::with_depth(4, 4, 4));
            info.comment_name = "swap 3".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Swap4 => {
            info.stack_effect = Some(StackEffect::with_depth(5, 5, 5));
            info.comment_name = "swap 4".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Swap5 => {
            info.stack_effect = Some(StackEffect::with_depth(6, 6, 6));
            info.comment_name = "swap 5".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Swap6 => {
            info.stack_effect = Some(StackEffect::with_depth(7, 7, 7));
            info.comment_name = "swap 6".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Swap7 => {
            info.stack_effect = Some(StackEffect::with_depth(8, 8, 8));
            info.comment_name = "swap 7".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Swap8 => {
            info.stack_effect = Some(StackEffect::with_depth(9, 9, 9));
            info.comment_name = "swap 8".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Swap9 => {
            info.stack_effect = Some(StackEffect::with_depth(10, 10, 10));
            info.comment_name = "swap 9".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Swap10 => {
            info.stack_effect = Some(StackEffect::with_depth(11, 11, 11));
            info.comment_name = "swap 10".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Swap11 => {
            info.stack_effect = Some(StackEffect::with_depth(12, 12, 12));
            info.comment_name = "swap 11".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Swap12 => {
            info.stack_effect = Some(StackEffect::with_depth(13, 13, 13));
            info.comment_name = "swap 12".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Swap13 => {
            info.stack_effect = Some(StackEffect::with_depth(14, 14, 14));
            info.comment_name = "swap 13".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Swap14 => {
            info.stack_effect = Some(StackEffect::with_depth(15, 15, 15));
            info.comment_name = "swap 14".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Swap15 => {
            info.stack_effect = Some(StackEffect::with_depth(16, 16, 16));
            info.comment_name = "swap 15".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }

        // === Stack: swapw ===
        SwapW1 => {
            info.stack_effect = Some(StackEffect::with_depth(8, 8, 8));
            info.comment_name = "swapw 1".into();
            info.is_known = true;
        }
        SwapW2 => {
            info.stack_effect = Some(StackEffect::with_depth(12, 12, 12));
            info.comment_name = "swapw 2".into();
            info.is_known = true;
        }
        SwapW3 => {
            info.stack_effect = Some(StackEffect::with_depth(16, 16, 16));
            info.comment_name = "swapw 3".into();
            info.is_known = true;
        }
        SwapDw => {
            info.stack_effect = Some(StackEffect::with_depth(16, 16, 16));
            info.comment_name = "swapdw".into();
            info.is_known = true;
        }

        // === Stack: movup ===
        MovUp2 => {
            info.stack_effect = Some(StackEffect::with_depth(3, 3, 3));
            info.comment_name = "movup 2".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovUp3 => {
            info.stack_effect = Some(StackEffect::with_depth(4, 4, 4));
            info.comment_name = "movup 3".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovUp4 => {
            info.stack_effect = Some(StackEffect::with_depth(5, 5, 5));
            info.comment_name = "movup 4".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovUp5 => {
            info.stack_effect = Some(StackEffect::with_depth(6, 6, 6));
            info.comment_name = "movup 5".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovUp6 => {
            info.stack_effect = Some(StackEffect::with_depth(7, 7, 7));
            info.comment_name = "movup 6".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovUp7 => {
            info.stack_effect = Some(StackEffect::with_depth(8, 8, 8));
            info.comment_name = "movup 7".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovUp8 => {
            info.stack_effect = Some(StackEffect::with_depth(9, 9, 9));
            info.comment_name = "movup 8".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovUp9 => {
            info.stack_effect = Some(StackEffect::with_depth(10, 10, 10));
            info.comment_name = "movup 9".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovUp10 => {
            info.stack_effect = Some(StackEffect::with_depth(11, 11, 11));
            info.comment_name = "movup 10".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovUp11 => {
            info.stack_effect = Some(StackEffect::with_depth(12, 12, 12));
            info.comment_name = "movup 11".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovUp12 => {
            info.stack_effect = Some(StackEffect::with_depth(13, 13, 13));
            info.comment_name = "movup 12".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovUp13 => {
            info.stack_effect = Some(StackEffect::with_depth(14, 14, 14));
            info.comment_name = "movup 13".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovUp14 => {
            info.stack_effect = Some(StackEffect::with_depth(15, 15, 15));
            info.comment_name = "movup 14".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovUp15 => {
            info.stack_effect = Some(StackEffect::with_depth(16, 16, 16));
            info.comment_name = "movup 15".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }

        // === Stack: movdn ===
        MovDn2 => {
            info.stack_effect = Some(StackEffect::with_depth(3, 3, 3));
            info.comment_name = "movdn 2".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovDn3 => {
            info.stack_effect = Some(StackEffect::with_depth(4, 4, 4));
            info.comment_name = "movdn 3".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovDn4 => {
            info.stack_effect = Some(StackEffect::with_depth(5, 5, 5));
            info.comment_name = "movdn 4".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovDn5 => {
            info.stack_effect = Some(StackEffect::with_depth(6, 6, 6));
            info.comment_name = "movdn 5".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovDn6 => {
            info.stack_effect = Some(StackEffect::with_depth(7, 7, 7));
            info.comment_name = "movdn 6".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovDn7 => {
            info.stack_effect = Some(StackEffect::with_depth(8, 8, 8));
            info.comment_name = "movdn 7".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovDn8 => {
            info.stack_effect = Some(StackEffect::with_depth(9, 9, 9));
            info.comment_name = "movdn 8".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovDn9 => {
            info.stack_effect = Some(StackEffect::with_depth(10, 10, 10));
            info.comment_name = "movdn 9".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovDn10 => {
            info.stack_effect = Some(StackEffect::with_depth(11, 11, 11));
            info.comment_name = "movdn 10".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovDn11 => {
            info.stack_effect = Some(StackEffect::with_depth(12, 12, 12));
            info.comment_name = "movdn 11".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovDn12 => {
            info.stack_effect = Some(StackEffect::with_depth(13, 13, 13));
            info.comment_name = "movdn 12".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovDn13 => {
            info.stack_effect = Some(StackEffect::with_depth(14, 14, 14));
            info.comment_name = "movdn 13".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovDn14 => {
            info.stack_effect = Some(StackEffect::with_depth(15, 15, 15));
            info.comment_name = "movdn 14".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MovDn15 => {
            info.stack_effect = Some(StackEffect::with_depth(16, 16, 16));
            info.comment_name = "movdn 15".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }

        // === Stack: movupw/movdnw ===
        MovUpW2 => {
            info.stack_effect = Some(StackEffect::with_depth(12, 12, 12));
            info.comment_name = "movupw 2".into();
            info.is_known = true;
        }
        MovUpW3 => {
            info.stack_effect = Some(StackEffect::with_depth(16, 16, 16));
            info.comment_name = "movupw 3".into();
            info.is_known = true;
        }
        MovDnW2 => {
            info.stack_effect = Some(StackEffect::with_depth(12, 12, 12));
            info.comment_name = "movdnw 2".into();
            info.is_known = true;
        }
        MovDnW3 => {
            info.stack_effect = Some(StackEffect::with_depth(16, 16, 16));
            info.comment_name = "movdnw 3".into();
            info.is_known = true;
        }

        // === Stack: reverse ===
        Reversew => {
            info.stack_effect = Some(StackEffect::with_depth(4, 4, 4));
            info.comment_name = "reversew".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }

        // === Stack: conditional ===
        CSwap => {
            info.stack_effect = Some(StackEffect::with_depth(3, 2, 3));
            info.comment_name = "cswap".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        CSwapW => {
            info.stack_effect = Some(StackEffect::with_depth(9, 8, 9));
            info.comment_name = "cswapw".into();
            info.is_known = true;
        }
        CDrop => {
            info.stack_effect = Some(StackEffect::with_depth(3, 1, 3));
            info.comment_name = "cdrop".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        CDropW => {
            info.stack_effect = Some(StackEffect::with_depth(9, 4, 9));
            info.comment_name = "cdropw".into();
            info.is_known = true;
        }

        // === Constants: push ===
        Push(imm) => {
            info.stack_effect = match imm {
                Immediate::Value(span) => match span.inner() {
                    PushValue::Word(_) => Some(StackEffect::new(0, 4)),
                    PushValue::Int(_) => Some(StackEffect::new(0, 1)),
                },
                Immediate::Constant(_) => Some(StackEffect::new(0, 1)),
            };
            info.comment_name = "push".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        PushFeltList(values) => {
            info.stack_effect = Some(StackEffect::new(0, values.len()));
            info.comment_name = "push (felt list)".into();
            info.is_known = true;
        }

        // === Field arithmetic ===
        Add => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "add".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        AddImm(_) => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "addImm".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Sub => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "sub".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        SubImm(_) => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "subImm".into();
            info.is_known = true;
        }
        Mul => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "mul".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        MulImm(_) => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "mulImm".into();
            info.is_known = true;
        }
        Div => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "div".into();
            info.is_known = true;
        }
        DivImm(_) => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "divImm".into();
            info.is_known = true;
        }
        Neg => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "neg".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Inv => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "inv".into();
            info.is_known = true;
        }
        Pow2 => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "pow2".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.is_known = true;
        }
        Incr => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "incr".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }

        // === Field comparison ===
        Eq => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "eq".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        EqImm(_) => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "eqImm".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Neq => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "neq".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        NeqImm(_) => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "neqImm".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Lt => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "lt".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Lte => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "lte".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Gt => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "gt".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Gte => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "gte".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        IsOdd => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "isOdd".into();
            info.is_known = true;
        }

        // === Field boolean ===
        And => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "and".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Or => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "or".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }
        Xor => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "xor".into();
            info.is_known = true;
        }
        Not => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "not".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }

        // === U32 tests/assertions ===
        U32Test => {
            info.stack_effect = Some(StackEffect::with_depth(0, 1, 1));
            info.comment_name = "u32Test".into();
            info.is_known = true;
        }
        U32TestW => {
            info.stack_effect = Some(StackEffect::with_depth(0, 1, 4));
            info.comment_name = "u32TestW".into();
            info.is_known = true;
        }
        U32Assert | U32AssertWithError(_) => {
            info.stack_effect = Some(StackEffect::with_depth(0, 0, 1));
            info.comment_name = "u32Assert".into();
            info.is_known = true;
        }
        U32Assert2 => {
            info.stack_effect = Some(StackEffect::with_depth(0, 0, 2));
            info.comment_name = "u32Assert2".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.is_known = true;
        }
        U32Assert2WithError(_) => {
            info.stack_effect = Some(StackEffect::with_depth(0, 0, 2));
            info.comment_name = "u32Assert2".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.is_known = true;
        }
        U32AssertW | U32AssertWWithError(_) => {
            info.stack_effect = Some(StackEffect::with_depth(0, 0, 4));
            info.comment_name = "u32AssertW".into();
            info.is_known = true;
        }

        // === U32 conversions ===
        U32Cast => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "u32Cast".into();
            info.is_known = true;
        }
        U32Split => {
            info.stack_effect = Some(StackEffect::new(1, 2));
            info.comment_name = "u32Split".into();
            info.has_step_lemma = true;
            info.needs_value_recovery = true;
            info.is_known = true;
        }

        // === U32 arithmetic (binary 2->1) ===
        U32WrappingAdd => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "u32WrappingAdd".into();
            info.is_known = true;
        }
        U32WrappingSub => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "u32WrappingSub".into();
            info.is_known = true;
        }
        U32WrappingMul => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "u32WrappingMul".into();
            info.is_known = true;
        }

        // === U32 arithmetic (unary Imm variants: 1->1) ===
        U32WrappingAddImm(_) => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "u32WrappingAdd (imm)".into();
            info.is_known = true;
        }
        U32WrappingSubImm(_) => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "u32WrappingSub (imm)".into();
            info.is_known = true;
        }
        U32WrappingMulImm(_) => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "u32WrappingMul (imm)".into();
            info.is_known = true;
        }

        // === U32 bitwise (binary 2->1) ===
        U32And => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "u32And".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.is_known = true;
        }
        U32Or => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "u32Or".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.is_known = true;
        }
        U32Xor => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "u32Xor".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.is_known = true;
        }
        U32Not => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "u32Not".into();
            info.is_known = true;
        }
        U32Popcnt => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "u32Popcnt".into();
            info.is_known = true;
        }

        // === U32 shift/rotate (binary 2->1) ===
        U32Shl => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "u32Shl".into();
            info.is_known = true;
        }
        U32Shr => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "u32Shr".into();
            info.is_known = true;
        }
        U32Rotl => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "u32Rotl".into();
            info.is_known = true;
        }
        U32Rotr => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "u32Rotr".into();
            info.is_known = true;
        }

        // === U32 shift/rotate Imm (unary 1->1) ===
        U32ShlImm(_) => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "u32Shl (imm)".into();
            info.is_known = true;
        }
        U32ShrImm(_) => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "u32Shr (imm)".into();
            info.is_known = true;
        }
        U32RotlImm(_) => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "u32Rotl (imm)".into();
            info.is_known = true;
        }
        U32RotrImm(_) => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "u32Rotr (imm)".into();
            info.is_known = true;
        }

        // === U32 comparison (binary 2->1) ===
        U32Lt => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "u32Lt".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.is_known = true;
        }
        U32Lte => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "u32Lte".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.is_known = true;
        }
        U32Gt => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "u32Gt".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.is_known = true;
        }
        U32Gte => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "u32Gte".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.is_known = true;
        }
        U32Min => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "u32Min".into();
            info.is_known = true;
        }
        U32Max => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "u32Max".into();
            info.is_known = true;
        }
        U32Div => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "u32Div".into();
            info.is_known = true;
        }
        U32Mod => {
            info.stack_effect = Some(StackEffect::new(2, 1));
            info.comment_name = "u32Mod".into();
            info.is_known = true;
        }
        U32ModImm(_) => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "u32Mod (imm)".into();
            info.is_known = true;
        }

        // === U32 bit counting (unary 1->1) ===
        U32Clz => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "u32Clz".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.is_known = true;
        }
        U32Ctz => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "u32Ctz".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.is_known = true;
        }
        U32Clo => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "u32Clo".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.is_known = true;
        }
        U32Cto => {
            info.stack_effect = Some(StackEffect::new(1, 1));
            info.comment_name = "u32Cto".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.is_known = true;
        }

        // === U32 widening/overflowing arithmetic (2->2) ===
        U32OverflowingAdd => {
            info.stack_effect = Some(StackEffect::new(2, 2));
            info.comment_name = "u32OverflowAdd".into();
            info.needs_hypothesis = true;
            info.needs_value_recovery = true;
            info.is_known = true;
        }
        U32OverflowingAddImm(_) => {
            info.stack_effect = Some(StackEffect::new(1, 2));
            info.comment_name = "u32OverflowAdd (imm)".into();
            info.needs_value_recovery = true;
            info.is_known = true;
        }
        U32WideningAdd => {
            info.stack_effect = Some(StackEffect::new(2, 2));
            info.comment_name = "u32WidenAdd".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.needs_value_recovery = true;
            info.is_known = true;
        }
        U32WideningAddImm(_) => {
            info.stack_effect = Some(StackEffect::new(1, 2));
            info.comment_name = "u32WidenAdd (imm)".into();
            info.needs_value_recovery = true;
            info.is_known = true;
        }
        U32OverflowingSub => {
            info.stack_effect = Some(StackEffect::new(2, 2));
            info.comment_name = "u32OverflowSub".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.needs_value_recovery = true;
            info.is_known = true;
        }
        U32OverflowingSubImm(_) => {
            info.stack_effect = Some(StackEffect::new(1, 2));
            info.comment_name = "u32OverflowSub (imm)".into();
            info.needs_value_recovery = true;
            info.is_known = true;
        }
        U32WideningMul => {
            info.stack_effect = Some(StackEffect::new(2, 2));
            info.comment_name = "u32WidenMul".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.needs_value_recovery = true;
            info.is_known = true;
        }
        U32WideningMulImm(_) => {
            info.stack_effect = Some(StackEffect::new(1, 2));
            info.comment_name = "u32WidenMul (imm)".into();
            info.needs_value_recovery = true;
            info.is_known = true;
        }
        U32WideningMadd => {
            info.stack_effect = Some(StackEffect::new(3, 2));
            info.comment_name = "u32WidenMadd".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.needs_value_recovery = true;
            info.is_known = true;
        }
        U32WideningAdd3 => {
            info.stack_effect = Some(StackEffect::new(3, 2));
            info.comment_name = "u32WidenAdd3".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;
            info.needs_value_recovery = true;
            info.is_known = true;
        }
        U32OverflowingAdd3 => {
            info.stack_effect = Some(StackEffect::new(3, 2));
            info.comment_name = "u32OverflowAdd3".into();
            info.needs_hypothesis = true;
            info.needs_value_recovery = true;
            info.is_known = true;
        }
        U32WrappingAdd3 => {
            info.stack_effect = Some(StackEffect::new(3, 1));
            info.comment_name = "u32WrappingAdd3".into();
            info.is_known = true;
        }
        U32DivMod => {
            info.stack_effect = Some(StackEffect::new(2, 2));
            info.comment_name = "u32DivMod".into();
            info.needs_value_recovery = true;
            info.is_known = true;
        }
        U32DivModImm(_) => {
            info.stack_effect = Some(StackEffect::new(1, 2));
            info.comment_name = "u32DivMod (imm)".into();
            info.needs_value_recovery = true;
            info.is_known = true;
        }

        // === Memory ===
        MemLoad => {
            info.stack_effect = Some(StackEffect::with_depth(1, 1, 1));
            info.comment_name = "memLoad".into();
            info.is_known = true;
        }
        MemLoadImm(_) => {
            info.stack_effect = Some(StackEffect::new(0, 1));
            info.comment_name = "memLoadImm".into();
            info.is_known = true;
        }
        MemStore => {
            info.stack_effect = Some(StackEffect::with_depth(2, 0, 2));
            info.comment_name = "memStore".into();
            info.is_known = true;
        }
        MemStoreImm(_) => {
            info.stack_effect = Some(StackEffect::with_depth(1, 0, 1));
            info.comment_name = "memStoreImm".into();
            info.is_known = true;
        }
        MemLoadWBe | MemLoadWLe => {
            info.stack_effect = Some(StackEffect::with_depth(5, 4, 5));
            info.comment_name = if matches!(inst, MemLoadWBe) {
                "memLoadwBe".into()
            } else {
                "memLoadwLe".into()
            };
            info.is_known = true;
        }
        MemLoadWBeImm(_) | MemLoadWLeImm(_) => {
            info.stack_effect = Some(StackEffect::with_depth(4, 4, 4));
            info.comment_name = if matches!(inst, MemLoadWBeImm(_)) {
                "memLoadwBeImm".into()
            } else {
                "memLoadwLeImm".into()
            };
            info.is_known = true;
        }
        MemStoreWBe | MemStoreWLe => {
            info.stack_effect = Some(StackEffect::with_depth(1, 0, 5));
            info.comment_name = if matches!(inst, MemStoreWBe) {
                "memStorewBe".into()
            } else {
                "memStorewLe".into()
            };
            info.is_known = true;
        }
        MemStoreWBeImm(_) | MemStoreWLeImm(_) => {
            info.stack_effect = Some(StackEffect::with_depth(0, 0, 4));
            info.comment_name = if matches!(inst, MemStoreWBeImm(_)) {
                "memStorewBeImm".into()
            } else {
                "memStorewLeImm".into()
            };
            info.is_known = true;
        }

        // === Locals ===
        LocLoad(_) => {
            info.stack_effect = Some(StackEffect::new(0, 1));
            info.comment_name = "locLoad".into();
            info.is_known = true;
        }
        LocStore(_) => {
            info.stack_effect = Some(StackEffect::with_depth(1, 0, 1));
            info.comment_name = "locStore".into();
            info.is_known = true;
        }

        // === Advice stack ===
        AdvPush(imm) => {
            info.stack_effect = match imm {
                Immediate::Value(span) => Some(StackEffect::new(0, *span.inner() as usize)),
                Immediate::Constant(_) => None,
            };
            info.comment_name = "advPush".into();
            info.has_step_lemma = true;
            info.needs_hypothesis = true;  // needs advice hypothesis
            info.is_known = true;
        }
        AdvLoadW => {
            info.stack_effect = Some(StackEffect::with_depth(4, 4, 4));
            info.comment_name = "advLoadW".into();
            info.is_known = true;
        }

        // === Events ===
        Emit => {
            info.stack_effect = Some(StackEffect::with_depth(0, 0, 1));
            info.comment_name = "emit".into();
            info.is_known = true;
        }
        EmitImm(_) => {
            info.stack_effect = Some(StackEffect::new(0, 0));
            info.comment_name = "emitImm".into();
            info.has_step_lemma = true;
            info.is_known = true;
        }

        // === Procedure calls ===
        Exec(t) => {
            // Stack effect is unknown without inter-procedural analysis
            let name = match t {
                InvocationTarget::Symbol(id) => id.as_str().to_string(),
                InvocationTarget::Path(p) => p.to_string(),
                _ => "?".into(),
            };
            info.comment_name = format!("exec \"{}\"", name);
            info.is_known = true;
        }
        Call(t) => {
            let name = match t {
                InvocationTarget::Symbol(id) => id.as_str().to_string(),
                InvocationTarget::Path(p) => p.to_string(),
                _ => "?".into(),
            };
            info.comment_name = format!("call \"{}\"", name);
            info.is_known = true;
        }
        SysCall(t) => {
            let name = match t {
                InvocationTarget::Symbol(id) => id.as_str().to_string(),
                InvocationTarget::Path(p) => p.to_string(),
                _ => "?".into(),
            };
            info.comment_name = format!("syscall \"{}\"", name);
            info.is_known = true;
        }

        // Unknown/unsupported
        _ => {}
    }

    info
}
