use anyhow::{anyhow, Result};
use miden_assembly_syntax::ast::{Immediate, Instruction, InvocationTarget};
use miden_assembly_syntax::parser::{IntValue, PushValue};
use miden_assembly_syntax::Felt;

/// Resolve an ImmFelt to its u64 value.
fn felt_imm(imm: &miden_assembly_syntax::ast::ImmFelt) -> Result<u64> {
    match imm {
        Immediate::Value(span) => Ok(span.inner().as_canonical_u64()),
        Immediate::Constant(id) => Err(anyhow!("unresolved constant: {}", id)),
    }
}

/// Resolve an ImmU32 to its value.
fn u32_imm(imm: &miden_assembly_syntax::ast::ImmU32) -> Result<u32> {
    match imm {
        Immediate::Value(span) => Ok(*span.inner()),
        Immediate::Constant(id) => Err(anyhow!("unresolved constant: {}", id)),
    }
}

/// Resolve an ImmU8 to its value.
fn u8_imm(imm: &miden_assembly_syntax::ast::ImmU8) -> Result<u8> {
    match imm {
        Immediate::Value(span) => Ok(*span.inner()),
        Immediate::Constant(id) => Err(anyhow!("unresolved constant: {}", id)),
    }
}

/// Extract a local index from an Immediate<u16>.
fn u16_imm(imm: &miden_assembly_syntax::ast::ImmU16) -> Result<u16> {
    match imm {
        Immediate::Value(span) => Ok(*span.inner()),
        Immediate::Constant(id) => Err(anyhow!("unresolved constant: {}", id)),
    }
}

/// Extract the error message string from an ErrorMsg.
fn error_msg(imm: &miden_assembly_syntax::ast::ErrorMsg) -> String {
    match imm {
        Immediate::Value(span) => span.inner().to_string(),
        Immediate::Constant(id) => id.to_string(),
    }
}

/// Resolve an invocation target to a string for use in `exec`.
fn target_name(target: &InvocationTarget) -> Result<String> {
    match target {
        InvocationTarget::MastRoot(_) => Err(anyhow!("MAST root targets not supported")),
        InvocationTarget::Symbol(ident) => Ok(ident.as_str().to_string()),
        InvocationTarget::Path(path) => Ok(path.to_string()),
    }
}

/// Extract a u64 value from a PushValue.
fn push_value_to_u64(pv: &PushValue) -> Option<u64> {
    match pv {
        PushValue::Int(iv) => Some(int_value_to_u64(iv)),
        PushValue::Word(_) => None,
    }
}

fn int_value_to_u64(iv: &IntValue) -> u64 {
    match iv {
        IntValue::U8(v) => *v as u64,
        IntValue::U16(v) => *v as u64,
        IntValue::U32(v) => *v as u64,
        IntValue::Felt(f) => f.as_canonical_u64(),
    }
}

fn felt_to_lean(f: &Felt) -> String {
    format!("{}", f.as_canonical_u64())
}

/// Translate a single MASM instruction to its Lean constructor string.
/// Returns the string after `.inst (` — e.g., `.nop` or `.push 42`.
/// For multi-op expansions (e.g., imm variants), returns comma-separated items.
pub fn translate_instruction(inst: &Instruction) -> Result<String> {
    use Instruction::*;
    let s = match inst {
        // No-op
        Nop => ".nop".into(),

        // Assertions
        Assert => ".assert".into(),
        AssertWithError(err) => format!(".assertWithError \"{}\"", error_msg(err)),
        Assertz => ".assertz".into(),
        AssertzWithError(err) => format!(".assertzWithError \"{}\"", error_msg(err)),
        AssertEq => ".assertEq".into(),
        AssertEqWithError(err) => format!(".assertEqWithError \"{}\"", error_msg(err)),
        AssertEqw => ".assertEqw".into(),
        AssertEqwWithError(_) => ".assertEqw".into(),

        // Stack: drop
        Drop => ".drop".into(),
        DropW => ".dropw".into(),

        // Stack: pad
        PadW => ".padw".into(),

        // Stack: dup
        Dup0 => ".dup 0".into(),
        Dup1 => ".dup 1".into(),
        Dup2 => ".dup 2".into(),
        Dup3 => ".dup 3".into(),
        Dup4 => ".dup 4".into(),
        Dup5 => ".dup 5".into(),
        Dup6 => ".dup 6".into(),
        Dup7 => ".dup 7".into(),
        Dup8 => ".dup 8".into(),
        Dup9 => ".dup 9".into(),
        Dup10 => ".dup 10".into(),
        Dup11 => ".dup 11".into(),
        Dup12 => ".dup 12".into(),
        Dup13 => ".dup 13".into(),
        Dup14 => ".dup 14".into(),
        Dup15 => ".dup 15".into(),

        // Stack: dupw
        DupW0 => ".dupw 0".into(),
        DupW1 => ".dupw 1".into(),
        DupW2 => ".dupw 2".into(),
        DupW3 => ".dupw 3".into(),

        // Stack: swap
        Swap1 => ".swap 1".into(),
        Swap2 => ".swap 2".into(),
        Swap3 => ".swap 3".into(),
        Swap4 => ".swap 4".into(),
        Swap5 => ".swap 5".into(),
        Swap6 => ".swap 6".into(),
        Swap7 => ".swap 7".into(),
        Swap8 => ".swap 8".into(),
        Swap9 => ".swap 9".into(),
        Swap10 => ".swap 10".into(),
        Swap11 => ".swap 11".into(),
        Swap12 => ".swap 12".into(),
        Swap13 => ".swap 13".into(),
        Swap14 => ".swap 14".into(),
        Swap15 => ".swap 15".into(),

        // Stack: swapw
        SwapW1 => ".swapw 1".into(),
        SwapW2 => ".swapw 2".into(),
        SwapW3 => ".swapw 3".into(),
        SwapDw => ".swapdw".into(),

        // Stack: movup
        MovUp2 => ".movup 2".into(),
        MovUp3 => ".movup 3".into(),
        MovUp4 => ".movup 4".into(),
        MovUp5 => ".movup 5".into(),
        MovUp6 => ".movup 6".into(),
        MovUp7 => ".movup 7".into(),
        MovUp8 => ".movup 8".into(),
        MovUp9 => ".movup 9".into(),
        MovUp10 => ".movup 10".into(),
        MovUp11 => ".movup 11".into(),
        MovUp12 => ".movup 12".into(),
        MovUp13 => ".movup 13".into(),
        MovUp14 => ".movup 14".into(),
        MovUp15 => ".movup 15".into(),

        // Stack: movdn
        MovDn2 => ".movdn 2".into(),
        MovDn3 => ".movdn 3".into(),
        MovDn4 => ".movdn 4".into(),
        MovDn5 => ".movdn 5".into(),
        MovDn6 => ".movdn 6".into(),
        MovDn7 => ".movdn 7".into(),
        MovDn8 => ".movdn 8".into(),
        MovDn9 => ".movdn 9".into(),
        MovDn10 => ".movdn 10".into(),
        MovDn11 => ".movdn 11".into(),
        MovDn12 => ".movdn 12".into(),
        MovDn13 => ".movdn 13".into(),
        MovDn14 => ".movdn 14".into(),
        MovDn15 => ".movdn 15".into(),

        // Stack: movupw / movdnw
        MovUpW2 => ".movupw 2".into(),
        MovUpW3 => ".movupw 3".into(),
        MovDnW2 => ".movdnw 2".into(),
        MovDnW3 => ".movdnw 3".into(),

        // Stack: reverse
        Reversew => ".reversew".into(),

        // Stack: conditional
        CSwap => ".cswap".into(),
        CSwapW => ".cswapw".into(),
        CDrop => ".cdrop".into(),
        CDropW => ".cdropw".into(),

        // Constants: push
        Push(imm) => match imm {
            Immediate::Value(span) => match push_value_to_u64(span.inner()) {
                Some(v) => format!(".push {}", v),
                None => {
                    // Word push: push.[a,b,c,d] puts a on top of stack
                    if let PushValue::Word(wv) = span.inner() {
                        let vals: Vec<String> = wv.0.iter().map(felt_to_lean).collect();
                        format!(".pushList [{}]", vals.join(", "))
                    } else {
                        unreachable!()
                    }
                }
            },
            Immediate::Constant(id) => {
                return Err(anyhow!("unresolved push constant: {}", id));
            }
        },
        PushFeltList(values) => {
            // push.a.b.c.d pushes values left-to-right, so d ends up on top.
            // Lean pushList prepends the whole list, so reverse to match.
            let vals: Vec<String> = values.iter().rev().map(felt_to_lean).collect();
            if vals.len() == 1 {
                format!(".push {}", vals[0])
            } else {
                format!(".pushList [{}]", vals.join(", "))
            }
        }

        // Field arithmetic
        Add => ".add".into(),
        AddImm(imm) => format!(".addImm {}", felt_imm(imm)?),
        Sub => ".sub".into(),
        SubImm(imm) => format!(".subImm {}", felt_imm(imm)?),
        Mul => ".mul".into(),
        MulImm(imm) => format!(".mulImm {}", felt_imm(imm)?),
        Div => ".div".into(),
        DivImm(imm) => format!(".divImm {}", felt_imm(imm)?),
        Neg => ".neg".into(),
        Inv => ".inv".into(),
        Pow2 => ".pow2".into(),
        Incr => ".incr".into(),

        // Field comparison
        Eq => ".eq".into(),
        EqImm(imm) => format!(".eqImm {}", felt_imm(imm)?),
        Neq => ".neq".into(),
        NeqImm(imm) => format!(".neqImm {}", felt_imm(imm)?),
        Lt => ".lt".into(),
        Lte => ".lte".into(),
        Gt => ".gt".into(),
        Gte => ".gte".into(),
        IsOdd => ".isOdd".into(),

        // Field boolean
        And => ".and".into(),
        Or => ".or".into(),
        Xor => ".xor".into(),
        Not => ".not".into(),

        // U32 assertions / tests
        U32Test => ".u32Test".into(),
        U32TestW => ".u32TestW".into(),
        U32Assert => ".u32Assert".into(),
        U32AssertWithError(_) => ".u32Assert".into(),
        U32Assert2 => ".u32Assert2".into(),
        U32Assert2WithError(_) => ".u32Assert2".into(),
        U32AssertW => ".u32AssertW".into(),
        U32AssertWWithError(_) => ".u32AssertW".into(),

        // U32 conversions
        U32Cast => ".u32Cast".into(),
        U32Split => ".u32Split".into(),

        // U32 arithmetic
        U32WideningAdd => ".u32WidenAdd".into(),
        U32WideningAddImm(imm) => {
            let v = u32_imm(imm)?;
            return Ok(format!(".inst (.push {v}), .inst .u32WidenAdd"));
        }
        U32OverflowingAdd => ".u32OverflowAdd".into(),
        U32OverflowingAddImm(imm) => {
            let v = u32_imm(imm)?;
            return Ok(format!(".inst (.push {v}), .inst .u32OverflowAdd"));
        }
        U32WrappingAdd => ".u32WrappingAdd".into(),
        U32WrappingAddImm(imm) => {
            let v = u32_imm(imm)?;
            return Ok(format!(".inst (.push {v}), .inst .u32WrappingAdd"));
        }
        U32WideningAdd3 => ".u32WidenAdd3".into(),
        U32OverflowingAdd3 => ".u32OverflowAdd3".into(),
        U32WrappingAdd3 => ".u32WrappingAdd3".into(),

        U32OverflowingSub => ".u32OverflowSub".into(),
        U32OverflowingSubImm(imm) => {
            let v = u32_imm(imm)?;
            return Ok(format!(".inst (.push {v}), .inst .u32OverflowSub"));
        }
        U32WrappingSub => ".u32WrappingSub".into(),
        U32WrappingSubImm(imm) => {
            let v = u32_imm(imm)?;
            return Ok(format!(".inst (.push {v}), .inst .u32WrappingSub"));
        }

        U32WideningMul => ".u32WidenMul".into(),
        U32WideningMulImm(imm) => {
            let v = u32_imm(imm)?;
            return Ok(format!(".inst (.push {v}), .inst .u32WidenMul"));
        }
        U32WrappingMul => ".u32WrappingMul".into(),
        U32WrappingMulImm(imm) => {
            let v = u32_imm(imm)?;
            return Ok(format!(".inst (.push {v}), .inst .u32WrappingMul"));
        }
        U32WideningMadd => ".u32WidenMadd".into(),
        U32WrappingMadd => ".u32WrappingMadd".into(),

        U32Div => ".u32Div".into(),
        U32DivImm(imm) => {
            let v = u32_imm(imm)?;
            return Ok(format!(".inst (.push {v}), .inst .u32Div"));
        }
        U32DivMod => ".u32DivMod".into(),
        U32DivModImm(imm) => {
            let v = u32_imm(imm)?;
            return Ok(format!(".inst (.push {v}), .inst .u32DivMod"));
        }
        U32Mod => ".u32Mod".into(),
        U32ModImm(imm) => {
            let v = u32_imm(imm)?;
            return Ok(format!(".inst (.push {v}), .inst .u32Mod"));
        }

        // U32 bitwise
        U32And => ".u32And".into(),
        U32Or => ".u32Or".into(),
        U32Xor => ".u32Xor".into(),
        U32Not => ".u32Not".into(),
        U32Shl => ".u32Shl".into(),
        U32ShlImm(imm) => format!(".u32ShlImm {}", u8_imm(imm)?),
        U32Shr => ".u32Shr".into(),
        U32ShrImm(imm) => format!(".u32ShrImm {}", u8_imm(imm)?),
        U32Rotl => ".u32Rotl".into(),
        U32RotlImm(imm) => format!(".u32RotlImm {}", u8_imm(imm)?),
        U32Rotr => ".u32Rotr".into(),
        U32RotrImm(imm) => format!(".u32RotrImm {}", u8_imm(imm)?),
        U32Popcnt => ".u32Popcnt".into(),
        U32Clz => ".u32Clz".into(),
        U32Ctz => ".u32Ctz".into(),
        U32Clo => ".u32Clo".into(),
        U32Cto => ".u32Cto".into(),

        // U32 comparison
        U32Lt => ".u32Lt".into(),
        U32Lte => ".u32Lte".into(),
        U32Gt => ".u32Gt".into(),
        U32Gte => ".u32Gte".into(),
        U32Min => ".u32Min".into(),
        U32Max => ".u32Max".into(),

        // Memory
        MemLoad => ".memLoad".into(),
        MemLoadImm(imm) => format!(".memLoadImm {}", u32_imm(imm)?),
        MemStore => ".memStore".into(),
        MemStoreImm(imm) => format!(".memStoreImm {}", u32_imm(imm)?),
        MemLoadWBe => ".memLoadwBe".into(),
        MemLoadWBeImm(imm) => format!(".memLoadwBeImm {}", u32_imm(imm)?),
        MemStoreWBe => ".memStorewBe".into(),
        MemStoreWBeImm(imm) => format!(".memStorewBeImm {}", u32_imm(imm)?),
        MemLoadWLe => ".memLoadwLe".into(),
        MemLoadWLeImm(imm) => format!(".memLoadwLeImm {}", u32_imm(imm)?),
        MemStoreWLe => ".memStorewLe".into(),
        MemStoreWLeImm(imm) => format!(".memStorewLeImm {}", u32_imm(imm)?),

        // Procedure locals
        LocLoad(idx) => format!(".locLoad {}", u16_imm(idx)?),
        LocStore(idx) => format!(".locStore {}", u16_imm(idx)?),
        LocLoadWBe(idx) => format!(".locLoadwBe {}", u16_imm(idx)?),
        LocLoadWLe(idx) => format!(".locLoadwLe {}", u16_imm(idx)?),
        LocStoreWBe(idx) => format!(".locStorewBe {}", u16_imm(idx)?),
        LocStoreWLe(idx) => format!(".locStorewLe {}", u16_imm(idx)?),
        Locaddr(idx) => format!(".locaddr {}", u16_imm(idx)?),

        // Advice stack
        AdvPush(imm) => match imm {
            Immediate::Value(span) => format!(".advPush {}", span.inner()),
            Immediate::Constant(id) => return Err(anyhow!("unresolved constant: {}", id)),
        },
        AdvLoadW => ".advLoadW".into(),

        // Events
        Emit => ".emit".into(),
        EmitImm(imm) => match imm {
            Immediate::Value(span) => {
                format!(".emitImm {}", span.inner().as_canonical_u64())
            }
            Immediate::Constant(id) => {
                // Events are no-ops in our model; emit 0 with a comment
                format!(".emitImm 0 /- {} -/", id)
            }
        },

        // Procedure calls
        Exec(t) => format!(".exec \"{}\"", target_name(t)?),
        Call(t) => format!(".exec \"{}\" /- call -/", target_name(t)?),
        SysCall(t) => format!(".exec \"{}\" /- syscall -/", target_name(t)?),

        // Unsupported instructions — emit a comment
        _ => return Err(anyhow!("unsupported instruction: {:?}", inst)),
    };
    Ok(s)
}

#[cfg(test)]
mod tests {
    use super::translate_instruction;
    use miden_assembly_syntax::ast::{ImmU16, ImmU32, Instruction};
    use miden_assembly_syntax::debuginfo::Span;

    #[test]
    fn translates_u32_wrapping_madd() {
        let lean = translate_instruction(&Instruction::U32WrappingMadd).unwrap();
        assert_eq!(lean, ".u32WrappingMadd");
    }

    // --- Local word memory instructions ---

    #[test]
    fn translates_loc_loadw_be() {
        let imm = ImmU16::Value(Span::unknown(4u16));
        let lean = translate_instruction(&Instruction::LocLoadWBe(imm)).unwrap();
        assert_eq!(lean, ".locLoadwBe 4");
    }

    #[test]
    fn translates_loc_loadw_le() {
        let imm = ImmU16::Value(Span::unknown(8u16));
        let lean = translate_instruction(&Instruction::LocLoadWLe(imm)).unwrap();
        assert_eq!(lean, ".locLoadwLe 8");
    }

    #[test]
    fn translates_loc_storew_be() {
        let imm = ImmU16::Value(Span::unknown(0u16));
        let lean = translate_instruction(&Instruction::LocStoreWBe(imm)).unwrap();
        assert_eq!(lean, ".locStorewBe 0");
    }

    #[test]
    fn translates_loc_storew_le() {
        let imm = ImmU16::Value(Span::unknown(12u16));
        let lean = translate_instruction(&Instruction::LocStoreWLe(imm)).unwrap();
        assert_eq!(lean, ".locStorewLe 12");
    }

    #[test]
    fn translates_locaddr() {
        let imm = ImmU16::Value(Span::unknown(32u16));
        let lean = translate_instruction(&Instruction::Locaddr(imm)).unwrap();
        assert_eq!(lean, ".locaddr 32");
    }

    #[test]
    fn translates_loc_loadw_be_zero_index() {
        let imm = ImmU16::Value(Span::unknown(0u16));
        let lean = translate_instruction(&Instruction::LocLoadWBe(imm)).unwrap();
        assert_eq!(lean, ".locLoadwBe 0");
    }

    // --- U32Div instructions ---

    #[test]
    fn translates_u32_div() {
        let lean = translate_instruction(&Instruction::U32Div).unwrap();
        assert_eq!(lean, ".u32Div");
    }

    #[test]
    fn translates_u32_div_imm() {
        let imm = ImmU32::Value(Span::unknown(4u32));
        let lean = translate_instruction(&Instruction::U32DivImm(imm)).unwrap();
        // Should expand to push + op (multi-instruction)
        assert_eq!(lean, ".inst (.push 4), .inst .u32Div");
    }

    // --- Negative: constant immediates should error ---

    #[test]
    fn loc_loadw_be_constant_errors() {
        let imm = ImmU16::Constant(
            miden_assembly_syntax::ast::Ident::new("SOME_CONST").unwrap(),
        );
        let result = translate_instruction(&Instruction::LocLoadWBe(imm));
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("unresolved constant"));
    }

    #[test]
    fn locaddr_constant_errors() {
        let imm = ImmU16::Constant(
            miden_assembly_syntax::ast::Ident::new("OFFSET").unwrap(),
        );
        let result = translate_instruction(&Instruction::Locaddr(imm));
        assert!(result.is_err());
    }

    #[test]
    fn u32_div_imm_constant_errors() {
        let imm = ImmU32::Constant(
            miden_assembly_syntax::ast::Ident::new("DIVISOR").unwrap(),
        );
        let result = translate_instruction(&Instruction::U32DivImm(imm));
        assert!(result.is_err());
    }
}
