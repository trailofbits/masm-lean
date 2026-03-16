use anyhow::{Result, anyhow};
use miden_assembly_syntax::ast::{Block, Immediate, Op};

use crate::instruction::translate_instruction;

/// Translate a block (list of ops) to a Lean `List Op` body.
/// Returns the inner items as comma-separated lines, each prefixed with `indent` spaces.
pub fn translate_block(block: &Block, indent: usize) -> Result<Vec<String>> {
    let mut items = Vec::new();
    for op in block.iter() {
        translate_op(op, indent, &mut items)?;
    }
    Ok(items)
}

/// Translate a single Op and append the result(s) to `items`.
fn translate_op(op: &Op, indent: usize, items: &mut Vec<String>) -> Result<()> {
    let pad = " ".repeat(indent);
    match op {
        Op::Inst(spanned_inst) => {
            let inst = spanned_inst.inner();

            // Special case: exec is handled at the Op level in Lean,
            // but at the Instruction level in MASM AST.
            // Our Lean model has it as an Instruction constructor though,
            // so we wrap it in .inst like everything else.
            let lean_str = translate_instruction(inst)?;

            // Some instructions expand to multiple ops (e.g., imm variants
            // that become push + op). These are comma-separated fully-formed
            // Op items like ".inst (.push 5), .inst .u32WidenAdd".
            if lean_str.contains(", .inst ") {
                for part in lean_str.split(", ") {
                    let part = part.trim();
                    items.push(format!("{}{}", pad, part));
                }
            } else {
                items.push(format!("{}.inst ({})", pad, lean_str));
            }
        }
        Op::If {
            then_blk,
            else_blk,
            ..
        } => {
            let then_items = translate_block(then_blk, indent + 2)?;
            let else_items = translate_block(else_blk, indent + 2)?;
            let inner_pad = " ".repeat(indent + 2);

            let then_body = if then_items.is_empty() {
                "[]".to_string()
            } else {
                format!("[\n{}\n{}]", then_items.join(",\n"), inner_pad.trim_end())
            };

            let else_body = if else_items.is_empty() {
                "[]".to_string()
            } else {
                format!("[\n{}\n{}]", else_items.join(",\n"), inner_pad.trim_end())
            };

            items.push(format!(
                "{}.ifElse {} {}",
                pad, then_body, else_body
            ));
        }
        Op::Repeat { count, body, .. } => {
            let n = match count {
                Immediate::Value(span) => *span.inner() as usize,
                Immediate::Constant(id) => {
                    return Err(anyhow!("unresolved repeat count constant: {}", id))
                }
            };

            let body_items = translate_block(body, indent + 2)?;
            let inner_pad = " ".repeat(indent + 2);

            if body_items.is_empty() {
                items.push(format!("{}.repeat {} []", pad, n));
            } else {
                items.push(format!(
                    "{}.repeat {} [\n{}\n{}]",
                    pad,
                    n,
                    body_items.join(",\n"),
                    inner_pad.trim_end()
                ));
            }
        }
        Op::While { body, .. } => {
            let body_items = translate_block(body, indent + 2)?;
            let inner_pad = " ".repeat(indent + 2);

            if body_items.is_empty() {
                items.push(format!("{}.whileTrue []", pad));
            } else {
                items.push(format!(
                    "{}.whileTrue [\n{}\n{}]",
                    pad,
                    body_items.join(",\n"),
                    inner_pad.trim_end()
                ));
            }
        }
    }
    Ok(())
}
