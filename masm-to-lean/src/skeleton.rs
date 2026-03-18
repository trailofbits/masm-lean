//! Proof skeleton generation for MASM procedures.
//!
//! Generates Lean 4 proof files containing:
//! - Theorem statements with typed inputs, preconditions, and sorry output
//! - Proof bodies using the tactic API contract (miden_setup, miden_step, etc.)
//! - Complexity classification annotations

use std::collections::{BTreeSet, HashMap};

use anyhow::Result;
use miden_assembly_syntax::ast::{Block, Immediate, Instruction, InvocationTarget, Module, Op};

use crate::classifier::{classify, Classification};
use crate::hypothesis::{infer_hypotheses, HypothesisKind, ProcHypotheses};
use crate::module::sanitize_lean_name;
use crate::stack_effect::{analyze_block, analyze_block_with_callees, ProcStackEffect};

/// Information about a single procedure's proof skeleton.
struct ProcSkeleton {
    /// MASM procedure name (e.g., "wrapping_mul").
    masm_name: String,
    /// Lean definition name (e.g., "wrapping_mul").
    #[allow(dead_code)]
    lean_def_name: String,
    /// Lean theorem name (e.g., "u64_wrapping_mul_correct").
    theorem_name: String,
    /// Fully qualified Lean procedure name (e.g., "Miden.Core.Math.U64.wrapping_mul").
    fq_lean_name: String,
    /// Stack effect analysis.
    stack_effect: ProcStackEffect,
    /// Hypothesis inference result.
    hypotheses: ProcHypotheses,
    /// Complexity classification.
    classification: Classification,
    /// The procedure body (for emitting tactic calls).
    body_ops: Vec<FlatOp>,
    /// Whether to use execWithEnv (has procedure calls).
    needs_proc_env: bool,
    /// Module prefix for naming (e.g., "u64" from the module name).
    module_prefix: String,
}

/// A flattened operation with its instruction index for proof body emission.
#[derive(Debug, Clone)]
enum FlatOp {
    /// A single instruction.
    Instruction {
        index: usize,
        lean_repr: String,
        needs_hypothesis: bool,
        is_exec: bool,
        exec_target: Option<String>,
        has_step_lemma: bool,
    },
    /// Start of a repeat block.
    RepeatStart { count: usize },
    /// End of a repeat block.
    RepeatEnd,
    /// Start of an if-else block.
    IfStart,
    /// Else branch.
    IfElse,
    /// End of if-else.
    IfEnd,
    /// Start of a while block.
    WhileStart,
    /// End of a while block.
    WhileEnd,
}

/// Flatten a block into a list of FlatOps for linear proof emission.
fn flatten_block(block: &Block, index: &mut usize, ops: &mut Vec<FlatOp>) {
    for op in block.iter() {
        flatten_op(op, index, ops);
    }
}

fn flatten_op(op: &Op, index: &mut usize, ops: &mut Vec<FlatOp>) {
    match op {
        Op::Inst(spanned_inst) => {
            let inst = spanned_inst.inner();
            let lean_repr = inst_to_comment_string(inst);
            let needs_hypothesis = inst_needs_hypothesis(inst);
            let is_exec = matches!(inst, Instruction::Exec(_) | Instruction::Call(_));
            let exec_target = match inst {
                Instruction::Exec(t) | Instruction::Call(t) => match t {
                    InvocationTarget::Symbol(ident) => Some(ident.as_str().to_string()),
                    InvocationTarget::Path(path) => Some(path.to_string()),
                    _ => None,
                },
                _ => None,
            };
            let has_step_lemma = inst_has_step_lemma(inst);

            // For imm variants that expand to push+op, emit two entries
            if is_multi_op_expansion(inst) {
                ops.push(FlatOp::Instruction {
                    index: *index,
                    lean_repr: format!("push (imm for {})", lean_repr),
                    needs_hypothesis: false,
                    is_exec: false,
                    exec_target: None,
                    has_step_lemma: false, // push handled by miden_step eventually
                });
                *index += 1;
                ops.push(FlatOp::Instruction {
                    index: *index,
                    lean_repr,
                    needs_hypothesis,
                    is_exec: false,
                    exec_target: None,
                    has_step_lemma,
                });
                *index += 1;
            } else {
                ops.push(FlatOp::Instruction {
                    index: *index,
                    lean_repr,
                    needs_hypothesis,
                    is_exec,
                    exec_target,
                    has_step_lemma,
                });
                *index += 1;
            }
        }
        Op::If {
            then_blk, else_blk, ..
        } => {
            ops.push(FlatOp::IfStart);
            flatten_block(then_blk, index, ops);
            ops.push(FlatOp::IfElse);
            flatten_block(else_blk, index, ops);
            ops.push(FlatOp::IfEnd);
        }
        Op::Repeat { count, body, .. } => {
            let n = match count {
                Immediate::Value(span) => *span.inner() as usize,
                Immediate::Constant(_) => 0,
            };
            ops.push(FlatOp::RepeatStart { count: n });
            flatten_block(body, index, ops);
            ops.push(FlatOp::RepeatEnd);
        }
        Op::While { body, .. } => {
            ops.push(FlatOp::WhileStart);
            flatten_block(body, index, ops);
            ops.push(FlatOp::WhileEnd);
        }
    }
}

fn is_multi_op_expansion(inst: &Instruction) -> bool {
    use Instruction::*;
    matches!(
        inst,
        U32WideningAddImm(_)
            | U32OverflowingAddImm(_)
            | U32WrappingAddImm(_)
            | U32OverflowingSubImm(_)
            | U32WrappingSubImm(_)
            | U32WideningMulImm(_)
            | U32WrappingMulImm(_)
            | U32DivModImm(_)
            | U32ModImm(_)
    )
}

/// Get the human-readable MASM-style name for an instruction.
/// Delegates to the consolidated instruction_info table.
fn inst_to_comment_string(inst: &Instruction) -> String {
    crate::instruction_info::instruction_info(inst).comment_name
}

/// Check if an instruction requires hypotheses.
/// Delegates to the consolidated instruction_info table.
fn inst_needs_hypothesis(inst: &Instruction) -> bool {
    crate::instruction_info::instruction_info(inst).needs_hypothesis
}

/// Check if an instruction has a step lemma.
/// Delegates to the consolidated instruction_info table.
fn inst_has_step_lemma(inst: &Instruction) -> bool {
    crate::instruction_info::instruction_info(inst).has_step_lemma
}

fn capitalize_segment(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
        None => String::new(),
    }
}

fn lean_module_path_from_target(module_path: &str) -> String {
    module_path
        .split("::")
        .filter(|segment| !segment.is_empty())
        .map(|segment| capitalize_segment(&sanitize_lean_name(segment)))
        .collect::<Vec<_>>()
        .join(".")
}

fn caller_namespace(caller_fq_name: &str) -> &str {
    caller_fq_name
        .rsplit_once('.')
        .map(|(namespace, _)| namespace)
        .unwrap_or(caller_fq_name)
}

fn namespace_tree_root(namespace: &str) -> &str {
    namespace
        .rsplit_once('.')
        .map(|(root, _)| root)
        .unwrap_or("")
}

fn resolve_target_in_namespace(target: &str, namespace: &str) -> String {
    if let Some((module_path, proc_name)) = target.rsplit_once("::") {
        let root = namespace_tree_root(namespace);
        let module_namespace = lean_module_path_from_target(module_path);
        let proc_name = sanitize_lean_name(proc_name);
        if root.is_empty() {
            format!("{}.{}", module_namespace, proc_name)
        } else {
            format!("{}.{}.{}", root, module_namespace, proc_name)
        }
    } else {
        let sanitized = sanitize_lean_name(target);
        format!("{}.{}", namespace, sanitized)
    }
}

/// Convert an exec target name (e.g., "overflowing_add" or "word::lt") to a
/// fully-qualified Lean name by using the namespace tree of the calling procedure.
fn sanitize_lean_target(target: &str, caller_fq_name: &str) -> String {
    resolve_target_in_namespace(target, caller_namespace(caller_fq_name))
}

fn target_generated_import(target: &str, current_generated_import: &str) -> Option<String> {
    let (module_path, _) = target.rsplit_once("::")?;
    let import_root = current_generated_import
        .rsplit_once('.')
        .map(|(root, _)| root)
        .unwrap_or(current_generated_import);
    let module_segments: Vec<_> = module_path
        .split("::")
        .filter(|segment| !segment.is_empty())
        .collect();
    let module_leaf = module_segments.last()?;
    Some(format!(
        "{}.{}",
        import_root,
        capitalize_segment(&sanitize_lean_name(module_leaf))
    ))
}

fn collect_generated_imports(
    generated_import: &str,
    skeletons: &[ProcSkeleton],
) -> BTreeSet<String> {
    let mut imports = BTreeSet::new();
    imports.insert(generated_import.to_string());

    for skel in skeletons {
        for op in &skel.body_ops {
            if let FlatOp::Instruction {
                exec_target: Some(target),
                ..
            } = op
            {
                if let Some(import_path) = target_generated_import(target, generated_import) {
                    imports.insert(import_path);
                }
            }
        }
    }

    imports
}

/// Generate parameter names for the given input arity.
/// Uses a/b/c/d for up to 4 parameters, x0..xN for larger arities.
fn generate_param_names(input_arity: usize) -> Vec<String> {
    if input_arity <= 4 {
        let names = ["a", "b", "c", "d"];
        names[..input_arity].iter().map(|s| s.to_string()).collect()
    } else {
        (0..input_arity).map(|i| format!("x{}", i)).collect()
    }
}

/// Compute the fuel value for a procedure.
/// For procedures with calls, uses a generous formula since the callee instruction
/// counts are already included in the instruction_count via inter-procedural analysis.
fn compute_fuel(stack_effect: &ProcStackEffect) -> usize {
    // Base fuel is instruction count + slack for procedure calls and loops
    let base = stack_effect.instruction_count;
    let call_slack = if stack_effect.has_calls {
        // Use a generous multiplier: callee instruction counts may not be fully
        // captured, and each call adds overhead for the exec dispatch.
        base * 2 + 20
    } else {
        0
    };
    let loop_slack = if stack_effect.has_loops { 20 } else { 0 };
    let repeat_slack = if stack_effect.has_repeats { 10 } else { 0 };
    base + call_slack + loop_slack + repeat_slack + 5 // +5 for safety margin
}

/// Emit the theorem statement for a procedure.
fn emit_theorem_statement(skel: &ProcSkeleton) -> String {
    let mut out = String::new();
    let param_names = generate_param_names(skel.hypotheses.input_arity);
    let fuel = compute_fuel(&skel.stack_effect);

    // Docstring
    out.push_str(&format!(
        "/-- {}.{}: (auto-generated skeleton)\n",
        skel.module_prefix, skel.masm_name
    ));
    out.push_str(&format!(
        "    Input stack:  [{}] ++ rest\n",
        param_names.join(", ")
    ));
    out.push_str("    Output stack: [sorry] ++ rest -/\n");

    // Theorem signature
    out.push_str(&format!("theorem {}\n", skel.theorem_name));

    // Parameters
    if !param_names.is_empty() {
        out.push_str(&format!(
            "    ({} : Felt) (rest : List Felt) (s : MidenState)\n",
            param_names.join(" ")
        ));
    } else {
        out.push_str("    (rest : List Felt) (s : MidenState)\n");
    }

    // Stack hypothesis
    let stack_expr = if param_names.is_empty() {
        "rest".to_string()
    } else {
        format!(
            "{} :: rest",
            param_names
                .iter()
                .map(|s| s.as_str())
                .collect::<Vec<_>>()
                .join(" :: ")
        )
    };
    out.push_str(&format!("    (hs : s.stack = {})\n", stack_expr));

    // Advice hypothesis if needed
    if skel.hypotheses.advice_consumed > 0 {
        let adv_names: Vec<String> = (0..skel.hypotheses.advice_consumed)
            .map(|i| format!("v{}", i))
            .collect();
        out.push_str(&format!(
            "    ({} : Felt) (adv_rest : List Felt)\n",
            adv_names.join(" ")
        ));
        out.push_str(&format!(
            "    (hadv : s.advice = {} :: adv_rest)\n",
            adv_names.join(" :: ")
        ));
    }

    // isU32 hypotheses
    for h in &skel.hypotheses.hypotheses {
        match &h.kind {
            HypothesisKind::IsU32 => {
                if h.entry_position < param_names.len() {
                    let param = &param_names[h.entry_position];
                    out.push_str(&format!(
                        "    (h{}_u32 : {}.isU32 = true)  -- from {} at instruction {}\n",
                        param, param, h.instruction_name, h.instruction_index
                    ));
                }
            }
            HypothesisKind::ValLeq63 => {
                if h.entry_position < param_names.len() {
                    let param = &param_names[h.entry_position];
                    out.push_str(&format!(
                        "    (h{}_leq63 : {}.val ≤ 63)  -- from {} at instruction {}\n",
                        param, param, h.instruction_name, h.instruction_index
                    ));
                }
            }
            HypothesisKind::AdviceLength(_) => {
                // Already handled by advice hypothesis above
            }
        }
    }

    // Result type
    out.push_str("    :\n");
    let exec_fn = if skel.needs_proc_env {
        format!("execWithEnv {}ProcEnv", skel.module_prefix)
    } else {
        "exec".to_string()
    };
    out.push_str(&format!(
        "    {} {} s {} =\n",
        exec_fn, fuel, skel.fq_lean_name
    ));
    out.push_str("    some (s.withStack (sorry :: rest))  -- TODO: specify output\n");
    out.push_str("    := by\n");

    out
}

/// Emit the proof body for a procedure.
fn emit_proof_body(skel: &ProcSkeleton) -> String {
    let mut out = String::new();

    // Setup tactic: use miden_setup_env for procedures with calls, miden_setup otherwise
    let setup_tactic = if skel.needs_proc_env {
        "miden_setup_env"
    } else {
        "miden_setup"
    };
    out.push_str(&format!("  {} {}\n", setup_tactic, skel.fq_lean_name));

    // Emit tactic calls for each operation
    for flat_op in &skel.body_ops {
        match flat_op {
            FlatOp::Instruction {
                index,
                lean_repr,
                is_exec,
                exec_target,
                has_step_lemma,
                needs_hypothesis,
                ..
            } => {
                if *is_exec {
                    let target_name = exec_target.as_deref().unwrap_or("unknown");
                    // Convert MASM target name to Lean qualified name
                    let lean_target = sanitize_lean_target(target_name, &skel.fq_lean_name);
                    out.push_str(&format!("  -- Instruction {}: {}\n", index + 1, lean_repr));
                    out.push_str(&format!("  simp only [{}ProcEnv]\n", skel.module_prefix));
                    out.push_str(&format!("  miden_call {}\n", lean_target));
                } else if *has_step_lemma {
                    if *needs_hypothesis {
                        out.push_str(&format!(
                            "  -- Instruction {}: {} (requires hypothesis)\n",
                            index + 1,
                            lean_repr
                        ));
                    } else {
                        out.push_str(&format!("  -- Instruction {}: {}\n", index + 1, lean_repr));
                    }
                    out.push_str("  miden_step\n");
                } else {
                    out.push_str(&format!(
                        "  -- Instruction {}: {} (no step lemma yet)\n",
                        index + 1,
                        lean_repr
                    ));
                    out.push_str("  sorry  -- TODO: manual tactic for this instruction\n");
                }
            }
            FlatOp::RepeatStart { count } => {
                out.push_str(&format!("  -- repeat {} begin\n", count));
                out.push_str(&format!(
                    "  repeat miden_loop  -- unfolds {} iterations\n",
                    count
                ));
            }
            FlatOp::RepeatEnd => {
                out.push_str("  -- repeat end\n");
            }
            FlatOp::IfStart => {
                out.push_str("  -- if.true begin\n");
                out.push_str("  sorry  -- TODO: branch handling (MANUAL)\n");
            }
            FlatOp::IfElse => {
                out.push_str("  -- else\n");
            }
            FlatOp::IfEnd => {
                out.push_str("  -- if.true end\n");
            }
            FlatOp::WhileStart => {
                out.push_str("  -- while.true begin\n");
                out.push_str("  sorry  -- TODO: while loop handling (MANUAL)\n");
            }
            FlatOp::WhileEnd => {
                out.push_str("  -- while.true end\n");
            }
        }
    }

    // If there are value recovery needs, add a sorry
    if skel.classification != Classification::Auto {
        out.push_str("  -- TODO: value recovery / remaining goals\n");
        out.push_str("  sorry\n");
    }

    out
}

/// Generate a complete proof skeleton file for a module.
pub fn generate_proof_skeletons(
    module: &Module,
    namespace: &str,
    module_prefix: &str,
    generated_import: &str,
) -> Result<String> {
    let mut out = String::new();

    // Collect classification summary
    let mut auto_count = 0;
    let mut semi_count = 0;
    let mut manual_count = 0;

    // Two-pass analysis for inter-procedural stack effects.
    // Pass 1: Analyze all procedures independently.
    let mut first_pass_effects: HashMap<String, ProcStackEffect> = HashMap::new();
    for proc in module.procedures() {
        let name = proc.name().to_string();
        let effect = analyze_block(proc.body());
        first_pass_effects.insert(name, effect);
    }

    // Pass 2: Re-analyze procedures that have calls, using first-pass results.
    let mut final_effects: HashMap<String, ProcStackEffect> = HashMap::new();
    for proc in module.procedures() {
        let name = proc.name().to_string();
        let first_effect = first_pass_effects.get(&name).unwrap();
        let effect = if first_effect.has_calls {
            analyze_block_with_callees(proc.body(), Some(&first_pass_effects))
        } else {
            first_effect.clone()
        };
        final_effects.insert(name.clone(), effect);
    }

    // Build skeletons using the refined effects.
    let mut skeletons = Vec::new();
    for proc in module.procedures() {
        let name = proc.name().to_string();
        let lean_def_name = sanitize_lean_name(&name);
        let theorem_name = format!("{}_{}_correct", module_prefix, name.replace('-', "_"));
        let fq_lean_name = format!("{}.{}", namespace, lean_def_name);

        let stack_effect = final_effects.get(&name).unwrap().clone();
        let hypotheses = infer_hypotheses(proc.body(), stack_effect.input_arity);
        let classification = classify(proc.body(), &stack_effect, &hypotheses);

        match classification {
            Classification::Auto => auto_count += 1,
            Classification::Semi => semi_count += 1,
            Classification::Manual => manual_count += 1,
        }

        let mut body_ops = Vec::new();
        let mut index = 0;
        flatten_block(proc.body(), &mut index, &mut body_ops);

        skeletons.push(ProcSkeleton {
            masm_name: name,
            lean_def_name,
            theorem_name,
            fq_lean_name,
            stack_effect: stack_effect.clone(),
            hypotheses,
            classification,
            body_ops,
            needs_proc_env: stack_effect.has_calls,
            module_prefix: module_prefix.to_string(),
        });
    }

    // File header
    out.push_str(&format!(
        "-- Generated by masm-to-lean proof skeleton generator.\n"
    ));
    out.push_str(&format!(
        "-- Classification summary: {} AUTO, {} SEMI, {} MANUAL\n",
        auto_count, semi_count, manual_count
    ));
    out.push_str("-- DO NOT EDIT: copy to MidenLean/Proofs/ and fill sorry holes there.\n\n");
    let generated_imports = collect_generated_imports(generated_import, &skeletons);

    out.push_str("import MidenLean.Proofs.Tactics\n");
    for import_path in generated_imports {
        out.push_str(&format!("import {}\n", import_path));
    }
    out.push('\n');
    out.push_str("namespace MidenLean.Proofs.Generated\n\n");
    out.push_str("open MidenLean\n");
    out.push_str("open MidenLean.StepLemmas\n");
    out.push_str("open MidenLean.Tactics\n");

    // Generate each procedure's skeleton
    for skel in &skeletons {
        out.push('\n');
        out.push_str(&format!(
            "-- Classification: {} | Instructions: {} | Inputs: {} | Calls: {} | Branches: {} | Loops: {} | Advice: {}\n",
            skel.classification,
            skel.stack_effect.instruction_count,
            skel.hypotheses.input_arity,
            skel.stack_effect.has_calls,
            skel.stack_effect.has_branches,
            skel.stack_effect.has_loops,
            skel.hypotheses.advice_consumed > 0,
        ));

        let heartbeats = if skel.stack_effect.instruction_count > 20 {
            8000000
        } else {
            4000000
        };
        out.push_str(&format!("set_option maxHeartbeats {} in\n", heartbeats));
        out.push_str(&emit_theorem_statement(skel));
        out.push_str(&emit_proof_body(skel));
        out.push('\n');
    }

    // ProcEnv definition if any procedure has calls
    let has_any_calls = skeletons.iter().any(|s| s.needs_proc_env);
    if has_any_calls {
        // Collect all exec targets
        let mut exec_targets: Vec<String> = Vec::new();
        for skel in &skeletons {
            for op in &skel.body_ops {
                if let FlatOp::Instruction {
                    exec_target: Some(target),
                    ..
                } = op
                {
                    if !exec_targets.contains(target) {
                        exec_targets.push(target.clone());
                    }
                }
            }
        }

        out.push_str(&format!(
            "\ndef {}ProcEnv : ProcEnv := fun name =>\n",
            module_prefix
        ));
        out.push_str("  match name with\n");
        for target in &exec_targets {
            let lean_name = resolve_target_in_namespace(target, namespace);
            out.push_str(&format!("  | \"{}\" => some {}\n", target, lean_name));
        }
        out.push_str("  | _ => none\n");
    }

    out.push_str(&format!("\nend MidenLean.Proofs.Generated\n"));

    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::classifier::Classification;
    use crate::hypothesis::ProcHypotheses;
    use crate::stack_effect::ProcStackEffect;

    fn dummy_stack_effect() -> ProcStackEffect {
        ProcStackEffect {
            input_arity: 0,
            output_arity: 0,
            net_effect: 0,
            instruction_count: 0,
            has_branches: false,
            has_loops: false,
            has_repeats: false,
            has_calls: false,
            has_advice: false,
            is_precise: true,
        }
    }

    #[test]
    fn test_sanitize_lean_target_local_symbol() {
        assert_eq!(
            sanitize_lean_target("lt", "Miden.Core.U64.min"),
            "Miden.Core.U64.lt"
        );
    }

    #[test]
    fn test_sanitize_lean_target_path_target() {
        assert_eq!(
            sanitize_lean_target("word::lt", "Miden.Core.U64.divmod"),
            "Miden.Core.Word.lt"
        );
    }

    #[test]
    fn test_emit_proof_body_does_not_use_invalid_with_hadv_syntax() {
        let skel = ProcSkeleton {
            masm_name: "divmod".into(),
            lean_def_name: "divmod".into(),
            theorem_name: "u64_divmod_correct".into(),
            fq_lean_name: "Miden.Core.U64.divmod".into(),
            stack_effect: dummy_stack_effect(),
            hypotheses: ProcHypotheses {
                input_arity: 0,
                hypotheses: vec![],
                advice_consumed: 4,
            },
            classification: Classification::Manual,
            body_ops: vec![],
            needs_proc_env: true,
            module_prefix: "u64".into(),
        };

        let body = emit_proof_body(&skel);
        assert!(body.starts_with("  miden_setup_env Miden.Core.U64.divmod\n"));
        assert!(!body.contains("with hadv"));
    }

    #[test]
    fn test_collect_generated_imports_includes_cross_module_targets() {
        let skel = ProcSkeleton {
            masm_name: "divmod".into(),
            lean_def_name: "divmod".into(),
            theorem_name: "u64_divmod_correct".into(),
            fq_lean_name: "Miden.Core.U64.divmod".into(),
            stack_effect: dummy_stack_effect(),
            hypotheses: ProcHypotheses {
                input_arity: 0,
                hypotheses: vec![],
                advice_consumed: 0,
            },
            classification: Classification::Semi,
            body_ops: vec![FlatOp::Instruction {
                index: 0,
                lean_repr: "exec \"word::lt\"".into(),
                needs_hypothesis: false,
                is_exec: true,
                exec_target: Some("word::lt".into()),
                has_step_lemma: false,
            }],
            needs_proc_env: true,
            module_prefix: "u64".into(),
        };

        let imports = collect_generated_imports("MidenLean.Generated.U64", &[skel]);

        assert!(imports.contains("MidenLean.Generated.U64"));
        assert!(imports.contains("MidenLean.Generated.Word"));
    }
}
