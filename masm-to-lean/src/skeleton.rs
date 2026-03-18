//! Proof skeleton generation for MASM procedures.
//!
//! Generates Lean 4 proof files containing:
//! - Theorem statements with typed inputs, preconditions, and sorry output
//! - Proof bodies using the tactic API contract (miden_setup, miden_step, etc.)
//! - Complexity classification annotations

use std::collections::{BTreeSet, HashMap};

use anyhow::Result;
use miden_assembly_syntax::ast::{Block, Immediate, Instruction, InvocationTarget, Module, Op};

use crate::classifier::{choose_scaffold_style, classify, Classification, ScaffoldStyle};
use crate::hypothesis::{infer_hypotheses, HypothesisKind, ProcHypotheses};
use crate::instruction_info::{BarrierKind, ProofStepKind};
use crate::module::sanitize_lean_name;
use crate::stack_effect::{analyze_block, analyze_block_with_callees, ProcStackEffect};

/// One generated proof-related file.
pub struct GeneratedProofFile {
    pub relative_path: String,
    pub content: String,
}

/// All generated proof files for a module.
pub struct GeneratedProofModule {
    pub files: Vec<GeneratedProofFile>,
    pub auto_count: usize,
    pub semi_count: usize,
    pub manual_count: usize,
}

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
    /// Shape to use for proof emission.
    scaffold_style: ScaffoldStyle,
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
        exec_target: Option<String>,
        proof_step_kind: ProofStepKind,
        barrier: Option<BarrierKind>,
    },
    /// Start of a single unfolded repeat iteration.
    RepeatIteration { iteration: usize, total: usize },
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
            let exec_target = match inst {
                Instruction::Exec(t) | Instruction::Call(t) => match t {
                    InvocationTarget::Symbol(ident) => Some(ident.as_str().to_string()),
                    InvocationTarget::Path(path) => Some(path.to_string()),
                    _ => None,
                },
                _ => None,
            };
            let proof_step_kind = inst_proof_step_kind(inst);
            let barrier = inst_barrier_kind(inst);

            // For imm variants that expand to push+op, emit two entries
            if is_multi_op_expansion(inst) {
                ops.push(FlatOp::Instruction {
                    index: *index,
                    lean_repr: format!("push (imm for {})", lean_repr),
                    needs_hypothesis: false,
                    exec_target: None,
                    proof_step_kind: ProofStepKind::ExplicitRewrite("stepPush"),
                    barrier: None,
                });
                *index += 1;
                ops.push(FlatOp::Instruction {
                    index: *index,
                    lean_repr,
                    needs_hypothesis,
                    exec_target: None,
                    proof_step_kind,
                    barrier,
                });
                *index += 1;
            } else {
                ops.push(FlatOp::Instruction {
                    index: *index,
                    lean_repr,
                    needs_hypothesis,
                    exec_target,
                    proof_step_kind,
                    barrier,
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
                Immediate::Constant(_) => 1,
            };
            for iteration in 0..n.max(1) {
                ops.push(FlatOp::RepeatIteration {
                    iteration: iteration + 1,
                    total: n.max(1),
                });
                flatten_block(body, index, ops);
            }
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

/// Determine the emitted proof-step shape for an instruction.
fn inst_proof_step_kind(inst: &Instruction) -> ProofStepKind {
    crate::instruction_info::proof_step_kind(inst)
}

/// Determine whether an instruction should trigger a chunk boundary.
fn inst_barrier_kind(inst: &Instruction) -> Option<BarrierKind> {
    crate::instruction_info::barrier_kind(inst)
}

fn capitalize_segment(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
        None => String::new(),
    }
}

fn procedure_module_name(masm_name: &str) -> String {
    sanitize_lean_name(masm_name)
        .split('_')
        .filter(|segment| !segment.is_empty())
        .map(capitalize_segment)
        .collect::<Vec<_>>()
        .join("")
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

fn proof_namespace(lean_name: &str) -> String {
    format!("MidenLean.Proofs.Generated.{}", lean_name)
}

fn proof_common_import_path(lean_name: &str) -> String {
    format!("{}.Common", proof_namespace(lean_name))
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

#[derive(Debug, Clone)]
struct ChunkSpec {
    name: String,
    ops: Vec<FlatOp>,
}

fn plan_chunks(ops: &[FlatOp]) -> Vec<ChunkSpec> {
    let mut chunks = Vec::new();
    let mut current = Vec::new();

    for flat_op in ops {
        current.push(flat_op.clone());

        let should_split = match flat_op {
            FlatOp::Instruction {
                barrier: Some(_), ..
            } => current.len() >= 4,
            _ => current.len() >= 12,
        };

        if should_split {
            let name = format!("chunk{}", chunks.len() + 1);
            chunks.push(ChunkSpec {
                name,
                ops: std::mem::take(&mut current),
            });
        }
    }

    if !current.is_empty() {
        let name = format!("chunk{}", chunks.len() + 1);
        chunks.push(ChunkSpec { name, ops: current });
    }

    chunks
}

fn emit_instruction_step(
    out: &mut String,
    module_prefix: &str,
    caller_fq_name: &str,
    scaffold_style: ScaffoldStyle,
    index: usize,
    lean_repr: &str,
    needs_hypothesis: bool,
    exec_target: Option<&str>,
    proof_step_kind: ProofStepKind,
) {
    if needs_hypothesis {
        out.push_str(&format!(
            "  -- Instruction {}: {} (requires hypothesis)\n",
            index + 1,
            lean_repr
        ));
    } else {
        out.push_str(&format!("  -- Instruction {}: {}\n", index + 1, lean_repr));
    }

    if matches!(
        scaffold_style,
        ScaffoldStyle::Chunked | ScaffoldStyle::Manual
    ) {
        out.push_str("  -- TODO: fill this step inside the chunked/manual scaffold\n");
        return;
    }

    match proof_step_kind {
        ProofStepKind::StructuralTactic(tactic) => {
            out.push_str(&format!("  try {}\n", tactic));
        }
        ProofStepKind::ExplicitRewrite(lemma) => {
            out.push_str(&format!("  try (rw [{}]; miden_bind)\n", lemma));
        }
        ProofStepKind::Search => {
            if matches!(
                scaffold_style,
                ScaffoldStyle::FlatAuto | ScaffoldStyle::FlatExplicit
            ) {
                out.push_str("  try miden_step\n");
            } else {
                out.push_str("  -- TODO: generic step search or manual follow-up\n");
            }
        }
        ProofStepKind::ProcCall => {
            let target_name = exec_target.unwrap_or("unknown");
            let lean_target = sanitize_lean_target(target_name, caller_fq_name);
            out.push_str(&format!("  try (simp only [{}ProcEnv])\n", module_prefix));
            out.push_str(&format!("  try (miden_call {})\n", lean_target));
        }
        ProofStepKind::ManualOnly => {
            out.push_str("  -- TODO: manual tactic for this instruction\n");
        }
    }
}

fn emit_chunk(out: &mut String, skel: &ProcSkeleton, name: &str, ops: &[FlatOp]) {
    if skel.scaffold_style == ScaffoldStyle::Chunked {
        out.push_str(&format!("  -- {} begin\n", name));
    }

    for flat_op in ops {
        match flat_op {
            FlatOp::Instruction {
                index,
                lean_repr,
                needs_hypothesis,
                exec_target,
                proof_step_kind,
                ..
            } => emit_instruction_step(
                out,
                &skel.module_prefix,
                &skel.fq_lean_name,
                skel.scaffold_style,
                *index,
                lean_repr,
                *needs_hypothesis,
                exec_target.as_deref(),
                *proof_step_kind,
            ),
            FlatOp::RepeatIteration { iteration, total } => {
                out.push_str(&format!("  -- repeat iteration {}/{}\n", iteration, total));
                out.push_str("  try miden_loop\n");
            }
            FlatOp::IfStart => {
                out.push_str("  -- if.true begin\n");
                out.push_str("  try sorry  -- TODO: branch handling (MANUAL)\n");
            }
            FlatOp::IfElse => {
                out.push_str("  -- else\n");
            }
            FlatOp::IfEnd => {
                out.push_str("  -- if.true end\n");
            }
            FlatOp::WhileStart => {
                out.push_str("  -- while.true begin\n");
                out.push_str("  try sorry  -- TODO: while loop handling (MANUAL)\n");
            }
            FlatOp::WhileEnd => {
                out.push_str("  -- while.true end\n");
            }
        }
    }

    if skel.scaffold_style == ScaffoldStyle::Chunked {
        out.push_str(&format!("  -- {} end\n", name));
    }
}

/// Emit the proof body for a procedure.
fn emit_proof_body(skel: &ProcSkeleton) -> String {
    let mut out = String::new();

    if matches!(
        skel.scaffold_style,
        ScaffoldStyle::FlatAuto | ScaffoldStyle::FlatExplicit
    ) {
        // Setup tactic: use miden_setup_env for procedures with calls, miden_setup otherwise
        let setup_tactic = if skel.needs_proc_env {
            "miden_setup_env"
        } else {
            "miden_setup"
        };
        out.push_str(&format!("  {} {}\n", setup_tactic, skel.fq_lean_name));
    } else {
        out.push_str("  -- Chunked/manual scaffold: fill chunk lemmas or manual proof here.\n");
    }

    let chunks = if skel.scaffold_style == ScaffoldStyle::Chunked {
        plan_chunks(&skel.body_ops)
    } else {
        vec![ChunkSpec {
            name: "chunk1".into(),
            ops: skel.body_ops.clone(),
        }]
    };

    for chunk in &chunks {
        emit_chunk(&mut out, skel, &chunk.name, &chunk.ops);
    }

    out.push_str("  try (simp only [pure, Pure.pure])\n");
    out.push_str("  try rfl\n");
    out.push_str("  all_goals sorry\n");

    out
}

fn build_skeletons(
    module: &Module,
    namespace: &str,
    module_prefix: &str,
) -> (Vec<ProcSkeleton>, usize, usize, usize) {
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
        let scaffold_style = choose_scaffold_style(proc.body(), &stack_effect, &hypotheses);

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
            scaffold_style,
            body_ops,
            needs_proc_env: stack_effect.has_calls,
            module_prefix: module_prefix.to_string(),
        });
    }

    (skeletons, auto_count, semi_count, manual_count)
}

fn emit_proc_env(namespace: &str, module_prefix: &str, skeletons: &[ProcSkeleton]) -> String {
    let mut out = String::new();

    let has_any_calls = skeletons.iter().any(|s| s.needs_proc_env);
    if !has_any_calls {
        return out;
    }

    let mut exec_targets: Vec<String> = Vec::new();
    for skel in skeletons {
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

    out
}

fn emit_common_file(
    lean_name: &str,
    namespace: &str,
    module_prefix: &str,
    generated_import: &str,
    skeletons: &[ProcSkeleton],
) -> String {
    let mut out = String::new();
    let generated_imports = collect_generated_imports(generated_import, skeletons);
    let proof_ns = proof_namespace(lean_name);

    out.push_str("-- Generated by masm-to-lean proof skeleton generator.\n");
    out.push_str("-- Shared support for per-procedure proof skeleton files.\n\n");
    out.push_str("import MidenLean.Proofs.Tactics\n");
    for import_path in generated_imports {
        out.push_str(&format!("import {}\n", import_path));
    }
    out.push('\n');
    out.push_str(&format!("namespace {}\n\n", proof_ns));
    out.push_str("open MidenLean\n");
    out.push_str("open MidenLean.StepLemmas\n");
    out.push_str("open MidenLean.Tactics\n");
    out.push_str("set_option linter.unreachableTactic false\n");
    out.push_str("set_option linter.unusedTactic false\n");
    out.push_str(&emit_proc_env(namespace, module_prefix, skeletons));
    out.push_str(&format!("\nend {}\n", proof_ns));

    out
}

fn emit_procedure_file(lean_name: &str, skel: &ProcSkeleton) -> String {
    let mut out = String::new();
    let proof_ns = proof_namespace(lean_name);

    out.push_str("-- Generated by masm-to-lean proof skeleton generator.\n");
    out.push_str("-- DO NOT EDIT: copy to MidenLean/Proofs/ and fill sorry holes there.\n\n");
    out.push_str(&format!(
        "import {}\n\n",
        proof_common_import_path(lean_name)
    ));
    out.push_str(&format!("namespace {}\n\n", proof_ns));
    out.push_str("open MidenLean\n");
    out.push_str("open MidenLean.StepLemmas\n");
    out.push_str("open MidenLean.Tactics\n");
    out.push_str("set_option linter.unreachableTactic false\n");
    out.push_str("set_option linter.unusedTactic false\n");
    out.push_str(&format!(
        "-- Classification: {} | Style: {} | Instructions: {} | Inputs: {} | Calls: {} | Branches: {} | Loops: {} | Advice: {}\n",
        skel.classification,
        skel.scaffold_style,
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
    out.push_str(&format!("\nend {}\n", proof_ns));

    out
}

fn emit_module_index(
    lean_name: &str,
    auto_count: usize,
    semi_count: usize,
    manual_count: usize,
    skeletons: &[ProcSkeleton],
) -> String {
    let mut out = String::new();

    out.push_str("-- Generated by masm-to-lean proof skeleton generator.\n");
    out.push_str(&format!(
        "-- Classification summary: {} AUTO, {} SEMI, {} MANUAL\n",
        auto_count, semi_count, manual_count
    ));
    out.push_str("-- Per-procedure proof scaffolding index.\n");
    out.push_str("-- Import individual procedure files from the corresponding subdirectory.\n\n");
    out.push_str(&format!("import {}\n", proof_common_import_path(lean_name)));
    out.push('\n');
    for skel in skeletons {
        out.push_str(&format!(
            "-- {}.{}\n",
            proof_namespace(lean_name),
            procedure_module_name(&skel.masm_name)
        ));
    }

    out
}

/// Generate per-procedure proof skeleton files for a module.
pub fn generate_proof_skeletons(
    module: &Module,
    lean_name: &str,
    namespace: &str,
    module_prefix: &str,
    generated_import: &str,
) -> Result<GeneratedProofModule> {
    let mut files = Vec::new();
    let (skeletons, auto_count, semi_count, manual_count) =
        build_skeletons(module, namespace, module_prefix);

    files.push(GeneratedProofFile {
        relative_path: format!("{lean_name}.lean"),
        content: emit_module_index(lean_name, auto_count, semi_count, manual_count, &skeletons),
    });

    files.push(GeneratedProofFile {
        relative_path: format!("{lean_name}/Common.lean"),
        content: emit_common_file(
            lean_name,
            namespace,
            module_prefix,
            generated_import,
            &skeletons,
        ),
    });

    for skel in &skeletons {
        files.push(GeneratedProofFile {
            relative_path: format!(
                "{lean_name}/{}.lean",
                procedure_module_name(&skel.masm_name)
            ),
            content: emit_procedure_file(lean_name, skel),
        });
    }

    Ok(GeneratedProofModule {
        files,
        auto_count,
        semi_count,
        manual_count,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::classifier::{Classification, ScaffoldStyle};
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
    fn test_procedure_module_name_uses_pascal_case() {
        assert_eq!(procedure_module_name("wrapping_mul"), "WrappingMul");
        assert_eq!(procedure_module_name("shr"), "Shr");
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
            classification: Classification::Semi,
            scaffold_style: ScaffoldStyle::FlatExplicit,
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
            scaffold_style: ScaffoldStyle::FlatExplicit,
            body_ops: vec![FlatOp::Instruction {
                index: 0,
                lean_repr: "exec \"word::lt\"".into(),
                needs_hypothesis: false,
                exec_target: Some("word::lt".into()),
                proof_step_kind: ProofStepKind::ProcCall,
                barrier: Some(BarrierKind::ProcCall),
            }],
            needs_proc_env: true,
            module_prefix: "u64".into(),
        };

        let imports = collect_generated_imports("MidenLean.Generated.U64", &[skel]);

        assert!(imports.contains("MidenLean.Generated.U64"));
        assert!(imports.contains("MidenLean.Generated.Word"));
    }

    #[test]
    fn test_emit_flat_explicit_proof_uses_step_add() {
        let skel = ProcSkeleton {
            masm_name: "add".into(),
            lean_def_name: "add".into(),
            theorem_name: "u64_add_correct".into(),
            fq_lean_name: "Miden.Core.U64.add".into(),
            stack_effect: dummy_stack_effect(),
            hypotheses: ProcHypotheses {
                input_arity: 0,
                hypotheses: vec![],
                advice_consumed: 0,
            },
            classification: Classification::Auto,
            scaffold_style: ScaffoldStyle::FlatExplicit,
            body_ops: vec![FlatOp::Instruction {
                index: 0,
                lean_repr: "add".into(),
                needs_hypothesis: false,
                exec_target: None,
                proof_step_kind: ProofStepKind::ExplicitRewrite("stepAdd"),
                barrier: None,
            }],
            needs_proc_env: false,
            module_prefix: "u64".into(),
        };

        let body = emit_proof_body(&skel);
        assert!(body.contains("try (rw [stepAdd]; miden_bind)"));
        assert!(!body.contains("  miden_step\n"));
    }

    #[test]
    fn test_emit_flat_explicit_proof_uses_structural_tactic_for_swap() {
        let skel = ProcSkeleton {
            masm_name: "swap".into(),
            lean_def_name: "swap".into(),
            theorem_name: "u64_swap_correct".into(),
            fq_lean_name: "Miden.Core.U64.swap".into(),
            stack_effect: dummy_stack_effect(),
            hypotheses: ProcHypotheses {
                input_arity: 0,
                hypotheses: vec![],
                advice_consumed: 0,
            },
            classification: Classification::Auto,
            scaffold_style: ScaffoldStyle::FlatExplicit,
            body_ops: vec![FlatOp::Instruction {
                index: 0,
                lean_repr: "swap 1".into(),
                needs_hypothesis: false,
                exec_target: None,
                proof_step_kind: ProofStepKind::StructuralTactic("miden_swap"),
                barrier: None,
            }],
            needs_proc_env: false,
            module_prefix: "u64".into(),
        };

        let body = emit_proof_body(&skel);
        assert!(body.contains("try miden_swap"));
    }

    #[test]
    fn test_chunk_planner_splits_shr_like_sequence_at_expected_points() {
        let ops = vec![
            FlatOp::Instruction {
                index: 0,
                lean_repr: "movup 2".into(),
                needs_hypothesis: false,
                exec_target: None,
                proof_step_kind: ProofStepKind::StructuralTactic("miden_movup"),
                barrier: None,
            },
            FlatOp::Instruction {
                index: 1,
                lean_repr: "swap 1".into(),
                needs_hypothesis: false,
                exec_target: None,
                proof_step_kind: ProofStepKind::StructuralTactic("miden_swap"),
                barrier: None,
            },
            FlatOp::Instruction {
                index: 2,
                lean_repr: "pow2".into(),
                needs_hypothesis: true,
                exec_target: None,
                proof_step_kind: ProofStepKind::Search,
                barrier: Some(BarrierKind::Pow2),
            },
            FlatOp::Instruction {
                index: 3,
                lean_repr: "u32Split".into(),
                needs_hypothesis: false,
                exec_target: None,
                proof_step_kind: ProofStepKind::ExplicitRewrite("stepU32Split"),
                barrier: None,
            },
            FlatOp::Instruction {
                index: 4,
                lean_repr: "swap 1".into(),
                needs_hypothesis: false,
                exec_target: None,
                proof_step_kind: ProofStepKind::StructuralTactic("miden_swap"),
                barrier: None,
            },
            FlatOp::Instruction {
                index: 5,
                lean_repr: "dup 1".into(),
                needs_hypothesis: false,
                exec_target: None,
                proof_step_kind: ProofStepKind::StructuralTactic("miden_dup"),
                barrier: None,
            },
            FlatOp::Instruction {
                index: 6,
                lean_repr: "u32DivMod".into(),
                needs_hypothesis: true,
                exec_target: None,
                proof_step_kind: ProofStepKind::Search,
                barrier: Some(BarrierKind::U32DivMod),
            },
            FlatOp::Instruction {
                index: 7,
                lean_repr: "u32OverflowSub".into(),
                needs_hypothesis: true,
                exec_target: None,
                proof_step_kind: ProofStepKind::Search,
                barrier: Some(BarrierKind::U32OverflowSub),
            },
            FlatOp::Instruction {
                index: 8,
                lean_repr: "u32DivMod".into(),
                needs_hypothesis: true,
                exec_target: None,
                proof_step_kind: ProofStepKind::Search,
                barrier: Some(BarrierKind::U32DivMod),
            },
            FlatOp::Instruction {
                index: 9,
                lean_repr: "div".into(),
                needs_hypothesis: true,
                exec_target: None,
                proof_step_kind: ProofStepKind::Search,
                barrier: Some(BarrierKind::Div),
            },
        ];

        let chunks = plan_chunks(&ops);
        assert!(chunks.len() >= 2);
        assert_eq!(chunks[0].name, "chunk1");
        assert!(chunks.iter().any(|chunk| {
            chunk.ops.iter().any(|op| {
                matches!(
                    op,
                    FlatOp::Instruction {
                        barrier: Some(BarrierKind::U32DivMod),
                        ..
                    }
                )
            })
        }));
    }

    #[test]
    fn test_chunked_emission_contains_chunk_markers() {
        let skel = ProcSkeleton {
            masm_name: "shr".into(),
            lean_def_name: "shr".into(),
            theorem_name: "u64_shr_correct".into(),
            fq_lean_name: "Miden.Core.U64.shr".into(),
            stack_effect: ProcStackEffect {
                instruction_count: 24,
                ..dummy_stack_effect()
            },
            hypotheses: ProcHypotheses {
                input_arity: 0,
                hypotheses: vec![],
                advice_consumed: 0,
            },
            classification: Classification::Semi,
            scaffold_style: ScaffoldStyle::Chunked,
            body_ops: vec![
                FlatOp::Instruction {
                    index: 0,
                    lean_repr: "pow2".into(),
                    needs_hypothesis: true,
                    exec_target: None,
                    proof_step_kind: ProofStepKind::Search,
                    barrier: Some(BarrierKind::Pow2),
                },
                FlatOp::Instruction {
                    index: 1,
                    lean_repr: "swap 1".into(),
                    needs_hypothesis: false,
                    exec_target: None,
                    proof_step_kind: ProofStepKind::StructuralTactic("miden_swap"),
                    barrier: None,
                },
                FlatOp::Instruction {
                    index: 2,
                    lean_repr: "u32DivMod".into(),
                    needs_hypothesis: true,
                    exec_target: None,
                    proof_step_kind: ProofStepKind::Search,
                    barrier: Some(BarrierKind::U32DivMod),
                },
                FlatOp::Instruction {
                    index: 3,
                    lean_repr: "div".into(),
                    needs_hypothesis: true,
                    exec_target: None,
                    proof_step_kind: ProofStepKind::Search,
                    barrier: Some(BarrierKind::Div),
                },
            ],
            needs_proc_env: false,
            module_prefix: "u64".into(),
        };

        let body = emit_proof_body(&skel);
        assert!(body.contains("-- chunk1 begin"));
        assert!(body.contains("-- chunk"));
        assert!(body.contains("all_goals sorry"));
    }
}
