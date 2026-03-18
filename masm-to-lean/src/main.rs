use anyhow::{Context, Result};
use clap::Parser;
use miden_assembly_syntax::ast::ModuleKind;
use miden_assembly_syntax::debuginfo::DefaultSourceManager;
use miden_assembly_syntax::{ModuleParser, PathBuf as MasmPathBuf};
use std::path::PathBuf;
use std::sync::Arc;

mod classifier;
mod hypothesis;
mod instruction;
mod instruction_info;
mod module;
mod skeleton;
mod stack_effect;
mod translate;

#[derive(Parser)]
#[command(
    name = "masm-to-lean",
    about = "Translate MASM procedures to Lean 4 definitions"
)]
struct Cli {
    /// Input .masm files
    #[arg(required = true)]
    files: Vec<PathBuf>,

    /// Output directory for .lean files
    #[arg(short, long, default_value = "output")]
    output: PathBuf,

    /// Lean namespace prefix (e.g., "Miden.Core")
    #[arg(short, long)]
    namespace: Option<String>,

    /// Generate proof skeletons alongside definitions
    #[arg(long)]
    generate_proofs: bool,

    /// Output directory for generated proof skeletons (default: <output>/Proofs/Generated)
    #[arg(long)]
    proofs_output: Option<PathBuf>,
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    std::fs::create_dir_all(&cli.output)?;

    let proofs_output = cli
        .proofs_output
        .clone()
        .unwrap_or_else(|| cli.output.join("Proofs").join("Generated"));

    if cli.generate_proofs {
        std::fs::create_dir_all(&proofs_output)?;
    }

    let source_manager = Arc::new(DefaultSourceManager::default());

    for path in &cli.files {
        let file_name = path
            .file_stem()
            .context("Invalid file name")?
            .to_string_lossy();

        // Derive module name from file path
        let module_name = format!("masm::{}", file_name);

        let mut parser = ModuleParser::new(ModuleKind::Library);
        let module_path = MasmPathBuf::new(&module_name)
            .map_err(|e| anyhow::anyhow!("Invalid module name '{}': {}", module_name, e))?;
        let parsed = parser
            .parse_file(&module_path, path, source_manager.clone())
            .map_err(|e| anyhow::anyhow!("Failed to parse {}: {}", path.display(), e))?;

        // Determine the Lean namespace
        let lean_name = capitalize(&file_name);
        let namespace = match &cli.namespace {
            Some(ns) => format!("{}.{}", ns, lean_name),
            None => lean_name.clone(),
        };

        // Generate definitions (existing behavior)
        let lean_code = module::translate_module(&parsed, &namespace)?;

        let output_path = cli.output.join(format!("{}.lean", lean_name));
        std::fs::write(&output_path, &lean_code)?;

        let proc_count = parsed.procedures().count();
        eprintln!(
            "Wrote {} ({} procedures)",
            output_path.display(),
            proc_count
        );

        // Generate proof skeletons if requested
        if cli.generate_proofs {
            // Derive the module prefix for theorem naming (e.g., "u64" from "U64")
            let module_prefix = file_name.to_lowercase();

            // Derive the import path for the generated definitions
            let generated_import = format!("MidenLean.Generated.{}", lean_name);

            let proof_code = skeleton::generate_proof_skeletons(
                &parsed,
                &namespace,
                &module_prefix,
                &generated_import,
            )?;

            let proof_output_path = proofs_output.join(format!("{}.lean", lean_name));
            std::fs::write(&proof_output_path, &proof_code)?;

            // Count classifications (two-pass analysis for accurate results)
            let mut first_pass: std::collections::HashMap<String, stack_effect::ProcStackEffect> =
                std::collections::HashMap::new();
            for proc in parsed.procedures() {
                let name = proc.name().to_string();
                let effect = stack_effect::analyze_block(proc.body());
                first_pass.insert(name, effect);
            }
            let mut auto = 0;
            let mut semi = 0;
            let mut manual = 0;
            for proc in parsed.procedures() {
                let name = proc.name().to_string();
                let first_effect = first_pass.get(&name).unwrap();
                let effect = if first_effect.has_calls {
                    stack_effect::analyze_block_with_callees(proc.body(), Some(&first_pass))
                } else {
                    first_effect.clone()
                };
                let hyps = hypothesis::infer_hypotheses(proc.body(), effect.input_arity);
                match classifier::classify(proc.body(), &effect, &hyps) {
                    classifier::Classification::Auto => auto += 1,
                    classifier::Classification::Semi => semi += 1,
                    classifier::Classification::Manual => manual += 1,
                }
            }

            eprintln!(
                "Wrote {} ({} skeletons: {} AUTO, {} SEMI, {} MANUAL)",
                proof_output_path.display(),
                proc_count,
                auto,
                semi,
                manual
            );
        }
    }

    Ok(())
}

fn capitalize(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
    }
}
