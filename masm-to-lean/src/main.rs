use anyhow::{Context, Result};
use clap::Parser;
use miden_assembly_syntax::ast::ModuleKind;
use miden_assembly_syntax::debuginfo::DefaultSourceManager;
use miden_assembly_syntax::{ModuleParser, PathBuf as MasmPathBuf};
use std::path::{Path, PathBuf};
use std::process::Command;
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

        let source_commit = resolve_source_commit(path);

        // Generate definitions (existing behavior)
        let lean_code = module::translate_module(&parsed, &namespace, source_commit.as_deref())?;

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

            let proof_module = skeleton::generate_proof_skeletons(
                &parsed,
                &lean_name,
                &namespace,
                &module_prefix,
                &generated_import,
            )?;

            let module_dir = proofs_output.join(&lean_name);
            std::fs::create_dir_all(&module_dir)?;

            for generated_file in &proof_module.files {
                let proof_output_path = proofs_output.join(&generated_file.relative_path);
                if let Some(parent) = proof_output_path.parent() {
                    std::fs::create_dir_all(parent)?;
                }
                std::fs::write(&proof_output_path, &generated_file.content)?;
            }

            eprintln!(
                "Wrote {} proof files under {} ({} skeletons: {} AUTO, {} SEMI, {} MANUAL)",
                proof_module.files.len(),
                module_dir.display(),
                proc_count,
                proof_module.auto_count,
                proof_module.semi_count,
                proof_module.manual_count
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

fn resolve_source_commit(path: &Path) -> Option<String> {
    let cwd = path.parent().unwrap_or(path);
    let output = Command::new("git")
        .arg("-C")
        .arg(cwd)
        .arg("rev-parse")
        .arg("HEAD")
        .output()
        .ok()?;

    if !output.status.success() {
        return None;
    }

    let commit = String::from_utf8(output.stdout).ok()?;
    let commit = commit.trim();
    if commit.is_empty() {
        None
    } else {
        Some(commit.to_string())
    }
}
