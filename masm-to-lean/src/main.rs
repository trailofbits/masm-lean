use anyhow::{Context, Result};
use clap::Parser;
use miden_assembly_syntax::ast::ModuleKind;
use miden_assembly_syntax::debuginfo::DefaultSourceManager;
use miden_assembly_syntax::{ModuleParser, PathBuf as MasmPathBuf};
use std::path::PathBuf;
use std::sync::Arc;

mod instruction;
mod module;
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
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    std::fs::create_dir_all(&cli.output)?;

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
            .parse_file(
                &module_path,
                path,
                source_manager.clone(),
            )
            .map_err(|e| anyhow::anyhow!("Failed to parse {}: {}", path.display(), e))?;

        // Determine the Lean namespace
        let lean_name = capitalize(&file_name);
        let namespace = match &cli.namespace {
            Some(ns) => format!("{}.{}", ns, lean_name),
            None => lean_name.clone(),
        };

        let lean_code = module::translate_module(&parsed, &namespace)?;

        let output_path = cli.output.join(format!("{}.lean", lean_name));
        std::fs::write(&output_path, &lean_code)?;

        let proc_count = parsed.procedures().count();
        eprintln!(
            "Wrote {} ({} procedures)",
            output_path.display(),
            proc_count
        );
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
