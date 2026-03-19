use anyhow::Result;
use miden_assembly_syntax::ast::Module;

use crate::translate::translate_block;

fn emit_module_header(namespace: &str, source_commit: Option<&str>) -> String {
    let mut out = String::new();
    let commit = source_commit.unwrap_or("unknown");
    out.push_str(&format!("-- MASM source repo commit: {}\n", commit));
    out.push_str("import MidenLean.Semantics\n\n");
    out.push_str("open MidenLean\n\n");
    out.push_str(&format!("namespace {}\n", namespace));
    out
}

/// Translate an entire MASM module to a Lean file.
pub fn translate_module(
    module: &Module,
    namespace: &str,
    source_commit: Option<&str>,
) -> Result<String> {
    let mut out = emit_module_header(namespace, source_commit);

    // Translate each procedure
    for proc in module.procedures() {
        let name = proc.name().to_string();
        let lean_name = sanitize_lean_name(&name);

        out.push('\n');

        let items = translate_block(proc.body(), 2)?;

        if items.is_empty() {
            out.push_str(&format!("def {} : List Op := []\n", lean_name));
        } else {
            out.push_str(&format!("def {} : List Op := [\n", lean_name));
            out.push_str(&items.join(",\n"));
            out.push('\n');
            out.push_str("]\n");
        }
    }

    // Footer
    out.push_str(&format!("\nend {}\n", namespace));

    Ok(out)
}

/// Sanitize a MASM procedure name for use as a Lean identifier.
/// MASM names may contain characters that aren't valid in Lean.
pub fn sanitize_lean_name(name: &str) -> String {
    // Lean identifiers: alphanumeric + underscores, must not start with digit.
    // MASM names are typically already valid Lean identifiers.
    // Replace any problematic characters with underscores.
    let sanitized: String = name
        .chars()
        .map(|c| {
            if c.is_alphanumeric() || c == '_' {
                c
            } else {
                '_'
            }
        })
        .collect();

    // If it starts with a digit, prefix with underscore
    if sanitized
        .chars()
        .next()
        .map_or(false, |c| c.is_ascii_digit())
    {
        format!("_{}", sanitized)
    } else {
        sanitized
    }
}

/// Convert a MASM module path like "miden::core::word" to a Lean namespace like "Miden.Core.Word".
#[allow(dead_code)]
pub fn masm_path_to_lean_namespace(path: &str) -> String {
    path.split("::")
        .map(|segment| {
            let mut chars = segment.chars();
            match chars.next() {
                None => String::new(),
                Some(c) => {
                    let upper = c.to_uppercase().collect::<String>();
                    upper + chars.as_str()
                }
            }
        })
        .collect::<Vec<_>>()
        .join(".")
}

#[cfg(test)]
mod tests {
    use super::emit_module_header;

    #[test]
    fn test_emit_module_header_includes_source_commit() {
        let header = emit_module_header("Miden.Core.Word", Some("deadbeef"));
        assert!(header.starts_with("-- MASM source repo commit: deadbeef\n"));
        assert!(header.contains("namespace Miden.Core.Word"));
    }

    #[test]
    fn test_emit_module_header_uses_unknown_when_commit_missing() {
        let header = emit_module_header("Miden.Core.Word", None);
        assert!(header.starts_with("-- MASM source repo commit: unknown\n"));
    }
}
