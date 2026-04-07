//! Symbolic constraint extraction via p3 SymbolicAirBuilder.
//!
//! Runs the actual Miden constraint code with a symbolic builder,
//! calling each sub-module separately to produce per-module Lean files.

use miden_air::constraints;
use miden_air::constraints::op_flags::{ExprDecoderAccess, OpFlags};
use miden_air::trace::{MainTraceRow, TRACE_WIDTH};
use miden_core::Felt;
use p3_air::symbolic::{
    AirLayout, BaseLeaf, SymbolicAirBuilder, SymbolicExpression, SymbolicVariable, BaseEntry,
    ExtLeaf, SymbolicExpressionExt, ExtEntry,
};
use p3_air::{AirBuilder, WindowAccess};
use std::borrow::Borrow;
use std::fs;
use std::path::Path;

type EF = Felt;

const STACK_TRACE_OFFSET: usize = 30;
const DECODER_TRACE_OFFSET: usize = 6;
const USER_OP_HELPERS_OFFSET: usize = 10;

// Global column indices for the decoder "extra" columns (degree-reduction composites).
// These are pre-computed products of op bits that exist in the trace for degree reduction,
// but the canonical Lean AIR model works with the raw op-bit products directly.
// We inline-expand them during extraction so bridge proofs don't need conditional hypotheses.
//
// e0 = b6 * (1 - b5) * b4   (col 13 * (1 - col 12) * col 11)
// e1 = b6 * b5               (col 13 * col 12)
const E0_GLOBAL_COL: usize = 28; // DECODER_TRACE_OFFSET + OP_BITS_EXTRA_COLS_OFFSET = 6 + 22
const E1_GLOBAL_COL: usize = 29; // E0_GLOBAL_COL + 1
// Op bits used in the expansion (global column indices):
const B4_GLOBAL_COL: usize = 11; // DECODER_TRACE_OFFSET + OP_BITS_OFFSET + 4 = 6 + 1 + 4
const B5_GLOBAL_COL: usize = 12; // DECODER_TRACE_OFFSET + OP_BITS_OFFSET + 5
const B6_GLOBAL_COL: usize = 13; // DECODER_TRACE_OFFSET + OP_BITS_OFFSET + 6

fn make_layout() -> AirLayout {
    AirLayout {
        preprocessed_width: 0,
        main_width: TRACE_WIDTH,
        num_public_values: 40, // WORD_SIZE + 2*MIN_STACK_DEPTH + WORD_SIZE
        permutation_width: 8,
        num_permutation_challenges: 2,
        num_permutation_values: 8,
        num_periodic_columns: 20,
    }
}

/// Run a constraint function on a fresh builder, return (base_count, ext_count, base_exprs, ext_exprs)
fn extract_module<F>(
    f: F,
) -> (
    Vec<SymbolicExpression<Felt>>,
    Vec<SymbolicExpressionExt<Felt, EF>>,
)
where
    F: FnOnce(
        &mut SymbolicAirBuilder<Felt>,
        &MainTraceRow<SymbolicVariable<Felt>>,
        &MainTraceRow<SymbolicVariable<Felt>>,
    ),
{
    let mut builder = SymbolicAirBuilder::<Felt>::new(make_layout());
    let main_window = builder.main();
    let local: &MainTraceRow<_> = main_window.current_slice().borrow();
    let next: &MainTraceRow<_> = main_window.next_slice().borrow();
    f(&mut builder, local, next);
    (builder.base_constraints(), builder.extension_constraints())
}

struct Module {
    name: &'static str,
    base: Vec<SymbolicExpression<Felt>>,
    ext: Vec<SymbolicExpressionExt<Felt, EF>>,
}

fn main() {
    let output_dir = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "output".to_string());

    // Extract each sub-module separately for manageable Lean file sizes
    let modules: Vec<Module> = vec![
        // System
        {
            let (b, e) = extract_module(|builder, local, next| {
                constraints::system::enforce_main(builder, local, next);
            });
            Module { name: "System", base: b, ext: e }
        },
        // Range checker
        {
            let (b, e) = extract_module(|builder, local, next| {
                constraints::range::enforce_main(builder, local, next);
            });
            Module { name: "Range", base: b, ext: e }
        },
        // Stack sub-modules (split for compilation speed)
        {
            let (b, e) = extract_module(|builder, local, next| {
                let op_flags = OpFlags::new(ExprDecoderAccess::new(local));
                constraints::stack::general::enforce_main(builder, local, next, &op_flags);
            });
            Module { name: "StackGeneral", base: b, ext: e }
        },
        {
            let (b, e) = extract_module(|builder, local, next| {
                let op_flags = OpFlags::new(ExprDecoderAccess::new(local));
                constraints::stack::overflow::enforce_main(builder, local, next, &op_flags);
            });
            Module { name: "StackOverflow", base: b, ext: e }
        },
        {
            let (b, e) = extract_module(|builder, local, next| {
                let op_flags = OpFlags::new(ExprDecoderAccess::new(local));
                constraints::stack::ops::enforce_main(builder, local, next, &op_flags);
            });
            Module { name: "StackOps", base: b, ext: e }
        },
        {
            let (b, e) = extract_module(|builder, local, next| {
                let op_flags = OpFlags::new(ExprDecoderAccess::new(local));
                constraints::stack::crypto::enforce_main(builder, local, next, &op_flags);
            });
            Module { name: "StackCrypto", base: b, ext: e }
        },
        {
            let (b, e) = extract_module(|builder, local, next| {
                let op_flags = OpFlags::new(ExprDecoderAccess::new(local));
                constraints::stack::stack_arith::enforce_main(builder, local, next, &op_flags);
            });
            Module { name: "StackArith", base: b, ext: e }
        },
        // Decoder
        {
            let (b, e) = extract_module(|builder, local, next| {
                let op_flags = OpFlags::new(ExprDecoderAccess::new(local));
                constraints::decoder::enforce_main(builder, local, next, &op_flags);
            });
            Module { name: "Decoder", base: b, ext: e }
        },
        // Chiplet sub-modules (split)
        {
            let (b, e) = extract_module(|builder, local, next| {
                constraints::chiplets::selectors::enforce_chiplet_selectors(builder, local, next);
            });
            Module { name: "ChipletSelectors", base: b, ext: e }
        },
        {
            let (b, e) = extract_module(|builder, local, next| {
                constraints::chiplets::hasher::enforce_hasher_constraints(builder, local, next);
            });
            Module { name: "ChipletHasher", base: b, ext: e }
        },
        {
            let (b, e) = extract_module(|builder, local, next| {
                constraints::chiplets::bitwise::enforce_bitwise_constraints(builder, local, next);
            });
            Module { name: "ChipletBitwise", base: b, ext: e }
        },
        {
            let (b, e) = extract_module(|builder, local, next| {
                constraints::chiplets::memory::enforce_memory_constraints(builder, local, next);
            });
            Module { name: "ChipletMemory", base: b, ext: e }
        },
        {
            let (b, e) = extract_module(|builder, local, next| {
                constraints::chiplets::ace::enforce_ace_constraints(builder, local, next);
            });
            Module { name: "ChipletAce", base: b, ext: e }
        },
        {
            let (b, e) = extract_module(|builder, local, next| {
                constraints::chiplets::kernel_rom::enforce_kernel_rom_constraints(builder, local, next);
            });
            Module { name: "ChipletKernelRom", base: b, ext: e }
        },
        // Public inputs (boundary constraints on stack vs claimed I/O)
        {
            let (b, e) = extract_module(|builder, local, _next| {
                constraints::public_inputs::enforce_main(builder, local);
            });
            Module { name: "PublicInputs", base: b, ext: e }
        },
        // Bus (aux trace)
        {
            let (b, e) = extract_module(|builder, local, next| {
                constraints::enforce_bus(builder, local, next);
            });
            Module { name: "Bus", base: b, ext: e }
        },
    ];

    // Print summary
    let mut total_base = 0;
    let mut total_ext = 0;
    for m in &modules {
        eprintln!("{:12}: {} base + {} ext = {} constraints",
            m.name, m.base.len(), m.ext.len(), m.base.len() + m.ext.len());
        total_base += m.base.len();
        total_ext += m.ext.len();
    }
    eprintln!("Total: {} base + {} ext = {}", total_base, total_ext, total_base + total_ext);

    // Emit per-module Lean files
    let out_path = Path::new(&output_dir);
    fs::create_dir_all(out_path).unwrap();

    for m in &modules {
        let lean = emit_module_lean(m);
        let file_path = out_path.join(format!("{}.lean", m.name));
        fs::write(&file_path, &lean).unwrap();
        eprintln!("Wrote {} ({} lines)", file_path.display(), lean.lines().count());
    }
}

const CHUNK_SIZE: usize = 20; // Max constraints per def to avoid heartbeat timeout

fn emit_module_lean(m: &Module) -> String {
    let mut out = String::new();
    out.push_str("import MidenLean.AIR.SymbolicFrame\n");
    out.push_str(&format!(
        "/-! {} AIR constraints: {} base + {} ext. Auto-extracted. -/\n\n",
        m.name, m.base.len(), m.ext.len()
    ));
    out.push_str(&format!(
        "namespace MidenLean.AIR.Constraints.Symbolic.{}\n\n",
        m.name
    ));
    out.push_str("open MidenLean MidenLean.AIR\n\n");

    // Base constraints — chunked if large
    if !m.base.is_empty() {
        emit_chunked_list(&mut out, "base", &m.base, m.name, |c| sym_expr_to_lean(c), "SymbolicConstraint");
    }

    // Extension constraints — chunked if large
    if !m.ext.is_empty() {
        emit_chunked_list(&mut out, "bus", &m.ext, m.name, |c| ext_expr_to_lean(c), "SymbolicBusConstraint");
    }

    out.push_str(&format!(
        "end MidenLean.AIR.Constraints.Symbolic.{}\n",
        m.name
    ));
    out
}

fn emit_chunked_list<T, F: Fn(&T) -> String>(
    out: &mut String,
    list_name: &str,
    items: &[T],
    module_name: &str,
    to_lean: F,
    type_name: &str,
) {
    if items.len() <= CHUNK_SIZE {
        // Small enough — emit as a single def
        out.push_str(&format!("def {} : List {} := [\n", list_name, type_name));
        for (i, c) in items.iter().enumerate() {
            let comma = if i + 1 < items.len() { "," } else { "" };
            out.push_str(&format!("  -- {}.{}[{}]\n", module_name, list_name, i));
            out.push_str(&format!("  fun f => {}{}\n", to_lean(c), comma));
        }
        out.push_str("]\n\n");
    } else {
        // Chunk into pieces
        let chunks: Vec<_> = items.chunks(CHUNK_SIZE).collect();
        for (ci, chunk) in chunks.iter().enumerate() {
            let start = ci * CHUNK_SIZE;
            let end = start + chunk.len() - 1;
            out.push_str(&format!(
                "private def {}_{}_to_{} : List {} := [\n",
                list_name, start, end, type_name
            ));
            for (i, c) in chunk.iter().enumerate() {
                let global_i = start + i;
                let comma = if i + 1 < chunk.len() { "," } else { "" };
                out.push_str(&format!("  -- {}.{}[{}]\n", module_name, list_name, global_i));
                out.push_str(&format!("  fun f => {}{}\n", to_lean(c), comma));
            }
            out.push_str("]\n\n");
        }
        // Combine
        out.push_str(&format!("def {} : List {} :=\n", list_name, type_name));
        let chunk_names: Vec<String> = chunks
            .iter()
            .enumerate()
            .map(|(ci, chunk)| {
                let start = ci * CHUNK_SIZE;
                let end = start + chunk.len() - 1;
                format!("{}_{}_to_{}", list_name, start, end)
            })
            .collect();
        out.push_str(&format!("  {}\n\n", chunk_names.join(" ++ ")));
    }
}

// ============================================================================
// Expression → Lean conversion (same as before)
// ============================================================================

fn sym_expr_to_lean(expr: &SymbolicExpression<Felt>) -> String {
    use p3_air::symbolic::SymbolicExpr;
    match expr {
        SymbolicExpr::Leaf(leaf) => leaf_to_lean(leaf),
        SymbolicExpr::Add { x, y, .. } => format!("({} + {})", sym_expr_to_lean(x), sym_expr_to_lean(y)),
        SymbolicExpr::Sub { x, y, .. } => format!("({} - {})", sym_expr_to_lean(x), sym_expr_to_lean(y)),
        SymbolicExpr::Neg { x, .. } => format!("(-{})", sym_expr_to_lean(x)),
        SymbolicExpr::Mul { x, y, .. } => format!("({} * {})", sym_expr_to_lean(x), sym_expr_to_lean(y)),
    }
}

fn leaf_to_lean(leaf: &BaseLeaf<Felt>) -> String {
    match leaf {
        BaseLeaf::Constant(c) => {
            use p3_field::PrimeField64;
            let val = c.as_canonical_u64();
            match val {
                0 => "0".into(),
                1 => "1".into(),
                _ => format!("Felt.ofNat {}", val),
            }
        }
        BaseLeaf::Variable(var) => sym_var_to_lean(var),
        BaseLeaf::IsFirstRow => "f.is_first_row".into(),
        BaseLeaf::IsLastRow => "f.is_last_row".into(),
        BaseLeaf::IsTransition => "f.is_transition".into(),
    }
}

fn sym_var_to_lean(var: &SymbolicVariable<Felt>) -> String {
    let col = var.index;

    // Public values and periodic columns
    match var.entry {
        BaseEntry::Public => return format!("f.publicValue {}", col),
        BaseEntry::Periodic => return format!("f.periodic {}", col),
        BaseEntry::Preprocessed { .. } => return format!("f.preprocessed {}", col),
        BaseEntry::Main { .. } => {} // fall through to column mapping
    }

    let is_next = matches!(var.entry, BaseEntry::Main { offset: 1 });
    if col >= STACK_TRACE_OFFSET && col < STACK_TRACE_OFFSET + 16 {
        let i = col - STACK_TRACE_OFFSET;
        if is_next { format!("f.s' {}", i) } else { format!("f.s {}", i) }
    } else if col >= STACK_TRACE_OFFSET + 16 && col < STACK_TRACE_OFFSET + 19 {
        let name = match col - STACK_TRACE_OFFSET - 16 {
            0 => "b0", 1 => "b1", 2 => "h0_overflow", _ => unreachable!(),
        };
        if is_next { format!("f.{}'", name) } else { format!("f.{}", name) }
    } else if col >= DECODER_TRACE_OFFSET + USER_OP_HELPERS_OFFSET
        && col < DECODER_TRACE_OFFSET + USER_OP_HELPERS_OFFSET + 6
    {
        let i = col - DECODER_TRACE_OFFSET - USER_OP_HELPERS_OFFSET;
        if is_next { format!("f.h' {}", i) } else { format!("f.h {}", i) }
    } else if col == E0_GLOBAL_COL {
        // e0 = b6 * (1 - b5) * b4, expanded to raw op-bit products
        let (b4, b5, b6) = if is_next {
            (format!("f.colNext {}", B4_GLOBAL_COL),
             format!("f.colNext {}", B5_GLOBAL_COL),
             format!("f.colNext {}", B6_GLOBAL_COL))
        } else {
            (format!("f.colCurr {}", B4_GLOBAL_COL),
             format!("f.colCurr {}", B5_GLOBAL_COL),
             format!("f.colCurr {}", B6_GLOBAL_COL))
        };
        format!("({} * (1 - {}) * {})", b6, b5, b4)
    } else if col == E1_GLOBAL_COL {
        // e1 = b6 * b5, expanded to raw op-bit products
        let (b5, b6) = if is_next {
            (format!("f.colNext {}", B5_GLOBAL_COL),
             format!("f.colNext {}", B6_GLOBAL_COL))
        } else {
            (format!("f.colCurr {}", B5_GLOBAL_COL),
             format!("f.colCurr {}", B6_GLOBAL_COL))
        };
        format!("({} * {})", b6, b5)
    } else if col == 0 {
        if is_next { "f.clk'".into() } else { "f.clk".into() }
    } else if col == 1 {
        if is_next { "f.ctx'".into() } else { "f.ctx".into() }
    } else if is_next {
        format!("f.colNext {}", col)
    } else {
        format!("f.colCurr {}", col)
    }
}

fn ext_expr_to_lean(expr: &SymbolicExpressionExt<Felt, EF>) -> String {
    use p3_air::symbolic::SymbolicExpr;
    match expr {
        SymbolicExpr::Leaf(leaf) => ext_leaf_to_lean(leaf),
        SymbolicExpr::Add { x, y, .. } => format!("({} + {})", ext_expr_to_lean(x), ext_expr_to_lean(y)),
        SymbolicExpr::Sub { x, y, .. } => format!("({} - {})", ext_expr_to_lean(x), ext_expr_to_lean(y)),
        SymbolicExpr::Neg { x, .. } => format!("(-{})", ext_expr_to_lean(x)),
        SymbolicExpr::Mul { x, y, .. } => format!("({} * {})", ext_expr_to_lean(x), ext_expr_to_lean(y)),
    }
}

fn ext_leaf_to_lean(leaf: &ExtLeaf<Felt, EF>) -> String {
    match leaf {
        ExtLeaf::Base(base_expr) => format!("(QuadFelt.ofFelt ({}))", sym_expr_to_lean(base_expr)),
        ExtLeaf::ExtVariable(var) => {
            let idx = var.index;
            match var.entry {
                ExtEntry::Permutation { offset } => {
                    if offset == 0 { format!("f.auxCurr {}", idx) }
                    else { format!("f.auxNext {}", idx) }
                }
                ExtEntry::Challenge => format!("f.challenge {}", idx),
                ExtEntry::PermutationValue => format!("f.permValue {}", idx),
            }
        }
        ExtLeaf::ExtConstant(c) => {
            use p3_field::PrimeField64;
            let val = c.as_canonical_u64();
            match val {
                0 => "QuadFelt.zero".into(),
                1 => "QuadFelt.one".into(),
                _ => format!("(QuadFelt.ofFelt (Felt.ofNat {}))", val),
            }
        }
    }
}
