import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# Symbolic simp attribute sets

Custom simp attributes used by symbolic reflection automation.
-/

/-- Simp set for `miden_reflect` target canonicalization and cleanup. -/
register_simp_attr miden_reflect_norm
