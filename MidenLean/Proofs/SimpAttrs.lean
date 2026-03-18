import Lean.Meta.Tactic.Simp.RegisterCommand

/-!
# Miden simp attribute sets

Custom simp attribute sets for Miden proof automation.

- `miden_simp`: general Miden simplification lemmas (MidenState projections, Felt values, etc.)
- `miden_bound`: bound and value recovery lemmas (u32/Felt bounds, `felt_ofNat_val_lt`, etc.)
- `miden_dispatch`: instruction dispatch lemmas (step lemmas for individual instructions)

These attributes cannot be used in the same file where they are declared,
so they are declared here and used in `Helpers.lean`, `StepLemmas.lean`, etc.
-/

/-- Simp set for general Miden simplification: MidenState projections, Felt values, boolean lemmas. -/
register_simp_attr miden_simp

/-- Simp set for Miden bound lemmas: u32 bounds, Felt value recovery, isU32 facts. -/
register_simp_attr miden_bound

/-- Simp set for Miden instruction dispatch: step lemmas for each instruction. -/
register_simp_attr miden_dispatch
