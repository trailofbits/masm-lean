import MidenLean.Proofs.StepLemmas

namespace MidenLean.Tactics

open MidenLean.StepLemmas

-- ============================================================================
-- Core bind normalization
-- ============================================================================

/-- Simplify one Option.bind step after a rewrite.
    Also normalizes List.set (from stepSwap), List.eraseIdx (from stepMovup),
    and insertAt/List.take/List.drop/List.append (from stepMovdn). -/
syntax "miden_bind" : tactic
macro_rules
  | `(tactic| miden_bind) =>
    `(tactic| simp only [bind, Bind.bind, Option.bind,
      List.set, List.eraseIdx, MidenLean.insertAt, List.take, List.drop,
      List.cons_append, List.nil_append, List.append_nil])

-- ============================================================================
-- Individual instruction tactics
-- ============================================================================

/-- Apply stepSwap with automatic argument resolution and normalize List.set. -/
syntax "miden_swap" : tactic
macro_rules
  | `(tactic| miden_swap) =>
    `(tactic|
      rw [stepSwap (hn := by decide) (htop := rfl) (hnth := rfl)]; miden_bind)

/-- Apply stepDup with automatic index resolution. -/
syntax "miden_dup" : tactic
macro_rules
  | `(tactic| miden_dup) =>
    `(tactic| rw [stepDup (h := rfl)]; miden_bind)

/-- Apply stepMovup with automatic element resolution. -/
syntax "miden_movup" : tactic
macro_rules
  | `(tactic| miden_movup) =>
    `(tactic| rw [stepMovup (hn := rfl) (hv := rfl)]; miden_bind)

/-- Apply stepMovdn. -/
syntax "miden_movdn" : tactic
macro_rules
  | `(tactic| miden_movdn) =>
    `(tactic| rw [stepMovdn (hn := rfl)]; miden_bind)

-- ============================================================================
-- miden_step: try all step lemmas
-- ============================================================================

/-- Try to apply a step lemma and simplify the bind.
    Covers hypothesis-free step lemmas and u32/conditional step lemmas whose
    hypotheses can be resolved by `assumption`. -/
syntax "miden_step" : tactic
macro_rules
  | `(tactic| miden_step) =>
    `(tactic| first
      -- Stack manipulation
      | rw [stepDrop]; miden_bind
      | rw [stepDropw]; miden_bind
      | miden_dup
      | miden_swap
      | miden_movup
      | miden_movdn
      | rw [stepReversew]; miden_bind
      | rw [stepDupw0]; miden_bind
      | rw [stepPush]; miden_bind
      | rw [stepPadw]; miden_bind
      -- Field comparison
      | rw [stepEqImm]; miden_bind
      | rw [stepEq]; miden_bind
      | rw [stepNeq]; miden_bind
      | rw [stepLt]; miden_bind
      | rw [stepGt]; miden_bind
      | rw [stepLte]; miden_bind
      | rw [stepGte]; miden_bind
      -- Field boolean (on ite-form booleans)
      | rw [stepAndIte]; miden_bind
      | rw [stepOrIte]; miden_bind
      | rw [stepNotIte]; miden_bind
      -- Conditional (on ite-form booleans)
      | rw [stepCswapIte]; miden_bind
      | rw [stepCdropIte]; miden_bind
      -- Field arithmetic
      | rw [stepAdd]; miden_bind
      | rw [stepSub]; miden_bind
      | rw [stepMul]; miden_bind
      | rw [stepAddImm]; miden_bind
      | rw [stepNeg]; miden_bind
      | rw [stepIncr]; miden_bind
      -- Field div (with nonzero hypothesis via assumption)
      | (rw [stepDiv (hb := by assumption)]; miden_bind)
      -- Pow2
      | (rw [stepPow2 (ha := by assumption)]; miden_bind)
      -- U32 split
      | rw [stepU32Split]; miden_bind
      -- U32 divmod (with isU32 + nonzero hypotheses via assumption)
      | (rw [stepU32DivMod (ha := by assumption) (hb := by assumption) (hbnz := by assumption)]; miden_bind)
      -- U32 arithmetic (with isU32 hypotheses via assumption)
      | (rw [stepU32WidenAdd (ha := by assumption) (hb := by assumption)]; miden_bind)
      | (rw [stepU32WidenAdd3 (ha := by assumption) (hb := by assumption) (hc := by assumption)]; miden_bind)
      | (rw [stepU32OverflowSub (ha := by assumption) (hb := by assumption)]; miden_bind)
      | (rw [stepU32WidenMul (ha := by assumption) (hb := by assumption)]; miden_bind)
      | (rw [stepU32WidenMadd (ha := by assumption) (hb := by assumption) (hc := by assumption)]; miden_bind)
      -- U32 bitwise (with isU32 hypotheses via assumption)
      | (rw [stepU32Not (ha := by assumption)]; miden_bind)
      | (rw [stepU32And (ha := by assumption) (hb := by assumption)]; miden_bind)
      | (rw [stepU32Or (ha := by assumption) (hb := by assumption)]; miden_bind)
      | (rw [stepU32Xor (ha := by assumption) (hb := by assumption)]; miden_bind)
      -- U32 assertions (with isU32 hypotheses via assumption)
      | (rw [stepU32Assert2 (ha := by assumption) (hb := by assumption)]; miden_bind)
      -- U32 comparison (with isU32 hypotheses via assumption)
      | (rw [stepU32Lt (ha := by assumption) (hb := by assumption)]; miden_bind)
      | (rw [stepU32Gt (ha := by assumption) (hb := by assumption)]; miden_bind)
      | (rw [stepU32Lte (ha := by assumption) (hb := by assumption)]; miden_bind)
      | (rw [stepU32Gte (ha := by assumption) (hb := by assumption)]; miden_bind)
      -- U32 bit counting (with isU32 hypotheses via assumption)
      | (rw [stepU32Clz (ha := by assumption)]; miden_bind)
      | (rw [stepU32Ctz (ha := by assumption)]; miden_bind)
      | (rw [stepU32Clo (ha := by assumption)]; miden_bind)
      | (rw [stepU32Cto (ha := by assumption)]; miden_bind)
      -- Assertions (with val hypotheses via assumption)
      | (rw [stepAssert (h := by assumption)]; miden_bind)
      | (rw [stepAssertWithError (h := by assumption)]; miden_bind)
      | (rw [stepAssertz (ha := by assumption)]; miden_bind)
      | rw [stepAssertEq]; miden_bind
      | (rw [stepAssertEqWithError]; miden_bind)
      -- Advice stack (with advice hypotheses via assumption)
      | (rw [stepAdvPush1 (hadv := by assumption)]; miden_bind)
      | (rw [stepAdvPush2 (hadv := by assumption)]; miden_bind)
      -- No-ops
      | rw [stepEmitImm]; miden_bind)

/-- Step through all remaining instructions, finishing with pure. -/
syntax "miden_steps" : tactic
macro_rules
  | `(tactic| miden_steps) =>
    `(tactic| repeat (first | miden_step | dsimp only [pure, Pure.pure]))

-- ============================================================================
-- miden_setup: automate the proof preamble
-- ============================================================================

open Lean Elab Tactic Meta in
/-- `miden_setup ProcName` automates the standard boilerplate for `exec`-based proofs.
    Destructures `s`, substitutes `hs`, unfolds `exec`/`execWithEnv`, and normalizes.
    After `miden_setup`, the goal is a chain of `execInstruction` calls bound with `>>=`. -/
elab "miden_setup " proc:term : tactic => do
  let s := mkIdent `s
  let hs := mkIdent `hs
  let stk := mkIdent `stk
  let mem := mkIdent `mem
  let locs := mkIdent `locs
  let adv := mkIdent `adv
  evalTactic (← `(tactic| obtain ⟨$stk, $mem, $locs, $adv⟩ := $s))
  evalTactic (← `(tactic| simp only [MidenState.withStack] at $hs ⊢))
  evalTactic (← `(tactic| subst $hs))
  let procId : TSyntax `ident := ⟨proc.raw⟩
  evalTactic (← `(tactic| unfold exec $procId execWithEnv))
  evalTactic (← `(tactic| simp only [List.foldlM]))

open Lean Elab Tactic Meta in
/-- `miden_setup_env ProcName` is like `miden_setup` but for `execWithEnv`-based proofs.
    Unfolds the procedure and execWithEnv (not `exec`). -/
elab "miden_setup_env " proc:term : tactic => do
  let s := mkIdent `s
  let hs := mkIdent `hs
  let stk := mkIdent `stk
  let mem := mkIdent `mem
  let locs := mkIdent `locs
  let adv := mkIdent `adv
  evalTactic (← `(tactic| obtain ⟨$stk, $mem, $locs, $adv⟩ := $s))
  evalTactic (← `(tactic| simp only [MidenState.withStack] at $hs ⊢))
  evalTactic (← `(tactic| subst $hs))
  let procId : TSyntax `ident := ⟨proc.raw⟩
  evalTactic (← `(tactic| unfold $procId execWithEnv))
  evalTactic (← `(tactic| simp only [List.foldlM]))

-- ============================================================================
-- miden_call: resolve a procedure call
-- ============================================================================

/-- Resolve a procedure call in the goal.
    After the `change` block introduces a `match env "proc_name" with ...`,
    `miden_call` unfolds the environment, reduces the match, unfolds the called
    procedure, and reduces the foldlM.

    Usage:
      miden_call proc_name
    where `proc_name` is the called procedure (e.g., `Miden.Core.U64.overflowing_add`).

    Prerequisite: the environment must be the first thing to resolve in the goal.
    Typically used after a step like:
      simp only [u64ProcEnv]
      miden_call Miden.Core.U64.overflowing_add -/
syntax "miden_call" ident : tactic
macro_rules
  | `(tactic| miden_call $proc) =>
    `(tactic|
      (dsimp only [bind, Bind.bind, Option.bind]
       unfold $proc execWithEnv
       simp only [List.foldlM]))

-- ============================================================================
-- miden_loop: unfold one repeat iteration
-- ============================================================================

/-- Unfold one iteration of a `repeat` loop (via `doRepeat`).
    Unfolds doRepeat. In the recursive case (n > 0), also unfolds
    the body's execWithEnv and reduces foldlM.
    In the base case (n = 0), the unfold produces `some st`. -/
syntax "miden_loop" : tactic
macro_rules
  | `(tactic| miden_loop) =>
    `(tactic|
      (unfold execWithEnv.doRepeat
       try (unfold execWithEnv; simp only [List.foldlM])))

-- ============================================================================
-- miden_recover: Felt.ofNat value recovery
-- ============================================================================

/-- Try to rewrite `(Felt.ofNat n).val` to `n` using `felt_ofNat_val_lt`.
    Attempts to prove `n < GOLDILOCKS_PRIME` using the miden bound lemmas and omega. -/
syntax "miden_recover" : tactic
macro_rules
  | `(tactic| miden_recover) =>
    `(tactic|
      first
      | rw [MidenLean.felt_ofNat_val_lt _ (by unfold MidenLean.GOLDILOCKS_PRIME; omega)]
      | rw [MidenLean.felt_ofNat_val_lt _ (MidenLean.u32_mod_lt_prime _)]
      | rw [MidenLean.felt_ofNat_val_lt _ (MidenLean.sum_div_2_32_lt_prime _ _)]
      | rw [MidenLean.felt_ofNat_val_lt _ (MidenLean.u32_prod_div_lt_prime _ _ (by assumption) (by assumption))]
      | rw [MidenLean.felt_ofNat_val_lt _ (MidenLean.u32_overflow_sub_fst_lt _ _)])

end MidenLean.Tactics
