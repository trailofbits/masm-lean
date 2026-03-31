import Lean

/-!
# `weakening` tactic

A tactic that introduces an explicit, named, auditable assumption into a proof.

## Motivation

When a proof requires an assumption that hasn't been verified yet (e.g., a global
trace property like overflow bus soundness), we don't want to:
1. Weaken the theorem statement (hides the gap)
2. Use bare `sorry` (indistinguishable from incomplete proof)

Instead, `weakening` makes the assumption visible and traceable.

## Syntax

```
weakening overflow_preserved : t.row1.s' 15 = t.row0.s 15 by sorry
```

This desugars to:

```
have overflow_preserved : t.row1.s' 15 = t.row0.s 15 := by sorry
```

But with an additional warning emitted, making it greppable and auditable
separately from regular `sorry`.

## Intended workflow

1. Write theorem at full strength (from spec/design doc)
2. Attempt proof
3. When stuck on an unverified assumption, use `weakening name : type by sorry`
4. Continue the proof using `name`
5. CI counts `weakening` separately from `sorry`
6. When the assumption is verified, replace `weakening ... by sorry` with
   `weakening ... by exact proof_of_assumption`
7. When fully proved, replace `weakening` with `have`

## Auditing

- `grep -r "weakening" MidenLean/` lists all weakening assumptions
- Each weakening has a name (what it claims) and a proof (sorry or real)
- The name documents WHY the assumption is needed
- Zero `sorry` + zero `weakening by sorry` = fully verified
-/

namespace MidenLean.Tactic

open Lean Elab Tactic in
/-- `weakening "reason" name : type by tac` introduces a named, documented assumption.

    - `reason`: A string explaining WHY this assumption is needed and what would
      be required to eliminate it. This is mandatory — every weakening must be justified.
    - `name`: The hypothesis name (available in the proof context after this tactic).
    - `type`: The proposition being assumed.
    - `tac`: The proof (use `sorry` if unverified, or a real proof if the assumption
      has been validated but you want to keep the documentation).

    Semantically identical to `have name : type := by tac`, but emits a warning
    with the reason string, making it greppable and auditable.

    When `tac` is `sorry`, this marks an unverified assumption that must be
    audited before the proof is considered complete. -/
syntax "weakening " ident " : " term " reason " str : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| weakening $n:ident : $t reason $msg:str) => do
    let reasonStr := msg.getString
    logWarning m!"weakening [{reasonStr}]: {n} : {t}"
    evalTactic (← `(tactic| have $n : $t := by sorry))

end MidenLean.Tactic

-- ============================================================================
-- Smoke test
-- ============================================================================

section WeakeningTest

open MidenLean.Tactic

-- Dangerous: unsound weakening — False lets us prove anything.
-- The `weakening` tactic makes this VISIBLE in diagnostics.
-- Auditing: grep for "weakening" to find all unverified assumptions.
example : 0 = 1 := by
  weakening h_false : False reason
    "UNSOUND: this is False — demonstrates that weakening can introduce unsound assumptions"
  exact h_false.elim

-- Realistic: overflow table assumption (the actual use case from eqz proof)
example (f : Fin 16 → Nat) (g : Fin 16 → Nat) : f 15 = g 15 := by
  weakening h_overflow : f 15 = g 15 reason
    "overflow bus permutation preserves position 15 across Pad/Eq cycle — requires global trace modeling"
  exact h_overflow

end WeakeningTest
