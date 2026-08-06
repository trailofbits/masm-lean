import Batteries.Tactic.Lint
import MidenLean.Symbolic.SimpAttrs

/-!
# Project-specific `#lint` linters

Three declaration-level linters (Batteries' `@[env_linter]` kind, which is what
CI's `#lint` job runs) checking invariants that no generic linter can express.
Each is here because the invariant it protects has already been violated in this
repository, and because the violation is *silent*: everything still compiles.

* `midenCorrectDocs` — `scripts/generate_verified_tables.py` regex-scrapes the
  doc comment attached to each `*_correct` theorem to build the README's
  verified-procedures table. A missing or placeholder comment therefore ships a
  blank row in the published table. Checking the real declaration (via
  `Lean.findDocString?`) instead of the file text means the check sees what the
  elaborator saw, and fails at the declaration rather than in a Python
  post-pass that runs long after review.

* `midenExecSummaryTagged` — an `execProcedure` summary theorem that is not
  registered with `@[miden_exec_summary]` is invisible to `miden_vcg` /
  `miden_reflect`, which then silently re-derive the callee body symbolically.
  That is pure cost with no visible symptom; a sweep found 29 untagged
  summaries at one point.

* `midenSoundnessCoverage` — a coverage invariant: every `MidenLean.Instruction`
  constructor should have a named `execInstruction_sound_<ctor>` lemma, or be
  listed in one of the two allowlists below with a reason.

## Implementation notes

`test` is called once per declaration in the linted package, so each test bails
out on the cheapest possible check (a name-suffix test) before touching the
environment. Nothing here iterates `Environment.constants`: at Mathlib scale
that turns a linter into a multi-hundred-second hang. All environment access is
by targeted `env.contains` / `env.find?`.

This module deliberately imports only `Batteries.Tactic.Lint` and the leaf
module `MidenLean.Symbolic.SimpAttrs` (core Lean only, so no import cycle with
`MidenLean.lean`). Constants belonging to the library proper are referred to by
unchecked `Name` literals and looked up in the environment, which keeps the
import surface at two modules; the lookups are guarded so that a renamed
anchor constant makes a linter *fail loudly* rather than pass vacuously.

`meta def` is required by `@[env_linter]`: the attribute rejects declarations
that are not `public` and `meta`, because `#lint` evaluates the linter from a
different module and needs its compiled code exported.
-/

namespace MidenLean.Linters

open Lean Meta

/-! ## Shared helpers -/

/-- Whitespace-separated non-empty tokens of `s`. -/
meta def tokens (s : String) : List String :=
  String.ofList (s.toList.map fun c => if c.isWhitespace then ' ' else c)
    |>.splitOn " " |>.filter (· != "")

/-- Markers at which `scripts/generate_verified_tables.py` truncates a theorem
    doc comment before using it as the README summary. Text from the first such
    marker onwards never reaches the table, so it must not count towards the
    summary's length either. -/
meta def summaryCutMarkers : List String :=
  ["Input stack:", "Output stack:", "Requires ", "where "]

/-- Number of words the table generator would extract from doc comment `doc`:
    lines are flattened, leading `*` bullets dropped, and the text truncated at
    the first `summaryCutMarkers` entry. Mirrors `normalize_comment` in
    `scripts/generate_verified_tables.py`. -/
meta def summaryWordCount (doc : String) : Nat :=
  let flat := " ".intercalate ((tokens doc).filter (· != "*"))
  let cut := summaryCutMarkers.foldl (init := flat) fun acc marker =>
    match acc.splitOn marker with
    | first :: _ :: _ => first
    | _ => acc
  (tokens cut).length

/-- A doc comment shorter than this many words is a placeholder, not a summary.
    The table generator itself warns below four words; one more here keeps the
    linter strictly ahead of the script. -/
meta def minSummaryWords : Nat := 5

/-- Namespace holding the manual correctness proofs. -/
meta def proofsNamespace : Name := `MidenLean.Proofs

/-- Namespace holding machine-generated proof scaffolding, which is not
    hand-maintained and so is exempt from the doc-comment rule. -/
meta def generatedProofsNamespace : Name := `MidenLean.Proofs.Generated

/-! ## `midenCorrectDocs` -/

/-- Every `*_correct` theorem under `MidenLean.Proofs` must carry a doc comment
    with a real high-level summary, because `generate_verified_tables.py`
    scrapes exactly that comment into the README's verified-procedures table. -/
@[env_linter] meta def midenCorrectDocs : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "All `_correct` theorems have a usable summary doc comment."
  errorsFound := "`_correct` THEOREMS WITH A MISSING OR PLACEHOLDER DOC COMMENT \
    (the README verified-procedures table is generated from these):"
  test declName := do
    -- Cheapest possible rejection first: this runs once per declaration.
    let .str _ suffix := declName | return none
    unless suffix.endsWith "_correct" do return none
    if isPrivateName declName then return none
    unless proofsNamespace.isPrefixOf declName do return none
    if generatedProofsNamespace.isPrefixOf declName then return none
    unless (← getConstInfo declName) matches .thmInfo _ do return none
    let env ← getEnv
    let some doc ← findDocString? env declName
      | return m!"has no doc comment, so the README table row for it would be empty"
    let words := summaryWordCount doc
    if words < minSummaryWords then
      return m!"has a doc comment that reduces to {words} word(s) of summary \
        (at least {minSummaryWords} required); the README table would show a \
        placeholder. Put a one-sentence English summary first, before any \
        `Input stack:` / `Output stack:` lines."
    return none

/-! ## `midenExecSummaryTagged` -/

/-- `MidenLean.execProcedure`, referred to by name so that this module need not
    import the library it lints. Guarded at use: if the constant disappears,
    the linter reports rather than silently passing. -/
meta def execProcedureName : Name := `MidenLean.execProcedure

/-- Substitute away leading `let` binders. Most execution summaries bind shared
    subterms in front of the equation (`let pow := …; execProcedure … = …`), so
    the conclusion's head is a `letE` rather than an `Eq`; `exposeExecEquation`
    in `Symbolic/Tactic.lean` does the same thing to the goal. `Meta.zetaReduce`
    is not usable here: it substitutes let-*fvars* from the local context, and
    these binders are still inside the type. The bound keeps a pathological type
    from spinning. -/
meta def peelLets (e : Expr) : Expr := Id.run do
  let mut e := e
  for _ in [:32] do
    match e with
    | .letE _ _ value body _ => e := body.instantiate1 value
    | _ => return e
  return e

/-- Is `ty` the statement of a callee execution summary, i.e. does its
    conclusion have the form `execProcedure env fuel state callee = _`?

    This shape test is what separates a real summary from a theorem that merely
    ends in `_exec` — `divmod_conditions_of_exec` concludes with a conjunction
    about the arithmetic conditions, and is no business of the registry. -/
meta def isExecSummaryShape (ty : Expr) : MetaM Bool :=
  forallTelescopeReducing ty fun _ body => do
    let some (_, lhs, _) := (peelLets body).eq? | return false
    return lhs.isAppOf execProcedureName && lhs.getAppNumArgs == 4

/-- Every theorem under `MidenLean.Proofs` that both ends in `_exec` and states
    an `execProcedure` summary must be registered with `@[miden_exec_summary]`.
    An unregistered summary is invisible to `miden_vcg`/`miden_reflect`, which
    then re-derive the callee body symbolically at every call site. -/
@[env_linter] meta def midenExecSummaryTagged : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "All `_exec` execution summaries are registered with \
    `@[miden_exec_summary]`."
  errorsFound := "`_exec` EXECUTION SUMMARIES MISSING `@[miden_exec_summary]` \
    (callers silently fall back to re-deriving the callee body):"
  test declName := do
    let .str _ suffix := declName | return none
    unless suffix.endsWith "_exec" do return none
    if isPrivateName declName then return none
    unless proofsNamespace.isPrefixOf declName do return none
    let info ← getConstInfo declName
    unless info matches .thmInfo _ do return none
    let env ← getEnv
    unless env.contains execProcedureName do
      return m!"cannot be checked: `{execProcedureName}` is not in the \
        environment. Fix `MidenLean.Linters.execProcedureName`."
    unless ← isExecSummaryShape info.type do return none
    if (MidenLean.Symbolic.getExecSummaryTheorems env).contains declName then
      return none
    return m!"states an `execProcedure` summary but is not tagged \
      `@[miden_exec_summary]`, so `miden_vcg`/`miden_reflect` cannot find it"

/-! ## `midenSoundnessCoverage` -/

/-- The symbolic executor. `midenSoundnessCoverage` does its work when asked
    about this one declaration and returns `none` for every other name, which is
    how a whole-environment coverage check is expressed as a per-declaration
    test without paying for it on every declaration. -/
meta def symbolicExecInstructionName : Name := `MidenLean.Symbolic.execInstruction

/-- The instruction datatype whose constructors must be covered. -/
meta def instructionTypeName : Name := `MidenLean.Instruction

/-- Namespace holding the per-constructor soundness lemmas. -/
meta def soundnessNamespace : Name := `MidenLean.Symbolic

/-- Instructions the symbolic executor deliberately does not support:
    `Symbolic/execInstruction` returns `none` for each of them, and a `none`
    can never yield a "verified" result, so there is nothing to prove sound.

    The six `mem*` entries are the dynamic-address memory instructions (address
    popped from the stack, hence not a statically known cell); `exec` is
    handled compositionally by `execOps` against a `ProcEnv` spec rather than
    by `execInstruction`. See the module comment in `Symbolic/Exec.lean`. -/
meta def unsupportedInstructions : List String :=
  [ "memLoad", "memStore"          -- dynamic-address load/store
  , "memLoadwBe", "memStorewBe"    -- dynamic-address word load/store, big-endian
  , "memLoadwLe", "memStorewLe"    -- dynamic-address word load/store, little-endian
  , "exec" ]                       -- procedure call: `execOps`, not `execInstruction`

/-- Instructions that *are* supported and *are* proved sound, but whose proof is
    written inline in the `execInstruction_sound` dispatcher in
    `Symbolic/Soundness.lean` instead of being factored into a named
    `execInstruction_sound_<ctor>` lemma.

    These are exactly the instructions that touch state outside the operand
    stack — memory at a static address, the local-frame window, the advice tape,
    the event channel — so they do not fit the `sound_stack_op` template that
    generates the named lemmas for the other 98 constructors. Extracting them
    into named lemmas would be a welcome refactor; until then each entry is a
    deliberate exception rather than a gap in the soundness argument. -/
meta def inlineSoundnessInstructions : List String :=
  [ "memLoadImm", "memStoreImm"                    -- static-address load/store
  , "memLoadwBeImm", "memStorewBeImm"              -- static-address word, big-endian
  , "memLoadwLeImm", "memStorewLeImm"              -- static-address word, little-endian
  , "locLoad", "locStore", "locaddr"               -- local-frame slots
  , "locLoadwBe", "locStorewBe"                    -- local-frame word, big-endian
  , "locLoadwLe", "locStorewLe"                    -- local-frame word, little-endian
  , "advPush", "advLoadW"                          -- advice tape
  , "emit", "emitImm" ]                            -- event channel

/-- Does a soundness lemma for constructor short name `ctor` exist?

    Checks the public name, then the `private` mangling of that name for each
    `MidenLean.*` module: the thirteen hand-written lemmas in
    `Symbolic/Soundness.lean` are `private`, so they only exist in the
    environment under `_private.<module>.0.<name>`. Both branches are targeted
    lookups — this never scans `env.constants`. -/
meta def soundnessLemmaExists (env : Environment) (midenModules : Array Name)
    (ctor : String) : Bool :=
  let base := soundnessNamespace ++ Name.mkSimple ("execInstruction_sound_" ++ ctor)
  env.contains base || midenModules.any fun m => env.contains (mkPrivateNameCore m base)

/-- Every `MidenLean.Instruction` constructor must have a named
    `MidenLean.Symbolic.execInstruction_sound_<ctor>` lemma, or appear in
    `unsupportedInstructions` / `inlineSoundnessInstructions`. Without this,
    extending the symbolic executor with a new instruction and forgetting its
    soundness lemma compiles cleanly and the gap is invisible. Stale allowlist
    entries are reported too, so the exception lists cannot quietly outlive
    their reason. -/
@[env_linter] meta def midenSoundnessCoverage : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "Every `Instruction` constructor has a soundness lemma or a \
    documented exception."
  errorsFound := "SYMBOLIC SOUNDNESS COVERAGE GAP:"
  test declName := do
    -- Coverage check: all the work happens on one declaration.
    unless declName == symbolicExecInstructionName do return none
    let env ← getEnv
    let some (.inductInfo instInfo) := env.find? instructionTypeName
      | return m!"cannot be checked: `{instructionTypeName}` is not an \
          inductive type in the environment. Fix \
          `MidenLean.Linters.instructionTypeName`."
    let midenModules := env.header.moduleNames.filter (`MidenLean).isPrefixOf
    let allowed := unsupportedInstructions ++ inlineSoundnessInstructions
    let ctors := instInfo.ctors.map fun c => c.updatePrefix .anonymous |>.toString
    let missing := ctors.filter fun c =>
      !allowed.contains c && !soundnessLemmaExists env midenModules c
    -- An allowlist entry that no longer names a constructor, or that now has a
    -- lemma after all, is stale: report it so the list stays honest.
    let notAConstructor := allowed.filter (!ctors.contains ·)
    let nowProved := allowed.filter fun c =>
      ctors.contains c && soundnessLemmaExists env midenModules c
    if missing.isEmpty && notAConstructor.isEmpty && nowProved.isEmpty then
      return none
    let mut msg := m!""
    unless missing.isEmpty do
      msg := msg ++ m!"\n  constructors with no `{soundnessNamespace}\
        .execInstruction_sound_<ctor>` lemma and no allowlist entry: {missing}"
    unless notAConstructor.isEmpty do
      msg := msg ++ m!"\n  allowlisted names that are not `{instructionTypeName}` \
        constructors (stale allowlist): {notAConstructor}"
    unless nowProved.isEmpty do
      msg := msg ++ m!"\n  allowlisted constructors that now DO have a named \
        lemma (drop them from the allowlist): {nowProved}"
    return msg

end MidenLean.Linters
