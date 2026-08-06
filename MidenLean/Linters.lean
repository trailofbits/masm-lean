import Batteries.Tactic.Lint
import MidenLean.Symbolic.SimpAttrs

/-!
# Project-specific `#lint` linters

Four declaration-level linters (Batteries' `@[env_linter]` kind, which is what
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

* `midenSimpBankNumerals` — the u32 modulus has three spellings here
  (`MidenLean.u32Max`, `2 ^ 32`, `4294967296`) and simp matching does not see
  through them, so a bank lemma keyed on one spelling never fires against a goal
  written in another. That cost two multi-hour debugging sessions, because the
  lemma is true, provable, applicable-looking, and simply never applies.

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

/-! ## `midenSimpBankNumerals`

The u32 modulus has three spellings in this codebase: `MidenLean.u32Max`,
`2 ^ 32`, and the literal `4294967296`. `simp` matching does not see through
them — a rewrite keyed on one spelling silently never fires against a goal
normalized to another — and the failure has no visible symptom, because the
lemma is true, provable, applicable-looking, and simply never applies. Finding
that out twice cost two multi-hour debugging sessions.

The convention that came out of those sessions, recorded at length in
`Symbolic/Reflect.lean`: a lemma in these banks should be phrased over
*structure* — an `Expr.eval` node applied to operands — so that its left-hand
side contains no numeral at all and cannot be out of step with the goal; and
where a numeral is unavoidable it must be spelled `2 ^ 32`, never `u32Max`,
because `simp` normalizes goals towards the literal (`Nat.reducePow`) and it is
`2 ^ 32` that survives matching.

So this linter reports a bank lemma whose *matched* side mentions `u32Max`. Only
the matched side counts: right-hand sides legitimately spell `u32Max` when they
are steering a reflected goal onto the spelling that the concrete semantics and
the manual `*_correct` statements use, which is exactly what
`u32CountLeadingOnes_eq` and `u32CountTrailingOnes_eq` do.

Two things are checked at the anchor declaration `MidenLean.u32Max` rather than
per lemma: that all four bank attributes are actually registered (otherwise
membership queries return nothing and the linter is vacuous), and that no
allowlist entry has gone stale. -/

/-- The `register_simp_attr` banks whose lemmas take part in u32 goal
    normalization, declared in `Proofs/SimpAttrs.lean` and
    `Symbolic/SimpAttrs.lean`. Membership is read out of the simp extension
    itself, so the check follows the attribute rather than a naming convention.

    `miden_cleanup` is deliberately absent: it is an unfold set whose members
    include the auto-generated `Expr.eval.eq_*` equations, whose right-hand
    sides mention `u32Max` because `Expr.eval` is *defined* that way. -/
meta def simpBankAttrs : List Name :=
  [`miden_val, `miden_bound, `miden_u32, `miden_reflect_norm]

/-- The u32 modulus constant. Referred to by name (this module does not import
    the library it lints); its absence from the environment is reported at the
    anchor rather than passing vacuously. -/
meta def u32MaxName : Name := `MidenLean.u32Max

/-- Bank lemmas allowed to match on the `u32Max` spelling, because relating the
    spellings is the lemma's whole purpose — a lemma stating `u32Max = 2 ^ 32`,
    or one whose left-hand side is `u32Max` so that it unfolds the modulus into
    the canonical spelling. One entry per line, each with its reason; entries
    that no longer name such a lemma are reported as stale, so this list cannot
    quietly outlive its justification.

    Empty today: of the two bank lemmas that used to match on `u32Max`,
    `u32Not_isU32` was restated over `2 ^ 32` and `u32Shl_isU32` was deleted as
    subsumed by `u32_mod_isU32`. -/
meta def numeralSpellingAllowlist : List Name := []

/-- Does `e` mention the `u32Max` constant? -/
meta def mentionsU32Max (e : Expr) : Bool :=
  (e.find? (·.isConstOf u32MaxName)).isSome

/-- The banks `declName` is a rewrite lemma in, each paired with whether the
    entry is reversed (`@[bank ←]`, which rewrites right-to-left and therefore
    matches goals against the statement's right-hand side).

    Read from the simp extensions, which is the only faithful source: these are
    `register_simp_attr` sets, so there is no per-set environment extension of
    names to consult the way `@[miden_exec_summary]` has one. `Origin`'s `BEq`
    ignores the pre/post flag, so a `↓` lemma is found by the same query. -/
meta def bankEntries (declName : Name) : MetaM (List (Name × Bool)) := do
  let mut entries := []
  for attr in simpBankAttrs do
    let some ext ← getSimpExtension? attr | continue
    let thms ← ext.getTheorems
    if thms.isLemma (.decl declName) then
      entries := (attr, false) :: entries
    if thms.isLemma (.decl declName (inv := true)) then
      entries := (attr, true) :: entries
  return entries

/-- The side of `ty`'s conclusion that `simp` matches goals against: the
    left-hand side, or the right-hand side for a reversed entry. Leading `let`
    binders are substituted away first, as in `isExecSummaryShape`. A conclusion
    that is not an equation or an iff is used by `simp` as `p = True`, so the
    whole conclusion is the matched side. -/
meta def matchedSide (ty : Expr) (reversed : Bool) : MetaM Expr :=
  forallTelescopeReducing ty fun _ body => do
    let body := peelLets body
    if let some (_, lhs, rhs) := body.eq? then
      return if reversed then rhs else lhs
    if let some (lhs, rhs) := body.iff? then
      return if reversed then rhs else lhs
    return body

/-- Allowlist entries that no longer name a bank lemma matching on `u32Max`:
    either the declaration is gone, or it left the banks, or it was restated and
    no longer mentions the modulus on its matched side. Any of those means the
    entry is dead weight and should be deleted. -/
meta def staleAllowlistEntries : MetaM (List Name) := do
  let mut stale := []
  for entry in numeralSpellingAllowlist do
    let entries ← bankEntries entry
    match (← getEnv).find? entry with
    | none => stale := entry :: stale
    | some info =>
      let mut needed := false
      for (_, reversed) in entries do
        if mentionsU32Max (← matchedSide info.type reversed) then needed := true
      unless needed do stale := entry :: stale
  return stale.reverse

/-- No lemma in the `miden_val` / `miden_bound` / `miden_u32` /
    `miden_reflect_norm` simp banks may match goals on the `MidenLean.u32Max`
    spelling of the u32 modulus: `simp` normalizes goals towards `2 ^ 32` and
    the literal `4294967296`, so a `u32Max`-keyed rewrite is dead weight that
    looks live. Right-hand sides are not checked — spelling the modulus
    `u32Max` there is how a reflected goal is steered onto the concrete
    semantics' spelling. Genuine spelling bridges go in
    `numeralSpellingAllowlist`, whose stale entries are reported too. -/
@[env_linter] meta def midenSimpBankNumerals : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "No simp-bank lemma is keyed on the `u32Max` spelling of the \
    u32 modulus."
  errorsFound := "SIMP-BANK LEMMAS KEYED ON `MidenLean.u32Max` (they cannot fire \
    against a goal whose modulus `simp` has normalized to `2 ^ 32` / \
    `4294967296`, and nothing about them looks wrong):"
  test declName := do
    -- Cheapest possible rejection first: this runs once per declaration.
    unless (`MidenLean).isPrefixOf declName do return none
    if declName == u32MaxName then
      -- Whole-bank checks, anchored on the modulus itself so that they are paid
      -- for on exactly one declaration.
      let env ← getEnv
      unless env.contains u32MaxName do
        return m!"is not in the environment, so every check in \
          `midenSimpBankNumerals` is vacuous. Fix \
          `MidenLean.Linters.u32MaxName`."
      let mut problems := []
      for attr in simpBankAttrs do
        if (← getSimpExtension? attr).isNone then
          problems := m!"\n  simp bank `{attr}` is not a registered simp \
            attribute, so its lemmas are not checked at all. Fix \
            `MidenLean.Linters.simpBankAttrs`." :: problems
      let stale ← staleAllowlistEntries
      unless stale.isEmpty do
        problems := m!"\n  allowlisted names that are no longer bank lemmas \
          matching on `{u32MaxName}` (stale allowlist): {stale}" :: problems
      if problems.isEmpty then return none
      return MessageData.joinSep problems.reverse ""
    let entries ← bankEntries declName
    if entries.isEmpty then return none
    if numeralSpellingAllowlist.contains declName then return none
    let info ← getConstInfo declName
    let mut offending := []
    for (attr, reversed) in entries do
      if mentionsU32Max (← matchedSide info.type reversed) then
        offending := (if reversed then m!"@[{attr} ←]" else m!"@[{attr}]") :: offending
    if offending.isEmpty then return none
    return m!"is in {MessageData.andList offending} and matches on \
      `{u32MaxName}`, so it can only ever fire against a goal that spells the \
      modulus the same way. State it over the `Expr.eval` structure, or spell \
      the modulus `2 ^ 32`. If relating the two spellings is the point of the \
      lemma, add it to `MidenLean.Linters.numeralSpellingAllowlist` with a \
      reason."

end MidenLean.Linters
