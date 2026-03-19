# Claude Notes: audit-0xmiden/masm-lean

## 2026-03-19: Vivisect run 14 (post-AC-50-53)

AC-50 through AC-53 verified. All overflow guards
confirmed in place. Previous Bad finding resolved.
Results: 18 Good, 0 Bad, 0 Broken, 0 Absurd.
Lean LSP: 0 errors, 0 warnings on key files.
Files: .vivisect/findings.md (run 14),
  .vivisect/analysis.md (updated to run 14),
  .vivisect/manual-analysis.md (run 14),
  .vivisect/patches.md (run 14, empty).

## 2026-03-19: Vivisect run 13 (verification pass)

No .lean file changes since run 12. Build re-verified:
1913 jobs, 0 errors, 0 warnings. Zero sorry.
Results: 17 Good, 1 Bad, 0 Broken, 0 Absurd.
Contrarian validated 8 functions: all SOUND.
35 proof scripts (24 writer + 11 breaker), 0 breaks.
Files: .vivisect/findings.md (run 13),
  .vivisect/analysis.md, .vivisect/patches.md,
  .vivisect/manual-analysis.md.
Spec divergence: 2 stale spec text items noted
(memory model description, assert semantics).
Ongoing: AC-50 to AC-53 (Tier 11) -- starting now.

### AC-50 plan: overflow guards
Handlers with net positive stack effect need overflow
guards. Check `s.stack.length + net > MAX_STACK_DEPTH`,
return `none` if so.

**Handlers to modify (net growth):**
- execPadw (+4), execPush (+1), execPushList (+N)
- execDup (+1), execDupw (+4)
- execU32Test (+1), execU32TestW (+1), execU32Split (+1)
- execMemLoadImm (+1), execLocLoad (+1)
- execAdvPush (+N)

**Step lemmas needing overflow hypothesis:**
- stepPush, stepDup, stepDupw, stepU32Split, stepAdvPush2

**Tactic:** miden_step discharges overflow via `by omega`

**Proofs:** add `hlen : rest.length + 30 <= MAX_STACK_DEPTH`
to correctness theorems. Tactic uses
`simp [List.length_cons]; omega` to discharge.

### AC-50/51/52 DONE
- 11 handlers in Semantics.lean got overflow guards
- 5 step lemmas got hov hypotheses
- Tactics.lean: miden_step discharges via simp+omega
- 30+ proof files updated with hlen hypotheses
- Build: 1913 jobs, 0 errors, 0 warnings, 0 sorry
- Also fixed: stale ha_align in Tactics.lean,
  stale -j 2 in CLAUDE.md and guidelines.md

## 2026-03-19: Tier 11 added (not yet started)

Per-instruction stack depth enforcement (AC-50 to AC-53).
This resolves the last Bad vivisect finding. Requires:
- AC-50: Add overflow/underflow guards to handlers
- AC-51: Update step lemmas with wellFormed hypotheses
- AC-52: Update all proof files
- AC-53: Stack depth edge case tests
Checkpoint tag: checkpoint-pre-tier11

## 2026-03-19: Vivisect run 12 (post-memory-refactor)

Ran vivisect on the codebase after the memory model
refactor from element-addressed to word-addressed.

Results: 17 Good, 1 Bad, 0 Broken, 0 Absurd.
- Previous "Bad: element-addressed memory" finding
  is now resolved (Good).
- Only remaining Bad: stack depth not enforced
  per-instruction (intentional simplification).
- Build: 0 errors, 0 warnings, 0 sorry (1913 jobs).
- Spec text at .galvanize/spec.md lines 155-156 and
  236-240 is stale (still says element-addressed).
- All memory operations verified correct against
  Rust VM semantics.
- Le variant confirmed as Rust-native order.
- writeMemoryElem0 correctly preserves elements 1-3.

Files written:
- .vivisect/findings.md (run 12)
- .vivisect/analysis.md (run 12)
- .vivisect/patches.md (run 12)
- .vivisect/manual-analysis.md (run 12 section added)

## 2026-03-19: AC-44 Word-addressed memory refactor

### Plan
Change memory model from `Nat -> Felt` (element-addressed)
to `Nat -> Word` (word-addressed, matching Rust VM).

**Files to change:**
1. State.lean: memory/locals type, write helpers
2. Semantics.lean: all memory/local instructions
3. StepLemmas.lean: step lemma signatures + proofs
4. Helpers.lean: withStack_memory/locals helpers
5. EquationLemmas.lean: should auto-update
6. Proofs/U64/Div,Mod,Divmod.lean: thread mem/locs
7. Proofs/Word/StoreWordU32sLe.lean: full rewrite
8. Tests/Semantics.lean: memory test states

**Key semantic changes:**
- memLoad: read `(s.memory addr).1` (element 0 of word)
- memStore: write element 0 via Word.set
- memStorew/memLoadw: read/write full Word directly
- Remove alignment checks (addr % 4) from word ops
- locLoad/locStore: same pattern as memLoad/memStore
- Output of writeMemory is cleaner (one if/then/else
  per word write, not per element)

**Risk:** StoreWordU32sLe proof needs full rewrite.
Currently outputs 8-level if/then/else; word model
outputs 2-level. Should be simpler but proof steps
change entirely.

## 2026-03-19: Galvanize CONVERGED (iteration 11)

### Final state
- 50/51 ACs complete (AC-44 deferred: full memory refactor)
- Build: 0 errors, 0 warnings, 0 sorry (1913 jobs)
- Vivisect: 16 Good, 2 Bad (intentional), 0 Broken, 0 Absurd
- Quality gate: all items PASS or N/A
- Lint fix: removed dead tactic in StoreWordU32sLe.lean
- Spec fix: assert semantics corrected (top = 1, not != 0)

## 2026-03-19: Galvanize iteration 10 (complete)

### Completed this session
- AC-34/35/36: shr/rotl/rotr semantic theorems
- AC-47: maxHeartbeats removal (98 removed, 1 retained
  in Felt.lean for primality). EquationLemmas.lean
  provides O(1) dispatch for all ~100 instructions.
- AC-45: events field added to MidenState. execEmit
  records top stack element. emitImm records argument.
  72+ files updated. Divmod/Div/Mod correctly track
  event ID 14153021663962350784 in output state.
- AC-48: ongoing check passes (1 exception: Felt.lean)
- Build: EXIT 0, 0 errors, 0 warnings, 0 sorry
- Status: 48/51 ACs complete

### Remaining ACs (Tier 10)
- AC-43: Bounded stack model (min 16, max 2^16)
  Approach: add padding at exec entry point, not per
  instruction. Lighter touch than changing List Felt.
- AC-44: Word-addressed memory (Nat -> Felt to
  Nat -> Word). Largest structural change remaining.

### Pre-existing U128 proof issues (not our bug)
Several U128 proofs reference undefined identifiers
(stepSwapw1, stepDupw1, stepU32WrappingMadd) and
missing tactics (miden_loop). These predate all our
changes and were masked by stale .olean caches.
Files: U128.Gt, U128.Max, U128.WrappingMul,
U128.OverflowingMul, Word.Eqz.

### Key technique: equation lemmas
Each instruction gets a theorem:
  execInstruction s .foo = execFoo s := rfl
O(1) dispatch via rfl. Step lemmas use:
  simp only [execInstruction_foo]; unfold execFoo; ...
DO NOT mark equation lemmas @[simp] -- causes eager
rewriting that breaks proofs using rw [stepFoo].

### Key technique: events field threading
When adding a field to MidenState:
1. Add with default value (events : List Felt := [])
2. Anonymous constructors need 5th field everywhere
3. obtain patterns need named binding (not _)
4. Call sites passing explicit params need evts added
5. Theorems with emitImm must track event in output
Use sed/python for bulk changes, fix call sites manually.

### Prior sessions (condensed)
See git log for full history.
