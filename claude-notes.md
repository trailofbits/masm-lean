# Claude Notes: audit-0xmiden/masm-lean

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
