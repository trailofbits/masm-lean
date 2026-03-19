# Vivisect Agent Guidelines

## CRITICAL RULES
- Trailmark and contrarian are Claude Code SKILLS,
  invoked ONLY via the Skill tool.
- NEVER: pip/npm/cargo install, git clone.
- After a successful Skill call, do NOT try Bash.
- Every finding must cite file:line refs.
- Wrap prose lines at 75 columns.

## Format References (read when writing output)
- Findings:
/home/parallels/.claude/skills/vivisect/references/vivisect-findings-format.md
- Analysis:
/home/parallels/.claude/skills/vivisect/references/vivisect-analysis-format.md
- Cross-check:
/home/parallels/.claude/skills/vivisect/references/vivisect-cross-check-format.md
- Rationalizations:
  /home/parallels/.claude/skills/vivisect/references/rationalizations.md

## Build Commands
- Build: timeout 300s systemd-run --user --scope
  -p MemoryMax=10G -- lake build -j 2 MidenLean
- Targeted: timeout 180s systemd-run --user --scope
  -p MemoryMax=10G -- lake build -j 2
  MidenLean.Proofs.U64.Shr
- Language: Lean 4 v4.28.0
- Test framework: proofs ARE the tests. lake build
  succeeding with zero sorry means all theorems are
  machine-checked.
- No separate test runner.
- MANDATORY memory cap on all lake build commands.

## Test Style
Match existing Lean 4 theorem style: `theorem
foo_correct` with step lemma rewrites and
`miden_bind`. No broken-proofs.md exists. Tests
are the proof theorems themselves.

## Project Context
Lean 4 formal verification project proving
correctness of Miden Assembly (MASM) core library
procedures. Proofs verify that generated Lean
translations of MASM procedures compute the
intended mathematical functions.

## Spec Reference
A spec file exists at .galvanize/spec.md. Flag any
impl-vs-spec divergence as findings.
