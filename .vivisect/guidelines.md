# Vivisect Agent Guidelines

## CRITICAL RULES
- Trailmark and contrarian are Claude Code SKILLS,
  invoked ONLY via the Skill tool.
- NEVER: pip/npm/cargo install, git clone.
- After a successful Skill call, do NOT try Bash.
- Every finding must cite file:line refs.
- Wrap prose lines at 75 columns.

## Format References (read when writing output)
- Findings: /home/parallels/.claude/skills/vivisect/references/vivisect-findings-format.md
- Analysis: /home/parallels/.claude/skills/vivisect/references/vivisect-analysis-format.md
- Cross-check: /home/parallels/.claude/skills/vivisect/references/vivisect-cross-check-format.md
- Rationalizations: /home/parallels/.claude/skills/vivisect/references/rationalizations.md

## Build Commands
- Build: systemd-run --user --scope -p MemoryMax=10G -- lake build -j 2 MidenLean
- Language: Lean 4 v4.28.0
- Test framework: #eval blocks with guard statements
  (lake build succeeding implies all tests pass)
- No separate test runner; tests compile as part of
  lake build.

## Test Style
No .vivisect/broken-proofs.md exists. Match existing
test style in MidenLean/Tests/Semantics.lean: #eval
blocks with guard checks. Tests pass when lake build
succeeds.

## Spec Reference
A spec file exists at .galvanize/spec.md. Flag any
impl-vs-spec divergence as findings.
