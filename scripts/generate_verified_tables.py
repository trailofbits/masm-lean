#!/usr/bin/env python3
"""Generate markdown tables for verified manual proof procedures.

The script:
1. builds each manual proof module component-wise with a strict timeout,
2. extracts the public `*_correct` theorem from each manual proof file,
3. parses the associated theorem doc comment for a short summary when present,
4. emits a markdown snippet with one table per module.

Warnings are written to stderr when:
- a build times out,
- a build fails,
- a build succeeds with Lean warnings,
- a proof file does not expose a public `*_correct` theorem,
- theorem metadata is missing or too weak to be useful.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
PROOFS_ROOT = REPO_ROOT / "MidenLean" / "Proofs"
GENERATED_ROOT = REPO_ROOT / "MidenLean" / "Generated"
MODULE_DIRS = {
    "u64": PROOFS_ROOT / "U64",
    "u128": PROOFS_ROOT / "U128",
    "word": PROOFS_ROOT / "Word",
}
GENERATED_MODULE_FILES = {
    "u64": GENERATED_ROOT / "U64.lean",
    "u128": GENERATED_ROOT / "U128.lean",
    "word": GENERATED_ROOT / "Word.lean",
}
MODULE_ORDER = ("u64", "u128", "word")
SUPPORT_FILES = {"Common.lean"}

THEOREM_RE = re.compile(r"(?m)^theorem\s+([A-Za-z0-9_]+_correct)\b")
DOC_COMMENT_RE = re.compile(r"/--(.*?)-/", re.DOTALL)
BUILD_WARNING_RE = re.compile(r"(?m)^warning:")
PROCEDURE_DEF_RE = re.compile(r"(?m)^def\s+([A-Za-z0-9_]+)\s*:\s*List Op\s*:=\s*\[")


@dataclass
class ProofRow:
    module: str
    procedure: str
    theorem: str
    summary: str
    path: Path


@dataclass
class WarningMessage:
    kind: str
    message: str


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Build manual proof files and generate verified-procedure tables."
    )
    parser.add_argument(
        "--timeout-seconds",
        type=int,
        default=180,
        help="Strict timeout for each `lake build` invocation (default: 180).",
    )
    parser.add_argument(
        "--modules",
        nargs="*",
        choices=tuple(MODULE_DIRS.keys()),
        default=list(MODULE_DIRS.keys()),
        help="Subset of proof modules to inspect (default: u64 u128 word).",
    )
    return parser.parse_args()


def warn(warnings: list[WarningMessage], kind: str, message: str) -> None:
    warnings.append(WarningMessage(kind=kind, message=message))


def progress(message: str) -> None:
    print(message, file=sys.stderr, flush=True)


def relative_posix(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def module_name_for_file(path: Path) -> str:
    rel = path.relative_to(REPO_ROOT).with_suffix("")
    return ".".join(rel.parts)


def find_public_correctness_theorem(content: str) -> re.Match[str] | None:
    matches = list(THEOREM_RE.finditer(content))
    if not matches:
        return None
    return matches[0]


def associated_doc_comment(content: str, theorem_start: int) -> str | None:
    candidate: re.Match[str] | None = None
    for match in DOC_COMMENT_RE.finditer(content):
        if match.end() <= theorem_start:
            candidate = match
        else:
            break
    if candidate is None:
        return None
    interstitial = content[candidate.end() : theorem_start]
    if interstitial.strip():
        return None
    return candidate.group(1)


def normalize_comment(text: str) -> str:
    lines = []
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith("*"):
            stripped = stripped[1:].strip()
        if stripped:
            lines.append(stripped)
    normalized = " ".join(lines)
    normalized = re.sub(r"\s+", " ", normalized).strip()
    for marker in ("Input stack:", "Output stack:", "Requires ", "where "):
        idx = normalized.find(marker)
        if idx != -1:
            normalized = normalized[:idx].strip()
    return normalized


def escape_md(text: str) -> str:
    return text.replace("|", r"\|")


def theorem_to_procedure(module: str, theorem: str) -> str | None:
    prefix = f"{module}_"
    suffix = "_correct"
    if theorem.startswith(prefix) and theorem.endswith(suffix):
        return theorem[len(prefix) : -len(suffix)]
    return None


def extract_row(
    path: Path, module: str, warnings: list[WarningMessage]
) -> ProofRow | None:
    content = path.read_text(encoding="utf-8")
    theorem_match = find_public_correctness_theorem(content)
    if theorem_match is None:
        warn(
            warnings,
            "structure",
            f"{relative_posix(path)}: no public `*_correct` theorem found; skipping.",
        )
        return None

    theorem = theorem_match.group(1)
    procedure = theorem_to_procedure(module, theorem)
    if procedure is None:
        warn(
            warnings,
            "structure",
            f"{relative_posix(path)}: theorem `{theorem}` does not match the expected `{module}_*_correct` naming scheme; skipping.",
        )
        return None

    doc_comment = associated_doc_comment(content, theorem_match.start())
    if doc_comment is None:
        warn(
            warnings,
            "metadata",
            f"{relative_posix(path)}: theorem `{theorem}` has no directly associated doc comment.",
        )
        summary = "Missing theorem comment."
    else:
        summary = normalize_comment(doc_comment)
        if len(summary.split()) < 4:
            warn(
                warnings,
                "metadata",
                f"{relative_posix(path)}: theorem `{theorem}` has insufficient metadata: `{summary}`.",
            )
            if not summary:
                summary = "Missing theorem comment."

    return ProofRow(
        module=module,
        procedure=procedure,
        theorem=theorem,
        summary=summary,
        path=path,
    )


def run_build(
    module_name: str, timeout_seconds: int
) -> subprocess.CompletedProcess[str]:
    cmd = ["timeout", f"{timeout_seconds}s", "lake", "build", module_name]
    try:
        return subprocess.run(
            cmd,
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
    except FileNotFoundError:
        return subprocess.run(
            ["lake", "build", module_name],
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            check=False,
            timeout=timeout_seconds,
        )


def build_file(
    path: Path,
    timeout_seconds: int,
    warnings: list[WarningMessage],
    *,
    kind: str = "proof",
) -> bool:
    module_name = module_name_for_file(path)
    progress(f"starting {kind} {module_name}")
    try:
        proc = run_build(module_name, timeout_seconds)
    except subprocess.TimeoutExpired:
        progress(f"{kind} {module_name} timed out")
        warn(
            warnings,
            "timeout",
            f"{module_name}: build exceeded {timeout_seconds}s.",
        )
        return False

    combined_output = (proc.stdout or "") + (proc.stderr or "")
    if proc.returncode == 124:
        progress(f"{kind} {module_name} timed out")
        warn(
            warnings,
            "timeout",
            f"{module_name}: build exceeded {timeout_seconds}s.",
        )
        return False
    if proc.returncode != 0:
        progress(f"{kind} {module_name} failed")
        warn(
            warnings,
            "build",
            f"{module_name}: build failed with exit code {proc.returncode}.",
        )
        return False
    if BUILD_WARNING_RE.search(combined_output):
        warn(
            warnings,
            "build-warning",
            f"{module_name}: build succeeded with Lean warnings.",
        )
    progress(f"{kind} {module_name} completed")
    return True


def iter_module_files(module_dir: Path) -> Iterable[Path]:
    for path in sorted(module_dir.glob("*.lean")):
        yield path


def count_total_procedures(module: str) -> int:
    generated_file = GENERATED_MODULE_FILES[module]
    content = generated_file.read_text(encoding="utf-8")
    return len(PROCEDURE_DEF_RE.findall(content))


def format_tables(
    rows_by_module: dict[str, list[ProofRow]], total_procedures_by_module: dict[str, int]
) -> str:
    total = sum(len(rows) for rows in rows_by_module.values())
    parts: list[str] = []
    module_counts = ", ".join(
        f"{len(rows_by_module[module])} in `{module}`"
        for module in MODULE_ORDER
        if module in rows_by_module
    )
    parts.append(
        f"The current checked manual proofs cover {total} procedures: {module_counts}."
    )
    for module in MODULE_ORDER:
        rows = rows_by_module.get(module)
        if rows is None:
            continue
        total_procedures = total_procedures_by_module[module]
        parts.append("")
        parts.append(f"### `{module}` ({len(rows)} / {total_procedures})")
        parts.append("")
        parts.append("| Procedure | Theorem | Summary | Manual proof file |")
        parts.append("| --- | --- | --- | --- |")
        for row in sorted(rows, key=lambda r: r.procedure):
            parts.append(
                "| "
                f"`{module}::{escape_md(row.procedure)}` | "
                f"`{escape_md(row.theorem)}` | "
                f"{escape_md(row.summary)} | "
                f"`{escape_md(relative_posix(row.path))}` |"
            )
    return "\n".join(parts)


def main() -> int:
    args = parse_args()
    warnings: list[WarningMessage] = []
    rows_by_module: dict[str, list[ProofRow]] = {module: [] for module in args.modules}
    total_procedures_by_module = {
        module: count_total_procedures(module) for module in args.modules
    }
    build_failures = False

    for module in args.modules:
        module_dir = MODULE_DIRS[module]
        for path in iter_module_files(module_dir):
            if path.name in SUPPORT_FILES:
                if not build_file(
                    path,
                    args.timeout_seconds,
                    warnings,
                    kind="support file",
                ):
                    build_failures = True
                continue

            row = extract_row(path, module, warnings)
            if row is None:
                continue
            if build_file(path, args.timeout_seconds, warnings):
                rows_by_module[module].append(row)
            else:
                build_failures = True

    print(format_tables(rows_by_module, total_procedures_by_module))

    for warning in warnings:
        print(f"warning[{warning.kind}]: {warning.message}", file=sys.stderr)

    return 1 if build_failures else 0


if __name__ == "__main__":
    sys.exit(main())
