#!/usr/bin/env python3
"""Audit Lean source placeholders and the kernel axioms reported for Audit.lean.

The source scan removes Lean comments, strings, and quoted identifiers before
matching declaration-level placeholder keywords.  The kernel scan consumes the
output of ``lake env lean Audit.lean`` and permits only Lean's standard logical
axioms.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import sys


ALLOWED_KERNEL_AXIOMS = frozenset({
    "Classical.choice",
    "Quot.sound",
    "propext",
})
FORBIDDEN_SOURCE_TOKENS = frozenset({
    "admit",
    "axiom",
    "native_decide",
    "sorry",
    "sorryAx",
    "unsafe",
})
REQUIRED_AUDIT_DECLARATIONS = frozenset({
    "TrafficShaping.causal_optimum_eq",
    "TrafficShaping.noncausal_optimum_eq",
})
REQUIRED_ARTICLE_ITEMS = frozenset(
    [f"equation-{i:02}" for i in range(1, 27)]
    + [f"lemma-{i}" for i in range(1, 5)]
    + [f"corollary-{i}" for i in range(1, 6)]
    + [
        "theorem-1", "budget-impossibility", "epsilon-independence",
        "full-input-reduction", "finite-game-duality", "privacy-interpretation",
        "corollary-1-sharpness", "gap-asymptotics", "matching-cost",
        "queue-cost", "matrix-cardinalities", "example-execution",
        "strict-threshold-endpoint", "periodic-observation", "qualitative-causality-gap",
    ]
    + [f"table-2-row-{i}" for i in range(1, 10)]
    + [f"table-3-row-{i}" for i in range(1, 9)]
)
DECLARATION_NAME_RE = re.compile(
    r"TrafficShaping(?:\.[A-Za-z_][A-Za-z0-9_']*)+\Z"
)
IMPORT_RE = re.compile(r"(?m)^[ \t]*import[ \t]+([^\r\n]+)$")
TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
PRINT_AXIOMS_RE = re.compile(
    r"(?m)^[ \t]*#print[ \t]+axioms[ \t]+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)"
    r"[ \t]*$"
)
AXIOM_REPORT_RE = re.compile(
    r"(?m)^[ \t]*(?:'(?P<quoted>[^\r\n]+?)'|"
    r"(?P<bare>[A-Za-z_][A-Za-z0-9_'.]*))"
    r"[ \t]+(?:depends on axioms:[ \t]*\[(?P<axioms>[^\]\r\n]*)\]"
    r"|does not depend on any axioms)[ \t]*$"
)


def _blank(text: str) -> str:
    """Replace one non-code character while preserving line/column positions."""
    return "\n" if text == "\n" else " "


def strip_lean_noncode(text: str) -> str:
    """Blank comments, strings, and quoted identifiers without changing lines."""
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    state = "code"
    while i < n:
        if state == "block":
            if text.startswith("/-", i):
                out.extend((" ", " "))
                block_depth += 1
                i += 2
            elif text.startswith("-/", i):
                out.extend((" ", " "))
                block_depth -= 1
                i += 2
                if block_depth == 0:
                    state = "code"
            else:
                out.append(_blank(text[i]))
                i += 1
            continue

        if state == "line":
            if text[i] == "\n":
                out.append("\n")
                state = "code"
            else:
                out.append(" ")
            i += 1
            continue

        if state == "string":
            if text[i] == "\\" and i + 1 < n:
                out.append(" ")
                out.append(_blank(text[i + 1]))
                i += 2
            elif text[i] == '"':
                out.append(" ")
                i += 1
                state = "code"
            else:
                out.append(_blank(text[i]))
                i += 1
            continue

        if state == "quoted_identifier":
            if text[i] == "»":
                out.append(" ")
                i += 1
                state = "code"
            else:
                out.append(_blank(text[i]))
                i += 1
            continue

        if text.startswith("--", i):
            out.extend((" ", " "))
            i += 2
            state = "line"
        elif text.startswith("/-", i):
            out.extend((" ", " "))
            i += 2
            block_depth = 1
            state = "block"
        elif text[i] == '"':
            out.append(" ")
            i += 1
            state = "string"
        elif text[i] == "«":
            out.append(" ")
            i += 1
            state = "quoted_identifier"
        else:
            out.append(text[i])
            i += 1

    if state == "block":
        raise ValueError("unterminated Lean block comment")
    if state == "string":
        raise ValueError("unterminated Lean string literal")
    if state == "quoted_identifier":
        raise ValueError("unterminated Lean quoted identifier")
    return "".join(out)


def source_files(formal_root: Path) -> list[Path]:
    entrypoint = formal_root / "TrafficShaping.lean"
    tree = formal_root / "TrafficShaping"
    if not entrypoint.is_file():
        raise ValueError(f"missing formal entrypoint: {entrypoint}")
    if not tree.is_dir():
        raise ValueError(f"missing formal source tree: {tree}")
    return [*sorted(formal_root.glob("*.lean")), *sorted(tree.rglob("*.lean"))]


def source_placeholder_errors(files: list[Path]) -> list[str]:
    errors = []
    for path in files:
        code = strip_lean_noncode(path.read_text())
        for match in TOKEN_RE.finditer(code):
            if match.group(0) in FORBIDDEN_SOURCE_TOKENS:
                line = code.count("\n", 0, match.start()) + 1
                column = match.start() - code.rfind("\n", 0, match.start())
                errors.append(
                    f"{path}:{line}:{column}: forbidden source token "
                    f"{match.group(0)!r}"
                )
    return errors


def audited_declarations(audit_source: str) -> list[str]:
    """Return every active ``#print axioms`` declaration in an audit file."""
    return [match.group("name") for match in PRINT_AXIOMS_RE.finditer(audit_source)]


def article_inventory(path: Path) -> tuple[set[str], list[str]]:
    """Require an explicit Lean anchor for every article formula and result.

    This checks inventory completeness, not the semantic accuracy of an anchor;
    the latter is established by reviewing the stated Lean propositions.
    """
    errors: list[str] = []
    names: set[str] = set()
    try:
        manifest = json.loads(path.read_text(encoding="utf-8"))
        if not isinstance(manifest, dict) or manifest.get("schema_version") != 1:
            return set(), ["article inventory must use schema_version 1"]
        items = manifest.get("items")
        if not isinstance(items, list) or not all(isinstance(x, dict) for x in items):
            return set(), ["article inventory items must be a list of objects"]
        ids = [item.get("id") for item in items]
        if not all(isinstance(item_id, str) for item_id in ids):
            return set(), ["article inventory ids must be strings"]
        counts = Counter(ids)
        for item_id, count in sorted(counts.items()):
            if count != 1:
                errors.append(f"duplicate article item: {item_id}")
        for item_id in sorted(REQUIRED_ARTICLE_ITEMS - set(ids)):
            errors.append(f"required article item missing: {item_id}")
        for item_id in sorted(set(ids) - REQUIRED_ARTICLE_ITEMS):
            errors.append(f"unrecognized article item: {item_id}")
        for item in items:
            declarations = item.get("declarations")
            if not isinstance(declarations, list) or not declarations:
                errors.append(f"article item has no Lean declarations: {item['id']}")
                continue
            for name in declarations:
                if not isinstance(name, str) or not DECLARATION_NAME_RE.fullmatch(name):
                    errors.append(f"invalid article declaration in {item['id']}: {name!r}")
                else:
                    names.add(name)
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        errors.append(f"cannot read article inventory: {exc}")
    return names, errors


def root_import_errors(formal_root: Path) -> list[str]:
    """Reject unchecked Lean files sitting outside the root import graph."""
    files = [formal_root / "TrafficShaping.lean",
             *sorted((formal_root / "TrafficShaping").rglob("*.lean"))]
    modules = {
        path.relative_to(formal_root).with_suffix("").as_posix().replace("/", "."): path
        for path in files
    }
    seen: set[str] = set()
    errors: list[str] = []
    allowed_top_level = {
        "TrafficShaping.lean", "Audit.lean", "AuditFoundations.lean", "AuditNoncausal.lean"
    }
    errors.extend(
        f"unexpected top-level formal source: {path.name}"
        for path in sorted(formal_root.glob("*.lean"))
        if path.name not in allowed_top_level
    )

    def visit(module: str) -> None:
        if module in seen:
            return
        seen.add(module)
        path = modules.get(module)
        if path is None:
            errors.append(f"missing local Lean import: {module}")
            return
        code = strip_lean_noncode(path.read_text(encoding="utf-8"))
        for match in IMPORT_RE.finditer(code):
            for imported in match.group(1).split():
                if imported == "TrafficShaping" or imported.startswith("TrafficShaping."):
                    visit(imported)

    visit("TrafficShaping")
    errors.extend(
        f"Lean module is not reachable from the root import: {module}"
        for module in sorted(set(modules) - seen)
    )
    return errors


def kernel_axiom_errors(
    output: str, audited_names: list[str]
) -> tuple[list[str], int]:
    """Check report names, report multiplicity, and each report's axioms."""
    errors = []
    reports = list(AXIOM_REPORT_RE.finditer(output))
    report_names = [
        report.group("quoted") or report.group("bare") for report in reports
    ]
    audited_counts = Counter(audited_names)
    report_counts = Counter(report_names)
    duplicate_commands = sorted(
        name for name, count in audited_counts.items() if count > 1
    )
    duplicate_reports = sorted(
        name for name, count in report_counts.items() if count > 1
    )
    if not audited_names:
        errors.append("Audit.lean contains no '#print axioms' command")
    if duplicate_commands:
        errors.append(
            "duplicate '#print axioms' commands: " + ", ".join(duplicate_commands)
        )
    if duplicate_reports:
        errors.append(
            "duplicate kernel axiom reports: " + ", ".join(duplicate_reports)
        )
    missing_reports = sorted((audited_counts - report_counts).elements())
    extra_reports = sorted((report_counts - audited_counts).elements())
    if missing_reports:
        errors.append("missing kernel axiom reports: " + ", ".join(missing_reports))
    if extra_reports:
        errors.append("unexpected kernel axiom reports: " + ", ".join(extra_reports))
    if re.search(r"\bsorryAx\b|\bsorry\b|\badmit\b", output):
        errors.append("Lean output contains sorry/admit evidence")
    for report in reports:
        names = {
            name.strip()
            for name in (report.group("axioms") or "").split(",")
            if name.strip()
        }
        unexpected = sorted(names - ALLOWED_KERNEL_AXIOMS)
        if unexpected:
            errors.append(
                "unexpected kernel axioms: " + ", ".join(unexpected)
            )
    return errors, len(reports)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--formal-root", type=Path, default=Path("formal"))
    parser.add_argument("--audit-file", type=Path, default=Path("formal/Audit.lean"))
    parser.add_argument("--axiom-output", type=Path, required=True)
    parser.add_argument("--article-inventory", type=Path,
                        default=Path("formal/article-coverage.json"))
    args = parser.parse_args()

    if not args.audit_file.is_file():
        print(f"missing final audit file: {args.audit_file}", file=sys.stderr)
        return 1
    try:
        audit_source = args.audit_file.read_text()
        audit_code = strip_lean_noncode(audit_source)
        audited_names = audited_declarations(audit_code)
        files = source_files(args.formal_root)
        if args.audit_file not in files:
            files.append(args.audit_file)
        errors = source_placeholder_errors(files)
        errors.extend(root_import_errors(args.formal_root))
    except (OSError, ValueError) as exc:
        print(f"formal source audit failed: {exc}", file=sys.stderr)
        return 1

    try:
        output = args.axiom_output.read_text()
        missing_inventory = sorted(REQUIRED_AUDIT_DECLARATIONS - set(audited_names))
        if missing_inventory:
            errors.extend(
                "required final audit declaration missing: " + name
                for name in missing_inventory
            )
        article_names, article_errors = article_inventory(args.article_inventory)
        errors.extend(article_errors)
        errors.extend(
            "article declaration is not kernel-audited: " + name
            for name in sorted(article_names - set(audited_names))
        )
        kernel_errors, report_count = kernel_axiom_errors(output, audited_names)
    except OSError as exc:
        print(f"kernel axiom audit failed: {exc}", file=sys.stderr)
        return 1
    errors.extend(kernel_errors)

    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(
        f"Formal source audit passed: {len(files)} files; "
        f"kernel axiom reports: {report_count}; "
        f"article items: {len(REQUIRED_ARTICLE_ITEMS)}; "
        "allowed axioms: Classical.choice, Quot.sound, propext"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
