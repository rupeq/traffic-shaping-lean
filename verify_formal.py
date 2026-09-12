#!/usr/bin/env python3
"""Run and record the final Lean formalization check.

The command deliberately keeps going after a failed subprocess so that every
requested log and the final FAIL record are available for diagnosis.  PASS is
possible only when the pinned inputs, all commands, and the source snapshot
checks succeed.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from typing import Any


ROOT = Path(__file__).resolve().parent
FORMAL = ROOT / "formal"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.33.1"
EXPECTED_LEAN_VERSION = "4.33.1"
EXPECTED_MATHLIB_REV = "0df444a360eaa60ab8c11dca51a86af692955474"
REPORT_RE = re.compile(
    r"(?m)^[ \t]*[^\r\n]+(?:depends on axioms:[ \t]*\["
    r"|does not depend on any axioms[ \t]*$)"
)
PRINT_RE = re.compile(r"(?m)^\s*#print\s+axioms\s+\S+")


def audit_module():
    spec = importlib.util.spec_from_file_location(
        "traffic_shaping_formal_audit", ROOT / ".github/scripts/audit_formal.py"
    )
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load the formal audit implementation")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def source_paths() -> list[Path]:
    paths = [
        *FORMAL.glob("*.lean"),
        *FORMAL.joinpath("TrafficShaping").rglob("*.lean"),
        FORMAL / "Audit.lean",
        FORMAL / "lean-toolchain",
        FORMAL / "lakefile.toml",
        FORMAL / "lake-manifest.json",
        FORMAL / "article-coverage.json",
        ROOT / ".github/scripts/audit_formal.py",
        ROOT / "verify_formal.py",
    ]
    return sorted(set(paths))


def snapshot() -> tuple[dict[str, str], list[str], list[str]]:
    hashes: dict[str, str] = {}
    missing: list[str] = []
    errors: list[str] = []
    for path in source_paths():
        relative = path.relative_to(ROOT).as_posix()
        try:
            if not path.is_file():
                missing.append(relative)
                continue
            hashes[relative] = hashlib.sha256(path.read_bytes()).hexdigest()
        except OSError as exc:
            errors.append(f"cannot hash {relative}: {exc}")
    return hashes, missing, errors


def resolve_lake(argument: str, env: dict[str, str]) -> tuple[str, Path | None]:
    candidate = Path(argument)
    if candidate.is_absolute() or candidate.parent != Path("."):
        path = candidate.resolve()
        return str(path), path if path.is_file() else None
    found = shutil.which(argument, path=env.get("PATH"))
    if found is None:
        return argument, None
    path = Path(found).resolve()
    return str(path), path


def run_command(
    command: list[str], cwd: Path, env: dict[str, str]
) -> tuple[int, str]:
    try:
        completed = subprocess.run(
            command,
            cwd=str(cwd),
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            errors="replace",
            check=False,
        )
        return completed.returncode, completed.stdout
    except OSError as exc:
        return 127, f"could not execute {' '.join(command)}: {exc}\n"


def check_inputs() -> tuple[bool, dict[str, Any], list[str]]:
    checks: dict[str, Any] = {}
    errors: list[str] = []
    toolchain_path = FORMAL / "lean-toolchain"
    manifest_path = FORMAL / "lake-manifest.json"
    try:
        declared = toolchain_path.read_text(encoding="utf-8").strip()
        checks["declared_toolchain"] = declared
        checks["lean_toolchain_pinned"] = declared == EXPECTED_TOOLCHAIN
        if declared != EXPECTED_TOOLCHAIN:
            errors.append(
                f"formal/lean-toolchain is {declared!r}, expected {EXPECTED_TOOLCHAIN!r}"
            )
    except (OSError, UnicodeError) as exc:
        checks["lean_toolchain_pinned"] = False
        errors.append(f"cannot read formal/lean-toolchain: {exc}")

    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        mathlibs = [p for p in manifest.get("packages", []) if p.get("name") == "mathlib"]
        mathlib = mathlibs[0] if len(mathlibs) == 1 else {}
        revision = mathlib.get("rev")
        input_revision = mathlib.get("inputRev")
        checks["mathlib_revision"] = revision
        checks["mathlib_input_revision"] = input_revision
        checks["mathlib_manifest_pinned"] = (
            revision == EXPECTED_MATHLIB_REV and input_revision == "v4.33.1"
        )
        if not checks["mathlib_manifest_pinned"]:
            errors.append(
                "formal/lake-manifest.json does not pin mathlib to "
                f"{EXPECTED_MATHLIB_REV} (inputRev v4.33.1)"
            )
    except (OSError, UnicodeError, json.JSONDecodeError, AttributeError, IndexError) as exc:
        checks["mathlib_manifest_pinned"] = False
        errors.append(f"cannot read formal/lake-manifest.json: {exc}")
    return not errors, checks, errors


def report_counts(output_dir: Path) -> dict[str, int]:
    audit_path = FORMAL / "Audit.lean"
    axioms_path = output_dir / "full-optimum-axioms.log"
    try:
        audit_text = audit_path.read_text(encoding="utf-8")
    except (OSError, UnicodeError):
        audit_text = ""
    try:
        axioms_text = axioms_path.read_text(encoding="utf-8")
    except (OSError, UnicodeError):
        axioms_text = ""
    audit = audit_module()
    return {
        "audit_commands": len(audit.audited_declarations(audit.strip_lean_noncode(audit_text))),
        "kernel_axiom_reports": len(audit.AXIOM_REPORT_RE.findall(axioms_text)),
        "required_article_items": len(audit.REQUIRED_ARTICLE_ITEMS),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lake", default="lake", help="lake executable or path")
    parser.add_argument(
        "--output-dir", default=".check-output/formal", help="artifact directory"
    )
    args = parser.parse_args()
    output_dir = (ROOT / args.output_dir).resolve()
    try:
        output_dir.mkdir(parents=True, exist_ok=True)
    except OSError as exc:
        print(f"cannot create output directory {output_dir}: {exc}", file=sys.stderr)
        return 1

    before, before_missing, before_errors = snapshot()
    input_ok, toolchain, errors = check_inputs()
    env = os.environ.copy()
    lake, lake_path = resolve_lake(args.lake, env)
    if lake_path is not None:
        env["PATH"] = str(lake_path.parent) + os.pathsep + env.get("PATH", "")
    toolchain["lake"] = lake

    commands: list[dict[str, Any]] = []
    exit_codes: dict[str, int] = {}

    def execute(name: str, command: list[str], cwd: Path, log: Path | None = None) -> str:
        code, output = run_command(command, cwd, env)
        commands.append({
            "name": name,
            "command": command,
            "cwd": cwd.relative_to(ROOT).as_posix(),
            "exit_code": code,
        })
        exit_codes[name] = code
        if log is not None:
            log.write_text(output, encoding="utf-8")
        return output

    version_output = execute(
        "lean_version",
        [lake, "env", "lean", "--version"],
        FORMAL,
    )
    version_ok = (
        exit_codes["lean_version"] == 0
        and re.search(r"Lean \(version " + re.escape(EXPECTED_LEAN_VERSION) + r"(?:,|\))", version_output) is not None
    )
    toolchain["actual_lean_version"] = version_output.strip()
    toolchain["lean_version_matches"] = version_ok
    if not version_ok:
        errors.append("actual Lean version is not 4.33.1")

    execute(
        "lake_build",
        [lake, "build"],
        FORMAL,
        output_dir / "full-optimum-build.log",
    )
    axioms_log = output_dir / "full-optimum-axioms.log"
    execute(
        "audit_axioms",
        [lake, "env", "lean", "Audit.lean"],
        FORMAL,
        axioms_log,
    )
    execute(
        "formal_audit",
        [
            sys.executable,
            ".github/scripts/audit_formal.py",
            "--formal-root",
            "formal",
            "--audit-file",
            "formal/Audit.lean",
            "--axiom-output",
            str(axioms_log),
        ],
        ROOT,
        output_dir / "full-optimum-audit.log",
    )

    after, after_missing, after_errors = snapshot()
    source_unchanged = (
        not before_missing
        and not after_missing
        and not before_errors
        and not after_errors
        and before == after
    )
    if not source_unchanged:
        errors.append("formal source snapshot changed or is incomplete")
    errors.extend(before_errors + after_errors)
    errors.extend(f"missing source before commands: {path}" for path in before_missing)
    errors.extend(f"missing source after commands: {path}" for path in after_missing)

    input_ok = input_ok and version_ok
    exit_codes["preflight"] = 0 if input_ok else 1
    status = "PASS" if input_ok and source_unchanged and all(
        code == 0 for name, code in exit_codes.items() if name != "preflight"
    ) else "FAIL"
    result: dict[str, Any] = {
        "status": status,
        "full_optimality_proof_complete": status == "PASS",
        "article_formalization_complete": status == "PASS",
        "created_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_sha256": after,
        "source_sha256_before": before,
        "source_sha256_after": after,
        "source_unchanged": source_unchanged,
        "commands": commands,
        "exitCodes": exit_codes,
        "toolchain": toolchain,
        "reportCounts": report_counts(output_dir),
    }
    if errors:
        result["errors"] = errors
    (output_dir / "FULL-OPTIMUM-CHECK.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (output_dir / "ARTICLE-FORMAL-CHECK.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(f"FULL-OPTIMUM-CHECK: {status}")
    if errors:
        print("\n".join(errors), file=sys.stderr)
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
