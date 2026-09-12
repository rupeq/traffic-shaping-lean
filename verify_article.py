#!/usr/bin/env python3
"""Check the complete article proof and its exact finite computational evidence.

Every invocation creates a fresh run directory, so old PASS files cannot mask
a failed or missing subprocess.  The source snapshot binds the Lean proof,
coverage inventory, checker implementations, and saved rational inputs.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import uuid

import verify_formal


ROOT = Path(__file__).resolve().parent

EXPECTED_COROLLARY_COUNTS = {
    "corollary_1_budget": {
        "parameter_sets": 1707,
        "offline_to_causal_schedule_maps": 88840,
        "covered_input_pairs_preserved": 3576760,
        "Eq15_threshold_checks": 772,
        "Eq15_sharpness_checks": 32,
    },
    "corollary_2_privacy_gap": {
        "parameter_sets": 1022,
        "source_schedule_input_pairs_covered": 1471630,
        "retention_trials": 38283201,
        "favorable_retention_trials": 5965347,
        "Eq19_binomial_identity_checks": 94,
        "Eq18_union_bound_checks": 94,
    },
    "corollary_3_full_indistinguishability": {
        "parameter_sets": 428,
        "Eq20_formula_checks": 428,
        "block_schedule_universal_input_checks": 51070,
        "B0_minus_1_schedule_checks": 35921,
        "large_delay_cases": 126,
    },
    "corollary_4_zero_delay": {
        "parameter_sets": 244,
        "offline_pair_checks": 4647458,
        "causal_pair_checks": 525824,
        "Eq21_checks": 488,
        "Eq22_checks": 77,
    },
    "corollary_5_no_savings_threshold": {
        "parameter_sets": 168,
        "Eq24_block_witness_tests": 357,
        "below_B0_offline_and_causal_schedule_checks": 109497,
        "Eq25_strict_threshold_representatives": 672,
        "B_lt_m_delivery_checks": 420,
    },
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_snapshot() -> dict[str, str]:
    paths = set(verify_formal.source_paths())
    paths.add(ROOT / "verify_article.py")
    for extension in ("*.py", "*.json", "*.csv"):
        paths.update((ROOT / "computations").glob(extension))
    paths.update((ROOT / "tests").glob("*.py"))
    return {path.relative_to(ROOT).as_posix(): digest(path) for path in sorted(paths)}


def expect(data: dict, key: str, value, context: str, errors: list[str]) -> None:
    if not isinstance(data, dict):
        errors.append(f"{context}: expected a JSON object")
        return
    if data.get(key) != value:
        errors.append(f"{context}.{key}: expected {value!r}, got {data.get(key)!r}")


def validate_corollaries(report: dict, errors: list[str]) -> None:
    expect(report, "status", "PASS", "corollaries", errors)
    expect(report, "checker", "corollaries_check.py", "corollaries", errors)
    expect(report, "optimizer_imported", False, "corollaries", errors)
    expect(report, "existing_checker_imported", False, "corollaries", errors)
    expect(report, "source_unchanged", True, "corollaries", errors)
    cases = report.get("corollaries", {})
    if not isinstance(cases, dict):
        errors.append("corollaries: missing result objects")
        cases = {}
    if set(cases) != set(EXPECTED_COROLLARY_COUNTS):
        errors.append("corollary code inventory differs from the five required corollaries")
    for case, counts in EXPECTED_COROLLARY_COUNTS.items():
        data = cases.get(case, {})
        expect(data, "status", "PASS", case, errors)
        for key, value in counts.items():
            expect(data, key, value, case, errors)
    example = report.get("article_example", {})
    for key, value in {
        "status": "PASS", "input_rows_exact_m": 28, "input_rows_at_most_m": 37,
        "causal_schedule_columns": 15, "offline_schedule_columns": 70,
        "Eq23_causal_policy_value": "1/3", "Eq23_causal_dual_value": "1/3",
        "offline_example_value": "5/9", "offline_example_delta": "4/9",
        "B0_schedule_covers_all_inputs": True,
    }.items():
        expect(example, key, value, "article_example", errors)
    for section in ("privacy_interpretation", "article_sizes", "saved_table_mapping"):
        expect(report.get(section, {}), "status", "PASS", section, errors)
    execution = example.get("algorithm1_examples", {}) if isinstance(example, dict) else {}
    expect(execution, "input", "11000000", "algorithm1_examples", errors)
    for key, output, switch, count in (
        ("base_01100011", "01100011", None, 4),
        ("base_00011011", "01100000", 1, 2),
    ):
        data = execution.get(key, {}) if isinstance(execution, dict) else {}
        for field, expected in {
            "output": output, "switch": switch, "count": count,
            "services": [[0, 1], [1, 2]], "cap_respected": True,
            "all_deadlines_met": True,
        }.items():
            expect(data, field, expected, key, errors)


def validate_tables(report: dict, errors: list[str]) -> None:
    expect(report, "status", "PASS", "tables", errors)
    expect(report, "checker", "table_consistency_check.py", "tables", errors)
    expect(report, "optimizer_imported", False, "tables", errors)
    expect(report, "lp_regenerated", False, "tables", errors)
    certificates = report.get("saved_certificates", {})
    for key, value in {
        "status": "PASS", "certificates": 95, "legacy_certificates": 79,
        "extra_certificates": 16, "primal_rows": 10356, "dual_columns": 39931,
        "extra_primal_rows": 4736, "extra_dual_columns": 4024,
    }.items():
        expect(certificates, key, value, "saved_certificates", errors)
    for section, count in (("table_2", 9), ("table_3", 8)):
        data = report.get(section, {})
        expect(data, "status", "PASS", section, errors)
        expect(data, "rows", count, section, errors)
        expect(data, "derived_rows_checked", count, section, errors)
    qualitative = report.get("qualitative_frontier", {})
    expect(qualitative, "status", "PASS", "qualitative_frontier", errors)
    expect(qualitative, "offline", {"coverage": "1/2", "delta": "1/2"}, "qualitative_frontier", errors)
    expect(qualitative, "causal", {"coverage": "0", "delta": "1"}, "qualitative_frontier", errors)


def validate_code_hashes(report: dict, script: str, errors: list[str]) -> None:
    expected = digest(ROOT / "computations" / script)
    expect(report, "code_sha256", expected, script, errors)
    inputs = report.get("saved_input_sha256")
    if not isinstance(inputs, dict) or not inputs:
        errors.append(f"{script}: missing saved-input hash inventory")
        return
    for name, recorded in inputs.items():
        path = (ROOT / "computations" / name).resolve()
        if not path.is_relative_to(ROOT / "computations"):
            errors.append(f"{script}: invalid input path {name!r}")
        elif not path.is_file() or digest(path) != recorded:
            errors.append(f"{script}: saved-input hash mismatch for {name}")


def validate_lean_transcription(current: str, regenerated: str,
                                errors: list[str]) -> None:
    strip = verify_formal.audit_module().strip_lean_noncode
    if strip(current).split() != strip(regenerated).split():
        errors.append("Lean table certificate transcription differs from the saved rational inputs")


def protected_release_check(manifest_path: Path | None, root: Path | None) -> dict:
    if manifest_path is None:
        return {"status": "NOT_REQUESTED"}
    if root is None:
        raise ValueError("--protected-root is required with --protected-manifest")
    baseline = json.loads(manifest_path.read_text(encoding="utf-8"))
    expected = baseline["r9_protected_sha256"]
    if not isinstance(expected, dict) or not expected:
        raise ValueError("protected-release manifest has no hashes")
    current = {}
    for relative in expected:
        path = (root / relative).resolve()
        if not path.is_relative_to(root):
            raise ValueError(f"invalid protected-release path: {relative}")
        current[relative] = digest(path)
    return {
        "status": "PASS" if current == expected else "FAIL",
        "manifest_sha256": digest(manifest_path),
        "files": len(current),
        "sha256": current,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--output-dir", type=Path, default=ROOT / ".check-output/article")
    parser.add_argument("--protected-manifest", type=Path)
    parser.add_argument("--protected-root", type=Path)
    args = parser.parse_args()
    output = args.output_dir.expanduser().resolve()
    run_id = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ") + "-" + uuid.uuid4().hex[:8]
    run_dir = output / run_id
    run_dir.mkdir(parents=True, exist_ok=False)
    running = json.dumps({"status": "RUNNING", "run_id": run_id,
        "article_formal_and_code_verification_complete": False}, indent=2) + "\n"
    (run_dir / "ARTICLE-CHECK.json").write_text(running, encoding="utf-8")
    (output / "ARTICLE-CHECK.json").write_text(running, encoding="utf-8")
    errors: list[str] = []
    commands: list[dict] = []
    artifacts: dict[str, str] = {}
    before = source_snapshot()
    env = os.environ.copy()
    protected_root = args.protected_root.expanduser().resolve() if args.protected_root else None
    protected_before = protected_release_check(args.protected_manifest, protected_root)

    def execute(name: str, command: list[str]) -> None:
        try:
            completed = subprocess.run(command, cwd=ROOT, env=env, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, errors="replace", check=False)
            code, command_output = completed.returncode, completed.stdout
        except OSError as exc:
            code, command_output = 127, f"could not execute {command[0]}: {exc}\n"
        log = run_dir / f"{name}.log"
        log.write_text(command_output, encoding="utf-8")
        commands.append({"name": name, "command": command, "exit_code": code,
            "log": str(log), "log_sha256": digest(log)})
        if code != 0:
            errors.append(f"{name} exited with code {code}")
        print(f"{name}: {'PASS' if code == 0 else 'FAIL'}", flush=True)

    execute("proof_gate_tests", [sys.executable, "-m", "unittest", "discover", "-s", "tests", "-v"])
    generated = run_dir / "regenerated-TableCertificates.lean"
    execute("certificate_transcription", [sys.executable,
        "computations/generate_lean_certificates.py", "--output", str(generated)])
    try:
        validate_lean_transcription(
            (ROOT / "formal/TrafficShaping/TableCertificates.lean").read_text(),
            generated.read_text(), errors)
        artifacts[str(generated)] = digest(generated)
    except (OSError, ValueError) as exc:
        errors.append(f"cannot compare the regenerated Lean table certificates: {exc}")
    execute("formal", [sys.executable, "verify_formal.py", "--lake", args.lake,
        "--output-dir", str(run_dir / "formal")])
    execute("corollaries", [sys.executable, "computations/corollaries_check.py",
        "--output-dir", str(run_dir / "computations")])
    execute("tables", [sys.executable, "computations/table_consistency_check.py",
        "--output-dir", str(run_dir / "computations")])

    reports: dict[str, dict] = {}
    for key, relative in {
        "formal": "formal/ARTICLE-FORMAL-CHECK.json",
        "corollaries": "computations/COROLLARIES-CHECK.json",
        "tables": "computations/TABLE-CONSISTENCY-CHECK.json",
    }.items():
        path = run_dir / relative
        try:
            report = json.loads(path.read_text(encoding="utf-8"))
            if not isinstance(report, dict):
                raise ValueError("report is not a JSON object")
            reports[key] = report
            artifacts[str(path)] = digest(path)
            expect(report, "status", "PASS", key, errors)
        except (OSError, UnicodeError, ValueError) as exc:
            errors.append(f"cannot read fresh {key} report: {exc}")
    if "formal" in reports:
        formal = reports["formal"]
        expect(formal, "article_formalization_complete", True, "formal", errors)
        expect(formal, "source_unchanged", True, "formal", errors)
    if "corollaries" in reports:
        validate_corollaries(reports["corollaries"], errors)
        validate_code_hashes(reports["corollaries"], "corollaries_check.py", errors)
    if "tables" in reports:
        validate_tables(reports["tables"], errors)
        validate_code_hashes(reports["tables"], "table_consistency_check.py", errors)
    after = source_snapshot()
    if before != after:
        errors.append("article proof, checker, or certificate source changed during verification")
    protected_after = protected_release_check(args.protected_manifest, protected_root)
    if protected_before != protected_after or protected_after["status"] == "FAIL":
        errors.append("protected prior release differs from its baseline")
    result = {
        "status": "FAIL" if errors else "PASS",
        "article_formal_and_code_verification_complete": not errors,
        "created_at_utc": datetime.now(timezone.utc).isoformat(),
        "run_id": run_id,
        "source_sha256_before": before, "source_sha256_after": after,
        "source_unchanged": before == after,
        "commands": commands, "artifact_sha256": artifacts,
        "protected_prior_release": protected_after,
        "errors": errors,
    }
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    (run_dir / "ARTICLE-CHECK.json").write_text(text, encoding="utf-8")
    (output / "ARTICLE-CHECK.json").write_text(text, encoding="utf-8")
    print(f"ARTICLE-CHECK: {result['status']} ({run_dir})")
    for error in errors:
        print(error, file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
