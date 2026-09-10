#!/usr/bin/env python3
"""Run the reproducibility checks in an isolated copy of this package.

The source directory is treated as immutable input.  Legacy checkers write
their reports into a temporary copy, and this driver copies only the fresh
reports and logs to the requested output directory.  With ``--full-regenerate``
it also solves and independently checks all 95 saved positive-delay games
from scratch, comparing exact coverage and delta values while ignoring solver
support choices and elapsed times.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from math import comb
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time


ROOT = Path(__file__).resolve().parent
IGNORED_DIRECTORY_NAMES = {".venv", "__pycache__"}
IGNORED_FILE_SUFFIXES = {".pyc"}

EXPECTED_FALLBACK = {
    "parameter_cases": 546,
    "input_schedule_pairs": 45622,
    "switches": 4069,
    "prefix_consistency_comparisons": 347870,
    "exact_tv_checks": 20532,
}
EXPECTED_NO_SAVINGS = {
    "parameter_sets": 375,
    "output_traces_across_instances": 83966,
    "input_checks_at_reserve": 52158,
    "structural_feasible_trace_checks": 55114,
    "Y_B_intersection_checks_for_B_lt_B0": 1755,
    "B_lt_m_impossibility_checks": 1485,
}


FULL_REGENERATION = r'''\
import json
from fractions import Fraction
from pathlib import Path
import time

from covering import solve
from independent_certificate_check import check

root = Path(__file__).resolve().parent
old = json.loads((root / "FRONTIERS.json").read_text())["records"]
extra = json.loads((root / "EXTRA-CERTIFICATES.json").read_text())
expected = old + extra["records"]
assert len(old) == 79 and len(extra["records"]) == 16

started = time.perf_counter()
fresh = []
for index, saved in enumerate(expected, 1):
    report = solve(
        saved["horizon"], saved["delay"], saved["max_arrivals"],
        saved["total_cap"], causal=saved["causal"], certify=True,
    )
    independent = check(report)
    assert Fraction(report["certificate"]["coverage"]) == Fraction(
        saved["certificate"]["coverage"]
    )
    assert Fraction(report["certificate"]["delta"]) == Fraction(
        saved["certificate"]["delta"]
    )
    assert independent["delta"] == saved["certificate"]["delta"]
    fresh.append({
        "source": "legacy79" if index <= 79 else "r4-extra16",
        "H": saved["horizon"], "D": saved["delay"],
        "m": saved["max_arrivals"], "B": saved["total_cap"],
        "causal": saved["causal"],
        "coverage": report["certificate"]["coverage"],
        "delta": report["certificate"]["delta"],
    })
    print(f"{index}/95: {fresh[-1]}", flush=True)

result = {
    "status": "PASS",
    "certificates": len(fresh),
    "legacy_certificates": sum(x["source"] == "legacy79" for x in fresh),
    "r4_extra_certificates": sum(x["source"] == "r4-extra16" for x in fresh),
    "exact_values_match": True,
    "support_comparison": "not required; solver may choose another optimum",
    "seconds": time.perf_counter() - started,
    "records": fresh,
}
(root / "FULL-REGENERATION.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({k: v for k, v in result.items() if k != "records"}))
'''


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def immutable_input_paths(root: Path) -> list[Path]:
    """Return every ordinary source file copied into the clean work tree."""
    paths = []
    for directory, names, filenames in os.walk(root):
        names[:] = sorted(
            name for name in names if name not in IGNORED_DIRECTORY_NAMES
        )
        for filename in sorted(filenames):
            path = Path(directory) / filename
            if (
                path.is_file()
                and not path.is_symlink()
                and path.suffix not in IGNORED_FILE_SUFFIXES
            ):
                paths.append(path)
    return sorted(paths, key=lambda path: path.relative_to(root).as_posix())


def immutable_input_snapshot(root: Path) -> dict[str, str]:
    return {
        path.relative_to(root).as_posix(): sha256(path)
        for path in immutable_input_paths(root)
    }


def reject_optimized_mode() -> None:
    """Refuse runs that could silently disable verification assertions."""
    if not __debug__ or sys.flags.optimize or os.environ.get("PYTHONOPTIMIZE"):
        raise SystemExit(
            "run_checks.py refuses optimized mode; unset PYTHONOPTIMIZE "
            "and run Python without -O"
        )


def output_text(value: str | bytes | None) -> str:
    """Normalize subprocess output before writing text logs."""
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode(errors="replace")
    return value


def run_command(label: str, executable: str, args: list[str], cwd: Path,
                outputdir: Path, *, site: bool, timeout: int = 900) -> dict:
    command = [executable]
    if not site:
        command.append("-S")
    command.extend(args)
    started = time.perf_counter()
    try:
        process = subprocess.run(
            command, cwd=cwd, text=True, capture_output=True,
            timeout=timeout, check=False,
        )
    except subprocess.TimeoutExpired as exc:
        stdout = output_text(exc.stdout)
        stderr = output_text(exc.stderr)
        (outputdir / f"{label}.stdout.log").write_text(stdout)
        (outputdir / f"{label}.stderr.log").write_text(stderr)
        raise RuntimeError(f"{label} exceeded {timeout} seconds") from exc
    (outputdir / f"{label}.stdout.log").write_text(output_text(process.stdout))
    (outputdir / f"{label}.stderr.log").write_text(output_text(process.stderr))
    if process.returncode:
        raise RuntimeError(
            f"{label} failed with exit code {process.returncode}; "
            f"see {label}.stderr.log"
        )
    return dict(
        command=command,
        seconds=time.perf_counter() - started,
        stdout=process.stdout,
        stderr=process.stderr,
    )


def copy_report(work: Path, outputdir: Path, name: str) -> dict:
    source = work / name
    if not source.exists():
        raise RuntimeError(f"Expected fresh report was not written: {name}")
    destination = outputdir / name
    shutil.copy2(source, destination)
    return json.loads(source.read_text())


def expected_positive_counts(work: Path) -> dict:
    old = json.loads((work / "FRONTIERS.json").read_text())["records"]
    extra = json.loads((work / "EXTRA-CERTIFICATES.json").read_text())
    records = old + extra["records"]
    assert len(old) == 79
    assert len(extra["records"]) == 16
    rows = columns = 0
    for report in records:
        h = report["horizon"]
        m = report["max_arrivals"]
        b = report["total_cap"]
        rows += comb(h, m)
        columns += comb(h - m, b - m) if report["causal"] else comb(h, b)
    return dict(
        legacy_certificates=len(old),
        r4_extra_certificates=len(extra["records"]),
        certificates=len(records),
        primal_rows=rows,
        dual_columns=columns,
    )


def run_standard_checks(work: Path, outputdir: Path, executable: str) -> dict:
    for name in (
        "CERTIFICATE-CHECK.json", "TABLE-1.csv", "FALLBACK-CHECK.json",
        "ZERO-DELAY-EXACT-CHECK.json", "EXTRA-CERTIFICATE-CHECK.json",
    ):
        (work / name).unlink(missing_ok=True)

    commands = {}
    commands["legacy_certificates"] = run_command(
        "legacy-certificates", executable,
        ["independent_certificate_check.py"], work, outputdir, site=False,
    )
    legacy_report = copy_report(work, outputdir, "CERTIFICATE-CHECK.json")
    shutil.copy2(work / "TABLE-1.csv", outputdir / "TABLE-1.csv")

    commands["extra_certificates"] = run_command(
        "extra-certificates", executable, ["verify_extra.py"], work,
        outputdir, site=False,
    )
    extra_report = copy_report(work, outputdir, "EXTRA-CERTIFICATE-CHECK.json")
    shutil.copy2(work / "TABLE-3.csv", outputdir / "TABLE-3.csv")

    commands["fallback"] = run_command(
        "fallback", executable, ["fallback_check.py"], work, outputdir,
        site=False,
    )
    fallback_report = copy_report(work, outputdir, "FALLBACK-CHECK.json")

    commands["zero-delay"] = run_command(
        "zero-delay", executable, ["zero_delay_independent_check.py"],
        work, outputdir, site=False,
    )
    zero_report = copy_report(work, outputdir, "ZERO-DELAY-EXACT-CHECK.json")

    commands["no-savings"] = run_command(
        "no-savings", executable, ["no_savings_check.py"], work, outputdir,
        site=False,
    )
    no_savings_report = json.loads(commands["no-savings"]["stdout"])
    (outputdir / "NO-SAVINGS-CHECK.json").write_text(
        json.dumps(no_savings_report, indent=2) + "\n"
    )

    assert legacy_report["certificates"] == 79
    assert legacy_report["all_passed"] is True
    assert extra_report["certificates"] == 16
    assert extra_report["original_certificates"] == 8
    assert extra_report["added_certificates"] == 8
    assert extra_report["all_passed"] is True
    assert zero_report["cases"] == 240
    assert zero_report["saved_values_all_match"] is True
    assert zero_report["primal_rows_checked"] == 4518
    assert zero_report["dual_columns_checked"] == 2295
    for key, value in EXPECTED_FALLBACK.items():
        assert fallback_report[key] == value, (key, fallback_report[key])
    assert fallback_report["passed"] is True
    assert no_savings_report["status"] == "PASS"
    assert no_savings_report["scope"]["parameter_sets"] == EXPECTED_NO_SAVINGS[
        "parameter_sets"
    ]
    for key, value in EXPECTED_NO_SAVINGS.items():
        if key == "parameter_sets":
            continue
        assert no_savings_report["aggregate_counts"][key] == value, (
            key, no_savings_report["aggregate_counts"][key]
        )
    return dict(
        commands={key: {
            "command": value["command"], "seconds": value["seconds"]
        } for key, value in commands.items()},
        legacy_certificate_report=legacy_report,
        extra_certificate_report=extra_report,
        fallback_report=fallback_report,
        zero_delay_report={k: v for k, v in zero_report.items() if k != "records"},
        no_savings_report=no_savings_report,
    )


def run_full_regeneration(work: Path, outputdir: Path, executable: str) -> dict:
    script = work / "_full_regenerate.py"
    script.write_text(FULL_REGENERATION)
    run = run_command(
        "full-regeneration", executable, [script.name], work, outputdir,
        site=True, timeout=1800,
    )
    report = copy_report(work, outputdir, "FULL-REGENERATION.json")
    assert report["status"] == "PASS"
    assert report["certificates"] == 95
    assert report["legacy_certificates"] == 79
    assert report["r4_extra_certificates"] == 16
    assert report["exact_values_match"] is True
    return dict(
        requested=True, status="PASS", seconds=run["seconds"],
        certificates=report["certificates"],
        legacy_certificates=report["legacy_certificates"],
        r4_extra_certificates=report["r4_extra_certificates"],
        exact_values_match=report["exact_values_match"],
        command=run["command"],
    )


def main() -> None:
    reject_optimized_mode()
    parser = argparse.ArgumentParser()
    parser.add_argument("--outputdir", type=Path, required=True)
    parser.add_argument(
        "--python", default=sys.executable,
        help="Python executable for the checks (default: current interpreter)",
    )
    parser.add_argument(
        "--full-regenerate", action="store_true",
        help="freshly solve and independently check all 95 positive games",
    )
    args = parser.parse_args()
    outputdir = args.outputdir.expanduser().resolve()
    if outputdir == ROOT or ROOT in outputdir.parents:
        raise SystemExit("outputdir must be outside computations/ so source stays immutable")
    outputdir.mkdir(parents=True, exist_ok=True)

    before = immutable_input_snapshot(ROOT)
    started = time.perf_counter()
    with tempfile.TemporaryDirectory(prefix="traffic-shaping-computations-") as temp:
        work = Path(temp) / "computations"
        shutil.copytree(
            ROOT, work,
            ignore=shutil.ignore_patterns("__pycache__", ".venv", "*.pyc"),
        )
        standard = run_standard_checks(work, outputdir, args.python)
        full = (run_full_regeneration(work, outputdir, args.python)
                if args.full_regenerate else {
                    "requested": False,
                    "status": "not-requested",
                    "note": "Pass --full-regenerate for fresh 95-LP reproduction",
                })

    after = immutable_input_snapshot(ROOT)
    assert before == after
    counts = expected_positive_counts(ROOT)
    assert counts == {
        "legacy_certificates": 79,
        "r4_extra_certificates": 16,
        "certificates": 95,
        "primal_rows": 10356,
        "dual_columns": 39931,
    }
    report = {
        "status": "PASS",
        "checker": "run_checks.py",
        "created_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_directory": str(ROOT),
        "output_directory": str(outputdir),
        "python_executable": str(Path(args.python).resolve()),
        "python": sys.version,
        "source_previous_pass_logs_used": False,
        "source_unchanged": before == after,
        "clean_copy": True,
        "positive_certificate_counts": counts,
        "standard_checks": standard,
        "full_regeneration": full,
        "immutable_input_sha256_before": before,
        "immutable_input_sha256_after": after,
        "elapsed_seconds": time.perf_counter() - started,
        "limitations": (
            "The certificate checks certify the saved finite witnesses and "
            "the requested finite algorithmic domains; they do not replace "
            "the manuscript proofs or establish scalability."
        ),
    }
    (outputdir / "REPRODUCIBILITY-CHECK.json").write_text(
        json.dumps(report, indent=2) + "\n"
    )
    print(json.dumps({
        "status": report["status"],
        "certificates": counts["certificates"],
        "full_regeneration": full["status"],
        "outputdir": str(outputdir),
        "elapsed_seconds": report["elapsed_seconds"],
    }, indent=2))


if __name__ == "__main__":
    main()
