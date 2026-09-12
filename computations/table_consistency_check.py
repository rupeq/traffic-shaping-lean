#!/usr/bin/env python3
"""Portable exact consistency check for the saved certificate tables.

This checker reads the 79 legacy records and 16 r4 records already present in
``computations/``.  It does not call the optimizer or regenerate an LP.  A
fresh augmenting-path matcher checks the rational primal row inequalities and
dual column inequalities for every saved certificate.  The checker then
derives the two published numeric tables from those exact values and records
content hashes for the code and all saved inputs.
"""

from __future__ import annotations

import argparse
import csv
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
import hashlib
import json
from math import comb
import os
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parent
# Keep the default portable inside the checkout.  The release output used by
# the article gate is selected explicitly with --output-dir below.
DEFAULT_OUTPUT = ROOT.parent / ".check-output/table-consistency"


def ensure(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def reject_optimized_mode() -> None:
    if not __debug__ or sys.flags.optimize or os.environ.get("PYTHONOPTIMIZE"):
        raise SystemExit(
            "table_consistency_check.py refuses optimized mode; run without -O"
        )


def binom(n: int, k: int) -> int:
    return comb(n, k) if 0 <= k <= n else 0


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def parse_fraction(value: str | int | float) -> Fraction:
    return Fraction(str(value))


def positions(trace: str) -> tuple[int, ...]:
    ensure(trace and set(trace) <= {"0", "1"}, f"invalid binary trace: {trace!r}")
    return tuple(index for index, bit in enumerate(trace) if bit == "1")


@lru_cache(maxsize=600_000)
def feasible(x: str, y: str, delay: int) -> bool:
    """Fresh interval matching for one arrival/schedule pair."""
    arrivals = positions(x)
    sends = set(positions(y))
    if len(arrivals) > len(sends):
        return False
    occupied: dict[int, int] = {}

    def augment(arrival: int, visited: set[int]) -> bool:
        horizon = len(y)
        latest = min(arrival + delay, horizon - 1)
        for service in range(arrival, latest + 1):
            if service not in sends or service in visited:
                continue
            visited.add(service)
            if service not in occupied or augment(occupied[service], visited):
                occupied[service] = arrival
                return True
        return False

    return all(augment(arrival, set()) for arrival in arrivals)


@lru_cache(maxsize=None)
def traces(horizon: int, weight: int) -> tuple[str, ...]:
    return tuple(
        "".join("1" if slot in subset else "0" for slot in range(horizon))
        for subset in combinations(range(horizon), weight)
    )


@lru_cache(maxsize=None)
def schedules(horizon: int, max_arrivals: int, budget: int, causal: bool) -> tuple[str, ...]:
    if not causal:
        return traces(horizon, budget)
    terminal = set(range(horizon - max_arrivals, horizon))
    return tuple(
        "".join(
            "1" if slot in terminal or slot in prefix else "0"
            for slot in range(horizon)
        )
        for prefix in combinations(range(horizon - max_arrivals), budget - max_arrivals)
    )


def dimensions(horizon: int, max_arrivals: int, budget: int, causal: bool) -> tuple[int, int]:
    rows = binom(horizon, max_arrivals)
    columns = (
        binom(horizon - max_arrivals, budget - max_arrivals)
        if causal
        else binom(horizon, budget)
    )
    return rows, columns


def check_certificate(record: dict, source: str) -> dict:
    horizon = record["horizon"]
    delay = record["delay"]
    max_arrivals = record["max_arrivals"]
    budget = record["total_cap"]
    causal = bool(record["causal"])
    certificate = record["certificate"]
    ensure(record["status"] == 0, f"{source}: nonzero status in certificate")
    ensure(certificate["verified"] is True, f"{source}: certificate not marked verified")

    q = {trace: parse_fraction(value) for trace, value in certificate["schedule_weights"].items()}
    w = {trace: parse_fraction(value) for trace, value in certificate["input_weights"].items()}
    ensure(q == {trace: parse_fraction(value) for trace, value in record["policy"].items()}, f"{source}: policy mismatch")
    ensure(sum(q.values(), Fraction(0)) == 1, f"{source}: primal weights not normalized")
    ensure(sum(w.values(), Fraction(0)) == 1, f"{source}: dual weights not normalized")
    ensure(all(weight >= 0 for weight in q.values()), f"{source}: negative primal weight")
    ensure(all(weight >= 0 for weight in w.values()), f"{source}: negative dual weight")
    ensure(all(len(trace) == horizon and trace.count("1") == budget for trace in q), f"{source}: bad primal schedule")
    ensure(all(len(trace) == horizon and trace.count("1") == max_arrivals for trace in w), f"{source}: bad dual input")
    if causal:
        ensure(all(trace.endswith("1" * max_arrivals) for trace in q), f"{source}: missing causal reserve")

    value = parse_fraction(certificate["coverage"])
    delta = parse_fraction(certificate["delta"])
    ensure(value >= 0 and value <= 1, f"{source}: coverage outside [0,1]")
    ensure(delta == 1 - value, f"{source}: delta/coverage mismatch")

    input_rows = traces(horizon, max_arrivals)
    schedule_columns = schedules(horizon, max_arrivals, budget, causal)
    expected_rows, expected_columns = dimensions(horizon, max_arrivals, budget, causal)
    ensure(len(input_rows) == expected_rows, f"{source}: row dimension mismatch")
    ensure(len(schedule_columns) == expected_columns, f"{source}: column dimension mismatch")
    ensure(record["inputs"] == expected_rows, f"{source}: saved input count mismatch")
    ensure(record["schedules"] == expected_columns, f"{source}: saved schedule count mismatch")
    ensure(record["variables"] == expected_columns + 1, f"{source}: saved variable count mismatch")

    primal_min = Fraction(1)
    for arrival in input_rows:
        covered_mass = sum(
            (weight for schedule, weight in q.items() if feasible(arrival, schedule, delay)),
            Fraction(0),
        )
        ensure(covered_mass >= value, f"{source}: primal row inequality failed for {arrival}")
        primal_min = min(primal_min, covered_mass)

    dual_max = Fraction(0)
    for schedule in schedule_columns:
        covered_mass = sum(
            (weight for arrival, weight in w.items() if feasible(arrival, schedule, delay)),
            Fraction(0),
        )
        ensure(covered_mass <= value, f"{source}: dual column inequality failed for {schedule}")
        dual_max = max(dual_max, covered_mass)

    ensure(primal_min == value, f"{source}: primal certificate does not attain claimed value")
    ensure(dual_max == value, f"{source}: dual certificate does not attain claimed value")
    return {
        "H": horizon,
        "D": delay,
        "m": max_arrivals,
        "B": budget,
        "causal": causal,
        "rows": expected_rows,
        "columns": expected_columns,
        "coverage": str(value),
        "delta": str(delta),
        "primal_support": len(q),
        "dual_support": len(w),
    }


def load_certificates() -> tuple[list[dict], list[dict]]:
    legacy = json.loads((ROOT / "FRONTIERS.json").read_text())["records"]
    extra = json.loads((ROOT / "EXTRA-CERTIFICATES.json").read_text())["records"]
    ensure(len(legacy) == 79, "expected 79 legacy certificates")
    ensure(len(extra) == 16, "expected 16 extra certificates")
    return legacy, extra


def check_saved_certificates() -> tuple[dict, list[dict], list[dict], list[dict]]:
    legacy, extra = load_certificates()
    summaries = [
        check_certificate(record, f"legacy[{index}]")
        for index, record in enumerate(legacy)
    ] + [
        check_certificate(record, f"extra[{index}]")
        for index, record in enumerate(extra)
    ]
    ensure(len(summaries) == 95, "saved certificate total changed")
    legacy_rows = sum(item["rows"] for item in summaries[: len(legacy)])
    legacy_columns = sum(item["columns"] for item in summaries[: len(legacy)])
    extra_rows = sum(item["rows"] for item in summaries[len(legacy) :])
    extra_columns = sum(item["columns"] for item in summaries[len(legacy) :])
    rows = legacy_rows + extra_rows
    columns = legacy_columns + extra_columns
    ensure((rows, columns) == (10356, 39931), "aggregate 95-certificate dimensions changed")
    ensure((extra_rows, extra_columns) == (4736, 4024), "aggregate 16-extra dimensions changed")
    return {
        "status": "PASS",
        "legacy_certificates": len(legacy),
        "extra_certificates": len(extra),
        "certificates": len(summaries),
        "legacy_primal_rows": legacy_rows,
        "legacy_dual_columns": legacy_columns,
        "extra_primal_rows": extra_rows,
        "extra_dual_columns": extra_columns,
        "primal_rows": rows,
        "dual_columns": columns,
        "row_and_column_inequalities": "all exact Fraction checks passed with fresh augmenting matcher",
    }, summaries, legacy, extra


TABLE_TWO_EXPECTED = {
        (8, 1): (6, "1/2", 6, 5),
        (8, 2): (4, "1", 4, 4),
        (8, 3): (4, "1", 4, 4),
        (12, 1): (8, "1/3", 8, 7),
        (12, 2): (6, "1/2", 6, 5),
        (12, 3): (6, "1/2", 6, 5),
        (16, 1): (11, "2/9", 11, 8),
        (16, 2): (8, "1/3", 8, 7),
        (16, 3): (7, "2/5", 7, 6),
}


def validate_table_two_rows(rows: list[dict], legacy: list[dict]) -> dict:
    expected = TABLE_TWO_EXPECTED
    ensure(len(rows) == 9 and len(expected) == 9, "Table 2 row count changed")
    families: dict[tuple[int, int], list[dict]] = {}
    for record in legacy:
        if record["causal"] and record["max_arrivals"] == 2:
            families.setdefault((record["horizon"], record["delay"]), []).append(record)
    checked = 0
    seen_keys: list[tuple[int, int]] = []
    k_values: dict[tuple[int, int], int] = {}
    for row in rows:
        key = (int(row["H"]), int(row["D"]))
        ensure(key in expected, f"unexpected Table 2 row {key}")
        ensure(key not in seen_keys, f"duplicate Table 2 row {key}")
        seen_keys.append(key)
        b0, least_delta, budget_01, budget_05 = expected[key]
        length = 2 + key[1]
        quotient, remainder = divmod(key[0], length)
        derived_b0 = 2 * quotient + min(2, remainder)
        derived_k = (key[0] + length - 1) // length
        ensure(derived_b0 == b0, f"Table 2 expected B0 is inconsistent for {key}")
        ensure(int(row["B0"]) == derived_b0, f"Table 2 B0 mismatch for {key}")
        ensure(derived_k <= 6, f"Table 2 K bound failed for {key}")
        ensure(Fraction(1, 10) < Fraction(1, derived_k), f"Table 2 threshold comparison failed for {key}")
        k_values[key] = derived_k
        ensure(row["least_positive_delta"] == least_delta, f"Table 2 least delta mismatch for {key}")
        ensure(int(row["B_on_01"]) == budget_01, f"Table 2 0.1 budget mismatch for {key}")
        ensure(int(row["B_on_05"]) == budget_05, f"Table 2 0.5 budget mismatch for {key}")
        records = families.get(key, [])
        ensure(
            sorted(record["total_cap"] for record in records) == list(range(2, b0 + 1)),
            f"Table 2 saved family is incomplete for {key}",
        )
        values = {record["total_cap"]: parse_fraction(record["certificate"]["delta"]) for record in records}
        ensure(min(values[b] for b in values if b < b0) == Fraction(least_delta), f"saved least delta mismatch for {key}")
        ensure(min(b for b, delta in values.items() if delta <= Fraction(1, 10)) == budget_01, f"saved 0.1 threshold mismatch for {key}")
        ensure(min(b for b, delta in values.items() if delta <= Fraction(1, 2)) == budget_05, f"saved 0.5 threshold mismatch for {key}")
        checked += 1
    ensure(set(seen_keys) == set(expected), "Table 2 key set is incomplete or has an unexpected key")
    ensure(set(families) >= set(expected), "Table 2 has an unrepresented saved family")
    return {
        "status": "PASS",
        "rows": len(rows),
        "derived_rows_checked": checked,
        "keys_checked": len(seen_keys),
        "K_values": {f"{h},{d}": k for (h, d), k in sorted(k_values.items())},
        "source": "TABLE-1.csv plus exact causal FRONTIERS certificates",
    }


def check_table_two(legacy: list[dict]) -> dict:
    with (ROOT / "TABLE-1.csv").open(newline="") as stream:
        rows = list(csv.DictReader(stream))
    return validate_table_two_rows(rows, legacy)


TABLE_THREE_EXPECTED = {
        (8, 1, 3, 5): (6, "1/2", "1"),
        (8, 2, 3, 4): (6, "1/2", "1"),
        (10, 1, 4, 7): (8, "1/2", "1"),
        (10, 2, 4, 7): (8, "1/2", "1"),
        (10, 1, 3, 7): (8, "1/3", "1/2"),
        (12, 2, 3, 7): (8, "1/3", "1/2"),
        (12, 1, 4, 9): (10, "2/5", "2/3"),
        (14, 2, 4, 9): (10, "2/5", "2/3"),
}


def validate_table_three_rows(rows: list[dict], extra: list[dict]) -> dict:
    expected = TABLE_THREE_EXPECTED
    ensure(len(rows) == 8, "Table 3 row count changed")
    groups: dict[tuple[int, int, int, int], dict[bool, dict]] = {}
    for record in extra:
        key = (
            record["horizon"],
            record["delay"],
            record["max_arrivals"],
            record["total_cap"],
        )
        groups.setdefault(key, {})[bool(record["causal"])] = record
    checked = 0
    seen_keys: list[tuple[int, int, int, int]] = []
    for row in rows:
        key = (int(row["H"]), int(row["D"]), int(row["m"]), int(row["B"]))
        ensure(key in expected, f"unexpected Table 3 row {key}")
        ensure(key not in seen_keys, f"duplicate Table 3 row {key}")
        seen_keys.append(key)
        b0, delta_off, delta_on = expected[key]
        length = key[1] + key[2]
        quotient, remainder = divmod(key[0], length)
        ensure(quotient * key[2] + min(key[2], remainder) == b0, f"Table 3 B0 mismatch for {key}")
        ensure(row["delta_off"] == delta_off, f"Table 3 offline delta mismatch for {key}")
        ensure(row["delta_on"] == delta_on, f"Table 3 causal delta mismatch for {key}")
        records = groups.get(key, {})
        ensure(set(records) == {False, True}, f"Table 3 classes missing for {key}")
        for causal, expected_delta in ((False, delta_off), (True, delta_on)):
            record = records[causal]
            certificate = record["certificate"]
            ensure(certificate["delta"] == expected_delta, f"Table 3 certificate delta mismatch for {key}, causal={causal}")
            ensure(certificate["coverage"] == str(1 - Fraction(expected_delta)), f"Table 3 certificate coverage mismatch for {key}, causal={causal}")
        checked += 1
    ensure(set(seen_keys) == set(expected), "Table 3 key set is incomplete or has an unexpected key")
    ensure(set(groups) == set(expected), "extra certificate tuples and Table 3 rows differ")
    return {
        "status": "PASS",
        "rows": len(rows),
        "derived_rows_checked": checked,
        "source": "TABLE-3.csv plus exact EXTRA-CERTIFICATES certificates",
        "certificate_count": len(extra),
        "primal_rows": sum(record["inputs"] for record in extra),
        "dual_columns": sum(record["schedules"] for record in extra),
    }


def check_table_three(extra: list[dict]) -> dict:
    with (ROOT / "TABLE-3.csv").open(newline="") as stream:
        rows = list(csv.DictReader(stream))
    return validate_table_three_rows(rows, extra)


def check_qualitative_frontier(legacy: list[dict]) -> dict:
    matches = {
        bool(record["causal"]): record
        for record in legacy
        if (
            record["horizon"],
            record["delay"],
            record["max_arrivals"],
            record["total_cap"],
        )
        == (8, 2, 2, 3)
    }
    ensure(set(matches) == {False, True}, "qualitative H=8,D=2,m=2,B=3 records missing")
    ensure(matches[False]["certificate"]["coverage"] == "1/2", "offline qualitative value changed")
    ensure(matches[False]["certificate"]["delta"] == "1/2", "offline qualitative delta changed")
    ensure(matches[True]["certificate"]["coverage"] == "0", "causal qualitative value changed")
    ensure(matches[True]["certificate"]["delta"] == "1", "causal qualitative delta changed")
    return {
        "status": "PASS",
        "H": 8,
        "D": 2,
        "m": 2,
        "B": 3,
        "offline": {"coverage": "1/2", "delta": "1/2"},
        "causal": {"coverage": "0", "delta": "1"},
    }


def check_quantitative_metadata() -> dict:
    path = ROOT / "QUANTITATIVE-CHECK.json"
    data = json.loads(path.read_text())
    ensure(data["status"] == "pass", "saved quantitative metadata is not pass")
    ensure(data["saved_frontier_records"] == 79, "saved quantitative frontier count changed")
    ensure(data["budget_price_check_count"] == 43, "saved 43 budget comparisons changed")
    ensure(data["privacy_bound_check_count"] == 66, "saved 66 privacy comparisons changed")
    current_frontiers = sha256(ROOT / "FRONTIERS.json")
    current_covering = sha256(ROOT / "covering.py")
    ensure(data["source_sha256"]["FRONTIERS.json"] == current_frontiers, "QUANTITATIVE source hash for FRONTIERS is stale")
    ensure(data["source_sha256"]["covering.py"] == current_covering, "QUANTITATIVE source hash for covering.py is stale")
    return {
        "status": "PASS",
        "budget_price_comparisons": data["budget_price_check_count"],
        "privacy_bound_comparisons": data["privacy_bound_check_count"],
        "saved_frontier_records": data["saved_frontier_records"],
        "source_hashes_match": True,
    }


def input_hashes() -> dict[str, str]:
    names = (
        "FRONTIERS.json",
        "EXTRA-CERTIFICATES.json",
        "TABLE-1.csv",
        "TABLE-3.csv",
        "QUANTITATIVE-CHECK.json",
        "covering.py",
        "independent_certificate_check.py",
        "verify_extra.py",
    )
    return {name: sha256(ROOT / name) for name in names}


def main() -> None:
    reject_optimized_mode()
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    output_dir = args.output_dir.expanduser().resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    certificate_result, summaries, legacy, extra = check_saved_certificates()
    report = {
        "status": "PASS",
        "checker": "table_consistency_check.py",
        "source_directory": str(ROOT),
        "output_directory": str(output_dir),
        "optimizer_imported": False,
        "lp_regenerated": False,
        "matching": "fresh augmenting-path matcher over exact interval edges",
        "arithmetic": "fractions.Fraction",
        "saved_certificates": certificate_result,
        "table_2": check_table_two(legacy),
        "table_3": check_table_three(extra),
        "qualitative_frontier": check_qualitative_frontier(legacy),
        "quantitative_metadata": check_quantitative_metadata(),
        "code_sha256": sha256(Path(__file__).resolve()),
        "saved_input_sha256": input_hashes(),
        "limitations": (
            "This check validates the saved rational witnesses, table mappings, and metadata. "
            "It does not regenerate LPs or replace the universal Lean proofs."
        ),
    }
    destination = output_dir / "TABLE-CONSISTENCY-CHECK.json"
    destination.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "status": report["status"],
        "output": str(destination),
        "code_sha256": report["code_sha256"],
        "saved_certificates": report["saved_certificates"],
        "table_2": report["table_2"],
        "table_3": report["table_3"],
        "qualitative_frontier": report["qualitative_frontier"],
        "quantitative_metadata": report["quantitative_metadata"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
