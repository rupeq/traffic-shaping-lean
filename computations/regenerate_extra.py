"""Regenerate the selected positive-delay certificate set for r4.

The first eight reports are the previously checked records and are preserved
from ``EXTRA-CERTIFICATES.json`` when that file is present.  The eight added
reports are solved afresh for the four new tuples below, two mechanism classes
per tuple.  Every report is checked immediately with the neighboring
standard-library independent checker.  No earlier 79-record frontier is run.
"""
from __future__ import annotations

import csv
import json
from pathlib import Path

from covering import solve
from independent_certificate_check import check


ROOT = Path(__file__).resolve().parent
ORIGINAL_CASES = (
    (8, 1, 3, 5),
    (8, 2, 3, 4),
    (10, 1, 4, 7),
    (10, 2, 4, 7),
)
ADDED_CASES = (
    (10, 1, 3, 7),
    (12, 2, 3, 7),
    (12, 1, 4, 9),
    (14, 2, 4, 9),
)


def rows_and_columns(horizon: int, max_arrivals: int, total_cap: int,
                     causal: bool) -> tuple[int, int]:
    """Return all independent-check matrix rows and columns for one class."""
    from math import comb

    rows = comb(horizon, max_arrivals)
    columns = (comb(horizon - max_arrivals, total_cap - max_arrivals)
               if causal else comb(horizon, total_cap))
    return rows, columns


def expected_keys(cases: tuple[tuple[int, int, int, int], ...]):
    return [(h, d, m, b, causal)
            for h, d, m, b in cases
            for causal in (False, True)]


def preserve_original_records() -> list[dict] | None:
    """Load and recheck the original eight without recomputing their LPs."""
    path = ROOT / "EXTRA-CERTIFICATES.json"
    if not path.exists():
        return None
    payload = json.loads(path.read_text())
    records = payload.get("records", [])
    if len(records) < 8:
        return None
    old = records[:8]
    actual = [(r["horizon"], r["delay"], r["max_arrivals"],
               r["total_cap"], r["causal"]) for r in old]
    if actual != expected_keys(ORIGINAL_CASES):
        return None
    for report in old:
        check(report)
    return old


def summary(report: dict, selection: str) -> dict:
    check_result = check(report)
    rows, columns = rows_and_columns(
        report["horizon"], report["max_arrivals"],
        report["total_cap"], report["causal"])
    assert check_result["delta"] == report["certificate"]["delta"]
    assert report["inputs"] == rows
    assert report["schedules"] == columns
    return dict(
        selection=selection,
        H=report["horizon"], D=report["delay"],
        m=report["max_arrivals"], B=report["total_cap"],
        causal=report["causal"], delta=check_result["delta"],
        coverage=report["certificate"]["coverage"],
        primal_rows=rows, dual_columns=columns,
        schedule_support=len(report["certificate"]["schedule_weights"]),
        input_support=len(report["certificate"]["input_weights"]),
    )


def main() -> None:
    original = preserve_original_records()
    if original is None:
        original = []
        for case in ORIGINAL_CASES:
            for causal in (False, True):
                original.append(solve(*case, causal=causal, certify=True))
        print("Original eight records were generated because no stored set was found.")
    else:
        print("Preserved and independently rechecked the stored original eight records.")

    added = []
    for case in ADDED_CASES:
        for causal in (False, True):
            report = solve(*case, causal=causal, certify=True)
            added.append(report)
            item = summary(report, "added")
            print(
                f"{len(added)}/8 added: H={item['H']}, D={item['D']}, "
                f"m={item['m']}, B={item['B']}, "
                f"class={'causal' if causal else 'offline'}, "
                f"rows={item['primal_rows']}, columns={item['dual_columns']}, "
                f"delta={item['delta']}",
                flush=True,
            )

    records = original + added
    checked = ([summary(report, "original") for report in original]
               + [summary(report, "added") for report in added])
    assert len(records) == len(checked) == 16

    lookup = {(item["selection"], item["H"], item["D"], item["m"],
               item["B"], item["causal"]): item for item in checked}
    table_fields = (
        "selection", "H", "D", "m", "B", "delta_off", "delta_on",
        "coverage_off", "coverage_on", "primal_rows", "offline_columns",
        "causal_columns", "offline_schedule_support",
        "causal_schedule_support", "offline_input_support",
        "causal_input_support",
    )
    table_rows = []
    for selection, cases in (("original", ORIGINAL_CASES),
                             ("added", ADDED_CASES)):
        for h, d, m, b in cases:
            offline = lookup[(selection, h, d, m, b, False)]
            causal = lookup[(selection, h, d, m, b, True)]
            table_rows.append(dict(
                selection=selection, H=h, D=d, m=m, B=b,
                delta_off=offline["delta"], delta_on=causal["delta"],
                coverage_off=offline["coverage"],
                coverage_on=causal["coverage"],
                primal_rows=offline["primal_rows"],
                offline_columns=offline["dual_columns"],
                causal_columns=causal["dual_columns"],
                offline_schedule_support=offline["schedule_support"],
                causal_schedule_support=causal["schedule_support"],
                offline_input_support=offline["input_support"],
                causal_input_support=causal["input_support"],
            ))
    with (ROOT / "TABLE-3.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=table_fields)
        writer.writeheader()
        writer.writerows(table_rows)

    original_checked = checked[:8]
    added_checked = checked[8:]
    payload = dict(
        description=(
            "Sixteen exact positive-delay primal/dual certificates: the "
            "original eight records are retained, and eight added records "
            "cover four further finite games in both classes. These are "
            "finite examples for checking the manuscript claims, not "
            "scalability benchmarks."
        ),
        generator="regenerate_extra.py",
        optimizer="neighboring covering.py:solve",
        independent_checker="neighboring independent_certificate_check.py:check",
        scope=(
            "original four tuples retained; added four tuples solved fresh; "
            "both causal and offline classes; no earlier frontier records"
        ),
        original_cases=[dict(H=h, D=d, m=m, B=b)
                        for h, d, m, b in ORIGINAL_CASES],
        added_cases=[dict(H=h, D=d, m=m, B=b)
                     for h, d, m, b in ADDED_CASES],
        records=records,
        checked=checked,
        original_checked=original_checked,
        added_checked=added_checked,
        original_certificates=len(original),
        added_certificates=len(added),
        certificates=len(records),
        original_primal_rows_checked=sum(i["primal_rows"] for i in original_checked),
        added_primal_rows_checked=sum(i["primal_rows"] for i in added_checked),
        original_dual_columns_checked=sum(i["dual_columns"] for i in original_checked),
        added_dual_columns_checked=sum(i["dual_columns"] for i in added_checked),
        primal_rows_checked=sum(i["primal_rows"] for i in checked),
        dual_columns_checked=sum(i["dual_columns"] for i in checked),
        table_rows=table_rows,
        all_passed=True,
    )
    (ROOT / "EXTRA-CERTIFICATES.json").write_text(
        json.dumps(payload, indent=2) + "\n"
    )
    print(
        f"Wrote EXTRA-CERTIFICATES.json: {len(original)} original + "
        f"{len(added)} added certificates; "
        f"{payload['primal_rows_checked']} primal rows, "
        f"{payload['dual_columns_checked']} dual columns.",
        flush=True,
    )


if __name__ == "__main__":
    main()
