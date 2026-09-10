"""Verify the stored original and added r4 certificates with stdlib only.

The matching algorithm and exact Fraction checks come from the neighboring
``independent_certificate_check.py``.  No optimizer, NumPy, or SciPy is
imported by this verifier.
"""
from __future__ import annotations

import csv
import json
from fractions import Fraction
from math import comb
from pathlib import Path

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


def dimensions(horizon: int, max_arrivals: int, total_cap: int,
               causal: bool) -> tuple[int, int]:
    rows = comb(horizon, max_arrivals)
    columns = (comb(horizon - max_arrivals, total_cap - max_arrivals)
               if causal else comb(horizon, total_cap))
    return rows, columns


def expected_keys(cases: tuple[tuple[int, int, int, int], ...],
                  selection: str):
    return [(h, d, m, b, causal, selection)
            for h, d, m, b in cases
            for causal in (False, True)]


def summarize(report: dict, selection: str) -> dict:
    result = check(report)
    rows, columns = dimensions(
        report["horizon"], report["max_arrivals"],
        report["total_cap"], report["causal"])
    assert result["delta"] == report["certificate"]["delta"]
    assert report["inputs"] == rows
    assert report["schedules"] == columns
    return dict(
        selection=selection,
        H=report["horizon"], D=report["delay"],
        m=report["max_arrivals"], B=report["total_cap"],
        causal=report["causal"], delta=result["delta"],
        coverage=report["certificate"]["coverage"],
        primal_rows=rows, dual_columns=columns,
        schedule_support=len(report["certificate"]["schedule_weights"]),
        input_support=len(report["certificate"]["input_weights"]),
    )


def make_table_rows(summaries: list[dict]) -> list[dict]:
    lookup = {(item["selection"], item["H"], item["D"], item["m"],
               item["B"], item["causal"]): item for item in summaries}
    rows = []
    for selection, cases in (("original", ORIGINAL_CASES),
                             ("added", ADDED_CASES)):
        for h, d, m, b in cases:
            offline = lookup[(selection, h, d, m, b, False)]
            causal = lookup[(selection, h, d, m, b, True)]
            rows.append(dict(
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
    return rows


def main() -> None:
    payload = json.loads((ROOT / "EXTRA-CERTIFICATES.json").read_text())
    records = payload["records"]
    assert len(records) == 16
    assert payload["certificates"] == 16
    assert payload["original_certificates"] == 8
    assert payload["added_certificates"] == 8
    assert payload["all_passed"] is True

    expected = expected_keys(ORIGINAL_CASES, "original") + expected_keys(
        ADDED_CASES, "added")
    actual = []
    for report, item in zip(records, payload["checked"]):
        actual.append((report["horizon"], report["delay"],
                       report["max_arrivals"], report["total_cap"],
                       report["causal"], item["selection"]))
    assert actual == expected

    summaries = [summarize(report, selection)
                 for report, selection in zip(
                     records, ("original",) * 8 + ("added",) * 8)]
    assert summaries == payload["checked"]
    assert payload["original_checked"] == summaries[:8]
    assert payload["added_checked"] == summaries[8:]

    original_rows = sum(item["primal_rows"] for item in summaries[:8])
    added_rows = sum(item["primal_rows"] for item in summaries[8:])
    original_columns = sum(item["dual_columns"] for item in summaries[:8])
    added_columns = sum(item["dual_columns"] for item in summaries[8:])
    assert (payload["original_primal_rows_checked"] == original_rows == 1064)
    assert payload["added_primal_rows_checked"] == added_rows == 3672
    assert (payload["original_dual_columns_checked"] == original_columns == 421)
    assert payload["added_dual_columns_checked"] == added_columns == 3603
    assert payload["primal_rows_checked"] == original_rows + added_rows == 4736
    assert payload["dual_columns_checked"] == original_columns + added_columns == 4024

    added_table = make_table_rows(summaries)[4:]
    assert all(Fraction(row["delta_on"]) < 1 for row in added_table)
    assert all(Fraction(row["coverage_on"]) > 0 for row in added_table)

    table_path = ROOT / "TABLE-3.csv"
    with table_path.open(newline="") as stream:
        table = list(csv.DictReader(stream))
    expected_table = make_table_rows(summaries)
    assert table == [{key: str(value) for key, value in row.items()}
                     for row in expected_table]
    assert len(table) == 8

    output = dict(
        checker="Independent augmenting-path matching and exact Fraction arithmetic",
        optimizer_imported=False,
        certificates=len(records),
        original_certificates=8,
        added_certificates=8,
        all_passed=True,
        original_primal_rows_checked=original_rows,
        added_primal_rows_checked=added_rows,
        primal_rows_checked=original_rows + added_rows,
        original_dual_columns_checked=original_columns,
        added_dual_columns_checked=added_columns,
        dual_columns_checked=original_columns + added_columns,
        finite_examples=True,
        scalability_benchmark=False,
        delta_on_note=(
            "The four added rows all have delta_on<1 and positive causal "
            "coverage: 1/2, 1/2, 2/3, and 2/3. The original eight records "
            "remain present and are reported separately."
        ),
        table_rows=expected_table,
        records=summaries,
    )
    (ROOT / "EXTRA-CERTIFICATE-CHECK.json").write_text(
        json.dumps(output, indent=2) + "\n"
    )
    print(
        f"16 stored certificates verified (8 original + 8 added); "
        f"{original_rows + added_rows} primal rows and "
        f"{original_columns + added_columns} dual columns checked; "
        "EXTRA-CERTIFICATE-CHECK.json written."
    )


if __name__ == "__main__":
    main()
