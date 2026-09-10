"""Independent exact certificates for the 240 reported zero-delay games.

Uses only the Python standard library.  With D=0, feasibility follows directly
from the service contract: every arrival slot must be a transmission slot.
No manuscript solver, greedy predicate, stored witness, or LP matrix is used.
"""
from fractions import Fraction
from itertools import combinations
from math import comb
from pathlib import Path
import hashlib
import json
import platform


ROOT = Path(__file__).resolve().parent
SAVED = ROOT / "QUANTITATIVE-CHECK.json"


def certify(h, m, b, causal):
    inputs = [frozenset(x) for x in combinations(range(h), m)]
    if causal:
        n, k = h - m, b - m
        tail = frozenset(range(n, h))
        schedules = [frozenset(z) | tail for z in combinations(range(n), k)]
        j = min(m, n)
        fixed_tail = frozenset(range(n, n + m - j))
        dual_inputs = [frozenset(x) | fixed_tail for x in combinations(range(n), j)]
        predicted = Fraction(comb(k, j), comb(n, j))
    else:
        schedules = [frozenset(y) for y in combinations(range(h), b)]
        dual_inputs = inputs
        predicted = Fraction(comb(b, m), comb(h, m))

    assert schedules and dual_inputs
    assert all(len(y) == b for y in schedules)
    assert all(len(x) == m for x in dual_inputs)
    if causal:
        assert all(set(range(h - m, h)) <= y for y in schedules)
    q_weight, p_weight = Fraction(1, len(schedules)), Fraction(1, len(dual_inputs))
    assert len(schedules) * q_weight == len(dual_inputs) * p_weight == 1
    assert q_weight > 0 and p_weight > 0

    # Check every primal row and every dual column, using exact subset tests.
    row_values = [Fraction(sum(x <= y for y in schedules), len(schedules))
                  for x in inputs]
    col_values = [Fraction(sum(x <= y for x in dual_inputs), len(dual_inputs))
                  for y in schedules]
    lower, upper = min(row_values), max(col_values)
    assert all(v >= predicted for v in row_values)
    assert all(v <= predicted for v in col_values)
    assert lower == upper == predicted
    return {
        "H": h, "m": m, "B": b, "causal": causal,
        "coverage": str(lower), "delta": str(1 - lower),
        "checked_primal_rows": len(inputs),
        "checked_dual_columns": len(schedules),
        "q_uniform_weight": str(q_weight),
        "q_support_transmission_slots": [sorted(y) for y in schedules],
        "p_uniform_weight": str(p_weight),
        "p_support_arrival_slots": [sorted(x) for x in dual_inputs],
        "primal_row_values": [str(v) for v in row_values],
        "dual_column_values": [str(v) for v in col_values],
        "verified": True,
    }


def main():
    records = [certify(h, m, b, causal)
               for h in range(1, 9)
               for m in range(1, h + 1)
               for b in range(m, h + 1)
               for causal in (False, True)]
    assert len(records) == 240
    saved = json.loads(SAVED.read_text())["d0_checks"]
    key = lambda x: (x["H"], x["m"], x["B"], x["causal"])
    expected = {key(x): Fraction(x["coverage"]) for x in saved}
    assert len(expected) == 240
    assert {key(x) for x in records} == set(expected)
    assert all(Fraction(x["coverage"]) == expected[key(x)] for x in records)
    report = {
        "status": "pass", "cases": len(records),
        "method": "Exact uniform primal/dual witnesses; independently constructed D=0 subset-containment matrix",
        "domain": "1<=H<=8; 1<=m<=B<=H; both classes; D=0",
        "primal_rows_checked": sum(x["checked_primal_rows"] for x in records),
        "dual_columns_checked": sum(x["checked_dual_columns"] for x in records),
        "saved_values_all_match": True,
        "saved_report_sha256": hashlib.sha256(SAVED.read_bytes()).hexdigest(),
        "python": platform.python_version(),
        "limitations": "Certifies the finite zero-delay games; does not independently prove the causal-game characterization or any unbounded parameter theorem.",
        "records": records,
    }
    output = ROOT / "ZERO-DELAY-EXACT-CHECK.json"
    output.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "records"}, ensure_ascii=False))


if __name__ == "__main__":
    main()
