"""Reproduce the manuscript zero-delay and resource-bound checks.

Reads the existing frontier and solver without modifying either.  No full
causal-kernel LP is rerun here: its equivalence is the theorem under assessment.
"""
from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
from hashlib import sha256
from math import comb
from pathlib import Path
import json
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
from covering import solve


def d0_coverage(h: int, m: int, b: int, causal: bool) -> Fraction:
    if not causal:
        return Fraction(comb(b, m), comb(h, m))
    n, k = h - m, b - m
    j = min(m, n)
    return Fraction(comb(k, j), comb(n, j)) if k >= j else Fraction(0)


def main() -> None:
    frontier_path = ROOT / 'FRONTIERS.json'
    solver_path = ROOT / 'covering.py'
    before = {p.name: sha256(p.read_bytes()).hexdigest()
              for p in (frontier_path, solver_path)}
    checks = []
    for h in range(1, 9):
        for m in range(1, h + 1):
            for b in range(m, h + 1):
                for causal in (False, True):
                    result = solve(h, 0, m, b, causal=causal, certify=True)
                    actual = Fraction(result['certificate']['coverage'])
                    expected = d0_coverage(h, m, b, causal)
                    assert actual == expected, (h, m, b, causal, actual, expected)
                    checks.append(dict(H=h, m=m, B=b, causal=causal,
                                       coverage=str(actual)))

    saved = json.loads(frontier_path.read_text())['records']
    privacy_bound_checks = []
    d0_by_case = defaultdict(dict)
    for rec in checks:
        d0_by_case[(rec['H'], rec['m'], rec['B'])][rec['causal']] = Fraction(rec['coverage'])
    for (h, m, b), values in d0_by_case.items():
        if b >= 2*m:
            r = Fraction(comb(b-m, m), comb(b, m))
            gap = values[False] - values[True]
            bound = (1-r)*values[False]
            assert 0 <= gap <= bound <= Fraction(m*m, b)
            privacy_bound_checks.append(dict(H=h, D=0, m=m, B=b,
                                              actual_gap=str(gap), bound=str(bound)))
    groups = defaultdict(dict)
    for rec in saved:
        assert rec['certificate']['verified']
        key = (rec['horizon'], rec['delay'], rec['max_arrivals'])
        mode = 'on' if rec['causal'] else 'off'
        groups[key].setdefault(mode, {})[rec['total_cap']] = Fraction(
            rec['certificate']['delta'])

    thresholds = [Fraction(0), Fraction(1, 100), Fraction(1, 10),
                  Fraction(1, 3), Fraction(1, 2), Fraction(9, 10)]
    families, price_checks = [], []
    for (h, d, m), modes in sorted(groups.items()):
        q, r = divmod(h, d + m)
        b0 = m * q + min(m, r)
        entry = dict(H=h, D=d, m=m, pure_budget=b0, modes={})
        for mode, frontier in modes.items():
            assert sorted(frontier) == list(range(m, b0 + 1))
            assert frontier[b0] == 0
            positive = [v for v in frontier.values() if v > 0]
            caps = {str(t): min(b for b, delta in frontier.items() if delta <= t)
                    for t in thresholds}
            assert caps['0'] == caps['1/100'] == caps['1/10'] == b0
            entry['modes'][mode] = dict(
                min_positive_delta=str(min(positive)) if positive else None,
                cap_at_delta=caps,
                exact_frontier={str(b): str(delta) for b, delta in frontier.items()})
        if 'off' in modes and 'on' in modes:
            for b in set(modes['off']) & set(modes['on']):
                if b >= 2*m:
                    r = Fraction(comb(b-m, m), comb(b, m))
                    gap = modes['on'][b] - modes['off'][b]
                    bound = (1-r)*(1-modes['off'][b])
                    assert 0 <= gap <= bound <= Fraction(m*m, b)
                    privacy_bound_checks.append(dict(H=h, D=d, m=m, B=b,
                                                      actual_gap=str(gap), bound=str(bound)))
            all_t = sorted(set(modes['off'].values()) | set(modes['on'].values()))
            for t in all_t:
                boff = min(b for b, delta in modes['off'].items() if delta <= t)
                bon = min(b for b, delta in modes['on'].items() if delta <= t)
                assert 0 <= bon - boff <= m
                price_checks.append(dict(H=h, D=d, m=m, delta=str(t),
                                         B_off=boff, B_on=bon, gap=bon-boff))
        families.append(entry)

    after = {p.name: sha256(p.read_bytes()).hexdigest()
             for p in (frontier_path, solver_path)}
    assert before == after
    report = dict(
        status='pass', source_sha256=before,
        d0_scope='H=1..8; all 1<=m<=B<=H; both games; D=0',
        d0_exact_LP_comparisons=len(checks), d0_checks=checks,
        saved_frontier_records=len(saved), saved_families=len(families),
        saved_frontier_scope='Existing records only; all families have m=2.',
        families=families, budget_price_checks=price_checks,
        budget_price_check_count=len(price_checks),
        privacy_bound_checks=privacy_bound_checks,
        privacy_bound_check_count=len(privacy_bound_checks),
        limitations='Finite checks support the general proofs; no independent '
                     'general proof follows from finite enumeration alone.')
    out = Path(__file__).with_name('QUANTITATIVE-CHECK.json')
    out.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ('families', 'd0_checks', 'budget_price_checks',
                                   'privacy_bound_checks')},
                     indent=2))
    for family in families:
        print(json.dumps(family))


if __name__ == '__main__':
    main()
