"""Check saved LP witnesses with only the standard library.

This file imports neither the optimizer nor its greedy feasibility predicate.
It checks packet assignment by an independent augmenting-path matching search.
"""
import json
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from pathlib import Path

import csv

ROOT = Path(__file__).resolve().parent


def schedules(h: int, count: int, reserved: int = 0):
    for prefix in combinations(range(h - reserved), count - reserved):
        ones = set(prefix) | set(range(h - reserved, h))
        yield ''.join('1' if t in ones else '0' for t in range(h))


@lru_cache(maxsize=300000)
def matches(x: str, y: str, d: int) -> bool:
    occupied = {}

    def augment(a: int, visited: set[int]) -> bool:
        for t in range(a, min(len(y), a + d + 1)):
            if y[t] != '1' or t in visited:
                continue
            visited.add(t)
            if t not in occupied or augment(occupied[t], visited):
                occupied[t] = a
                return True
        return False

    return all(augment(a, set()) for a, bit in enumerate(x) if bit == '1')


def check(report: dict) -> dict:
    h, d, m, b = (report[k] for k in ('horizon', 'delay', 'max_arrivals', 'total_cap'))
    c = report['certificate']
    q = {y: Fraction(p) for y, p in c['schedule_weights'].items()}
    w = {x: Fraction(p) for x, p in c['input_weights'].items()}
    v = Fraction(c['coverage'])
    assert sum(q.values()) == sum(w.values()) == 1
    assert min(q.values()) >= 0 and min(w.values()) >= 0
    assert Fraction(c['delta']) == 1 - v
    assert all(len(y) == h and set(y) <= {'0', '1'} and y.count('1') == b for y in q)
    assert all(len(x) == h and set(x) <= {'0', '1'} and x.count('1') == m for x in w)
    reserve = m if report['causal'] else 0
    if reserve:
        assert all(y.endswith('1' * m) for y in q)
    lower = min(sum((p for y, p in q.items() if matches(x, y, d)), Fraction())
                for x in schedules(h, m))
    upper = max(sum((p for x, p in w.items() if matches(x, y, d)), Fraction())
                for y in schedules(h, b, reserve))
    assert lower == upper == v
    assert {y: Fraction(p) for y, p in report['policy'].items()} == q
    return dict(H=h, D=d, m=m, B=b, causal=report['causal'], delta=str(1 - v))


def main() -> None:
    reports = json.loads((ROOT / 'FRONTIERS.json').read_text())['records']
    checked = [check(r) for r in reports]
    assert len(checked) == 79
    example = dict(horizon=8, delay=1, max_arrivals=2, total_cap=4, causal=True)
    q = {y: '1/3' for y in ('01100011', '01001011', '00011011')}
    w = {x: '1/3' for x in ('11000000', '10010000', '00110000')}
    example.update(certificate=dict(coverage='1/3', delta='2/3',
                                    schedule_weights=q, input_weights=w), policy=q)
    explicit = check(example)
    assert len(list(schedules(8, 2))) == 28
    assert len(list(schedules(8, 4, 2))) == 15
    families = {}
    for r in checked:
        if r['causal']:
            families.setdefault((r['H'], r['D'], r['m']), {})[r['B']] = Fraction(r['delta'])
    table = []
    for (h, d, m), frontier in sorted(families.items()):
        quotient, remainder = divmod(h, d+m)
        b0 = m*quotient + min(m, remainder)
        assert sorted(frontier) == list(range(m, b0+1)) and frontier[b0] == 0
        table.append(dict(H=h, D=d, m=m, B0=b0,
            least_positive_delta=str(min(v for b, v in frontier.items() if b < b0)),
            B_on_01=min(b for b, v in frontier.items() if v <= Fraction(1, 10)),
            B_on_05=min(b for b, v in frontier.items() if v <= Fraction(1, 2))))
    with (ROOT / 'TABLE-1.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(table[0]))
        writer.writeheader(); writer.writerows(table)
    output = dict(checker='Independent augmenting-path matching and exact Fraction arithmetic',
        optimizer_imported=False, certificates=len(checked), explicit_example=explicit,
        example_matrix_rows=28, example_matrix_columns=15, all_passed=True,
        table=table, records=checked)
    (ROOT / 'CERTIFICATE-CHECK.json').write_text(json.dumps(output, indent=2)+'\n')
    print('79 stored certificates and the explicit 28-by-15 example verified; TABLE-1.csv written.')


if __name__ == '__main__':
    main()
