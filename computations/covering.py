"""Finite covering-game synthesis for bounded event traffic.

This module does not import the older full input/output-kernel LP.  It uses
maximal (m-arrival) inputs and saturated schedules.
The manuscript execution rule is execute() in fallback_check.py.
Exact certificates are verified from reconstructed rational primal/dual
strategies; floating point is used only to propose those strategies.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import combinations
import json
from math import comb
from pathlib import Path
import time

import numpy as np
from scipy.optimize import linprog


def exact_masks(horizon: int, count: int) -> list[int]:
    return [sum(1 << t for t in ts) for ts in combinations(range(horizon), count)]


def trace(mask: int, horizon: int) -> str:
    return ''.join(str((mask >> t) & 1) for t in range(horizon))


def feasible(arrivals: int, schedule: int, horizon: int, delay: int) -> bool:
    """Greedily match sorted jobs to the earliest remaining service slot."""
    slots = [s for s in range(horizon) if schedule >> s & 1]
    cursor = 0
    for t in range(horizon):
        if not (arrivals >> t & 1):
            continue
        while cursor < len(slots) and slots[cursor] < t:
            cursor += 1
        if cursor == len(slots) or slots[cursor] > min(t + delay, horizon - 1):
            return False
        cursor += 1
    return True




def pure_budget(horizon: int, delay: int, max_arrivals: int) -> int:
    q, r = divmod(horizon, delay + max_arrivals)
    return q * max_arrivals + min(max_arrivals, r)


def pure_schedule(horizon: int, delay: int, max_arrivals: int) -> int:
    """D silent slots then m services, with a suffix of at most m services."""
    q, r = divmod(horizon, delay + max_arrivals)
    result = 0
    for j in range(q):
        for s in range(j * (delay + max_arrivals) + delay,
                       (j + 1) * (delay + max_arrivals)):
            result |= 1 << s
    for s in range(horizon - min(max_arrivals, r), horizon):
        result |= 1 << s
    return result


def solve(horizon: int, delay: int, max_arrivals: int, cap: int,
          causal: bool = True, certify: bool = True) -> dict:
    if not (1 <= max_arrivals <= cap <= horizon and delay >= 0):
        raise ValueError('Require 1 <= m <= B <= H and D >= 0.')
    started = time.perf_counter()
    inputs = exact_masks(horizon, max_arrivals)
    if causal:
        tail = ((1 << max_arrivals) - 1) << (horizon - max_arrivals)
        schedules = [p | tail for p in exact_masks(horizon - max_arrivals,
                                                   cap - max_arrivals)]
    else:
        schedules = exact_masks(horizon, cap)
    matrix = np.array([[feasible(x, y, horizon, delay) for y in schedules]
                       for x in inputs], dtype=np.int8)
    n = len(schedules)
    objective = np.zeros(n + 1)
    objective[-1] = -1
    constraints = np.column_stack((-matrix, np.ones(len(inputs))))
    norm = np.array([[1.] * n + [0.]])
    lp = linprog(objective, A_ub=constraints, b_ub=np.zeros(len(inputs)),
                 A_eq=norm, b_eq=[1.], bounds=[(0, None)] * n + [(0, 1)],
                 method='highs', options={'dual_feasibility_tolerance': 1e-9,
                                          'primal_feasibility_tolerance': 1e-9})
    if not lp.success:
        raise RuntimeError(lp.message)
    report = dict(horizon=horizon, delay=delay, max_arrivals=max_arrivals,
                  total_cap=cap, causal=causal, status=int(lp.status),
                  inputs=len(inputs), schedules=n, variables=n + 1,
                  coverage=float(lp.x[-1]), delta=float(1 - lp.x[-1]),
                  seconds=time.perf_counter() - started)
    report['policy'] = {trace(y, horizon): float(p)
                        for y, p in zip(schedules, lp.x[:-1]) if p > 1e-10}
    if certify:
        # A needlessly large denominator can fit solver roundoff instead of the
        # rational vertex.  No reconstruction is accepted without exact checks.
        f = lambda z: Fraction(float(z)).limit_denominator(10**6)
        q = [f(z) for z in lp.x[:-1]]
        value = f(lp.x[-1])
        assert sum(q) == 1 and min(q) >= 0
        covered = [sum((q[j] for j in np.flatnonzero(row)), Fraction())
                   for row in matrix]
        assert min(covered) >= value
        # A mixed input strategy certifies that no schedule can do better.
        # At v=1, an arbitrary input is already a valid dual witness.
        if value == 1:
            w = [Fraction(int(i == 0)) for i in range(len(inputs))]
        else:
            w = [f(-z) for z in lp.ineqlin.marginals]
        assert sum(w) == 1 and min(w) >= 0
        upper = [sum((w[i] for i in np.flatnonzero(matrix[:, j])), Fraction())
                 for j in range(n)]
        assert max(upper) <= value
        assert min(covered) == max(upper) == value
        report['certificate'] = dict(
            verified=True, coverage=str(value), delta=str(1 - value),
            schedule_weights={trace(y, horizon): str(p)
                              for y, p in zip(schedules, q) if p},
            input_weights={trace(x, horizon): str(p)
                           for x, p in zip(inputs, w) if p},
            checks='Fraction: nonnegative normalized primal and dual weights; '
                   'every input covered >= v; every schedule covers dual <= v; equality')
        report['policy'] = report['certificate']['schedule_weights']
    return report




def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--horizon', type=int, required=True)
    parser.add_argument('--delay', type=int, required=True)
    parser.add_argument('--arrivals', type=int, default=2)
    parser.add_argument('--cap', type=int, required=True)
    parser.add_argument('--offline', action='store_true')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = solve(args.horizon, args.delay, args.arrivals, args.cap,
                   causal=not args.offline)
    encoded = json.dumps(report, indent=2)
    if args.output:
        args.output.write_text(encoded + '\n')
    print(encoded)


if __name__ == '__main__':
    main()
