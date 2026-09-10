"""Independent finite audit of the stop-padding construction; standard library only.

This file does not import the original implementation or the adversarial checker.
Run in this directory with ordinary Python (not python -O).
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import hashlib
import json


def words(n, k):
    for places in combinations(range(n), k):
        chosen = set(places)
        yield tuple(int(t in chosen) for t in range(n))


def brute_feasible(arrivals, output, delay):
    slots = tuple(t for t, sent in enumerate(output) if sent)
    horizon = len(output)

    def visit(index, used):
        if index == len(arrivals):
            return True
        arrival = arrivals[index]
        return any(
            visit(index + 1, used | (1 << j))
            for j, t in enumerate(slots)
            if not (used >> j) & 1
            and arrival <= t <= min(arrival + delay, horizon - 1)
        )

    return visit(0, 0)


def execute(x, initial, delay):
    horizon = len(x)
    queue = []
    output = []
    deliveries = []
    switch = None
    for t in range(horizon):
        if x[t]:
            queue.append(t)
        if switch is None and not initial[t] and queue:
            if min(queue[0] + delay, horizon - 1) == t:
                switch = t
        send = initial[t] if switch is None else int(bool(queue))
        output.append(send)
        if send and queue:
            deliveries.append((queue.pop(0), t))
        assert all(min(a + delay, horizon - 1) > t for a in queue)
    assert not queue
    return tuple(output), tuple(deliveries), switch


def main():
    pairs = switches = tv_checks = causal_checks = cases = 0
    for horizon in range(1, 8):
        for maximum in range(1, horizon + 1):
            inputs = [x for k in range(maximum + 1) for x in words(horizon, k)]
            for budget in range(maximum, horizon + 1):
                schedules = [prefix + (1,) * maximum
                             for prefix in words(horizon - maximum, budget - maximum)]
                for delay in range(horizon + 1):
                    cases += 1
                    outputs = {x: Counter() for x in inputs}
                    bad = Counter()
                    for initial in schedules:
                        prefixes = {}
                        for x in inputs:
                            arrivals = tuple(t for t, bit in enumerate(x) if bit)
                            feasible = brute_feasible(arrivals, initial, delay)
                            z, delivery, switch = execute(x, initial, delay)
                            pairs += 1
                            assert sum(z) <= budget
                            assert len(delivery) == sum(x)
                            assert all(a <= t <= min(a + delay, horizon - 1)
                                       for a, t in delivery)
                            assert brute_feasible(arrivals, z, delay)
                            assert (z == initial) == feasible
                            if switch is not None:
                                switches += 1
                                assert switch < horizon - maximum
                                assert sum(z[:switch]) <= budget - maximum
                                assert sum(z[switch:]) <= maximum
                            for length in range(horizon + 1):
                                key = (length, x[:length])
                                prefix = z[:length]
                                assert prefixes.setdefault(key, prefix) == prefix
                                causal_checks += 1
                            outputs[x][z] += 1
                            bad[x] += not feasible
                    empty_law = outputs[(0,) * horizon]
                    assert empty_law == Counter(schedules)
                    for x, law in outputs.items():
                        keys = set(law) | set(empty_law)
                        distance = sum(abs(law[z] - empty_law[z]) for z in keys)
                        tv = Fraction(distance, 2 * len(schedules))
                        assert tv == Fraction(bad[x], len(schedules))
                        tv_checks += 1
    result = {
        'purpose': 'Independent finite check of fallback proof, not a novelty or universal proof',
        'domain': 'H=1..7; m=1..H; B=m..H; D=0..H; all inputs of weight <=m and all terminal-reserve schedules',
        'independent_matching': 'Recursive search over all injective assignments; no greedy matching import',
        'tested_prior': 'Uniform over all reserve schedules for each parameter tuple; theorem covers arbitrary priors',
        'parameter_cases': cases,
        'input_schedule_pairs': pairs,
        'switches': switches,
        'prefix_consistency_comparisons': causal_checks,
        'exact_tv_checks': tv_checks,
        'passed': True,
        'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    Path(__file__).with_name('FALLBACK-CHECK.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
