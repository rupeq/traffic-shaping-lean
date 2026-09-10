#!/usr/bin/env python3
"""Narrow exhaustive check for the no-savings block argument.

Scope: H <= 9, 1 <= m <= H, and 0 <= D <= H+1.  The final value H+1
represents all D >= H because deadlines are truncated at H-1.

This independent, deterministic checker verifies the block argument and
the fixed perfect-privacy schedule. It does not import the optimizer.
"""

from fractions import Fraction
from functools import lru_cache
from itertools import combinations
import json


def masks_of_weight_at_most(h, m):
    masks = []
    for weight in range(m + 1):
        for slots in combinations(range(h), weight):
            mask = 0
            for slot in slots:
                mask |= 1 << slot
            masks.append(mask)
    return masks


def feasible(x_mask, y_mask, h, delay):
    """Exact interval matching by memoized backtracking."""
    arrivals = [t for t in range(h) if (x_mask >> t) & 1]
    sends = [s for s in range(h) if (y_mask >> s) & 1]

    @lru_cache(None)
    def match(index, used):
        if index == len(arrivals):
            return True
        arrival = arrivals[index]
        latest = min(arrival + delay, h - 1)
        for send_index, send in enumerate(sends):
            if not (used >> send_index) & 1 and arrival <= send <= latest:
                if match(index + 1, used | (1 << send_index)):
                    return True
        return False

    return match(0, 0)


def check_instance(h, m, delay):
    block_length = delay + m
    full_blocks, remainder = divmod(h, block_length)
    block_count = (h + block_length - 1) // block_length
    required = [m] * full_blocks
    if remainder:
        required.append(min(m, remainder))
    assert len(required) == block_count
    b0 = sum(required)

    blocks = []
    tests = []
    for block_index in range(full_blocks):
        start = block_index * block_length
        end = start + block_length
        blocks.append((start, end))
        test = sum(1 << slot for slot in range(start, start + m))
        tests.append(test)
    if remainder:
        start = full_blocks * block_length
        blocks.append((start, h))
        count = min(m, remainder)
        tests.append(sum(1 << slot for slot in range(start, start + count)))

    assert len(blocks) == block_count
    assert sum(required) == m * full_blocks + min(m, remainder)

    all_traces = tuple(range(1 << h))

    # Every feasible test trace pays its required transmission count inside
    # that test's own disjoint block.
    structural_checks = 0
    for test, (start, end), count in zip(tests, blocks, required):
        block_mask = ((1 << (end - start)) - 1) << start
        for trace in all_traces:
            if feasible(test, trace, h, delay):
                structural_checks += 1
                assert (trace & block_mask).bit_count() >= count

    # Within Y_B = {y: |y| <= B}, the common intersection is empty for
    # every B < B0; at B0 at least one common trace exists.
    intersection_checks = 0
    for budget in range(b0):
        intersection_checks += 1
        common = any(
            trace.bit_count() <= budget
            and all(feasible(test, trace, h, delay) for test in tests)
            for trace in all_traces
        )
        assert not common
    common_at_b0 = any(
        trace.bit_count() <= b0
        and all(feasible(test, trace, h, delay) for test in tests)
        for trace in all_traces
    )
    assert common_at_b0

    # Explicit fixed terminal-reserve schedule.
    reserve = 0
    for block_index in range(full_blocks):
        start = block_index * block_length
        for slot in range(start + delay, start + delay + m):
            reserve |= 1 << slot
    if remainder:
        count = min(m, remainder)
        for slot in range(h - count, h):
            reserve |= 1 << slot
    assert reserve.bit_count() == b0

    all_inputs = masks_of_weight_at_most(h, m)
    reserve_checks = 0
    for input_mask in all_inputs:
        reserve_checks += 1
        assert feasible(input_mask, reserve, h, delay)

    # Delivery is impossible for every B < m, using m arrivals in the first
    # m slots as a witness.
    full_input = sum(1 << slot for slot in range(m))
    impossible_checks = 0
    for budget in range(m):
        impossible_checks += 1
        assert not any(
            trace.bit_count() <= budget and feasible(full_input, trace, h, delay)
            for trace in all_traces
        )

    return {
        "H": h,
        "m": m,
        "D": delay,
        "K": block_count,
        "B0": b0,
        "traces": len(all_traces),
        "inputs_weight_at_most_m": len(all_inputs),
        "structural_feasible_trace_checks": structural_checks,
        "Y_B_intersection_checks_for_B_lt_B0": intersection_checks,
        "reserve_input_checks": reserve_checks,
        "B_lt_m_impossibility_checks": impossible_checks,
    }


def main():
    instances = []
    for h in range(1, 10):
        for m in range(1, h + 1):
            for delay in range(0, h + 2):
                instances.append(check_instance(h, m, delay))

    # At equality delta=1/K, the noncausal boundary example permits B<B0.
    # Q is uniform on 10 and 01; an active input at t outputs the point mass
    # at its required slot.  At epsilon=0 the TV distance is exactly 1/2.
    empty_law = {1: Fraction(1, 2), 2: Fraction(1, 2)}
    boundary_values = []
    for arrival_trace in (1, 2):
        active_law = {arrival_trace: Fraction(1)}
        assert feasible(arrival_trace, arrival_trace, 2, 0)
        tv = sum(abs(empty_law.get(y, 0) - active_law.get(y, 0)) for y in (1, 2)) / 2
        assert tv == Fraction(1, 2)
        boundary_values.append(tv)
    assert max(boundary_values) == Fraction(1, 2)
    boundary = {
        "H": 2,
        "m": 1,
        "D": 0,
        "B": 1,
        "B0": 2,
        "K": 2,
        "epsilon": 0,
        "delta": "1/2",
        "delta_equals_1_over_K": True,
        "B_lt_B0": True,
        "class": "noncausal",
    }

    result = {
        "status": "PASS",
        "checker": "no_savings_check.py",
        "scope": {
            "H_max": 9,
            "m_range": [1, 9],
            "D_range_inclusive": [0, 10],
            "D_ge_H_equivalent_after_deadline_truncation": True,
            "parameter_sets": len(instances),
            "all_output_traces_enumerated": True,
            "all_inputs_of_weight_at_most_m_enumerated": True,
        },
        "checks": [
            "feasible test traces contain the required count in their own block",
            "Y_B intersection of all test-feasibility events is empty for every B<B0",
            "the fixed terminal-reserve schedule is feasible for every input of weight at most m",
            "every B<m is impossible",
        ],
        "boundary_certificate": boundary,
        "aggregate_counts": {
            "output_traces_across_instances": sum(item["traces"] for item in instances),
            "input_checks_at_reserve": sum(item["reserve_input_checks"] for item in instances),
            "structural_feasible_trace_checks": sum(
                item["structural_feasible_trace_checks"] for item in instances
            ),
            "Y_B_intersection_checks_for_B_lt_B0": sum(
                item["Y_B_intersection_checks_for_B_lt_B0"] for item in instances
            ),
            "B_lt_m_impossibility_checks": sum(
                item["B_lt_m_impossibility_checks"] for item in instances
            ),
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
