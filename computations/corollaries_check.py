#!/usr/bin/env python3
"""Independent exact checks for the five quantitative corollaries.

The checker deliberately does not import the optimizer or any existing checker.
It constructs arrival inputs and output schedules, derives admissibility with a
fresh augmenting-path matcher, and uses ``Fraction`` for every comparison.  It
checks the schedule maps and injections used in Corollaries 1--5, rather than
re-solving the finite covering LPs.

The default JSON report is written below the checkout's ignored
``.check-output/corollaries`` directory. Source inputs are never modified.
"""

from __future__ import annotations

import argparse
import csv
from datetime import datetime, timezone
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
import hashlib
import json
from math import ceil, comb
import os
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parent
DEFAULT_OUTPUT = ROOT.parent / ".check-output/corollaries"


def ensure(condition: bool, message: str) -> None:
    """Raise on every failed check, including when Python is optimized."""
    if not condition:
        raise AssertionError(message)


def binom(n: int, k: int) -> int:
    """Article convention C(n,k)=0 outside 0<=k<=n."""
    return comb(n, k) if 0 <= k <= n else 0


def reject_optimized_mode() -> None:
    if not __debug__ or sys.flags.optimize or os.environ.get("PYTHONOPTIMIZE"):
        raise SystemExit(
            "corollaries_check.py refuses optimized mode; run without -O"
        )


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def saved_input_paths() -> dict[str, Path]:
    """Return the saved artifacts consumed by the table-mapping checks."""
    names = (
        "FRONTIERS.json",
        "EXTRA-CERTIFICATES.json",
        "TABLE-1.csv",
        "TABLE-3.csv",
        "QUANTITATIVE-CHECK.json",
    )
    return {name: ROOT / name for name in names}


def saved_input_hashes() -> dict[str, str]:
    return {name: sha256(path) for name, path in saved_input_paths().items()}


@lru_cache(maxsize=None)
def position_subsets(horizon: int, weight: int) -> tuple[tuple[int, ...], ...]:
    ensure(0 <= weight <= horizon, f"invalid subset request H={horizon}, k={weight}")
    return tuple(tuple(item) for item in combinations(range(horizon), weight))


@lru_cache(maxsize=None)
def exact_inputs(horizon: int, max_arrivals: int) -> tuple[tuple[int, ...], ...]:
    return position_subsets(horizon, max_arrivals)


@lru_cache(maxsize=None)
def bounded_inputs(horizon: int, max_arrivals: int) -> tuple[tuple[int, ...], ...]:
    return tuple(
        item
        for weight in range(max_arrivals + 1)
        for item in position_subsets(horizon, weight)
    )


@lru_cache(maxsize=None)
def offline_schedules(horizon: int, budget: int) -> tuple[tuple[int, ...], ...]:
    return position_subsets(horizon, budget)


@lru_cache(maxsize=None)
def causal_schedules(
    horizon: int, max_arrivals: int, budget: int
) -> tuple[tuple[int, ...], ...]:
    ensure(max_arrivals <= budget <= horizon, "causal budget outside its domain")
    terminal = tuple(range(horizon - max_arrivals, horizon))
    return tuple(
        tuple(sorted(prefix + terminal))
        for prefix in position_subsets(horizon - max_arrivals, budget - max_arrivals)
    )


@lru_cache(maxsize=500_000)
def matching(
    arrivals: tuple[int, ...],
    schedule: tuple[int, ...],
    horizon: int,
    delay: int,
) -> tuple[tuple[int, int], ...] | None:
    """Return an explicit feasible injection, or ``None``.

    The augmenting-path search is independent of the existing greedy
    predicate.  Edges are the actual service intervals
    ``a <= s <= min(a + delay, H - 1)``.
    """
    if len(arrivals) > len(schedule):
        return None
    available = set(schedule)
    occupied: dict[int, int] = {}

    def augment(arrival: int, visited: set[int]) -> bool:
        latest = min(arrival + delay, horizon - 1)
        for service in range(arrival, latest + 1):
            if service not in available or service in visited:
                continue
            visited.add(service)
            if service not in occupied or augment(occupied[service], visited):
                occupied[service] = arrival
                return True
        return False

    for arrival in arrivals:
        if not augment(arrival, set()):
            return None
    return tuple(sorted((arrival, service) for service, arrival in occupied.items()))


def covers(
    arrivals: tuple[int, ...], schedule: tuple[int, ...], horizon: int, delay: int
) -> bool:
    return matching(arrivals, schedule, horizon, delay) is not None


def bit_string(schedule: tuple[int, ...], horizon: int) -> str:
    occupied = set(schedule)
    return "".join("1" if slot in occupied else "0" for slot in range(horizon))


def parse_bits(value: str) -> tuple[int, ...]:
    ensure(value and set(value) <= {"0", "1"}, f"invalid binary trace {value!r}")
    return tuple(index for index, bit in enumerate(value) if bit == "1")


def simulate_algorithm1(
    input_trace: str, base_trace: str, delay: int, cap: int
) -> dict:
    """Run the manuscript's switch-to-service rule on one FIFO trace.

    This deliberately small executable anchor is independent of the matching
    predicate above and of the optimizer.  Arrivals enter the FIFO before the
    current slot is processed; a silent base slot switches exactly when the
    FIFO head reaches its clipped deadline; after switching, service is sent
    whenever the FIFO is nonempty.
    """
    ensure(len(input_trace) == len(base_trace), "Algorithm 1 trace lengths differ")
    ensure(delay >= 0 and cap >= 0, "Algorithm 1 delay/cap must be nonnegative")
    ensure(set(input_trace) <= {"0", "1"}, "invalid Algorithm 1 input trace")
    ensure(set(base_trace) <= {"0", "1"}, "invalid Algorithm 1 base trace")
    horizon = len(input_trace)
    queue: list[int] = []
    output: list[int] = []
    services: list[tuple[int, int]] = []
    switch: int | None = None
    for slot in range(horizon):
        if input_trace[slot] == "1":
            queue.append(slot)
        if (
            switch is None
            and base_trace[slot] == "0"
            and queue
            and min(queue[0] + delay, horizon - 1) == slot
        ):
            switch = slot
        send = int(base_trace[slot] == "1") if switch is None else int(bool(queue))
        output.append(send)
        if send and queue:
            arrival = queue.pop(0)
            services.append((arrival, slot))
        # Every packet left in the FIFO must still have a future feasible slot.
        ensure(
            all(min(arrival + delay, horizon - 1) > slot for arrival in queue),
            f"Algorithm 1 missed a deadline at slot {slot}",
        )
    ensure(not queue, "Algorithm 1 left arrivals undelivered")
    ensure(sum(output) <= cap, "Algorithm 1 exceeded the output cap")
    deadline_bounds = [
        {
            "arrival": arrival,
            "service": service,
            "deadline": min(arrival + delay, horizon - 1),
            "release_respected": arrival <= service,
            "deadline_respected": service <= min(arrival + delay, horizon - 1),
        }
        for arrival, service in services
    ]
    ensure(all(item["release_respected"] for item in deadline_bounds), "Algorithm 1 release bound failed")
    ensure(all(item["deadline_respected"] for item in deadline_bounds), "Algorithm 1 deadline bound failed")
    ensure(len(services) == input_trace.count("1"), "Algorithm 1 service count mismatch")
    return {
        "input": input_trace,
        "base": base_trace,
        "output": "".join(str(bit) for bit in output),
        "services": [list(pair) for pair in services],
        "switch": switch,
        "count": sum(output),
        "cap": cap,
        "cap_respected": sum(output) <= cap,
        "deadline_bounds": deadline_bounds,
        "all_deadlines_met": all(
            item["release_respected"] and item["deadline_respected"]
            for item in deadline_bounds
        ),
    }


def terminal_slots(horizon: int, max_arrivals: int) -> tuple[int, ...]:
    return tuple(range(horizon - max_arrivals, horizon))


def block_parameters(horizon: int, delay: int, max_arrivals: int) -> tuple[int, int, int, int]:
    length = delay + max_arrivals
    full, remainder = divmod(horizon, length)
    b0 = max_arrivals * full + min(max_arrivals, remainder)
    blocks = full + (1 if remainder else 0)
    return length, full, remainder, b0


def block_schedule(
    horizon: int, delay: int, max_arrivals: int
) -> tuple[int, ...]:
    length, full, remainder, _ = block_parameters(horizon, delay, max_arrivals)
    result: set[int] = set()
    for index in range(full):
        start = index * length
        result.update(range(start + delay, start + length))
    if remainder:
        count = min(max_arrivals, remainder)
        result.update(range(horizon - count, horizon))
    return tuple(sorted(result))


def block_tests(
    horizon: int, delay: int, max_arrivals: int
) -> tuple[tuple[int, ...], ...]:
    length, full, remainder, _ = block_parameters(horizon, delay, max_arrivals)
    tests = [
        tuple(range(index * length, index * length + max_arrivals))
        for index in range(full)
    ]
    if remainder:
        start = full * length
        tests.append(tuple(range(start, start + min(max_arrivals, remainder))))
    return tuple(tests)


def complete_to_budget(
    retained: tuple[int, ...], horizon: int, budget: int, max_arrivals: int
) -> tuple[int, ...]:
    """Add the terminal reserve, then fill deterministically to ``budget``."""
    result = set(retained)
    result.update(terminal_slots(horizon, max_arrivals))
    for slot in range(horizon):
        if len(result) >= budget:
            break
        result.add(slot)
    ensure(len(result) == budget, "could not complete a schedule to the target budget")
    return tuple(sorted(result))


def lift_offline_schedule(
    schedule: tuple[int, ...], horizon: int, max_arrivals: int
) -> tuple[int, ...]:
    """The Corollary 1 map: add the terminal reserve and complete to B'."""
    budget = min(horizon, len(schedule) + max_arrivals)
    return complete_to_budget(schedule, horizon, budget, max_arrivals)


def transformed_schedule(
    retained: tuple[int, ...], horizon: int, max_arrivals: int, budget: int
) -> tuple[int, ...]:
    return complete_to_budget(retained, horizon, budget, max_arrivals)


def weighted_coverage(
    policy: dict[tuple[int, ...], Fraction],
    arrivals: tuple[int, ...],
    horizon: int,
    delay: int,
) -> Fraction:
    return sum(
        (weight for schedule, weight in policy.items() if covers(arrivals, schedule, horizon, delay)),
        Fraction(0),
    )


def weighted_schedule_mass(
    input_law: dict[tuple[int, ...], Fraction],
    schedule: tuple[int, ...],
    horizon: int,
    delay: int,
) -> Fraction:
    return sum(
        (weight for arrivals, weight in input_law.items() if covers(arrivals, schedule, horizon, delay)),
        Fraction(0),
    )


def total_variation(
    first: dict[object, Fraction], second: dict[object, Fraction]
) -> Fraction:
    support = set(first) | set(second)
    return sum(
        (abs(first.get(item, Fraction(0)) - second.get(item, Fraction(0))) for item in support),
        Fraction(0),
    ) / 2


def event_mass(law: dict[object, Fraction], event: set[object]) -> Fraction:
    return sum((law.get(item, Fraction(0)) for item in event), Fraction(0))


def check_privacy_interpretation() -> dict:
    """Small exact regressions for the unnumbered TV interpretation text."""
    identical_p = {"a": Fraction(1, 4), "b": Fraction(3, 4)}
    identical_q = dict(identical_p)
    disjoint_p = {"a": Fraction(1)}
    disjoint_q = {"b": Fraction(1)}
    first = {0: Fraction(1, 2), 1: Fraction(1, 3), 2: Fraction(1, 6)}
    second = {0: Fraction(1, 3), 1: Fraction(1, 2), 2: Fraction(1, 6)}
    third = {0: Fraction(1, 6), 1: Fraction(1, 3), 2: Fraction(1, 2)}

    for law in (identical_p, identical_q, disjoint_p, disjoint_q, first, second, third):
        ensure(sum(law.values(), Fraction(0)) == 1, "privacy regression law is not normalized")

    identical_tv = total_variation(identical_p, identical_q)
    disjoint_tv = total_variation(disjoint_p, disjoint_q)
    ensure(identical_tv == 0, "identical-law TV is not zero")
    ensure(disjoint_tv == 1, "disjoint-law TV is not one")

    triangle_checks = 0
    for left, middle, right in (
        (first, second, third),
        (identical_p, first, second),
        (disjoint_p, first, disjoint_q),
    ):
        ensure(
            total_variation(left, right)
            <= total_variation(left, middle) + total_variation(middle, right),
            "TV triangle inequality failed",
        )
        triangle_checks += 1

    event_checks = 0
    randomized_checks = 0
    randomized_maxima = []
    for left, right in (
        (identical_p, identical_q),
        (disjoint_p, disjoint_q),
        (first, second),
    ):
        support = tuple(sorted(set(left) | set(right), key=str))
        tv = total_variation(left, right)
        largest_event_gap = Fraction(0)
        for mask in range(1 << len(support)):
            event = {support[index] for index in range(len(support)) if mask & (1 << index)}
            gap = abs(event_mass(left, event) - event_mass(right, event))
            largest_event_gap = max(largest_event_gap, gap)
            event_checks += 1
            ensure(gap <= tv, "event gap exceeded TV")
        ensure(largest_event_gap == tv, "event characterization of TV failed")

        best_success = Fraction(0)
        for choices in product((Fraction(0), Fraction(1, 2), Fraction(1)), repeat=len(support)):
            test = dict(zip(support, choices))
            success = (
                sum((left.get(item, Fraction(0)) * test[item] for item in support), Fraction(0))
                + sum((right.get(item, Fraction(0)) * (1 - test[item]) for item in support), Fraction(0))
            ) / 2
            best_success = max(best_success, success)
            randomized_checks += 1
            # For every t in [0,1], linearity bounds the signed advantage by
            # the positive part of left-right, which is exactly TV.
            ensure(success <= (1 + tv) / 2, "randomized test exceeded TV success bound")
        ensure(best_success == (1 + tv) / 2, "best equal-prior test formula failed")
        randomized_maxima.append(str(best_success))

    return {
        "status": "PASS",
        "identical_law_TV": "0",
        "disjoint_law_TV": "1",
        "triangle_checks": triangle_checks,
        "event_checks": event_checks,
        "randomized_test_checks": randomized_checks,
        "best_equal_prior_success_values": randomized_maxima,
        "formula": "best success=(1+TV)/2",
        "randomized_test_range": "t(y) in [0,1], with exact {0,1/2,1} regression grid and positive-part bound",
    }


def check_article_sizes() -> dict:
    """Check the large finite schedule count quoted in Section 3.3."""
    value = binom(48, 8)
    ensure(value == 377_348_994, "C(48,8) article size mismatch")
    ensure(value == binom(50 - 2, 10 - 2), "causal schedule count specialization mismatch")
    return {
        "status": "PASS",
        "C(48,8)": value,
        "specialization": "C(50-2,10-2)=C(48,8) for H=50,m=2,B=10",
    }


def check_saved_table_mapping() -> dict:
    """Read-only freshness/mapping check for the saved Table 2 and Table 3.

    The neighboring independent checkers certify matching witnesses.  This
    group does not solve an LP or re-check every witness; it verifies that the
    published CSV rows still agree exactly with the saved rational certificate
    values and with Eq. (20)'s B0.
    """
    table_one_path = ROOT / "TABLE-1.csv"
    table_three_path = ROOT / "TABLE-3.csv"
    frontier_path = ROOT / "FRONTIERS.json"
    extra_path = ROOT / "EXTRA-CERTIFICATES.json"

    with table_one_path.open(newline="") as stream:
        table_one = list(csv.DictReader(stream))
    with table_three_path.open(newline="") as stream:
        table_three = list(csv.DictReader(stream))
    frontiers = json.loads(frontier_path.read_text())["records"]
    extra = json.loads(extra_path.read_text())
    ensure(len(frontiers) == 79, "saved frontier count changed")
    ensure(len(extra["records"]) == 16, "saved extra certificate count changed")

    expected_table_one = {
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
    ensure(len(table_one) == len(expected_table_one), "Table 2 row count changed")
    frontier_groups: dict[tuple[int, int], list[dict]] = {}
    for record in frontiers:
        ensure(record["status"] == 0, "saved frontier has nonzero status")
        certificate = record["certificate"]
        ensure(certificate["verified"] is True, "saved frontier certificate is unverified")
        ensure(
            Fraction(certificate["coverage"]) + Fraction(certificate["delta"]) == 1,
            "saved frontier coverage/delta mismatch",
        )
        if record["causal"] and record["max_arrivals"] == 2:
            frontier_groups.setdefault((record["horizon"], record["delay"]), []).append(record)

    for row in table_one:
        key = (int(row["H"]), int(row["D"]))
        ensure(key in expected_table_one, f"unexpected Table 2 row {key}")
        b0, least_delta, budget_01, budget_05 = expected_table_one[key]
        ensure(int(row["B0"]) == b0, "Table 2 B0 mismatch")
        # The CSV column has the historical ASCII name; use positional lookup
        # so the check remains valid for the generated file's Unicode header.
        delta_field = next(
            name for name in row if "delta" in name.lower() or "δ" in name
        )
        ensure(row[delta_field] == least_delta, "Table 2 least-delta mismatch")
        ensure(int(row["B_on_01"]) == budget_01, "Table 2 B_on(0.1) mismatch")
        ensure(int(row["B_on_05"]) == budget_05, "Table 2 B_on(0.5) mismatch")

        records = frontier_groups.get(key, [])
        ensure(
            sorted(record["total_cap"] for record in records) == list(range(2, b0 + 1)),
            f"saved causal frontier missing a Table 2 budget for {key}",
        )
        values = {
            record["total_cap"]: Fraction(record["certificate"]["delta"])
            for record in records
        }
        ensure(min(values[b] for b in values if b < b0) == Fraction(least_delta), "saved least delta mismatch")
        ensure(min(b for b, delta in values.items() if delta <= Fraction(1, 10)) == budget_01, "saved B_on(0.1) mismatch")
        ensure(min(b for b, delta in values.items() if delta <= Fraction(1, 2)) == budget_05, "saved B_on(0.5) mismatch")

    expected_table_three = {
        (8, 1, 3, 5): (6, "1/2", "1"),
        (8, 2, 3, 4): (6, "1/2", "1"),
        (10, 1, 4, 7): (8, "1/2", "1"),
        (10, 2, 4, 7): (8, "1/2", "1"),
        (10, 1, 3, 7): (8, "1/3", "1/2"),
        (12, 2, 3, 7): (8, "1/3", "1/2"),
        (12, 1, 4, 9): (10, "2/5", "2/3"),
        (14, 2, 4, 9): (10, "2/5", "2/3"),
    }
    ensure(len(table_three) == len(expected_table_three), "Table 3 row count changed")
    extra_groups: dict[tuple[int, int, int, int], dict[bool, dict]] = {}
    for record in extra["records"]:
        key = (record["horizon"], record["delay"], record["max_arrivals"], record["total_cap"])
        extra_groups.setdefault(key, {})[record["causal"]] = record
        certificate = record["certificate"]
        ensure(certificate["verified"] is True, "saved extra certificate is unverified")
        ensure(
            Fraction(certificate["coverage"]) + Fraction(certificate["delta"]) == 1,
            "saved extra coverage/delta mismatch",
        )
    for row in table_three:
        key = (int(row["H"]), int(row["D"]), int(row["m"]), int(row["B"]))
        ensure(key in expected_table_three, f"unexpected Table 3 row {key}")
        b0, delta_off, delta_on = expected_table_three[key]
        ensure(block_parameters(key[0], key[1], key[2])[3] == b0, "Table 3 Eq.20 B0 mismatch")
        ensure(row["delta_off"] == delta_off, "Table 3 offline delta mismatch")
        ensure(row["delta_on"] == delta_on, "Table 3 causal delta mismatch")
        records = extra_groups.get(key, {})
        ensure(set(records) == {False, True}, f"Table 3 certificate classes missing for {key}")
        ensure(records[False]["certificate"]["delta"] == delta_off, "saved Table 3 offline value mismatch")
        ensure(records[True]["certificate"]["delta"] == delta_on, "saved Table 3 causal value mismatch")
        ensure(records[False]["certificate"]["coverage"] == str(1 - Fraction(delta_off)), "saved Table 3 offline coverage mismatch")
        ensure(records[True]["certificate"]["coverage"] == str(1 - Fraction(delta_on)), "saved Table 3 causal coverage mismatch")

    return {
        "status": "PASS",
        "table_2_rows": len(table_one),
        "table_3_rows": len(table_three),
        "legacy_frontiers_loaded": len(frontiers),
        "extra_certificates_loaded": len(extra["records"]),
        "lp_regenerated": False,
        "mapping": "exact saved rational certificate values and Eq.20 B0",
    }


def check_corollary_4_zero_delay() -> tuple[dict, dict[tuple[int, int], dict[int, tuple[Fraction, Fraction]]]]:
    """Check Eq. (21) by counting actual subset containments through matching."""
    games = 0
    offline_pair_checks = 0
    causal_pair_checks = 0
    frontiers: dict[tuple[int, int], dict[int, tuple[Fraction, Fraction]]] = {}

    for horizon in range(1, 13):
        for max_arrivals in range(1, min(4, horizon) + 1):
            inputs = exact_inputs(horizon, max_arrivals)
            for budget in range(max_arrivals, horizon + 1):
                games += 1
                off = offline_schedules(horizon, budget)
                on = causal_schedules(horizon, max_arrivals, budget)

                off_counts = []
                for arrivals in inputs:
                    count = sum(
                        covers(arrivals, schedule, horizon, 0) for schedule in off
                    )
                    off_counts.append(count)
                    offline_pair_checks += len(off)
                expected_off_count = binom(horizon - max_arrivals, budget - max_arrivals)
                ensure(
                    all(count == expected_off_count for count in off_counts),
                    f"Eq.21 offline count failed H={horizon}, m={max_arrivals}, B={budget}",
                )
                off_value = Fraction(min(off_counts), len(off))
                expected_off = Fraction(binom(budget, max_arrivals), binom(horizon, max_arrivals))
                ensure(off_value == expected_off, "Eq.21 offline ratio failed")

                on_counts = []
                for arrivals in inputs:
                    count = sum(
                        covers(arrivals, schedule, horizon, 0) for schedule in on
                    )
                    on_counts.append(count)
                    causal_pair_checks += len(on)
                n = horizon - max_arrivals
                k = budget - max_arrivals
                j = min(max_arrivals, n)
                expected_on = Fraction(binom(k, j), binom(n, j))
                on_value = Fraction(min(on_counts), len(on))
                ensure(on_value == expected_on, "Eq.21 causal ratio failed")
                ensure(min(on_counts) == binom(n - j, k - j), "Eq.21 causal count failed")
                frontiers.setdefault((horizon, max_arrivals), {})[budget] = (
                    1 - off_value,
                    1 - on_value,
                )

    eq22_checks = 0
    for horizon in range(2, 13):
        for budget in range(1, horizon + 1):
            off_delta, on_delta = frontiers[(horizon, 1)][budget]
            expected_gap = Fraction(horizon - budget, horizon * (horizon - 1))
            ensure(on_delta - off_delta == expected_gap, "Eq.22 failed")
            eq22_checks += 1

    return (
        {
            "status": "PASS",
            "parameter_sets": games,
            "games": games,
            "scope": {
                "H": [1, 12],
                "m": "1..min(4,H)",
                "B": "m..H",
                "D": 0,
                "all_exact_m_inputs_and_exact_B_schedules": True,
            },
            "offline_pair_checks": offline_pair_checks,
            "causal_pair_checks": causal_pair_checks,
            "Eq21_checks": games * 2,
            "Eq22_checks": eq22_checks,
            "boundaries_included": ["B=m", "B=H", "H=m", "H>m"],
        },
        frontiers,
    )


def check_corollary_1(
    frontiers: dict[tuple[int, int], dict[int, tuple[Fraction, Fraction]]]
) -> dict:
    """Check the deterministic budget lift and D=0 threshold consequences."""
    parameter_sets = 0
    schedule_maps = 0
    covered_pairs = 0
    threshold_checks = 0
    sharpness_checks = 0

    # The schedule map is checked with actual interval matching for every
    # covered exact-m input.  This is the constructive part of (15).
    for horizon in range(1, 11):
        for max_arrivals in range(1, min(4, horizon) + 1):
            inputs = exact_inputs(horizon, max_arrivals)
            for delay in range(0, horizon + 3):
                for budget in range(max_arrivals, horizon + 1):
                    parameter_sets += 1
                    target = min(horizon, budget + max_arrivals)
                    for schedule in offline_schedules(horizon, budget):
                        lifted = lift_offline_schedule(schedule, horizon, max_arrivals)
                        schedule_maps += 1
                        ensure(len(lifted) == target, "Corollary 1 lift has wrong budget")
                        ensure(
                            set(terminal_slots(horizon, max_arrivals)) <= set(lifted),
                            "Corollary 1 lift lost terminal reserve",
                        )
                        for arrivals in inputs:
                            if covers(arrivals, schedule, horizon, delay):
                                covered_pairs += 1
                                ensure(
                                    covers(arrivals, lifted, horizon, delay),
                                    "Corollary 1 lift lost a covered input",
                                )

    # Use the independently counted Eq. (21) frontiers to check B_g(delta)
    # over all breakpoints and their adjacent midpoints.  The arbitrary-D
    # statement is supplied by the schedule map above; this is a concrete
    # exact threshold audit at the closed-form boundary.
    for (horizon, max_arrivals), frontier in frontiers.items():
        values = {Fraction(0), Fraction(1)}
        values.update(delta for pair in frontier.values() for delta in pair)
        ordered = sorted(values)
        values.update(
            (left + right) / 2
            for left, right in zip(ordered, ordered[1:])
        )
        for delta in sorted(values):
            off_budget = min(
                budget
                for budget, (off_delta, _) in frontier.items()
                if off_delta <= delta
            )
            on_budget = min(
                budget
                for budget, (_, on_delta) in frontier.items()
                if on_delta <= delta
            )
            ensure(0 <= on_budget - off_budget <= max_arrivals, "Eq.15 gap failed")
            ensure(
                on_budget <= min(horizon, off_budget + max_arrivals),
                "Eq.15 constructive upper bound failed",
            )
            threshold_checks += 1

    # The article's sharpness family is an exact threshold statement, not
    # merely an asymptotic claim.  Read both budgets from the independently
    # counted D=0 frontiers and check B_off=m, B_on=2m.
    for horizon in range(2, 13):
        for max_arrivals in range(1, min(4, horizon // 2) + 1):
            frontier = frontiers[(horizon, max_arrivals)]
            delta = Fraction(1) - Fraction(1, binom(horizon, max_arrivals))
            off_budget = min(
                budget
                for budget, (off_delta, _) in frontier.items()
                if off_delta <= delta
            )
            on_budget = min(
                budget
                for budget, (_, on_delta) in frontier.items()
                if on_delta <= delta
            )
            ensure(off_budget == max_arrivals, "Corollary 1 sharpness failed offline")
            ensure(on_budget == 2 * max_arrivals, "Corollary 1 sharpness failed causal")
            sharpness_checks += 1

    return {
        "status": "PASS",
        "scope": {
            "H": [1, 10],
            "m": "1..min(4,H)",
            "D": [0, 12],
            "B": "m..H",
            "exact_m_inputs": True,
        },
        "parameter_sets": parameter_sets,
        "offline_to_causal_schedule_maps": schedule_maps,
        "covered_input_pairs_preserved": covered_pairs,
        "Eq15_threshold_checks": threshold_checks,
        "Eq15_sharpness_checks": sharpness_checks,
        "class_inclusion_checked": True,
        "sharpness_target": {
            "construction": "D=0, H>=2m, delta=1-1/C(H,m), B_off=m and B_on=2m",
            "verified_separately": "corollary_4 and article_example checks",
        },
    }


def check_corollary_2() -> dict:
    """Check the random deletion injection behind Eqs. (16)--(19)."""
    parameter_sets = 0
    source_pairs = 0
    retention_trials = 0
    favorable_trials = 0
    rho_identity_checks = 0
    union_bound_checks = 0

    for horizon in range(2, 11):
        for max_arrivals in range(1, min(4, horizon // 2) + 1):
            inputs = exact_inputs(horizon, max_arrivals)
            for budget in range(2 * max_arrivals, horizon + 1):
                rho = Fraction(comb(budget - max_arrivals, max_arrivals), comb(budget, max_arrivals))
                left = Fraction(
                    comb(budget - max_arrivals, budget - 2 * max_arrivals),
                    comb(budget, budget - max_arrivals),
                )
                ensure(left == rho, "Eq.19 binomial identity failed")
                rho_identity_checks += 1
                ensure(1 - rho <= Fraction(max_arrivals * max_arrivals, budget), "Eq.18 union bound failed")
                union_bound_checks += 1

                for delay in range(0, horizon + 3):
                    parameter_sets += 1
                    for schedule in offline_schedules(horizon, budget):
                        for arrivals in inputs:
                            assignment = matching(arrivals, schedule, horizon, delay)
                            if assignment is None:
                                continue
                            source_pairs += 1
                            matched_services = {service for _, service in assignment}
                            denominator = 0
                            favorable = 0
                            for retained in position_subsets(budget, budget - max_arrivals):
                                # ``retained`` indexes the ordered slots of y.
                                kept = tuple(schedule[index] for index in retained)
                                transformed = transformed_schedule(
                                    kept, horizon, max_arrivals, budget
                                )
                                denominator += 1
                                retention_trials += 1
                                ensure(
                                    len(transformed) == budget
                                    and set(terminal_slots(horizon, max_arrivals)) <= set(transformed),
                                    "Eq.19 transformation left S_on(B)",
                                )
                                if matched_services <= set(kept):
                                    favorable += 1
                                    favorable_trials += 1
                                    ensure(
                                        covers(arrivals, transformed, horizon, delay),
                                        "Eq.19 retained matching was not preserved",
                                    )
                            expected_denominator = comb(budget, budget - max_arrivals)
                            expected_favorable = comb(
                                budget - max_arrivals, budget - 2 * max_arrivals
                            )
                            ensure(denominator == expected_denominator, "wrong deletion sample space")
                            ensure(favorable == expected_favorable, "wrong favorable deletion count")
                            ensure(
                                Fraction(favorable, denominator) == rho,
                                "pointwise rho coverage bound failed",
                            )

    return {
        "status": "PASS",
        "scope": {
            "H": [2, 10],
            "m": "1..min(4,floor(H/2))",
            "D": [0, 12],
            "B": "2m..H",
            "all_exact_m_inputs_and_exact_B_offline_schedules": True,
        },
        "parameter_sets": parameter_sets,
        "source_schedule_input_pairs_covered": source_pairs,
        "retention_trials": retention_trials,
        "favorable_retention_trials": favorable_trials,
        "Eq19_binomial_identity_checks": rho_identity_checks,
        "Eq18_union_bound_checks": union_bound_checks,
        "pointwise_injection_implies_v_on_ge_rho_v_off": True,
        "class_inclusion_implies_nonnegative_privacy_gap": True,
    }


def check_corollary_3() -> dict:
    """Check Eq. (20) and universal block schedules by actual matching."""
    parameter_sets = 0
    formula_checks = 0
    universal_input_checks = 0
    lower_bound_schedule_checks = 0
    large_delay_cases = 0
    b0_equals_m_cases = 0
    b0_equals_h_cases = 0

    for horizon in range(1, 13):
        for max_arrivals in range(1, min(4, horizon) + 1):
            for delay in range(0, horizon + 3):
                parameter_sets += 1
                length, full, remainder, b0 = block_parameters(
                    horizon, delay, max_arrivals
                )
                quotient, rem = divmod(horizon, delay + max_arrivals)
                expected_b0 = max_arrivals * quotient + min(max_arrivals, rem)
                ensure((length, full, remainder) == (delay + max_arrivals, quotient, rem), "Eq.20 decomposition failed")
                ensure(b0 == expected_b0, "Eq.20 budget formula failed")
                formula_checks += 1
                if delay >= horizon:
                    large_delay_cases += 1
                if b0 == max_arrivals:
                    b0_equals_m_cases += 1
                if b0 == horizon:
                    b0_equals_h_cases += 1

                schedule = block_schedule(horizon, delay, max_arrivals)
                ensure(len(schedule) == b0, "block schedule has wrong B0")
                ensure(
                    set(terminal_slots(horizon, max_arrivals)) <= set(schedule),
                    "block schedule lacks the terminal reserve",
                )
                for arrivals in bounded_inputs(horizon, max_arrivals):
                    universal_input_checks += 1
                    ensure(
                        covers(arrivals, schedule, horizon, delay),
                        f"block schedule failed H={horizon},m={max_arrivals},D={delay},x={arrivals}",
                    )

                tests = block_tests(horizon, delay, max_arrivals)
                ensure(len(tests) == full + (1 if remainder else 0), "wrong block test count")
                if b0 > 0:
                    for candidate in offline_schedules(horizon, b0 - 1):
                        lower_bound_schedule_checks += 1
                        ensure(
                            not all(
                                covers(test, candidate, horizon, delay) for test in tests
                            ),
                            "a B0-1 schedule covered every block witness",
                        )

    return {
        "status": "PASS",
        "scope": {
            "H": [1, 12],
            "m": "1..min(4,H)",
            "D": [0, 14],
            "all_inputs_of_weight_at_most_m": True,
        },
        "parameter_sets": parameter_sets,
        "Eq20_formula_checks": formula_checks,
        "block_schedule_universal_input_checks": universal_input_checks,
        "B0_minus_1_schedule_checks": lower_bound_schedule_checks,
        "large_delay_cases": large_delay_cases,
        "B0_equals_m_cases": b0_equals_m_cases,
        "B0_equals_H_cases": b0_equals_h_cases,
        "exact_block_witnesses_used": True,
    }


def check_corollary_5() -> dict:
    """Check the Eq. (24)--(26) threshold and its strict boundary example.

    The no-savings checker in the release covers H<=9 and every m.  This
    targeted extension uses H=10..12 and m<=4, plus the exact H=2 boundary.
    """
    parameter_sets = 0
    threshold_schedule_checks = 0
    b_lt_m_checks = 0
    threshold_equal_checks = 0
    witness_test_checks = 0
    domain_h = range(10, 13)

    for horizon in domain_h:
        for max_arrivals in range(1, min(4, horizon) + 1):
            for delay in range(0, horizon + 3):
                parameter_sets += 1
                _, _, _, b0 = block_parameters(horizon, delay, max_arrivals)
                k = ceil(horizon / (delay + max_arrivals))
                tests = block_tests(horizon, delay, max_arrivals)
                ensure(len(tests) == k, "Eq.24 K does not match block witnesses")
                witness_test_checks += len(tests)
                threshold = Fraction(1, k)

                for budget in range(max_arrivals, b0):
                    for schedule in offline_schedules(horizon, budget):
                        threshold_schedule_checks += 1
                        ensure(
                            any(not covers(test, schedule, horizon, delay) for test in tests),
                            "Eq.24 witness union was covered below B0",
                        )
                    for schedule in causal_schedules(horizon, max_arrivals, budget):
                        threshold_schedule_checks += 1
                        ensure(
                            any(not covers(test, schedule, horizon, delay) for test in tests),
                            "Eq.24 causal witness union was covered below B0",
                        )

                # At B0 the explicit block schedule covers every admissible
                # input, so both classes have B_g(delta)=B0 for every delta
                # strictly below 1/K.  Check two exact representatives.
                schedule = block_schedule(horizon, delay, max_arrivals)
                ensure(len(schedule) == b0, "Eq.25 block schedule budget mismatch")
                ensure(
                    all(
                        covers(arrivals, schedule, horizon, delay)
                        for arrivals in bounded_inputs(horizon, max_arrivals)
                    ),
                    "Eq.25 B0 schedule failed",
                )
                for delta in (Fraction(0), threshold / 2):
                    ensure(delta < threshold, "internal threshold representative error")
                    threshold_equal_checks += 2

                # Delivery itself rules out every B<m, independently of the
                # block union argument.
                full_input = tuple(range(max_arrivals))
                for budget in range(0, max_arrivals):
                    b_lt_m_checks += 1
                    for schedule in offline_schedules(horizon, budget):
                        ensure(
                            not covers(full_input, schedule, horizon, delay),
                            "B<m schedule delivered all m packets",
                        )

    # Eq. (25) is intentionally strict.  At equality the H=2,m=1,D=0,
    # offline game with B=1 has the exact uniform value 1/2.
    horizon, max_arrivals, delay, budget = 2, 1, 0, 1
    inputs = exact_inputs(horizon, max_arrivals)
    schedules = offline_schedules(horizon, budget)
    counts = [
        sum(covers(arrivals, schedule, horizon, delay) for schedule in schedules)
        for arrivals in inputs
    ]
    boundary_value = Fraction(min(counts), len(schedules))
    ensure(boundary_value == Fraction(1, 2), "Eq.25 equality boundary value failed")
    _, _, _, boundary_b0 = block_parameters(horizon, delay, max_arrivals)
    ensure(boundary_b0 == 2 and Fraction(1, 2) == Fraction(1, 2), "bad Eq.25 boundary parameters")

    return {
        "status": "PASS",
        "scope": {
            "new_extension_H": [10, 12],
            "m": "1..min(4,H)",
            "D": [0, 14],
            "all_exact_B_schedules_below_B0": True,
        },
        "parameter_sets": parameter_sets,
        "Eq24_block_witness_tests": witness_test_checks,
        "below_B0_offline_and_causal_schedule_checks": threshold_schedule_checks,
        "Eq25_strict_threshold_representatives": threshold_equal_checks,
        "B_lt_m_delivery_checks": b_lt_m_checks,
        "boundary_certificate": {
            "H": 2,
            "m": 1,
            "D": 0,
            "B": 1,
            "B0": boundary_b0,
            "K": 2,
            "delta_equals_1_over_K": True,
            "delta_off": "1/2",
            "B_off_at_equality": 1,
            "B_on_at_equality": 2,
        },
        "strict_inequality_in_Eq25_checked": True,
    }


def check_article_example() -> dict:
    """Verify Eq. (23), its dual witnesses, Eq. (22)'s role, and B0=6."""
    horizon, delay, max_arrivals, budget = 8, 1, 2, 4
    causal_policy_raw = {
        "01100011": "1/3",
        "01001011": "1/3",
        "00011011": "1/3",
    }
    causal_dual_raw = {
        "11000000": "1/3",
        "10010000": "1/3",
        "00110000": "1/3",
    }
    offline_policy_raw = {
        "11000011": "1/9",
        "01101100": "2/9",
        "01101001": "1/9",
        "01100011": "1/9",
        "01011001": "1/9",
        "01001011": "1/9",
        "00011011": "1/9",
        "00010111": "1/9",
    }
    offline_dual_raw = {
        "11000000": "2/9",
        "01010000": "1/9",
        "01000001": "1/9",
        "00011000": "2/9",
        "00010001": "1/9",
        "00000011": "2/9",
    }

    def law(raw: dict[str, str]) -> dict[tuple[int, ...], Fraction]:
        result = {parse_bits(trace): Fraction(weight) for trace, weight in raw.items()}
        ensure(sum(result.values(), Fraction(0)) == 1, "example law is not normalized")
        return result

    causal_policy = law(causal_policy_raw)
    causal_dual = law(causal_dual_raw)
    offline_policy = law(offline_policy_raw)
    offline_dual = law(offline_dual_raw)
    ensure(all(len(item) == budget for item in causal_policy), "Eq.23 policy budget failed")
    ensure(all(set(terminal_slots(horizon, max_arrivals)) <= set(item) for item in causal_policy), "Eq.23 reserve failed")
    ensure(all(len(item) == budget for item in offline_policy), "offline example budget failed")
    ensure(all(len(item) == max_arrivals for item in causal_dual), "causal dual input weight failed")
    ensure(all(len(item) == max_arrivals for item in offline_dual), "offline dual input weight failed")

    all_inputs = bounded_inputs(horizon, max_arrivals)
    causal_masses = [weighted_coverage(causal_policy, arrivals, horizon, delay) for arrivals in all_inputs]
    ensure(min(causal_masses) == Fraction(1, 3), "Eq.23 causal primal certificate failed")
    ensure(
        max(weighted_schedule_mass(causal_dual, schedule, horizon, delay) for schedule in causal_schedules(horizon, max_arrivals, budget))
        == Fraction(1, 3),
        "Eq.23 causal dual certificate failed",
    )
    ensure(
        min(weighted_coverage(offline_policy, arrivals, horizon, delay) for arrivals in exact_inputs(horizon, max_arrivals))
        == Fraction(5, 9),
        "offline example primal certificate failed",
    )
    ensure(
        max(weighted_schedule_mass(offline_dual, schedule, horizon, delay) for schedule in offline_schedules(horizon, budget))
        == Fraction(5, 9),
        "offline example dual certificate failed",
    )

    witness_coverage = {
        trace: [
            bit_string(schedule, horizon)
            for schedule in causal_schedules(horizon, max_arrivals, budget)
            if covers(parse_bits(trace), schedule, horizon, delay)
        ]
        for trace in causal_dual_raw
    }
    witness_sets = [set(items) for items in witness_coverage.values()]
    ensure(
        all(
            not (left & right)
            for index, left in enumerate(witness_sets)
            for right in witness_sets[index + 1 :]
        ),
        "Eq.23 witness overlap failed",
    )

    # The two concrete executions printed immediately after Eq. (23) are
    # checked by a fresh FIFO implementation of Algorithm 1.  This is a
    # separate operational anchor from the certificate/matching checks above.
    example_input = "11000000"
    base_a = simulate_algorithm1(example_input, "01100011", delay=1, cap=4)
    base_b = simulate_algorithm1(example_input, "00011011", delay=1, cap=4)
    ensure(base_a["output"] == "01100011", "Algorithm 1 first example output changed")
    ensure(base_b["output"] == "01100000", "Algorithm 1 switched example output changed")
    ensure(base_a["services"] == [[0, 1], [1, 2]], "Algorithm 1 first service trace changed")
    ensure(base_b["services"] == [[0, 1], [1, 2]], "Algorithm 1 switched service trace changed")
    ensure(base_a["switch"] is None and base_b["switch"] == 1, "Algorithm 1 switch trace changed")
    ensure(base_a["count"] == 4 and base_b["count"] == 2, "Algorithm 1 output counts changed")
    ensure(base_a["all_deadlines_met"] and base_b["all_deadlines_met"], "Algorithm 1 deadline check failed")
    ensure(base_a["cap_respected"] and base_b["cap_respected"], "Algorithm 1 cap check failed")

    b6 = block_schedule(8, 1, 2)
    ensure(len(b6) == 6 and all(covers(x, b6, 8, 1) for x in all_inputs), "Eq.20 B=6 example failed")

    return {
        "status": "PASS",
        "parameters": {"H": horizon, "D": delay, "m": max_arrivals, "B": budget},
        "causal_schedule_columns": len(causal_schedules(horizon, max_arrivals, budget)),
        "offline_schedule_columns": len(offline_schedules(horizon, budget)),
        "input_rows_exact_m": len(exact_inputs(horizon, max_arrivals)),
        "input_rows_at_most_m": len(all_inputs),
        "Eq23_causal_policy_value": "1/3",
        "Eq23_causal_dual_value": "1/3",
        "offline_example_value": "5/9",
        "offline_example_delta": "4/9",
        "Eq23_witness_coverage": witness_coverage,
        "algorithm1_examples": {
            "input": example_input,
            "delay": 1,
            "cap": 4,
            "base_01100011": base_a,
            "base_00011011": base_b,
            "implementation": "independent FIFO switch-to-service simulation",
        },
        "B0_schedule_at_B6": bit_string(b6, horizon),
        "B0_schedule_covers_all_inputs": True,
        "matching_implementation": "fresh augmenting-path injection",
    }


def as_jsonable(value):
    if isinstance(value, Fraction):
        return str(value)
    if isinstance(value, dict):
        return {str(key): as_jsonable(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [as_jsonable(item) for item in value]
    return value


def main() -> None:
    reject_optimized_mode()
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    output_dir = args.output_dir.expanduser().resolve()
    output_dir.mkdir(parents=True, exist_ok=True)

    code_path = Path(__file__).resolve()
    code_sha256_before = sha256(code_path)
    saved_input_sha256_before = saved_input_hashes()

    zero_delay, frontiers = check_corollary_4_zero_delay()
    corollary_1 = check_corollary_1(frontiers)
    corollary_2 = check_corollary_2()
    corollary_3 = check_corollary_3()
    corollary_5 = check_corollary_5()
    article_example = check_article_example()
    privacy_interpretation = check_privacy_interpretation()
    article_sizes = check_article_sizes()
    saved_table_mapping = check_saved_table_mapping()

    code_sha256_after = sha256(code_path)
    saved_input_sha256_after = saved_input_hashes()
    ensure(code_sha256_before == code_sha256_after, "checker source changed during the run")
    ensure(
        saved_input_sha256_before == saved_input_sha256_after,
        "saved input changed during the run",
    )

    report = {
        "status": "PASS",
        "checker": "corollaries_check.py",
        "created_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_directory": str(ROOT),
        "output_directory": str(output_dir),
        "code_sha256": code_sha256_after,
        "code_sha256_before": code_sha256_before,
        "code_sha256_after": code_sha256_after,
        "saved_input_sha256": saved_input_sha256_after,
        "saved_input_sha256_before": saved_input_sha256_before,
        "saved_input_sha256_after": saved_input_sha256_after,
        "source_unchanged": True,
        "optimizer_imported": False,
        "existing_checker_imported": False,
        "arithmetic": "fractions.Fraction",
        "matching": "fresh augmenting-path injection over actual interval edges",
        "corollaries": {
            "corollary_1_budget": corollary_1,
            "corollary_2_privacy_gap": corollary_2,
            "corollary_3_full_indistinguishability": corollary_3,
            "corollary_4_zero_delay": zero_delay,
            "corollary_5_no_savings_threshold": corollary_5,
        },
        "article_example": article_example,
        "privacy_interpretation": privacy_interpretation,
        "article_sizes": article_sizes,
        "saved_table_mapping": saved_table_mapping,
        "preexisting_coverage": {
            "saved_certificates": "79 legacy + 16 r4 exact certificates; 10,356 primal rows and 39,931 dual columns",
            "queue_algorithm": "H=1..7, all m<=B<=H, D=0..H with 45,622 input/schedule pairs, 4,069 switches, 347,870 prefix comparisons, and 20,532 TV checks",
            "zero_delay": "240 games for H=1..8, all m<=B<=H, both classes; 4,518 primal rows and 2,295 dual columns",
            "saved_quantitative": "43 saved budget comparisons and 66 saved fixed-budget privacy-gap comparisons",
            "no_savings": "375 parameter sets for H=1..9, every m, D=0..H+1, including the strict-threshold boundary",
            "explicit_example": "existing independent certificate checker already checks the causal 28-by-15 example",
        },
        "added_verification": {
            "corollary_1": "actual-input preservation under the B -> min(H,B+m) terminal-reserve lift, plus exact B_g threshold breakpoints and midpoints",
            "corollary_2": "pointwise random-retention injection, Eq.19 identity, and Eq.18 union bound over all listed bounded source pairs",
            "corollary_3": "Eq.20 decomposition, universal block schedule and B0-1 witness schedules through fresh matching; extends to H<=12, m<=4 and D<=H+2",
            "corollary_4": "actual subset coverage counts for Eq.21 and Eq.22 through H<=12, m<=4",
            "corollary_5": "new extension H=10..12, m<=4, D<=H+2 with all exact-B schedules below B0, plus equality boundary",
            "article_example": "rechecks Eq.23 three-schedule/three-input causal certificate, 5/9 offline certificate, and B0=6 example",
            "privacy_interpretation": "exact TV triangle, event characterization, identical/disjoint laws, and equal-prior randomized-test success on finite laws",
            "article_sizes": "exact C(48,8)=377348994 and its H=50,m=2,B=10 specialization",
            "saved_table_mapping": "read-only exact mapping of TABLE-1/TABLE-3 rows to FRONTIERS/EXTRA-CERTIFICATES; no LP regeneration",
        },
        "limitations": (
            "Finite checks certify the displayed constructions, injections, and bounded exhaustive domains. "
            "They do not replace the universal Lean proofs or solve the covering LP anew."
        ),
    }
    destination = output_dir / "COROLLARIES-CHECK.json"
    destination.write_text(json.dumps(as_jsonable(report), indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({
        "status": report["status"],
        "output": str(destination),
        "corollary_parameter_sets": {
            key: value["parameter_sets"]
            for key, value in report["corollaries"].items()
            if "parameter_sets" in value
        },
        "article_example": report["article_example"]["status"],
        "privacy_interpretation": report["privacy_interpretation"]["status"],
        "article_sizes": report["article_sizes"]["status"],
        "saved_table_mapping": report["saved_table_mapping"]["status"],
    }, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
