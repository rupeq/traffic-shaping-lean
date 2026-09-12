#!/usr/bin/env python3
"""Generate the kernel-checked Lean table certificate module.

The JSON files contain exact rational weights.  This script clears all
denominators, emits finite weighted supports, and delegates every row/column
check to the executable certificate checker in ``CertificateHelpers``.
"""

from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction
from pathlib import Path


def parse_fraction(value: str | int | float) -> Fraction:
    return Fraction(str(value))


def lcm(left: int, right: int) -> int:
    return left * right // math.gcd(left, right)


def trace_literal(bits: str) -> str:
    slots = [str(index) for index, bit in enumerate(bits) if bit == "1"]
    return "{" + ", ".join(slots) + "}" if slots else "∅"


def certificate_scale(certificate: dict) -> int:
    scale = 1
    for weights in (
        {"coverage": certificate["coverage"]},
        certificate["schedule_weights"],
        certificate["input_weights"],
    ):
        for value in weights.values():
            scale = lcm(scale, parse_fraction(value).denominator)
    return scale


def weighted_item(
    bits: str,
    kind: str,
    horizon: int,
    arrivals: int,
    budget: int,
    causal: bool,
    weight: int,
) -> str:
    trace = trace_literal(bits)
    if kind == "schedule":
        if causal:
            value = (
                f"(⟨{trace}, by decide +kernel, by decide +kernel⟩ : "
                f"OnSchedule {horizon} {arrivals} {budget})"
            )
        else:
            value = (
                f"(⟨{trace}, by decide +kernel⟩ : "
                f"OffSchedule {horizon} {budget})"
            )
    else:
        value = (
            f"(⟨{trace}, by decide +kernel⟩ : "
            f"FullInput {horizon} {arrivals})"
        )
    return f"({value}, {weight})"


def partition_check(
    kind: str, horizon: int, free_slots: int, cardinality: int, support_size: int
) -> str:
    """Bound each kernel reduction by splitting complementary slot predicates.

    The cardinality calculation only selects proof granularity.  Lean's generic
    partition theorem proves that the two children cover the complete parent,
    and Lean independently checks every emitted leaf.
    """
    def render(slot: int, selected: int, indent: int) -> list[str]:
        remaining = cardinality - selected
        count = (
            math.comb(free_slots - slot, remaining)
            if 0 <= remaining <= free_slots - slot
            else 0
        )
        prefix = " " * indent
        if count * support_size <= 2048 or slot == free_slots:
            return [prefix + "decide +kernel"]
        lines = [
            prefix + f"refine {kind}CheckedOnFinset_partition _ _ _ _ "
            f"(fun x => ({slot} : Fin {horizon}) ∈ x.1) ?_ ?_"
        ]
        for next_selected in (selected + 1, selected):
            lines.append(prefix + "·")
            lines.extend(render(slot + 1, next_selected, indent + 2))
        return lines

    return "(by\n" + "\n".join(render(0, 0, 6)) + ")"


def render_theorem(record: dict) -> str:
    horizon = record["horizon"]
    delay = record["delay"]
    arrivals = record["max_arrivals"]
    budget = record["total_cap"]
    causal = record["causal"]
    certificate = record["certificate"]
    scale = certificate_scale(certificate)
    coverage = parse_fraction(certificate["coverage"])
    numerator = coverage * scale
    assert numerator.denominator == 1

    mode = "on" if causal else "off"
    theorem_name = (
        f"certificate_value_{mode}_H{horizon}_m{arrivals}_B{budget}_D{delay}"
    )
    value_proofs = "(by decide +kernel) (by decide +kernel)" if causal else "(by decide +kernel)"
    schedule_type = (
        f"OnSchedule {horizon} {arrivals} {budget}"
        if causal
        else f"OffSchedule {horizon} {budget}"
    )
    schedule_items = ",\n      ".join(
        weighted_item(
            bits,
            "schedule",
            horizon,
            arrivals,
            budget,
            causal,
            (parse_fraction(weight) * scale).numerator,
        )
        for bits, weight in certificate["schedule_weights"].items()
    )
    input_items = ",\n      ".join(
        weighted_item(
            bits,
            "input",
            horizon,
            arrivals,
            budget,
            False,
            (parse_fraction(weight) * scale).numerator,
        )
        for bits, weight in certificate["input_weights"].items()
    )
    row_check = partition_check(
        "rows", horizon, horizon, arrivals, len(certificate["schedule_weights"])
    )
    col_check = partition_check(
        "cols", horizon, horizon - arrivals if causal else horizon,
        budget - arrivals if causal else budget,
        len(certificate["input_weights"]),
    )

    lines = [
        f"theorem {theorem_name} :",
        f"    {mode}GameValue {horizon} {arrivals} {budget} {delay} "
        f"(by decide +kernel) {value_proofs} = ({certificate['coverage']} : ℝ) := by",
        f"  let schedules : Finset ({schedule_type} × ℕ) :=",
        f"    {{ {schedule_items} }}",
        f"  let inputs : Finset (FullInput {horizon} {arrivals} × ℕ) :=",
        f"    {{ {input_items} }}",
        f"  have hs : (∑ p ∈ schedules, p.2) = {scale} := by decide +kernel",
        f"  have hi : (∑ p ∈ inputs, p.2) = {scale} := by decide +kernel",
        f"  let rows := fullInputEnum {horizon} {arrivals}",
        f"  have hrows : rows = Finset.univ := fullInputEnum_eq_univ {horizon} {arrivals}",
    ]
    if causal:
        lines.extend(
            [
                f"  let cols := optimizedOnScheduleEnum {horizon} {arrivals} {budget} "
                "(by decide +kernel) (by decide +kernel)",
                "  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ "
                "(by decide +kernel) (by decide +kernel)",
                f"  have h := on_certificate_value (H := {horizon}) "
                f"(m := {arrivals}) (B := {budget}) (D := {delay})",
                f"    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules {scale} hs "
                f"(by decide +kernel) {numerator.numerator} inputs hi",
                f"    rows hrows {row_check}",
                f"    cols hcols {col_check}",
            ]
        )
    else:
        lines.extend(
            [
                f"  let cols := offScheduleEnum {horizon} {budget}",
                f"  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ {horizon} {budget}",
                f"  have h := off_certificate_value (H := {horizon}) "
                f"(m := {arrivals}) (B := {budget}) (D := {delay})",
                f"    (by decide +kernel) (by decide +kernel) schedules {scale} hs (by decide +kernel) "
                f"{numerator.numerator} inputs hi",
                f"    rows hrows {row_check}",
                f"    cols hcols {col_check}",
            ]
        )
    lines.extend(["  norm_num at h ⊢", "  exact h", ""])
    return "\n".join(lines)


def load_records(root: Path) -> list[dict]:
    frontiers = json.loads(
        (root / "computations/FRONTIERS.json").read_text()
    )["records"]
    extras = json.loads(
        (root / "computations/EXTRA-CERTIFICATES.json").read_text()
    )["records"]
    records = frontiers + extras
    assert len(records) == 95, len(records)
    keys = [
        (
            record["horizon"],
            record["max_arrivals"],
            record["total_cap"],
            record["delay"],
            record["causal"],
        )
        for record in records
    ]
    assert len(set(keys)) == len(keys), "duplicate theorem keys"
    return records


def render_module(records: list[dict]) -> str:
    pieces = [
        "import TrafficShaping.CertificatePartitions",
        "import TrafficShaping.CertificateOnEnumeration",
        "",
        "-- Elaborate these expensive closed certificates sequentially.",
        "set_option Elab.async false",
        "",
        "namespace TrafficShaping",
        "",
        "open scoped BigOperators",
        "",
        "set_option maxHeartbeats 100000000",
        "set_option maxRecDepth 1000000",
        "",
        "/- Each theorem replays one independently checked rational primal/dual",
        "   certificate over the complete finite input and schedule types. -/",
        "",
    ]
    pieces.extend(render_theorem(record) for record in records)
    pieces.append("end TrafficShaping")
    return "\n".join(pieces) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="traffic-shaping-lean repository root",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=None,
        help="output Lean path (defaults to formal/TrafficShaping/TableCertificates.lean)",
    )
    args = parser.parse_args()
    root = args.root.resolve()
    output = args.output or root / "formal/TrafficShaping/TableCertificates.lean"
    output.write_text(render_module(load_records(root)))
    print(f"wrote {output} ({len(load_records(root))} theorems)")


if __name__ == "__main__":
    main()
