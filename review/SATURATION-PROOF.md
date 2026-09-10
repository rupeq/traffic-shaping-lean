# Saturation lemmas for the converse

The module `formal/TrafficShaping/Saturation.lean` contains only finite-set
facts over the definitions in `TrafficShaping.Model`; `Model.lean` is left
unchanged.  No probability, mechanism representation, online repair, or
algorithmic efficiency is assumed here.

The standing hypotheses are the natural ones for a terminal reserve:
`m ≤ H`, and, where a budget is used, `m ≤ B ≤ H`.

## Terminal and prefix partition

`terminal H m` is the set of the last `m` elements of `Fin H`.  The theorem
`terminal_card` proves

```text
(terminal H m).card = m.
```

The proof builds an explicit finite equivalence between `Fin m` and the
subtype of terminal slots.  A terminal slot `H - m + i` is below `H` because
`i < m ≤ H`.  The inverse subtracts `H-m`; the two inverse laws are natural
number arithmetic under the terminal membership inequality.

`prefix_disjoint_terminal` proves that slots below `H-m` and terminal slots
are disjoint.  `prefix_terminal_partition` and
`prefix_terminal_card_partition` state the corresponding partition of any
trace:

```text
tracePrefix (H-m) y ∪ (y ∩ terminal H m) = y
card(prefix) + card(y ∩ terminal) = card(y).
```

`union_terminal_eq_prefix_union_terminal` records the useful saturation
identity

```text
y ∪ terminal H m = tracePrefix (H-m) y ∪ terminal H m.
```

Thus adding the whole terminal reserve costs exactly the missing prefix
count plus `m`, even when `y` already contains some terminal slots.

## Finite cardinal saturation

`exists_trace_superset_card_eq` is the basic finite extension lemma.  A trace
of cardinality at most `B` can be enlarged to cardinality exactly `B` when
`B ≤ H`; it uses Mathlib's finite `exists_superset_card_eq` theorem on
`Fin H`.

`extendTraceToCard` is a `Classical.choose` witness with the two specifications
`extendTraceToCard_subset` and `extendTraceToCard_card`.  `saturateOff` packages
the same witness as an `OffSchedule` and exposes `saturateOff_subset` and
`saturateOff_card`.

`exists_offSchedule` follows by extending the empty trace.  `exists_onSchedule`
extends the terminal trace, using `terminal_card`, so it proves nonemptiness
of `OnSchedule H m B` for `m ≤ B ≤ H`.

## Causal terminal saturation

If

```text
(tracePrefix (H-m) y).card ≤ B-m,
```

then `exists_onSchedule_superset` enlarges `y` to a trace of cardinality `B`
that contains every terminal slot.  The proof first adds the terminal set;
the partition identity shows that this intermediate trace has cardinality at
most `B`, and finite saturation supplies the remaining slots.  The
noncomputable `saturateOn` packages the witness as an `OnSchedule`; its
specifications are `saturateOn_subset`, `saturateOn_terminal_subset`, and
`saturateOn_card`.

This is a support transformation only.  It does not claim that an online
mechanism can observe the future or perform this extension while running.

## Full-input completion

`exists_fullInput_superset` extends every `Input H m` to a `FullInput H m`
containing it, because `x.card ≤ m ≤ H`.  `extendInputToFull` and
`extendInputToFull_subset` provide a choice witness and its specification.

## Terminal-input converse lemma

`terminal_subset_of_feasible` proves that if a trace is feasible for the input
whose arrivals are exactly the terminal slots, then it contains every
terminal slot.  For each terminal arrival, the release-time inequality forces
its assigned service slot to be terminal as well.  The assignment therefore
induces an injective self-map of the finite subtype of terminal slots.
`Finite.surjective_of_injective` makes this map surjective, so every terminal
slot occurs in the output trace.

Finally, `prefix_card_le_sub_of_terminal_feasible` combines that inclusion
with the partition count.  If `y.card ≤ B` and `y` is feasible for the
terminal input, then

```text
card (tracePrefix (H-m) y) ≤ B-m.
```

This is the exact finite support fact needed before transferring the
empty-prefix event through causality.

## Verification

The module builds with the cached Lean/Mathlib environment using:

```text
/private/tmp/lean-4.33.1-darwin_aarch64/bin/lake build TrafficShaping.Saturation
```

The successful build contains no `sorry`, `axiom`, `unsafe`, or
`native_decide`.  The only noncomputable definitions are the explicitly
documented `Classical.choose` saturation witnesses.
