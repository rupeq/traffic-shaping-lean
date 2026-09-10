# Semantic converse proof record

`formal/TrafficShaping/Mechanism.lean` and
`formal/TrafficShaping/Converse.lean` contain the support-based converse.  The
argument is stated for an arbitrary finite law on complete binary traces; it
does not use a random-seed representation, a state machine, or an online
algorithm.

## Mechanism interface

For parameters `H`, `m`, `B`, and `D`, a `Mechanism` supplies

```text
law       : Input H m → Law (Trace H)
feasible  : positive output mass implies Feasible D input output
support_cap : positive output mass implies output.card ≤ B
```

`Causal M` says that two admissible inputs with the same arrival prefix at
time `t` induce equal laws after mapping complete traces through
`tracePrefix t`.  This is a semantic prefix-law condition, so it applies to
stateful implementations once they are shown to induce the same finite law.

`Private M ε δ` records the two event inequalities between every nonempty
admissible input and the empty input.  This is the exact privacy direction
used by the lower bound: the active law has zero mass on the complement of an
event, so `Law.forbidden_event` bounds the empty-law mass of that complement.

The file also defines `feasibleEvent`, the generic `coverageMatrix`, and the
two finite matrices used by the converse:

```text
offMatrix H m B D : FullInput H m → OffSchedule H B → ℝ
onMatrix  H m B D : FullInput H m → OnSchedule H m B → ℝ
```

`coverageMatrix_eq_mass` identifies matrix coverage under a law with the mass
of the corresponding feasible schedule event.  This is the bridge from the
semantic support argument to the finite game in `Game.lean`.

## Active-event mass

For a full input `x`, let `E_x` be the set of traces feasible for `x`.  The
active law `M.law x` assigns zero mass to `E_xᶜ` by the support feasibility
condition.  Applying privacy to `x` and the empty input gives

```text
1 - δ ≤ (M.law (emptyInput H m)).mass E_x.
```

The proof is finite and event-wise.  It does not assume that the empty law is
feasible for `x`, and it does not use any privacy parameter simplification;
the finite real `ε` disappears because the active event-complement mass is
zero in the second privacy inequality.

## Noncausal saturation

`offSaturator` maps every trace to an exact-cardinality `OffSchedule H B`.
When an input trace has positive empty-law mass, the mechanism cap gives
`y.card ≤ B`; `saturateOff` therefore exists and contains `y`.  Feasibility is
monotone in the output, so a trace in `E_x` remains feasible after saturation.

`coverage_lower_after_map` packages the finite push-forward argument: if a
mass `1 - δ` event is mapped into the feasible schedule event, the resulting
schedule law covers the same row by at least `1 - δ`.  Applying this to every
full input produces a law `q` on exact-cardinality schedules with

```text
1 - δ ≤ worst (offMatrix H m B D) q.
```

`Game.worst_le_value` then yields the checked theorem

```text
1 - value (offMatrix H m B D) ≤ δ.
```

The theorem result contains local `Nonempty` witnesses for `FullInput H m`
and `OffSchedule H B`, constructed from `m ≤ H` and `B ≤ H`.  This makes the
`value` and `worst` instances explicit at the theorem boundary while keeping
the user-facing hypotheses arithmetic.

## Causal terminal-reserve saturation

For the causal bound, compare the terminal full input with the empty input at
time `H - m`.  Their arrival prefixes are both empty, so causality gives equal
prefix laws.  Every positive terminal-input output is feasible for the
terminal input and has cardinality at most `B`.  The finite matching lemma in
`Saturation.lean` forces it to contain the complete terminal reserve, and the
prefix partition then gives

```text
card (tracePrefix (H-m) y) ≤ B - m.
```

The corresponding bad-prefix event has zero terminal-law mass and therefore
zero empty-law prefix mass.  A positive point mass of the empty law pushes
forward to a positive point mass of the prefix law, so every positive empty
law output satisfies the same prefix cap.

`onSaturator` now extends each positive trace to an exact-cardinality schedule
that contains the terminal reserve.  It preserves every feasible trace by
output monotonicity, and the same event push-forward lemma gives a law `q` on
`OnSchedule H m B` with row coverage at least `1 - δ`.  The resulting theorem
is

```text
1 - value (onMatrix H m B D) ≤ δ.
```

This saturation is a proof-level support transformation.  It does not claim
that an online mechanism can see future arrivals or carry out the extension
while running.

## Verification

The modules compile with Lean 4.33.1 and mathlib v4.33.1 using:

```text
cd /Users/artem.derevago/master_thesis/traffic-shaping-lean/formal
/private/tmp/lean-4.33.1-darwin_aarch64/bin/lake env lean TrafficShaping/Mechanism.lean
/private/tmp/lean-4.33.1-darwin_aarch64/bin/lake env lean TrafficShaping/Converse.lean
/private/tmp/lean-4.33.1-darwin_aarch64/bin/lake env lean TrafficShaping.lean
```

All three commands exit successfully.  The converse file contains no
unfinished proof placeholders.  The only noncomputable choices are the
finite saturation functions supplied by `Saturation.lean`; they expose the
subset and exact-cardinality specifications used by the proof.
