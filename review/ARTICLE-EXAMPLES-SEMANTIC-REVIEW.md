# Semantic review of the Eq. (23) article examples

This review compares `formal/TrafficShaping/ArticleExamples.lean` with the
r9 manuscript's Section 5.3 example (`manuscript.md:249–255`) and the
finite-game definitions imported by that file. It covers the executable scan,
the causal and noncausal rational certificates, the reduction from exact
two-arrival rows to all inputs of weight at most two, and the two concrete
executions printed after Eq. (23).

## Verdict

**PASS for the Eq. (23) causal certificate, the independently stated
noncausal certificate, and the resulting optima.** The source constructs the
same three causal schedules and three causal dual inputs as the manuscript,
checks every exact row and every schedule column in the finite Lean types, and
uses `matching_certificate` to obtain the exact values (1/3) and (5/9).
The `MainTheorem` identities then derive (2/3) and (4/9) for every finite
nonnegative epsilon.

**PASS for the executable matcher bridge.** `articleScanFeasible` is a
structurally recursive wrapper around the sorted two-pointer scan. Its fuel is
provably sufficient for every sorted input list, and
`articleScanFeasible_true_iff` identifies its Boolean result with the semantic
injective-assignment predicate used by the game matrix.

**PASS for the concrete examples.** The base execution preserves
`01100011`; the third schedule switches at slot 1 and produces `01100000`.
The added state-level claims identify service pairs `(0,1)` and `(1,2)`, the
first service-mode state, and output cardinalities 4 and 2. These are direct
kernel reductions of `executeState`/`execute`, rather than comments about an
uninspected simulator.

## Finite universes and representation

At (H=8,m=2,B=4), `FullInput 8 2` is the subtype of traces with exactly two
arrival slots. It has **28 rows**, as **C(8,2)**. The causal schedule subtype
`OnSchedule 8 2 4` contains exactly four transmission slots and requires the
terminal slots 6 and 7, leaving **C(6,2)=15 columns**. The noncausal
`OffSchedule 8 4` has **C(8,4)=70 columns**. These are the actual finite
types quantified by `articleScanRowsChecked` and `articleScanColsChecked`; the
checks are not over only the named certificate entries.

The manuscript's full input class has 37 traces of weight at most two (one
empty trace, eight singleton traces, and 28 exact-two traces). The formal
`articleCausalPolicy_full_rows` theorem covers all 28 exact rows. The imported
`input_coverage_lower` theorem lifts that bound to every smaller input, and
`articleCausalPolicy_all_inputs` states the resulting (1/3) coverage
explicitly. `articleCausalPolicy_nonempty_inputs` also gives the nonempty
form used by the privacy definition. Thus the exact-row computation is not
being presented as a check of only the 28 two-arrival examples.

The three causal definitions at lines 243–250 are the sets

```text
01100011 = {1,2,6,7}
01001011 = {1,4,6,7}
00011011 = {3,4,6,7}.
```

Each carries the exact-cardinality and terminal-reserve proofs required by
`OnSchedule`. The causal policy weights are all one with scale 3. The three
dual inputs are `11000000`, `10010000`, and `00110000`, also with unit weights
and scale 3. The sum theorems at lines 273–283 establish normalization before
the sparse laws are used.

The eight noncausal schedule definitions at lines 305–327 are the exact
four-slot traces in the independent certificate. Their weights are

```text
1, 2, 1, 1, 1, 1, 1, 1,
```

with scale 9. The six noncausal dual inputs at lines 329–345 have weights
`2,1,1,2,1,2`, also with scale 9. The two sum theorems at lines 365–369
establish that both are probability laws.

## Executable feasibility and fuel

`articleTraceList` filters `List.finRange H` by trace membership. Since
`finRange` is increasing and filtering preserves `Pairwise`,
`articleSortedTrace` is a valid `SortedTrace`; line 101 proves that converting
it back to a trace returns the original finite set. The length bound at lines
105–108 gives

```text
(articleSortedTrace x).slots.length ≤ H.
```

`articleAdvanceFuel` follows the same earliest-available-slot logic as
`advance`: it skips slots before the arrival, accepts the first slot in the
deadline interval, and fails when that first eligible slot is late or absent.
`articleAdvanceFuel_spec` and `articleAdvanceFuel_spec_full` prove both the
acceptance bit and the remaining suffix agree with `advance`.

`articleScanFuel_eq_scanBool` is parameterized by an explicit hypothesis
`xs.length ≤ fuel`; it is not an assumption hidden in a closed example.
`articleScanFeasible` supplies fuel (H), while
`articleSortedTrace_length_le` supplies the hypothesis for the actual input
list. The empty-list and zero-fuel branches are included in the induction.
Combining this equality with `scan_true_iff_feasible` and
`articleSortedTrace_toTrace` gives the semantic equivalence at lines 114–119:

```text
articleScanFeasible D x y = true  ↔  Feasible D x y.
```

The deadline comparison uses `s.val ≤ a.val + D`. This is the same un-clipped
natural-number form used by `Feasible`; clipping at `H-1` is automatic because
`s : Fin H` already has `s.val < H`. No probabilistic or finite-set search
oracle is used by the executable certificate predicate.

The row and column bridge lemmas (lines 151–239) first identify each matrix
entry with the scan Boolean, then convert the natural weighted counts into
real coverage divided by the positive scale. Consequently the checks at
lines 285–301 and 371–387 produce the exact inequalities consumed by the
game proof, rather than merely proving an unrelated Boolean property.

## Causal primal and dual certificates

`articleCausalPolicy_rows` checks every `FullInput 8 2` row against threshold
1. Through `article_row_ineq_of_checked`, the associated sparse law therefore
covers every full row by at least (1/3). `articleCausalDual_cols` checks
every `OnSchedule 8 2 4` column against threshold 1 for the three dual rows.
After normalization, every causal schedule has dual coverage at most (1/3).
This formally captures the manuscript's statement that no reserve schedule
can serve more than one of the three dual inputs: all three dual weights are
one, so an integer count bounded by one is exactly the required support
separation.

`articleCausalValue` installs the two sparse laws as `Law`/simplex points and
passes these row and column inequalities to `matching_certificate`. That
lemma proves both `value (onMatrix 8 2 4 1) = 1/3` and that the displayed
policy has worst coverage exactly (1/3). The proof therefore contains both
directions of optimality; it does not infer the value from the primal policy
alone.

`articleCausalOptimum` rewrites the general causal optimum theorem and obtains

```text
causalOptimum 8 2 4 1 ε = 1 - 1/3 = 2/3
```

under the explicit hypothesis `0 ≤ ε`. The parameter facts `1 ≤ m ≤ B ≤ H`
are discharged by kernel arithmetic at the call site.

## Noncausal certificate

`articleNoncausalPolicy_rows` checks all 28 exact rows against integer
threshold 5, and the scale-9 law therefore covers every row by at least
(5/9). `articleNoncausalDual_cols` checks all 70 exact-cap columns against
the six weighted dual inputs, with weighted count at most 5. The resulting
column bound is at most (5/9). `articleNoncausalValue` applies the same
matching certificate to conclude

```text
value (offMatrix 8 2 4 1) = 5/9.
```

`articleNoncausalOptimum` then gives the manuscript's

```text
noncausalOptimum 8 2 4 1 ε = 1 - 5/9 = 4/9
```

for every finite nonnegative epsilon. The formal source thus verifies both
the causal and independent noncausal claims in the paragraph following
Eq. (23), including the privacy conversion.

## Concrete execution anchors

For input `{0,1}` and base schedule `{1,2,6,7}`, `articleExecute_base`
proves that `execute 1` returns exactly `{1,2,6,7}`, the set representation of
`01100011`. The queue serves arrival 0 at slot 1 and arrival 1 at slot 2,
while slots 6 and 7 remain transmission dummies.

For the third base schedule `{3,4,6,7}`, `articleExecute_switch` proves that
the output is exactly `{1,2}`, the set representation of `01100000`. The
state claims at lines 523–561 provide the finer trace:

* `articleExecute_base_servicePairs` and
  `articleExecute_switch_servicePairs` prove the two service pairs
  `(arrival,slot) = (0,1)` and `(1,2)` by checking the served set immediately
  before and after each slot.
* `articleExecute_switch_first_activation` proves schedule mode through the
  state after slot 0 and service mode in the state after slot 1, with service
  activated at `⟨1, by decide⟩`. This matches the current-slot switch rule:
  arrival 0 has deadline 1, slot 1 is absent from the base schedule, and the
  queue is served at that same slot.
* The transmission-card theorems prove cards 4 and 2 for the base and
  switched outputs, respectively, so the drop in transmission count is part
  of the complete output trace as stated in the manuscript.

These proofs are direct `decide` reductions of the finite operational
definitions. They do not add a postulated service pairing or a separately
defined simulator.

## Threshold endpoint

The final declaration, `articleStrictThresholdEndpoint` (lines 563–586),
formalizes the manuscript's strict-boundary example for (H=2,m=1,D=0).
It proves `perfectBudget = 2`, `testBlockCount = 2`, the exact noncausal loss

```text
1 - offGameValue 2 1 1 0 = 1/2,
```

and `noncausalBudget ... (1/2) = 1`. The value is obtained from the formal
zero-delay game theorem and the budget equality from adjacent exact
certificates, so the endpoint is not just a numeral reduction of an
unrelated formula. Since `testBlockCount` is the quotient-plus-remainder
ceiling used for the article's (K), its value 2 supplies the stated
`1/K = 1/2` boundary.

The formal source also contains `articlePerfectPrivacyB6` (lines 495–504),
which specializes Corollary 3 to prove `perfectBudget = 6` and both
zero-loss budget functions equal 6. `articlePerfectScheduleB6`
(lines 506–513) identifies the fixed schedule as `01101111`, proves its
cardinality is 6, and proves it feasible for every trace of weight at most
two. This closes the source-level link between the manuscript's “at B=6”
sentence and the general perfect-privacy theorem. The separate
standard-library checker independently confirms the same schedule and all 37
bounded inputs.

## Independent and kernel validation

The source contains no `sorry`, `axiom`, `unsafe`, or `native_decide` marker.
The module was compiled with the repository's Lean 4.33 toolchain; it
completed successfully with only unused-pattern and `letI` style warnings.
The kernel's axiom report for the principal declarations contains only the
ordinary `propext`, `Classical.choice`, and `Quot.sound` dependencies.

The separate standard-library checker recorded in
`computations/COROLLARIES-CHECKS.md` uses fresh augmenting-path matching and
exact `Fraction` arithmetic. Its Eq. (23) scope checks all 28 exact rows, all
37 bounded inputs, all 15 causal columns, and all 70 noncausal columns; it
also checks the two execution outputs, service traces, switch slot, and the
`B=6` block schedule `01101111`. The earlier
`computations/verification-final.log` independently reports the explicit
28-by-15 certificate check. These checks are supplementary evidence; the
universal semantic conclusions in this file come from the Lean theorems
above.

## Scope note

The review concerns the finite (H=8,m=2,D=1,B=4) certificate and its
execution examples. The matrix certificates establish exact game values for
the formal finite types and the imported optimum theorem supplies the
mechanism-level interpretation. They do not by themselves prove the general
closed-form budget and zero-delay statements; those are separate modules and
checks. Likewise, the sorted-list scan bridge proves semantic feasibility,
while the execution-cost theorem in `MatchingComplexity.lean` has its own
representation qualification about sorting and finite-set preprocessing.
