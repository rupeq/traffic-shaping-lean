# Zero-delay formulas and Corollary 1 sharpness: semantic review

Audit date: 2026-09-11. This independent source review covers
`formal/TrafficShaping/ZeroDelay.lean` and
`formal/TrafficShaping/Corollary1Sharpness.lean` against the r9 manuscript,
Corollary 4, Eq. (21), Eq. (22), and the sharpness family in the proof of
Corollary 1. No source files were edited and no repository-wide build was run
for this review.

## Zero-delay model and the noncausal formula

`feasible_zero_iff_subset` at `ZeroDelay.lean:19--35` proves the exact
zero-delay semantics: `Feasible 0 x y` is equivalent to `x ⊆ y`. The forward
direction uses both deadline inequalities to force the injective service map
to fix each arrival slot; the reverse direction uses the identity assignment.
Consequently, the matrix entries at `:37--45` are precisely the subset
indicators for both schedule classes.

The noncausal counting and certificate are complete:

* `card_off_containing` (`:83--105`) counts exact-`B` schedules containing a
  fixed full input as `C(H-m,B-m)`.
* `off_uniform_row` (`:154--162`) uses the uniform exact-`B` schedule law and
  the binomial product identity to obtain, for every full row,

  ```text
  C(B,m) / C(H,m).
  ```

* `off_uniform_col` (`:580--588`) uses the uniform full-input law and counts
  the `m`-subsets contained in any fixed `B`-schedule by `C(B,m)`. This is an
  actual dual column bound, independent of the selected schedule.
* `zero_delay_offGameValue` (`:589--608`) passes these two rational
  certificates to `matching_certificate`, so the equality is for the actual
  finite game value, not merely for one primal law.

The hypotheses `m≤H`, `m≤B`, and `B≤H` are exactly the nonempty finite-domain
conditions. Positive denominators follow from these inequalities. The public
theorem carries `1≤m` as part of the article's workload domain; the counting
argument itself is also well behaved at `m=0`.

## Causal formula, monotonic lower bound, and the exact dual construction

Write `n=H-m`, `k=B-m`, and `j=min(m,n)` as in the manuscript. The causal
schedule type contains the whole terminal set and has exactly `k` prefix
slots. `card_on_containing` (`:186--338`) counts schedules containing a full
input by first removing the forced terminal slots. It correctly handles both
cases: a prefix arrival set of size `c` is containable when `c≤k`, with count
`C(n-c,k-c)`, and has count zero otherwise.

`on_uniform_row` (`:340--358`) turns that count into the exact coverage of a
uniform causal schedule law. For a full input, `U=tracePrefix n x` has
`c=|U|≤j`. When `j≤k`, `containment_probability_symmetry` rewrites the row
coverage as

```text
C(k,c) / C(n,c),
```

and `choose_ratio_mono` proves this is at least
`C(k,j)/C(n,j)` for every `c≤j`. When `k<j`, the target numerator
`C(k,j)` is zero and `on_uniform_lower` (`:360--455`) obtains the lower bound
from nonnegativity of coverage. This explicitly includes the manuscript's
zero-value regime; it is not silently restricted to `k≥j`.

The dual upper certificate is an actual input law, not a schematic symmetry
claim. `on_fixed_upper` (`:456--579`) fixes a terminal subset
`t0 ⊆ terminal H m` of size `m-j`, then maps a uniformly chosen
`j`-subset `u` of the public prefix `P` to the full input
`u ∪ t0`. The prefix and terminal sets are disjoint, so this has exactly `m`
arrivals. The fixed terminal arrivals are contained in every causal schedule.
For an arbitrary causal schedule `y`, its prefix intersection `Y=y∩P` has
exactly `k` slots. The embedded input is contained in `y` exactly when
`u⊆Y`, whose uniform probability is `C(k,j)/C(n,j)`, including probability
zero when `k<j`. Thus the dual law is independent of `y` and gives the correct
column bound for every causal schedule.

`zero_delay_onGameValue` (`:610--626`) combines the uniform causal schedule
law, the pointwise lower bound, and this fixed-terminal dual law through
`matching_certificate`. It proves the full Eq. (21) causal formula as an
equality of `onGameValue`, with no enumeration assumption.

## Boundary `H=m`, `n=j=k=0`, and zero cases

The formula is well defined at the full-input boundary. If `H=m`, then the
domain conditions force `B=m`, hence

```text
n = H-m = 0,   k = B-m = 0,   j = min(m,n) = 0.
```

Both binomial ratios are `C(0,0)/C(0,0)=1`. The proofs use the nonempty
zero-subset type and never divide by a zero binomial coefficient. The explicit
theorem `zero_delay_full_input_boundary` (`:662--669`) records both game
values as one. The same branch is covered internally by the uniform row and
dual constructions: the prefix is empty, the terminal reserve is the whole
horizon, and the exact causal schedule is unique.

The helper `zero_delay_onGameValue_zero_of_lt` (`:647--652`) exposes the
causal zero case directly when
`B-m < min(m,H-m)`, by rewriting Eq. (21) and applying the zero rule for
`Nat.choose`. This is consistent with, and more general than, the `k<j`
branch used in the lower-bound proof.

## Eq. (22) at game and semantic-optimum levels

For `m=1` and `H≥2`, `zero_delay_m_one_gap` (`:628--645`) specializes Eq. (21)
to

```text
offGameValue = B/H,
onGameValue  = (B-1)/(H-1),
offGameValue - onGameValue = (H-B)/(H*(H-1)).
```

The casted natural subtractions are guarded by `B≤H` and the denominator is
nonzero under `H≥2`. The theorem also accepts the boundary budget `B=H`,
where the gap is zero, and the minimum budget `B=1`.

`zero_delay_m_one_optimum_gap` (`:654--660`) then rewrites both actual
semantic optima using `causal_optimum_eq` and `noncausal_optimum_eq` for an
arbitrary finite real `ε` with `0≤ε`. Therefore Eq. (22) is not only a
zero-epsilon game identity: it is the exact privacy-loss gap for both
mechanism classes throughout the theorem's finite-epsilon domain.

## Corollary 1 sharpness family

`Corollary1Sharpness.lean` assumes `1≤m`, `m≤H`, and `2m≤H`, exactly the
sharpness family in the manuscript. `earlyTrace` (`:30--53`) is the full
input occupying the first `m` prefix slots; the `2m≤H` hypothesis makes it a
valid full input disjoint from the terminal suffix.

`onGameValue_zero_of_budget_lt_twice` (`:55--106`) proves the causal game
value is zero for every `m≤B<2m`. If such a causal schedule were feasible for
the early full input at zero delay, subset feasibility would force all `m`
early slots into its prefix. The schedule already contains `m` terminal slots,
so its exact budget would be at least `2m`, contradicting `B<2m`. The proof
uses one full test input and a pointwise zero row, then applies the row
infimum and nonnegativity of the game value; it does not incorrectly union
arrivals from different tests.

`corollary1_sharpness` (`:131--215`) sets
`δ=1-1/C(H,m)`. `sharp_delta_bounds` proves `0≤δ≤1`, with
`C(H,m)>1` supplied by `2m≤H` and `m≥1`. The noncausal value at `B=m` is
`1/C(H,m)`, so the budget threshold is met at `m`; the general budget lower
bound forces the exact noncausal minimum to equal `m`.

For the causal upper bound, the Corollary 1 padding theorem maps the
noncausal `B=m` law to the causal budget `min(H,m+m)=2m`, preserving coverage.
This gives the threshold at `2m` and hence a causal budget upper bound of
`2m`. For the lower bound, `causalBudget_spec` supplies the actual selected
budget's domain and threshold. If it were below `2m`, the zero-game-value
lemma would force `1≤δ`, contradicting the strict `δ<1` established from
`C(H,m)>1`. Therefore the semantic causal minimum is exactly `2m`.

This proves the requested sharpness claim for actual `noncausalBudget` and
`causalBudget`, rather than only for the two zero-delay game values.

## Verdict and release conditions

No substantive semantic defect was found. The source proves both formulas in
Eq. (21), including `k<j` and `H=m`; it contains the correct fixed-terminal
dual construction; it proves Eq. (22) for arbitrary finite nonnegative
epsilon at the semantic-optimum level; and it proves the Corollary 1
sharpness family under `2m≤H`.

The release text should retain the domain qualifiers `D=0`, `1≤m≤B≤H` for
the public Eq. (21) value theorem, `H≥2` and `1≤B≤H` for Eq. (22), and
`1≤m`, `m≤H`, `2m≤H` for sharpness. The coordinator's integrated compilation
remains the final build gate; this review intentionally did not rerun it.
