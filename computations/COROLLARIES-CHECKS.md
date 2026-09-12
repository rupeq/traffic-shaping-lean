# Independent checks for the five quantitative corollaries

`corollaries_check.py` is a new standard-library checker for the formulas and
finite constructions in Sections 4--5 of the r9 manuscript.  It does not
import `covering.py`, the optimizer, or another checker.  Every feasibility
claim is derived from the actual arrival and transmission slots by a fresh
augmenting-path injection search, and all probabilities and inequalities use
`fractions.Fraction`.

The checker writes its machine-readable result to
`.check-output/corollaries/COROLLARIES-CHECK.json` by default.
Run it from the repository root with:

```sh
python3 computations/corollaries_check.py
```

Use `--output-dir /path/to/results` to select a release directory. The complete
`verify_article.py` command runs this checker in its own fresh run directory
and binds the result to the source hashes.

The run also performs a read-only freshness check for the saved numeric tables:
all 9 `TABLE-1.csv` rows (the manuscript's Table 2) and all 8 `TABLE-3.csv`
rows are matched to the exact rational values in `FRONTIERS.json` and
`EXTRA-CERTIFICATES.json`, with Eq. (20) recomputing each `B0`.  This group
does not regenerate an LP; the neighboring independent checker remains the
source of the full matching-witness validation for those saved certificates.

## Corollary coverage

The checker covers the following article statements.

* Corollary 1, Eqs. (15): for every covered input, the explicit map from an
  offline schedule of budget `B` to a causal schedule of budget
  `min(H, B+m)` preserves the matching; the class inclusion and exact
  `B_g(delta)` breakpoints are checked on the independently counted zero-delay
  frontiers.  The sharpness family `D=0`, `H >= 2m`,
  `delta = 1 - 1/C(H,m)` is checked for `B_off=m` and `B_on=2m`.
* Corollary 2, Eqs. (16)--(19): for every covered offline schedule/input pair,
  an explicit matching is retained under all `C(B,B-m)` deletion choices.
  The favorable count and the binomial identity for `rho` are checked exactly,
  as is `1-rho <= m^2/B`.  This pointwise injection is the finite certificate
  for averaging to `v_on >= rho v_off`.
* Corollary 3, Eq. (20): every bounded input is matched by the fixed schedule
  formed from the final `m` service slots of each full `(D+m)` block and the
  final `min(m,b)` slots of the remainder.  Every exact `B0-1` schedule is
  rejected by at least one disjoint block witness.
* Corollary 4, Eqs. (21)--(22): all exact-m inputs and exact-B schedules are
  counted through `H <= 12`, `m <= 4`, including `H=m`, `B=m`, and `B=H`.
  The zero-delay ratios and the exact `m=1` gap formula are checked from actual
  subset containment through the matcher.
* Corollary 5, Eqs. (24)--(26): all exact-B offline and causal schedules below
  `B0` are checked against the block witnesses on the new extension
  `H=10..12`, `m <= 4`, `D <= H+2`.  The strict boundary
  `H=2,m=1,D=0,B=1,delta=1/K=1/2` is checked directly.

The article example in Section 5.3 is checked separately.  The three causal
Eq. (23) schedules cover every one of the 37 inputs of weight at most two, the
three listed dual inputs have pairwise disjoint causal schedule supports, and
the primal/dual values are both `1/3`.  The independently transcribed offline
certificate has value `5/9` and delta `4/9`.  At `B=6`, the block schedule
`01101111` covers every bounded input.

The unnumbered privacy interpretation in Section 2.2 also has small exact
regressions: identical finite laws have TV zero, disjoint laws have TV one,
the TV triangle inequality holds for three law triples, and exhaustive finite
events attain the TV distance.  All `{0, 1/2, 1}` randomized tests on the
finite supports obey and attain the equal-prior bound
`best_success=(1+TV)/2`; the positive-part argument supplies the full
`[0,1]` test bound.  The quoted design-size count is checked independently as
`C(48,8)=377348994`, equal to `C(50-2,10-2)`.

## Required verification domains and exact counts

| check | finite scope | exact count |
| --- | --- | ---: |
| Corollary 1 schedule lift | `H<=10`, `m<=4`, `D<=H+2`, `B=m..H` | 1,707 parameter sets; 88,840 maps; 3,576,760 covered pairs; 772 threshold checks; 32 sharpness checks |
| Corollary 2 deletion injection | `H<=10`, `m<=floor(H/2), m<=4`, `D<=H+2`, `B>=2m` | 1,022 parameter sets; 1,471,630 covered source pairs; 38,283,201 retention trials; 5,965,347 favorable trials; 94 Eq. (19) identities |
| Corollary 3 block formula | `H<=12`, `m<=4`, `D<=H+2` | 428 parameter sets; 51,070 universal input checks; 35,921 `B0-1` schedule checks; 126 large-delay cases |
| Corollary 4 zero delay | `H<=12`, `m<=4`, `B=m..H` | 244 games; 4,647,458 offline pairs; 525,824 causal pairs; 488 Eq. (21) checks; 77 Eq. (22) checks |
| Corollary 5 threshold extension | `H=10..12`, `m<=4`, `D<=H+2` | 168 parameter sets; 109,497 below-`B0` schedule checks; 357 block witnesses; 420 `B<m` checks; 672 strict-threshold representatives |
| Eq. (23) and examples | `H=8,D=1,m=2,B=4` and `B=6` | 28 exact-m rows; 15 causal columns; 70 offline columns; all 37 bounded inputs checked |
| Privacy interpretation and article size | finite laws and exact binomial | 3 TV triangle checks; 16 event checks; 45 randomized tests; `C(48,8)=377,348,994` |
| Saved table freshness/mapping | `TABLE-1.csv`, `TABLE-3.csv`, saved rational JSON | 9 Table 2 rows; 8 Table 3 rows; 79 legacy frontiers; 16 extra certificates |

## Relation to the pre-existing release checks

The repository already contains 79 legacy and 16 r4 exact certificates,
independent queue checks through `H=7`, a 240-game zero-delay grid through
`H=8`, 43 saved budget comparisons, 66 saved fixed-budget gap comparisons, and
the `H<=9` all-`m` no-savings grid.  Its independent certificate checker also
checks the causal 28-by-15 example.

This checker does not regenerate those LPs.  Its added verification is the
actual schedule-lift proof for Corollary 1, the pointwise random-retention
injection for Corollary 2, the exact matching based block schedule and larger
`H<=12,m<=4` formula domain, the larger zero-delay count domain plus Eq. (22),
the new `H=10..12` threshold extension, and an explicit recheck of both
Eq. (23) certificates and the `B0=6` example.  The saved table mapping is
read-only and does not regenerate LPs.  The finite checks complement,
and do not replace, the universal Lean proofs.
