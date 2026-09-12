# Table 2 statements and budget bridges: semantic review

Audit date: 2026-09-11. This review covers
`formal/TrafficShaping/ArticleTableBounds.lean` and
`formal/TrafficShaping/BudgetCertificates.lean` against Section 6.2 and
Table 2 of the r9 manuscript. It also checks the current 67-item article
inventory and the exact saved frontier/table checks. No proof source was
edited.

## Verdict

The generic table bridges are semantically sound. `ArticleTable2Row` has the
right meaning for the perfect-privacy reserve, both 0.1 budget columns, the
0.5 causal budget column, and the minimum positive causal loss over every
budget below the reserve, uniformly for every finite nonnegative epsilon.
The adjacent-budget argument correctly turns one fitting certificate and one
strictly failing predecessor into an actual `Nat.find` budget. The H=16,
D=1, B=8 accuracy statement is also the correct 0.75 consequence of
epsilon-zero participation privacy.

The concrete table source is now integrated. `TableBudgetStatements.lean`
instantiates `article_table2_row_of_values` for all nine published Table 2
tuples, proves all eight Table 3 rows, proves the qualitative
H=8,D=2,m=2 causality gap and its causal lower bound, and connects the
H=16,D=1,B=8 row to an actually attaining causal mechanism with the 3/4
accuracy guarantee. The 67-item inventory has nonempty declaration lists for
all items, and the root imports the statement module. This is a source-level
and semantic PASS; the subsequent full kernel and code check passed; see the integration evidence below.

## Meaning of the row proposition

`ArticleTable2Row` (`ArticleTableBounds.lean:28--40`) expands to the exact
columns in Table 2 for `m=2`:

* `perfectBudget H 2 D = R` is the equation-(20) common perfect-privacy
  budget;
* `testBlockCount H 2 D ≤ 6` is the sufficient bound needed for the 0.1
  no-savings interval;
* both `noncausalBudget ... (1/10)` and `causalBudget ... (1/10)` equal `R`;
* `causalBudget ... (1/2) = C` is the causal 0.5 threshold column;
* `0 < μ` and the final `IsLeast` statement specify the least positive
  causal loss below the reserve.

The final set is

```text
{ δ | ∃ B, 2 ≤ B ∧ B < R ∧ δ = causalOptimum H 2 B D ε }.
```

It includes every admissible sub-reserve budget, including `R-1`, and the
row proposition quantifies it for every real `ε ≥ 0`. Since the exact main
theorem identifies `causalOptimum` with `1 - onGameValue` for every such
epsilon and the game value lies in `[0,1]`, the set is the semantic set of
privacy losses, rather than a set of merely formal infima. Requiring `μ>0`
plus `IsLeast` also forces every loss in the set to be positive; no separate
positivity premise for each budget is missing.

The proposition does not silently assume `R-1` is admissible. The row
constructor requires `2 < R` and `R ≤ H`, and derives `2 ≤ R-1` and
`R-1 ≤ H`. It also requires `2 ≤ C ≤ H`, which is the domain needed by the
0.5 game value and budget definition. It does not require `C<R`, correctly
allowing the two rows whose 0.5 budget is still the perfect-privacy budget.

## Perfect budget and the 0.1 columns

`small_threshold_budgets_of_six_tests` (`ArticleTableBounds.lean:13--24`)
applies `corollary5_eq25_unconditional` with
`δ ≤ 1/10`. It proves `K=testBlockCount H m D` is positive from the workload
domain and rewrites `K≤6` into `1/10 < 1/K`. Therefore both semantic
`Nat.find` budgets equal `perfectBudget`, with the correct proof arguments
for `0≤δ` and `δ≤1` supplied internally.

The first field of `ArticleTable2Row` makes `R` exactly that perfect budget,
so `article_table2_row_of_values` rewrites the two generic threshold results
to `R` (`:52--55`). This is stronger than checking a single game value at
`B=R`: `corollary5_eq25_unconditional` supplies the lower bound for every
smaller selected budget and the explicit perfect-schedule witness supplies
the upper bound. The distinction matters for a minimum-budget table.

The underlying equation-(20) construction and strict no-savings theorem were
reviewed separately and apply for all natural delays, including empty
remainders and the one-block case. The table bridge uses exactly their
unconditional form; it does not smuggle in a finite enumeration assumption.

## The 0.5 causal budget column

`causalBudget_eq_of_adjacent_certificates`
(`BudgetCertificates.lean:27--44`) proves the exact minimum budget from:

1. `hfit`: the value at `B` meets the requested loss `δ`, giving
   `causalBudget ≤ B` by `causalBudget_minimal`;
2. `hfail`: either `B=m`, so there is no predecessor, or the loss at `B-1`
   is strictly above `δ`;
3. monotonicity of `onGameValue` under budget increase, which makes every
   budget below `B` no better than `B-1`.

In the second branch, the proof obtains the selected `Nat.find` budget `b`
from `causalBudget_bounds`, derives `b≤B-1`, and combines
`onGameValue_mono_budget` with `causalBudget_threshold`. The resulting
inequalities contradict the strict predecessor failure. This proves both
directions of equality and handles the boundary `B=m` explicitly.

`causalOptimum_antitone_budget` (`BudgetCertificates.lean:11--17`) is the
needed semantic monotonicity statement: it rewrites both optima using the
exact finite-epsilon theorem and subtracts the game-value monotonicity from
one. The required hypotheses ensure both budgets lie in `[m,H]`; the proof
does not compare undefined game domains.

`article_table2_row_of_values` applies this bridge at `m=2`, `δ=1/2`, with
the published row's `C`, `hfit`, and `hfail` (`ArticleTableBounds.lean:56--58`).
Each concrete row theorem uses only an exact value-one-or-less certificate at
`C` and a strict value failure at `C-1`; the monotonicity bridge avoids
enumerating every lower budget in Lean.

## Minimum positive causal loss

`causal_subreserve_loss_isLeast` (`BudgetCertificates.lean:65--76`) proves
the last budget below `R`, namely `R-1`, is a least element of the complete
sub-reserve loss set. Membership is witnessed by `R-1` itself. For any
`B<R`, budget monotonicity gives

```text
causalOptimum H m (R-1) D ε ≤ causalOptimum H m B D ε.
```

The row constructor rewrites the exact value at `R-1` using `hlast`, obtains
`causalOptimum ... (R-1) = μ` from `causal_optimum_eq`, and transports the
least-element proof to `μ` (`ArticleTableBounds.lean:59--66`). The argument is
valid for every finite real `ε≥0`; no zero-epsilon specialization is hidden
in the table minimum.

The phrase “minimum positive” in the manuscript is therefore represented
correctly when a concrete row supplies `μ>0`: if any sub-reserve optimum were
zero, the `IsLeast` lower-bound clause would contradict `0<μ`. All nine
concrete rows now supply the required `hlast`, `hfit`, and `hfail` witnesses
in `TableBudgetStatements.lean:10--143`; each witness is an exact
`TableCertificates` value followed by rational normalization.

## Numerical Table 2 values

The manuscript's Table 2 and `computations/TABLE-1.csv` agree on all nine
tuples:

| `(H,D)` | `R=B₀` | `μ` | `B_on(0.1)` | `B_on(0.5)` |
| --- | ---: | ---: | ---: | ---: |
| `(8,1)` | 6 | 1/2 | 6 | 5 |
| `(8,2)` | 4 | 1 | 4 | 4 |
| `(8,3)` | 4 | 1 | 4 | 4 |
| `(12,1)` | 8 | 1/3 | 8 | 7 |
| `(12,2)` | 6 | 1/2 | 6 | 5 |
| `(12,3)` | 6 | 1/2 | 6 | 5 |
| `(16,1)` | 11 | 2/9 | 11 | 8 |
| `(16,2)` | 8 | 1/3 | 8 | 7 |
| `(16,3)` | 7 | 2/5 | 7 | 6 |

The read-only `computations/table_consistency_check.py` run passed with
fresh augmenting-path matching and exact rational arithmetic. It checked all
79 saved legacy frontier records, all nine Table 2 keys, and every causal
budget from `2` through the corresponding `B₀`; it found the listed minimum
losses and threshold budgets. It also checked the qualitative
`H=8,D=2,m=2,B=3` frontier (`δ_off=1/2`, `δ_on=1`). This establishes the
numeric computational claims against the saved finite games. The universal
Lean theorem chain now transfers those exact game values to the finite-
epsilon semantic optima through the concrete row anchors below.

## Accuracy bound at H=16, D=1, B=8

`table2_H16_half_privacy_accuracy`
(`ArticleTableBounds.lean:68--74`) assumes a mechanism with
`Private M 0 (1/2)` at exactly `H=16,m=2,B=8,D=1`, any nonempty active
input, and any randomized equal-prior decision function
`d : Trace 16 → ℝ` taking values in `[0,1]`. It applies
`participation_accuracy_bound`, whose conclusion is

```text
testSuccess ≤ (1 + δ)/2.
```

Normalizing `δ=1/2` yields `3/4`. The result is semantically sound and in
fact applies to every mechanism with those parameters, so it covers the
attaining construction once the Table 2 row establishes that the causal
0.5 budget is 8. `table2_H16_half_attainable_accuracy`
(`TableBudgetStatements.lean:261--277`) now uses that exact budget,
`causalBudget_attainable`, and this bound to state the existential result
directly: it produces a causal, `Private M 0 (1/2)` mechanism and proves the
3/4 bound for every active input and every randomized test in `[0,1]`.
This is the twentieth concrete statement in the table-statement module.

## Concrete Table 2, Table 3, and qualitative anchors

`TableBudgetStatements.lean:10--143` proves the nine Table 2 rows using the
generic bridge. Each row has the published `(R, C, μ)` values and supplies an
exact on-value at `R-1`, an exact fit at `C`, and a strict predecessor failure
at `C-1` (or the `C=2` branch). The certificate names are visible at the row
anchors and all 95 declarations in `TableCertificates.lean` are included in
the audit list.

`TableBudgetStatements.lean:145--239` proves the eight Table 3 rows uniformly
for every finite `ε ≥ 0`, rewriting the exact certificates through
`noncausal_optimum_eq` and `causal_optimum_eq`. The two qualitative theorems
at `:241--259` prove both exact optima `(1/2, 1)` and the converse lower bound
`1 ≤ δ` for every causal private mechanism at that frontier. These statements
are now concrete anchors rather than uninstantiated generic bridges.

## Coverage inventory audit

The current `formal/article-coverage.json` has exactly 67 unique required
items, matching the fixed requirement set in `.github/scripts/audit_formal.py`:

* equations 1--26;
* Lemmas 1--4 and Theorem 1;
* Corollaries 1--5;
* the additional budget, epsilon, input-reduction, duality, privacy,
  asymptotic, matching-cost, queue-cost, matrix-cardinality, execution,
  endpoint, and periodic-observation claims;
* the qualitative causality-gap item;
* all nine Table 2 rows and all eight Table 3 rows.

That scope captures the article's own numbered formulas, theorem and
corollary consequences, explicit execution/example claims, periodic timing
counterexample, qualitative frontier, and every displayed numerical table
row. Repeated statements in the abstract, introduction, discussion, and
conclusion are already represented by those anchors. The exact matrix-size
claim `C(48,8)=377348994` is retained under `matrix-cardinalities` because it
is a mathematical combinatorial fact, while reported run/certificate totals
such as 79, 95, 546, 45,622, 4,069, 20,532, 240, 43, and 66 are historical
verification metadata and are appropriately left to the exact-code audit.
Literature comparisons, citations, repository-access status, funding,
authorship, and other provenance statements are likewise outside the Lean
claim inventory. The manifest's scope field explicitly states this boundary.

The inventory's scope and declaration coverage are now complete at the source
level: all 67 required items have nonempty lists; the 129 distinct manifest
declarations are present in `Audit.lean`; and the root import reaches
`TableBudgetStatements`. At the source-review checkpoint, `Audit.lean` contained 253 `#print axioms`
commands, including every one of the 95 exact certificate declarations and
all 20 concrete table/qualitative/attainment statements. The coordinating task subsequently refreshed the human-readable
map and completed the integrated verification; see the evidence below.

## Verification limits

The saved-table checker passed as described above. The source reviewer did not run a repository-wide Lean
build. The coordinating task subsequently completed that build together
with the axiom and code gates, as recorded below. This review is source-semantic and read-only. No proof or source
file was edited here.

## Integration evidence appended by the coordinating task

Run `20260912T134526Z-0bf54535` completed at `2026-09-12T13:47:31.281731+00:00` with PASS. The [complete report](../verification/article-complete/ARTICLE-CHECK.json) SHA-256 is `80fde35447373f7816ce8e141a8f1c7b7371c62358074a97ba654d3733f1e116`. The formal gate emitted 257 reports for 257 requested declarations and accepted all 67 inventory items. The combined gate also passed the regression tests, source regeneration of all 95 certificates, exact corollary checks, and table checks. This subsequent integration evidence is distinct from the source reviewer's work.
