# Article completeness and table statement semantic review

Audit date: 2026-09-11. This is a read-only source-semantic review of the r9
article inventory, the concrete Table 2/Table 3 statements, and their exact
certificate bridges. It does not replace the parent task's single kernel
compilation or final formal audit.

## Verdict

Source coverage is complete: `formal/article-coverage.json` contains the 67
required mathematical items, every item has a nonempty declaration list, and
all 129 distinct manifest declarations occur in `formal/Audit.lean`. The root
module imports `TrafficShaping.TableBudgetStatements`, so the concrete table
statements are in the checked import graph. At the source-review checkpoint, `Audit.lean` contained 253
`#print axioms` commands; all 95 declarations in `TableCertificates.lean` and
all 20 concrete declarations in `TableBudgetStatements.lean` are included.

The source-semantic verdict is PASS for coverage and for the reviewed table
propositions. The subsequent integrated kernel/full-gate verdict is PASS; see the coordinating task's evidence below.
This separation matters: declaration names and source proofs establish the
intended evidence, while the kernel run establishes that the current checkout
elaborates and uses only the permitted axioms.

## Scope

The manifest identifies article revision r9 (11 September 2026) and scopes the
inventory to the article's own mathematical statements. It deliberately
excludes literature attributions and reported program-run counts, which are
provenance or exact-code-audit evidence rather than universal Lean claims.
The 67-item scope is 26 equations, four lemmas, Theorem 1, five corollaries,
13 additional named claims, one qualitative frontier, nine Table 2 rows, and
eight Table 3 rows. Repeated prose in the abstract, introduction, discussion,
and conclusion is represented by these mathematical anchors.

## Concrete table evidence

`ArticleTable2Row` defines the numerical content of a Table 2 row: the exact perfect-privacy
reserve `R`, the six-test condition for both 0.1 budgets, the causal 0.5 budget
`C`, and the least positive causal loss `μ` over every admissible budget below
`R`. `article_table2_row_of_values` derives those columns from the exact value
at `R-1`, a fit at `C`, and a strict failure at `C-1` (or the `C=2` base
branch), using budget monotonicity. The source definition and bridge are in
`ArticleTableBounds.lean:26–66`; the monotonicity and adjacent-certificate
lemmas are in `BudgetCertificates.lean:11–76`.

The nine concrete Table 2 rows in `TableBudgetStatements.lean:10–143` are:

| `(H,D)` | `R=B₀` | `C=B_on(1/2)` | `μ` |
| --- | ---: | ---: | ---: |
| `(8,1)` | 6 | 5 | 1/2 |
| `(8,2)` | 4 | 4 | 1 |
| `(8,3)` | 4 | 4 | 1 |
| `(12,1)` | 8 | 7 | 1/3 |
| `(12,2)` | 6 | 5 | 1/2 |
| `(12,3)` | 6 | 5 | 1/2 |
| `(16,1)` | 11 | 8 | 2/9 |
| `(16,2)` | 8 | 7 | 1/3 |
| `(16,3)` | 7 | 6 | 2/5 |

Each row's proof rewrites an exact `TableCertificates` on-value and closes the
rational inequalities with `norm_num`. The nine values therefore anchor all
published Table 2 columns through the generic semantic bridge rather than
merely repeating numerical literals.

The eight Table 3 theorems at `TableBudgetStatements.lean:145–239` quantify
`ε ≥ 0` and prove the exact perfect budget together with both noncausal and
causal losses. Their values are `(1/2,1)` for rows 1–4, `(1/3,1/2)` for rows
5–6, and `(2/5,2/3)` for rows 7–8. The qualitative theorems at
`:241–259` prove the H=8,D=2,m=2,B=3 gap `(1/2,1)` for every finite epsilon
and prove `1 ≤ δ` for every causal private mechanism at that frontier.

The additional concrete statement `table2_H16_half_attainable_accuracy`
(`TableBudgetStatements.lean:261–277`) extracts the exact row-7 causal budget,
uses `causalBudget_attainable`, and proves an existential causal mechanism with
`Private M 0 (1/2)` whose randomized equal-prior test success is at most 3/4
for every active input and every decision function valued in `[0,1]`. This is
the twentieth concrete statement in that module and closes the attainment
connection that the generic accuracy bound alone did not provide.

## 67-item coverage table

The table below records the exact manifest label and declaration anchor for
every required item. “Source evidence PASS” means the item has a nonempty
manifest anchor and that anchor is present in the audit command list. The
kernel column records the subsequent integration run, separately from this source review.

| # | ID | Article claim | Lean anchor(s) | Source evidence | Kernel gate |
| ---: | --- | --- | --- | --- | --- |
| 1 | `equation-01` | Slot delivery deadline | `TrafficShaping.Feasible`; `TrafficShaping.deadline` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 2 | `equation-02` | Two-sided participation privacy | `TrafficShaping.Private`; `TrafficShaping.Law.PrivatePair` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 3 | `equation-03` | Total variation and zero-epsilon equivalence | `TrafficShaping.Law.tv`; `TrafficShaping.Law.privatePair_zero_iff_tv` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 4 | `equation-04` | Noncausal exact-budget schedules | `TrafficShaping.OffSchedule` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 5 | `equation-05` | Causal schedules with terminal reserve | `TrafficShaping.OnSchedule`; `TrafficShaping.terminal` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 6 | `equation-06` | Attained finite covering-game value | `TrafficShaping.coverage`; `TrafficShaping.worst`; `TrafficShaping.value`; `TrafficShaping.value_attained` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 7 | `equation-07` | Primal covering linear program | `TrafficShaping.value_attained`; `TrafficShaping.off_exists_strongly_optimal`; `TrafficShaping.on_exists_strongly_optimal` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 8 | `equation-08` | Dual linear program | `TrafficShaping.dualValue`; `TrafficShaping.dual_value_isLeast`; `TrafficShaping.off_strong_duality`; `TrafficShaping.on_strong_duality`; `TrafficShaping.matching_certificate` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 9 | `equation-09` | Exact causal and noncausal optima | `TrafficShaping.noncausal_optimum_eq`; `TrafficShaping.causal_optimum_eq`; `TrafficShaping.both_optima_attained_at_zero` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 10 | `equation-10` | Empty-law mass of the forbidden feasibility event | `TrafficShaping.eq10_feasible_complement_le_delta` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 11 | `equation-11` | Almost-sure empty-prefix reserve bound | `TrafficShaping.eq11_empty_prefix_cap_mass_one` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 12 | `equation-12` | Terminal FIFO service times and deadlines | `TrafficShaping.terminal_actual_fifo_eq12`; `TrafficShaping.fifoServices_get_eq_max` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 13 | `equation-13` | Post-switch FIFO service times and deadlines | `TrafficShaping.switch_actual_fifo_eq13`; `TrafficShaping.fifoServices_get_eq_max` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 14 | `equation-14` | Exact repair total variation | `TrafficShaping.onMechanism_tv`; `TrafficShaping.repairMechanism_tv` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 15 | `equation-15` | Additive budget bounds | `TrafficShaping.corollary1_real_difference_bounds`; `TrafficShaping.corollary1_budget_bounds` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 16 | `equation-16` | Binomial thinning factor | `TrafficShaping.privacyRho` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 17 | `equation-17` | Coverage comparison after input-independent thinning | `TrafficShaping.onGameValue_ge_rho_mul_offGameValue`; `TrafficShaping.thinning_mass_lower` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 18 | `equation-18` | Semantic privacy gap bounds | `TrafficShaping.privacy_gap_bounds` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 19 | `equation-19` | Exact survival probability | `TrafficShaping.eq19_binomial_identity`; `TrafficShaping.thinContainment_mass`; `TrafficShaping.thinningOutput_feasible` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 20 | `equation-20` | Minimum perfect-privacy budget | `TrafficShaping.corollary3_eq20`; `TrafficShaping.perfectSchedule_card`; `TrafficShaping.perfectSchedule_feasible`; `TrafficShaping.perfect_privacy_mechanism_budget_lower` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 21 | `equation-21` | Both zero-delay formulas | `TrafficShaping.zero_delay_offGameValue`; `TrafficShaping.zero_delay_onGameValue`; `TrafficShaping.zero_delay_onGameValue_zero_of_lt` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 22 | `equation-22` | Exact one-arrival zero-delay gap | `TrafficShaping.zero_delay_m_one_gap`; `TrafficShaping.zero_delay_m_one_optimum_gap` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 23 | `equation-23` | Explicit matched positive-delay certificate | `TrafficShaping.articleCausalPolicyItems_sum`; `TrafficShaping.articleCausalDualItems_sum`; `TrafficShaping.articleCausalPolicy_all_inputs`; `TrafficShaping.articleCausalDual_cols`; `TrafficShaping.articleCausalValue`; `TrafficShaping.articleNoncausalValue`; `TrafficShaping.articleCausalOptimum`; `TrafficShaping.articleNoncausalOptimum`; `TrafficShaping.articlePerfectPrivacyB6`; `TrafficShaping.articlePerfectScheduleB6` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 24 | `equation-24` | No-savings lower bound | `TrafficShaping.corollary5_eq24`; `TrafficShaping.testBlockCount_eq_real_ceil` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 25 | `equation-25` | Minimum budgets in the strict no-savings interval | `TrafficShaping.corollary5_eq25_unconditional` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 26 | `equation-26` | Explicit bad-event union probability and sum chain | `TrafficShaping.block_noSavings_eq26_chain`; `TrafficShaping.testBlockCount_eq_real_ceil` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 27 | `lemma-1` | Greedy matching correctness and sorted scan cost | `TrafficShaping.greedy_true_iff_feasible`; `TrafficShaping.scan_true_iff_feasible`; `TrafficShaping.scan_ops_le_five_mul_H` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 28 | `lemma-2` | Terminal feasibility forces reserve slots | `TrafficShaping.terminal_subset_of_feasible`; `TrafficShaping.prefix_card_le_sub_of_terminal_feasible` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 29 | `lemma-3` | Concrete causal execution delivery and hard cap | `TrafficShaping.onRepair_feasible`; `TrafficShaping.executeState_served_eq`; `TrafficShaping.execute_cap`; `TrafficShaping.execute_causal` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 30 | `lemma-4` | Preservation of feasible base schedules | `TrafficShaping.execute_eq_of_feasible` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 31 | `theorem-1` | All mechanisms: converse, attained optimum and epsilon independence | `TrafficShaping.noncausal_converse_bound`; `TrafficShaping.causal_converse_bound`; `TrafficShaping.noncausal_optimum_eq`; `TrafficShaping.causal_optimum_eq`; `TrafficShaping.both_optima_attained_at_zero` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 32 | `corollary-1` | Additive budget penalty and ratio | `TrafficShaping.corollary1_real_difference_bounds`; `TrafficShaping.corollary1_budget_bounds`; `TrafficShaping.corollary1_ratio_le_two`; `TrafficShaping.corollary1_sharpness` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 33 | `corollary-2` | Uniform same-budget privacy comparison | `TrafficShaping.onGameValue_ge_rho_mul_offGameValue`; `TrafficShaping.privacy_gap_bounds` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 34 | `corollary-3` | Perfect privacy at the exact common minimum budget | `TrafficShaping.corollary3_perfect_privacy_budgets`; `TrafficShaping.corollary3_eq20`; `TrafficShaping.perfect_privacy_both_attainable`; `TrafficShaping.perfect_privacy_mechanism_budget_lower` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 35 | `corollary-4` | Zero delay, including degenerate prefix and one arrival | `TrafficShaping.zero_delay_offGameValue`; `TrafficShaping.zero_delay_onGameValue`; `TrafficShaping.zero_delay_onGameValue_zero_of_lt`; `TrafficShaping.zero_delay_m_one_optimum_gap` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 36 | `corollary-5` | Strict no-savings interval and endpoint exclusion | `TrafficShaping.corollary5_eq24`; `TrafficShaping.corollary5_eq25_unconditional`; `TrafficShaping.block_noSavings_eq26_chain` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 37 | `budget-impossibility` | No admissible mechanism when the cap is below workload | `TrafficShaping.mechanism_impossible_of_budget_lt` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 38 | `epsilon-independence` | Exact optima are independent of finite nonnegative epsilon | `TrafficShaping.noncausal_optimum_epsilon_independent`; `TrafficShaping.causal_optimum_epsilon_independent` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 39 | `full-input-reduction` | All active input rows reduce exactly to full-weight rows | `TrafficShaping.full_row_reduction`; `TrafficShaping.activeRowMinimum_eq_worst` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 40 | `finite-game-duality` | Strong duality and matching optimal primal-dual laws | `TrafficShaping.off_strong_duality`; `TrafficShaping.on_strong_duality`; `TrafficShaping.off_exists_strongly_optimal`; `TrafficShaping.on_exists_strongly_optimal` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 41 | `privacy-interpretation` | Optimal randomized equal-prior accuracy and active-pair bound | `TrafficShaping.Law.tv_triangle`; `TrafficShaping.Law.optimal_equal_prior_accuracy`; `TrafficShaping.active_pair_tv_bound`; `TrafficShaping.participation_accuracy_bound`; `TrafficShaping.table2_H16_half_privacy_accuracy`; `TrafficShaping.table2_H16_half_attainable_accuracy` | Manifest anchor is present; the concrete H=16 attainment statement is at `TableBudgetStatements.lean:263–277`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 42 | `corollary-1-sharpness` | Entire family with B_off=m and B_on=2m | `TrafficShaping.corollary1_sharpness` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 43 | `gap-asymptotics` | Actual loss gap: O(1/H) uniformly over D and general zero limit | `TrafficShaping.privacy_gap_uniform_inverse_bound`; `TrafficShaping.privacy_gap_isBigO_inverse`; `TrafficShaping.privacy_gap_tendsto_zero` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 44 | `matching-cost` | Correct operational sorted matcher with explicit linear bound | `TrafficShaping.scan_true_iff_feasible`; `TrafficShaping.scan_ops_le_five_mul_H`; `TrafficShaping.fastMatch_iff_feasible` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 45 | `queue-cost` | Actual H transitions and queue capacity m | `TrafficShaping.execute_exactly_H_steps`; `TrafficShaping.executeState_queue_length_le` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 46 | `matrix-cardinalities` | Exact row/column counts and C(48,8)=377348994 | `TrafficShaping.fullInput_card`; `TrafficShaping.offSchedule_card`; `TrafficShaping.onSchedule_card`; `TrafficShaping.onSchedule_card_fifty` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 47 | `example-execution` | Exact unchanged and switched output traces | `TrafficShaping.articleExecute_base`; `TrafficShaping.articleExecute_switch`; `TrafficShaping.articleExecute_base_servicePairs`; `TrafficShaping.articleExecute_switch_servicePairs`; `TrafficShaping.articleExecute_switch_first_activation`; `TrafficShaping.articleExecute_base_transmission_card`; `TrafficShaping.articleExecute_switch_transmission_card` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 48 | `strict-threshold-endpoint` | H=2,m=1,D=0,B=1 endpoint counterexample | `TrafficShaping.articleStrictThresholdEndpoint` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 49 | `periodic-observation` | Equal limiting density and disjoint deterministic timing laws | `TrafficShaping.phase_zero_density`; `TrafficShaping.phase_one_density`; `TrafficShaping.phase_laws_tv_one` | Manifest anchor is present and its declaration(s) are listed in `Audit.lean`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 50 | `qualitative-causality-gap` | H=8,D=2,m=2,B=3: noncausal loss 1/2 and causal loss 1 | `TrafficShaping.qualitative_causality_gap`; `TrafficShaping.qualitative_causal_loss_lower` | Concrete exact gap and lower-bound theorems at `TableBudgetStatements.lean:241–259`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 51 | `table-2-row-1` | Table 2 exact thresholds: H=8, D=1, m=2 | `TrafficShaping.table2_row_1` | Concrete row theorem and exact certificates at `TableBudgetStatements.lean:10–23`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 52 | `table-2-row-2` | Table 2 exact thresholds: H=8, D=2, m=2 | `TrafficShaping.table2_row_2` | Concrete row theorem and exact certificates at `TableBudgetStatements.lean:25–38`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 53 | `table-2-row-3` | Table 2 exact thresholds: H=8, D=3, m=2 | `TrafficShaping.table2_row_3` | Concrete row theorem and exact certificates at `TableBudgetStatements.lean:40–53`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 54 | `table-2-row-4` | Table 2 exact thresholds: H=12, D=1, m=2 | `TrafficShaping.table2_row_4` | Concrete row theorem and exact certificates at `TableBudgetStatements.lean:55–68`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 55 | `table-2-row-5` | Table 2 exact thresholds: H=12, D=2, m=2 | `TrafficShaping.table2_row_5` | Concrete row theorem and exact certificates at `TableBudgetStatements.lean:70–83`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 56 | `table-2-row-6` | Table 2 exact thresholds: H=12, D=3, m=2 | `TrafficShaping.table2_row_6` | Concrete row theorem and exact certificates at `TableBudgetStatements.lean:85–98`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 57 | `table-2-row-7` | Table 2 exact thresholds: H=16, D=1, m=2 | `TrafficShaping.table2_row_7` | Concrete row theorem and exact certificates at `TableBudgetStatements.lean:100–113`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 58 | `table-2-row-8` | Table 2 exact thresholds: H=16, D=2, m=2 | `TrafficShaping.table2_row_8` | Concrete row theorem and exact certificates at `TableBudgetStatements.lean:115–128`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 59 | `table-2-row-9` | Table 2 exact thresholds: H=16, D=3, m=2 | `TrafficShaping.table2_row_9` | Concrete row theorem and exact certificates at `TableBudgetStatements.lean:130–143`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 60 | `table-3-row-1` | Table 3 exact losses: H=8, D=1, m=3, B=5 | `TrafficShaping.table3_row_1` | Concrete exact-loss theorem at `TableBudgetStatements.lean:145–155`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 61 | `table-3-row-2` | Table 3 exact losses: H=8, D=2, m=3, B=4 | `TrafficShaping.table3_row_2` | Concrete exact-loss theorem at `TableBudgetStatements.lean:157–167`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 62 | `table-3-row-3` | Table 3 exact losses: H=10, D=1, m=4, B=7 | `TrafficShaping.table3_row_3` | Concrete exact-loss theorem at `TableBudgetStatements.lean:169–179`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 63 | `table-3-row-4` | Table 3 exact losses: H=10, D=2, m=4, B=7 | `TrafficShaping.table3_row_4` | Concrete exact-loss theorem at `TableBudgetStatements.lean:181–191`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 64 | `table-3-row-5` | Table 3 exact losses: H=10, D=1, m=3, B=7 | `TrafficShaping.table3_row_5` | Concrete exact-loss theorem at `TableBudgetStatements.lean:193–203`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 65 | `table-3-row-6` | Table 3 exact losses: H=12, D=2, m=3, B=7 | `TrafficShaping.table3_row_6` | Concrete exact-loss theorem at `TableBudgetStatements.lean:205–215`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 66 | `table-3-row-7` | Table 3 exact losses: H=12, D=1, m=4, B=9 | `TrafficShaping.table3_row_7` | Concrete exact-loss theorem at `TableBudgetStatements.lean:217–227`. | Source evidence PASS; integrated kernel/full gate PASS. |
| 67 | `table-3-row-8` | Table 3 exact losses: H=14, D=2, m=4, B=9 | `TrafficShaping.table3_row_8` | Concrete exact-loss theorem at `TableBudgetStatements.lean:229–239`. | Source evidence PASS; integrated kernel/full gate PASS. |

## Verification boundary

The saved exact-table checker already passed for all nine Table 2 rows, the
qualitative frontier, and the saved finite-game records. This review also
confirmed the source-level set counts above and the exact concrete theorem
ranges. No additional kernel compilation was started here, so this document
makes no claim about the parent task's final compiler or axiom-gate output.

## Integration evidence appended by the coordinating task

Run `20260912T134526Z-0bf54535` completed at `2026-09-12T13:47:31.281731+00:00` with PASS. The [complete report](../verification/article-complete/ARTICLE-CHECK.json) SHA-256 is `80fde35447373f7816ce8e141a8f1c7b7371c62358074a97ba654d3733f1e116`. The formal gate emitted 257 reports for 257 requested declarations and accepted all 67 inventory items. The combined gate also passed the regression tests, source regeneration of all 95 certificates, exact corollary checks, and table checks. This subsequent integration evidence is distinct from the source reviewer's work.
