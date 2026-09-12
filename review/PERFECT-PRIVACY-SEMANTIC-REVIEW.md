# Perfect privacy and the strict no-savings threshold: semantic review

Audit date: 2026-09-11. This review covers
`formal/TrafficShaping/PerfectPrivacy.lean`,
`formal/TrafficShaping/Corollary5.lean`, and
`formal/TrafficShaping/Corollary3.lean`. It checks the explicit schedule,
its cardinality and feasibility for every bounded input, the true minimum
budget claim in Eq. (20), and the unconditional strict-threshold claim in
Eq. (25), against the r9 article statements and their boundary cases.

No source files were edited and no repository-wide build was run.

## Verdict

**PASS.** No substantive semantic defect was found. `perfectSchedule` has
exactly the Eq. (20) number of slots, contains the terminal reserve, and is
feasible for every trace with at most `m` arrivals. The two Dirac repair
mechanisms turn this one fixed schedule into zero-loss noncausal and causal
witnesses. The disjoint block tests prove the strict lower threshold for
every semantic mechanism, and `corollary5_eq25_unconditional` combines that
lower bound with the witnesses to obtain both actual `Nat.find` budget
minima. The strict endpoint is correctly excluded.

## Explicit schedule and Eq. (20) cardinality

Let `p=D+m`, `a=H/p`, and `b=H%p`. The local definitions in
`PerfectPrivacy.lean` implement exactly the article construction:

* `fullBlockSlots q` (`:14--33`) is the image of `Fin m` under
  `q*p + D + j`, namely the last `m` slots of full block `q`.
* `remainderSlots` (`:35--55`) is the image of `Fin (min m b)` under
  `a*p + (b-min m b)+j`, namely the last `min(m,b)` slots of the remainder.
* The bounds and injectivity lemmas (`:57--205`) show that these images are
  within `Fin H`, have the claimed cardinalities, and occupy disjoint
  intervals.

`fullBlockUnion_card` (`:249--271`) sums `m` over the `a` pairwise disjoint
full blocks. `perfectSchedule_eq_block_union` (`:709--734`) proves both
inclusions between the filter definition and that union plus the remainder.
Consequently `perfectSchedule_card` (`:736--741`) derives

```text
|perfectSchedule| = m * (H / (D+m)) + min(m, H%(D+m)).
```

`perfectBudget_eq_quotient_remainder` in `BlockArithmetic.lean` rewrites
this to `m*a + min(m,b)` under the article's
`H=a(D+m)+b`, `b<D+m` decomposition. The natural-number type already
supplies `0≤b`.

`perfectSchedule_terminal_subset` (`:743--751`) proves that the final `m`
slots are present. Thus the same trace is a valid exact-cap
`OffSchedule` and `OnSchedule` at the Eq. (20) budget. The proof works when
the remainder is empty (`b=0`) and when the whole horizon is a remainder
(`a=0`); under `1≤m≤H`, the latter has `min(m,H)=m` slots.

## Feasibility for every bounded input

The key matching fact is `interval_assignment` (`:480--575`). For arrivals
in an interval `[base,base+len)`, it orders the finite set of arrivals,
assigns the rank-indexed service slot in the final `c=min(m,len)` positions,
and takes the maximum with the arrival time. The proof establishes:

```text
base+start ≤ f(a) < base+len,
a ≤ f(a) ≤ a+D,
```

along with injectivity. The inequality `start≤D` follows from
`len≤D+m`; it is also valid when `len≤m`, where `start=0`.

`pp_block_assignment` (`:575--654`) applies that lemma independently to
each full block and to the final partial block. It uses only
`x.card≤m`, so each block's arrival subset has enough final service slots.
`perfectSchedule_feasible` (`:779--985`) partitions every input arrival by
`q=a.val/(D+m)`, applies the block assignment, and combines the assignments.
Outputs from different blocks are injective because each assignment lies in
its own block interval; outputs within a block are injective by the local
assignment theorem. The resulting map is into `Fin H`, lands in
`perfectSchedule`, and satisfies both release and deadline inequalities.

This handles all natural delays, including `D=0`, `D≥H`, and delays larger
than the horizon. At `D=0`, the schedule is all `H` slots and the formula
gives `B0=H`. When `D+m>H`, there is one partial block and the schedule is
the terminal `m` slots, giving `B0=m`.

The block-test converse is independent of the constructive matching. Each
`blockTest` in `BlockTests.lean` is a separate admissible input with
`min(m,H-i(D+m))` arrivals at the beginning of its block. Any feasible
output for that test has an injective assignment into that block's service
interval. `blockService_pairwise_disjoint` and the sigma-type injection in
`block_tests_lower_bound` combine these separate assignments, yielding
`perfectBudget≤|y|` whenever one trace serves all tests. No union of test
arrivals is treated as an admissible input.

## Exact perfect-privacy budgets and attainability

`perfectOffSchedule` and `perfectOnSchedule` in `Corollary5.lean` package the
fixed schedule at the exact Eq. (20) cardinality. The corresponding
`perfectOffMechanism` and `perfectOnMechanism` use a Dirac law on that
base schedule and the standard repairs.

For every full input row, `perfectSchedule_feasible` makes the coverage
matrix entry equal to one. `perfect_off_private_zero` and
`perfect_on_private_zero` therefore obtain `Private M 0 0` from the repair
lemmas. The on witness additionally satisfies `Causal M` by
`onMechanism_causal`; its causal execution preserves the fixed schedule
because the schedule is feasible for every input. Since a zero-TV witness
also gives `Private M ε 0` for every finite `ε≥0`, the construction has
the article's finite-epsilon scope.

`corollary5_eq25_unconditional` first turns these witnesses into game values
one at `B0`, then applies the no-savings budget theorem. Consequently
`corollary3_perfect_privacy_budgets` (`Corollary3.lean:12--21`) proves both
actual `noncausalBudget` and `causalBudget` are exactly `B0` at
`δ=0`. `corollary3_eq20` (`:23--32`) rewrites that identity to the displayed
quotient-remainder formula. `perfect_privacy_causal_attainable` and
`perfect_privacy_both_attainable` (`:48--63`) provide explicit mechanism
attainment at that exact budget for every finite nonnegative epsilon. The
lower theorem `perfect_privacy_mechanism_budget_lower` (`:36--46`) proves
the stronger universal statement: every semantic mechanism with
`Private M ε 0`, causal or not, has `B≥B0`; it does not assume a particular
implementation or require `B≤H`.

## Eq. (24) and the unconditional Eq. (25) threshold

`testBlockCount` is the number of nonempty blocks. `testBlockCount_pos`
requires exactly the article domain `1≤m≤H`, and
`testBlockCount_eq_real_ceil` proves that it equals
`ceil(H/(D+m))`. Thus the source's `K=testBlockCount H m D` is the article's
`K=ceil(H/(D+m))`, not a rounded approximation.

`block_noSavings_delta_lower` in `NoSavingsBlocks.lean` applies the finite
privacy-event union argument to the separate block tests. If `B<B0`, the
mechanism cap prevents any support trace of the empty-input law from being
feasible for all tests simultaneously. Each active test's infeasible event
has empty-law mass at most `δ` by the second privacy inequality, so the
finite union bound gives

```text
1 ≤ K*δ,  hence 1/K ≤ δ.
```

This is independent of the value of finite `ε` and applies to arbitrary
semantic mechanisms. `corollary5_eq24` exposes the article's stated domain
`m≤B<B0` and carries the mechanism privacy hypothesis directly.

`corollary5_eq25_unconditional` (`Corollary5.lean:105--115`) then uses the
zero-loss witnesses at `B0` for the upper budget bound and the preceding
strict lower bound for any smaller selected `Nat.find` budget. It proves

```text
B_noncausal(δ) = B_causal(δ) = B0
```

for `0≤δ≤1` and `δ<1/K`. The explicit `δ≤1` hypothesis is consistent with
the article's privacy parameter domain; given `K≥1` and the strict
`δ<1/K`, it is redundant but harmless.

## Boundary comparison with the article

The Lean hypotheses match the r9 statements and cover the relevant edges:

* `H≥1`, `1≤m≤H`, and `D≥0` are represented by natural parameters plus
  `hm1` and `hm`. `B0` lies in `[m,H]` by `perfectBudget_lower` and
  `perfectBudget_upper`.
* `b=0` gives no remainder test and `K=a`; `b>0` adds exactly one partial
  test with `min(m,b)` arrivals.
* `H=m` gives `B0=m` and `K=1`; the fixed schedule is the whole horizon and
  both budgets equal `m` throughout the strict interval `δ<1`.
* `D=0` gives `B0=H`, while `D+m>H` gives `B0=m` and `K=1`. Both are
  admitted by the universal construction and checker.
* The strict Eq. (25) endpoint is necessary. At `H=2,m=1,D=0`, `B0=2`
  and `K=2`; at `δ=1/K=1/2`, the noncausal budget at `B=1` already meets
  the threshold. The source intentionally proves only `δ<1/K`.

The theorem names `corollary5_eq25_unconditional` and
`corollary3_perfect_privacy_budgets` do not hide additional game-value
hypotheses: the former derives the value-one facts from the explicit
witnesses, and the latter supplies the strict threshold at `δ=0`.

## Verification evidence

Direct compilation with the pinned Lean installation succeeded for:

```text
PATH=/private/tmp/lean-4.33.1-darwin_aarch64/bin:$PATH \
  lake env lean TrafficShaping/PerfectPrivacy.lean
PATH=/private/tmp/lean-4.33.1-darwin_aarch64/bin:$PATH \
  lake env lean TrafficShaping/Corollary5.lean
PATH=/private/tmp/lean-4.33.1-darwin_aarch64/bin:$PATH \
  lake env lean TrafficShaping/Corollary3.lean
```

The first command emitted only linter warnings about unused simp arguments
and names; the second was silent; the third emitted only the existing
unused-`hε` warning in the universal lower-bound theorem. No elaboration
errors occurred.

The independent exact checker
`computations/corollaries_check.py` also completed with `PASS`. Its current
run checked 428 Eq. (20) parameter sets (`H≤12`, `m≤4`, `D≤H+2`), 51,070
universal input/schedule matches, and 35,921 below-budget schedule witnesses.
The Eq. (24)--(25) extension checked 168 parameter sets, 357 block tests,
109,497 below-`B0` offline and causal schedules, 672 strict-threshold
representatives, and the equality boundary above. The checker uses fresh
augmenting-path matching and exact rational arithmetic; these finite checks
support the universal Lean proof but do not replace it.

## Conclusion

The perfect-privacy construction, its all-input feasibility claim, the
minimum-budget identity in Eq. (20), and the unconditional strict
no-savings interval in Eq. (25) are semantically aligned with the article.
No release-blocking issue was found. The only qualification is routine:
`corollary3_eq20` takes the quotient-remainder decomposition as hypotheses,
while the arithmetic module separately supplies the canonical quotient and
remainder facts.

