# Optimum semantic audit against manuscript r5

This audit covers the optimum theorem and its semantic dependency chain in
`Model.lean`, `Law.lean`, `Game.lean`, `Mechanism.lean`, `Saturation.lean`,
`Matching.lean`, `Converse.lean`, `Achievability.lean`, `MainTheorem.lean`,
and the current execution files.  The comparison target is Theorem 1 and the
causal construction in Sect. 3 of the r5 manuscript.

## Verdict

**PASS for Theorem 1 in both mechanism classes, under the manuscript’s stated
finite-session hypotheses.**  The finite model, the arbitrary-mechanism
converse, the noncausal repair, the causal execution, and both `IsLeast`
proofs are connected by actual Lean theorems.  The exact identities are

```text
noncausal optimum = 1 - value(offMatrix)
causal optimum    = 1 - value(onMatrix)
```

for `1 ≤ m ≤ H`, `m ≤ B ≤ H`, every `D : ℕ`, and every finite real
`ε ≥ 0`.  The secondary budget bounds, privacy-gap bound, perfect-privacy
formula, zero-delay formula, and no-savings threshold are a separate scope:
they are described in the manuscript and checked by the computation scripts,
but are not formal Lean theorems in the current root module.

## Model and privacy semantics

`Trace H` and `Input H m` are finite sets of one-slots and inputs with at most
`m` arrivals (`Model.lean:7–11`).  This is exactly the manuscript’s binary
arrival and binary output model; set membership rules out simultaneous
duplicate arrivals and duplicate transmissions.  `Feasible` is an injective
map from arrivals to `Fin H` service slots, with release and delay bounds
(`Model.lean:21–27`).  Its codomain enforces delivery by slot `H - 1`, and
injectivity enforces unit service capacity.  The hard budget is intentionally
separate from `Feasible` and is imposed by the mechanism support contract.

`Mechanism` assigns a complete-trace finite law to every admissible input and
requires every positive-mass output to be feasible and to satisfy the cap
(`Mechanism.lean:16–25`).  Since laws are simplex points with nonnegative
masses, this is an almost-sure support statement and matches the manuscript’s
hard constraints.  `Causal` is equality of the push-forward laws of output
prefixes under equal input prefixes (`Mechanism.lean:29–35`), which is the
manuscript’s causal definition for randomized stateful mechanisms.  The
formalization uses an extensional law interface rather than an explicit state
machine; a representation theorem from every such finite prefix-law family
to an implementation is not included.  This is appropriate as the semantic
mechanism class used by the converse, but implementation claims must use the
concrete execution construction.

`Private` quantifies over every nonempty admissible input and applies the two
event inequalities in `Law.PrivatePair` against the empty-input law
(`Mechanism.lean:36–39`, `Law.lean:250–254`).  The complete finite trace is the
event alphabet.  The loss sets add the manuscript domain `0 ≤ δ ≤ 1`
(`MainTheorem.lean:15–21`); the `PrivatePair` predicate itself does not impose
parameter-domain bounds, so the theorem’s explicit `hε : 0 ≤ ε` and loss-set
side conditions are material.

The finite TV lemmas are semantically suitable: event differences are bounded
by the complete-alphabet TV distance, zero-epsilon event privacy is equivalent
to TV, and the forbidden-event lemma removes the multiplicative term when the
active law gives an event zero mass (`Law.lean:152–192`, `256–276`).  The exact
repair identity (`Law.lean:223–247`) proves equality from a same-seed coupling,
not merely an upper bound.

## Finite game and saturation

`Game.lean` defines row coverage, worst coverage, and the compact finite-simplex
value (`Game.lean:21–32`, `69–88`).  The coverage matrices in
`Mechanism.lean:46–67` use full inputs as rows and exact-cardinality schedules
as columns.  `OffSchedule` and `OnSchedule` enforce respectively `|y| = B`
and `|y| = B` plus the last `m` terminal slots (`Model.lean:28–31`), matching
Eqs. (4)–(6) of the manuscript.  The explicit nonempty witnesses in
`MainTheorem.lean:49–59` are supplied from `m ≤ H` and `m ≤ B ≤ H`.

The game value is attained by compactness and the matrix entries are bounded
in `[0,1]` (`Game.lean:69–88`, `145–166`).  `Matching.lean:311–358`
establishes the greedy earliest-slot characterization of `Feasible`, which is
the finite matching principle used by the execution argument and the
manuscript’s Lemma 1.

The saturation lemmas extend an arbitrary trace to exact budget while
preserving its slots (`Saturation.lean:85–167`).  For the causal family they
also add the terminal reserve when the prefix-cardinality bound holds
(`Saturation.lean:130–167`).  `terminal_subset_of_feasible` and
`prefix_card_le_sub_of_terminal_feasible` prove that a feasible terminal full
input forces all terminal slots and leaves at most `B - m` prefix slots
(`Saturation.lean:185–221`).  These are the exact support facts needed for the
causal converse; the saturation functions are proof-level transformations of
the empty law and do not claim to be online actions.

## Converse

`active_feasible_mass_lower` applies the second privacy inequality to the
complement of the active feasible event and obtains

```text
1 - δ ≤ P₀(Fₓ).
```

(`Converse.lean:38–60`).  This correctly uses only hard support feasibility,
and the bound is independent of epsilon.  `off_row_lower` pushes the empty law
through exact-budget saturation and uses output monotonicity
(`Converse.lean:131–153`).  `on_row_lower` adds the equal-prefix terminal-input
argument and the prefix-cardinality bound before causal saturation
(`Converse.lean:155–180`).  The exported theorems
`noncausal_converse_bound` and `causal_converse_bound` then take the worst row
and the finite game value (`Converse.lean:182–223`).

Thus the formal noncausal and causal lower bounds are universal over the
semantic `Mechanism` class and correctly cover all full rows.  The smaller
input class is handled on the achievability side by extension to a full input.

## Noncausal attainment and optimum

The generic repair layer has the right law-level semantics
(`Achievability.lean:26–92`).  It pushes an input-independent schedule law
through a deterministic repair, proves that the empty input leaves the base
law unchanged, and proves causality when same-seed output prefixes agree.  Its
exact TV theorem and `input_coverage_lower` lift full-input game coverage to
every admissible input (`Achievability.lean:72–125`).

`offRepair` retains a feasible exact-budget base schedule and otherwise emits
the arrival trace (`Achievability.lean:127–152`).  The fallback is feasible by
`feasible_self` and has at most `m ≤ B` transmissions.  On the empty input all
traces are feasible, so the base law is retained.  `offMechanism_private` and
`noncausal_attainment` assemble the exact noncausal construction from an
optimal game law (`Achievability.lean:154–177`).

`noncausal_optimum_isLeast` proves both directions of a true minimum: an
attaining mechanism at `1 - offGameValue`, and the converse inequality for an
arbitrary loss witness (`MainTheorem.lean:79–91`).  The `sInf` equality and
epsilon-independence follow from that `IsLeast` result
(`MainTheorem.lean:93–104`).  Under `1 ≤ m ≤ H` and `m ≤ B ≤ H`, this covers
the manuscript’s complete noncausal statement for every finite
`ε ≥ 0`, including `ε = 0`.

## Causal attainment and the concrete execution bridge

The causal construction is now connected all the way to the optimum theorem.
`onRepair` is the actual `execute` function on an `OnSchedule` base trace
(`OnAchievability.lean:12–13`).  Its four required repair properties are
proved separately:

* `onRepair_cap` delegates to `execute_cap`, whose mode and queue invariants
  bound every concrete output by `B` (`OnAchievability.lean:15–18`,
  `ExecutionBudget.lean:8–42`).
* `onRepair_prefix` delegates to `execute_causal`, which proves equality of
  output-prefix traces from equality of input prefixes by induction over the
  actual `step` transition (`OnAchievability.lean:20–24`,
  `ExecutionCausality.lean:58–80`, `180–198`).
* `onRepair_empty` is the concrete empty-input execution identity
  (`OnAchievability.lean:26–28`, `ExecutionCausality.lean:200–203`).
* `onRepair_feasible` combines the actual served-packet matching theorem with
  the actual terminal-reserve delivery theorem
  (`OnAchievability.lean:30–37`).  `executeState_servedFeasible` is proved by
  induction over `step` (`Execution.lean:67–163`), while
  `executeState_served_eq` follows from `executeState_queue_empty` and the
  queue-prefix invariant (`ExecutionDelivery.lean:150–223`).  The latter uses
  the terminal reserve at every concrete transition; it is not an assumed
  final-delivery hypothesis.

The preservation property required for the exact TV identity is also proved
from the real execution.  `onRepair_fixes` calls
`execute_eq_of_feasible` (`OnAchievability.lean:50–52`), whose induction in
`ExecutionPreservation.lean:356–519` maintains schedule mode, exact output
prefix equality, and a feasible matching from unserved arrivals to residual
base slots.  At a silent slot whose head deadline would trigger a switch, the
residual matching yields a contradiction; at a scheduled one-slot, the
matching is updated by the FIFO earliest-slot theorem.  This is the concrete
schedule-preservation proof needed by the manuscript’s Lemma 4.

`onMechanism` then pushes an arbitrary law on `OnSchedule` through this actual
repair (`OnAchievability.lean:39–41`).  `onMechanism_causal` applies the
generic law-level causality lemma to `onRepair_prefix` (`43–48`), and
`onMechanism_tv` applies the exact repair identity using
`onRepair_feasible`, `onRepair_cap`, and `onRepair_fixes` (`54–61`).
`onMechanism_private` lifts that TV identity to every finite `ε ≥ 0`
(`63–69`).  Finally, `causal_attainment` chooses an optimizer of the on-game
and returns an actual causal `Mechanism` with the target privacy loss
(`71–82`).  No step in this chain supplies a postulated feasibility,
preservation, or causality hypothesis: each is discharged by the named Lean
theorem above.

## Both optimum proofs and parameter domain

`causal_optimum_isLeast` is the exact causal counterpart of the noncausal
proof (`MainTheorem.lean:107–120`).  Its first direction obtains membership in
the loss set from `onGameValue_bounds` and `causal_attainment`; its second
direction applies `causal_converse_bound` to an arbitrary loss witness
`δ ∈ causalLosses`.  Therefore it proves a true minimum over all semantic
mechanisms satisfying the hard support/cap contract and the prefix-law
causality predicate, rather than only over the constructed execution.  The
noncausal `IsLeast` proof has the same universal structure
(`MainTheorem.lean:80–92`).

`causal_optimum_eq` and `noncausal_optimum_eq` derive the respective `sInf`
equalities from `IsLeast` (`MainTheorem.lean:94–98`, `122–126`), so neither
infimum equality relies on an unproved attainment assumption.  The two
epsilon-independence theorems rewrite the same game value at `ε` and `0`
(`MainTheorem.lean:100–105`, `128–133`), and
`both_optima_attained_at_zero` records the two minimum statements at zero
(`MainTheorem.lean:135–141`).

The hypotheses match r5: `hm1 : 1 ≤ m`, `hm : m ≤ H`, `hmb : m ≤ B`, and
`hB : B ≤ H` are explicit in both optimum theorems.  Thus `H ≥ 1` is not
hidden: it follows by arithmetic from `1 ≤ m ≤ H`, and it supplies the
`0 < H` argument required by the concrete execution.  `D : ℕ` encodes the
manuscript condition `D ≥ 0`; there is no additional delay restriction.  The
epsilon parameter is a real number, hence finite, and `hε : 0 ≤ ε` is explicit
in attainment and both optimum theorems.  The loss sets themselves impose
`0 ≤ δ ≤ 1` (`MainTheorem.lean:16–22`), and the game bounds prove that the
attaining value `1 - v` lies in this interval.

For `B < m`, `mechanism_impossible_of_budget_lt` proves
`IsEmpty (Mechanism H m B D)` from a terminal full input and the positive-mass
law point (`MainTheorem.lean:30–48`).  The optimum identities deliberately
require `m ≤ B`; the source does not assign a substantive value to the
`sInf` of an empty loss set in the impossible-budget regime.

## Secondary results are separate

The current Lean root imports the model, games, converses, both attainment
constructions, and the two optimum theorems (`TrafficShaping.lean:1–15`).  It
does not contain formal declarations for manuscript Theorem 2 (additional
budget), Theorem 3 (fixed-budget privacy gap), Proposition 1 (perfect privacy
budget), Proposition 2 (zero-delay closed forms), or Proposition 3 (the
no-savings threshold).  The current proof map explicitly keeps these
secondary statements outside the completed Lean inventory.  The
Python/computation artifacts provide finite-instance certificates and checks;
they do not turn those general secondary statements into Lean proofs.  The
PASS verdict here is therefore specifically for Theorem 1 and the
noncausal/causal optimum identities, not for those later manuscript claims.

## Verification

The full formal target builds with Lean 4.33.1 and the pinned Mathlib cache:

```text
cd /Users/artem.derevago/master_thesis/traffic-shaping-lean/formal
/private/tmp/lean-4.33.1-darwin_aarch64/bin/lake build
/private/tmp/lean-4.33.1-darwin_aarch64/bin/lake env lean Audit.lean
```

The build completed all 8,723 jobs with only linter warnings.  `Audit.lean`
prints the dependency axioms for the completed foundations, both converse
bounds, both execution bridges, both attainment theorems, both `IsLeast`
theorems, the two `sInf` equalities, epsilon-independence, zero-epsilon
attainment, and the impossible-budget theorem.  Every listed result depends
only on Lean’s standard logical axioms `[propext, Classical.choice,
Quot.sound]`; there are no `sorry`, `admit`, user axioms, `unsafe`, or
`native_decide` declarations in the checked chain.
