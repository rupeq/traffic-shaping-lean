# Semantic audit of the foundation modules

This audit covers only `formal/TrafficShaping/Model.lean`,
`formal/TrafficShaping/Law.lean`, and `formal/TrafficShaping/Game.lean`, against
the model and Theorem 1 in
`article-1-final-2026-09-10-r4/international-en/manuscript.md` (sections 2–3).
It is a semantic review of the definitions and helper theorems; it is not a
claim that the execution, converse, or main assembly is complete.

## Verdict

**PASS under the manuscript's stated finite-session assumptions.** The three
modules do not silently change the intended binary, unit-service model. A
`Trace` is an extensional binary slot trace, `Feasible` is exactly an
injective assignment of all arrivals to distinct visible transmission slots,
`Law.tv` is half the finite L1 distance, and the repair identity is valid for
every finite source law subject to its two explicit map conditions. `Game`
proves attainment of the supremum by compactness and validates the required
primal/dual matching certificate.

The findings below are conditions that the later mechanism, converse, and root
theorem must supply explicitly. They are not hidden assumptions in the proofs,
but the foundation modules do not supply them themselves.

## `Model.lean`

### What matches

* `Trace H := Finset (Fin H)` (`Model.lean:7`) is an exact finite encoding of a
  binary trace on slots `0, ..., H-1`: membership means one visible
  transmission and set extensionality prevents duplicate transmissions in a
  slot. This matches the manuscript's `Y ∈ {0,1}^H` and the one-transmission
  per-slot assumption (`manuscript.md:49–53`). It intentionally does not carry
  a real/dummy label.
* `Input H m` and `FullInput H m` (`Model.lean:9–11`) encode respectively
  `|x| ≤ m` and `|x| = m`. Since an input is a set of slot positions, each one
  is one real packet, exactly as in the binary-arrival model.
* `Feasible` (`Model.lean:21–26`) has a total function from the subtype of
  arrivals in `x` to `Fin H`, requires injectivity, requires every assigned
  slot to belong to `y`, and imposes
  `arrival ≤ service ≤ arrival + D`. Thus every real packet is served exactly
  once, distinct packets use distinct slots, and extra elements of `y` are
  available as dummies. The finite codomain enforces service before slot `H`.
* The manuscript writes the upper bound as
  `service ≤ min(arrival + D, H - 1)` (`manuscript.md:49–53`). For a service
  value in `Fin H`, `service < H` already holds, so the inequality in
  `Feasible` is equivalent to that clipped deadline. No deadline condition is
  lost by the natural-number formulation.
* `feasible_self`, `Feasible.mono_input`, and `Feasible.mono_output`
  (`Model.lean:51–71`) establish the intended assignment monotonicities, and
  `Feasible.card_le` (`Model.lean:76–85`) proves that a feasible output has at
  least as many slots as the input has arrivals. These are the exact finite
  facts used by the coverage construction and support extension.
* `OffSchedule` and `OnSchedule` (`Model.lean:28–31`) match the saturated
  classes in equations (4)–(5): exact budget `B`, with all terminal `m` slots
  present in the on class.

The model permits an arbitrary injective matching rather than imposing FIFO.
That is correct for the manuscript's definition of the feasible set
(`manuscript.md:71–77`); FIFO belongs to the later online construction and its
greedy proof.

### Conditions and limits

1. **The parameter inequalities are external.** The types do not enforce
   `H ≥ 1`, `1 ≤ m ≤ H`, or `m ≤ B ≤ H`. In particular, `terminal H m` is the
   last `m` slots only under `m ≤ H`; if `m > H`, natural subtraction makes it
   the whole horizon. Theorem 1's row and schedule classes therefore need
   explicit nonemptiness proofs under `1 ≤ m ≤ H` and `m ≤ B ≤ H`.
2. **The cap is deliberately separate from feasibility.** `Feasible D x y`
   has no `y.card ≤ B` premise. This is semantically right because a cap is a
   mechanism property, while feasibility concerns delivery, but a later
   mechanism theorem must impose the hard cap on every output law. Privacy
   slack cannot be used to excuse a cap or deadline violation.
3. **Exact-budget classes are canonical saturated supports.** `OffSchedule`
   and `OnSchedule` contain traces with exactly `B` slots. They are not by
   themselves the class of all legal outputs with at most `B` slots. Passing
   from an arbitrary capped trace to an exact-budget trace requires a separate
   finite extension argument together with `Feasible.mono_output`; it is not
   a consequence of the subtype definitions alone.
4. **No operational causality is present here.** `Model.lean` contains no
   output law, state, arrival-observation order, or prefix-equality condition.
   It establishes the support predicate only. The online causal semantics and
   the fact that a concrete execution produces a feasible, capped trace must
   come from later modules.
5. **The representation has the manuscript's scope.** It assumes binary
   arrivals, unit service, a fixed finite horizon, and no simultaneous packets
   or variable-size/batched service. Those are model boundaries, not bugs in
   the encoding.

## `Law.lean`

### What matches

* `Law α := stdSimplex ℝ α` (`Law.lean:7`) is a nonnegative real mass
  function summing to one on a finite alphabet. `mass`, `map`, `mass_map`, and
  `map_comp` (`Law.lean:20–24`, `59–113`) implement event mass and finite
  push-forward without measure-theoretic assumptions.
* `tv p q := (∑ a, |p a - q a|) / 2` (`Law.lean:116–117`) is exactly the
  manuscript's `1/2` L1 definition (`manuscript.md:65–67`). The proof of
  `tv_eq_event_difference` (`Law.lean:152–159`) selects the positive-difference
  event and establishes the finite variational identity. The event bounds,
  `zero_privacy_iff_tv`, and `tv_le_one` (`Law.lean:161–198`) correctly give
  the two-sided zero-epsilon privacy equivalence and the usual `[0,1]` TV
  bound.
* `coupling_tv_le` (`Law.lean:206–221`) is the shared-seed coupling inequality:
  the TV distance between `map f p` and `map g p` is at most the source mass
  on which the deterministic maps differ.
* `repair_tv_identity` (`Law.lean:223–247`) is genuinely general for every
  finite law `p`: if `repair` always lands in finite set `F` and agrees with
  `base` whenever `base` is in `F`, then
  `TV(map repair p, map base p)` equals the base mass outside `F`. The first
  inequality is the coupling bound; the reverse inequality uses the event
  `Fᶜ`, whose repair mass is zero. This is exactly the identity needed when a
  sampled base schedule is repaired by a deterministic function of the same
  sampled schedule.
* `PrivatePair` (`Law.lean:250–258`) contains both event inequalities. The
  `privatePair_zero_iff_tv` theorem and `privatePair_of_tv`
  (`Law.lean:256–269`) correctly connect zero-epsilon TV privacy to finite
  nonnegative epsilon.
* `forbidden_event` (`Law.lean:271–276`) has the converse orientation needed
  for an infeasible event: if the first law gives that event mass zero, the
  second privacy inequality bounds its mass under the other law, independently
  of epsilon.

### Conditions and limits

1. **The identity is for deterministic shared-source maps.** The theorem's
   laws are `p.map repair` and `p.map base`, so both outputs use the same source
   sample. It does not assert the same equality for an arbitrary stochastic
   repair kernel or for independently resampled randomness. A later mechanism
   may apply it only after exposing the common sampled base schedule (or another
   common seed).
2. **The alphabet is complete and finite.** Events are `Finset α` and TV sums
   over all of `α`. This is exactly right for `Trace H` and finite schedule
   classes, including laws that assign zero mass to capped-out traces, but it
   does not cover an unbounded or continuous output alphabet.
3. **The privacy parameter domain is not encoded in `PrivatePair`.** `ε` and
   `δ` are arbitrary reals in the definition. The manuscript requires finite
   `ε ≥ 0` and `0 ≤ δ ≤ 1` (`manuscript.md:61–69`); the root theorem must carry
   those assumptions. In particular, the lift from TV to `PrivatePair` uses the
   explicit hypothesis `hε : 0 ≤ ε` (`Law.lean:260–269`).
4. **The library does not create mechanism laws.** It proves finite-law
   algebra and the repair/coupling facts. Causality, hard feasibility, and the
   cap still have to be established for the concrete execution and for an
   arbitrary mechanism in the converse.

## `Game.lean`

### What matches

* `coverage`, `worst`, and `value` (`Game.lean:21–32`) are precisely
  `∑s q_s A_{is}`, the minimum over input rows, and the supremum of attainable
  worst coverage. For an indicator matrix, coverage is the law mass of the
  feasible schedule event.
* `coverage_continuous` and `worst_continuous` (`Game.lean:38–50`) establish
  continuity of the finite linear rows and their finite minimum.
* `exists_optimal` (`Game.lean:69–82`) applies compactness of the finite
  simplex and continuity to obtain a maximizer `qStar`; it then proves both
  `worst q ≤ worst qStar` for every law and `worst qStar = value`. Thus
  attainment is proved, rather than assumed. `value_attained` and
  `worst_le_value` (`Game.lean:84–96`) expose this fact for later use.
* `weak_duality_certificate` (`Game.lean:168–212`) checks the needed data
  explicitly: both vectors are nonnegative and normalized, every row has
  coverage at least `v`, and every column has weighted coverage at most `u`.
  The finite-sum rearrangement then proves `v ≤ u`. `value_le_of_column_certificate`
  and `matching_certificate` (`Game.lean:257–298`) provide the stronger
  certificate workflow: a common scalar with the row and column inequalities
  pins down both the game value and the candidate primal law's worst coverage.

### Conditions and limits

1. **This is a generic matrix game, not yet the scheduling instantiation.**
   The module does not identify `I` with `FullInput H m`, `S` with
   `OffSchedule H B` or `OnSchedule H m B`, or `A` with the feasibility
   indicator. The root assembly must provide those definitions, the finite
   instances, and nonemptiness. For the manuscript's theorem these require
   `1 ≤ m ≤ H` and `m ≤ B ≤ H`; otherwise `worst` or the schedule simplex may
   have no intended elements.
2. **Entrywise coverage bounds are hypotheses, not part of `A`.** `A` is an
   arbitrary real matrix. The bounds `0 ≤ A ≤ 1` are proved only by the
   separate lemmas with explicit hypotheses (`Game.lean:108–166`). An
   indicator coverage matrix must be shown to satisfy those hypotheses before
   claiming `0 ≤ value ≤ 1` or interpreting `1 - value` as a privacy
   parameter.
3. **The certificate is weak duality plus a matching checker.** The module
   does not prove a general dual optimizer or a standalone strong-duality
   theorem. That is sufficient for an exact rational candidate: checking the
   row and column inequalities with a common value invokes `matching_certificate`.
   A claim of strong duality for every instantiated game still needs the finite
   LP/minimax bridge in the root proof or an explicitly imported theorem.

## Read-only verification and remaining scope

The audited helper declarations were checked with Lean's `#print axioms`.
`Feasible.card_le`, `Law.tv_eq_event_difference`, `Law.coupling_tv_le`,
`Law.repair_tv_identity`, `Law.privatePair_zero_iff_tv`, `exists_optimal`, and
`matching_certificate` report only `propext`, `Classical.choice`, and
`Quot.sound`, with no project-specific axiom or unfinished-proof dependency.

This audit therefore clears the three foundation modules for use under the
explicit assumptions above. It does not establish the manuscript's Theorem 1:
the concrete causal execution, arbitrary-mechanism converse, saturation of
cap-bounded outputs into the exact schedule classes, and final theorem assembly
remain separate proof obligations.
