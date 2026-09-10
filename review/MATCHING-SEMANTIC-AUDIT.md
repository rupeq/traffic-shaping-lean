# Semantic audit of the greedy matching lemma

This audit covers `formal/TrafficShaping/Matching.lean` against the greedy
feasibility lemma in both the r4 and r5 English manuscripts. The relevant
manuscript text is unchanged between those revisions: the model is binary,
unit-service, finite-horizon, and feasibility means an injective assignment
whose service slot lies between the arrival and its deadline
(`international-en/manuscript.md:49–77`). `Execution.lean` was inspected only
to identify the interface with the operational FIFO rule; this document does
not issue an execution-correctness verdict.

## Verdict

**PASS for the finite matching predicate, including empty inputs and `Fin 0`.**
The recursive Boolean predicate chooses the least arrival, then the least
unused output slot not before that arrival, checks its deadline, erases the
chosen pair, and recurses. The theorem
`greedy_true_iff_feasible` (`Matching.lean:311–356`) proves equivalence with
the injective assignment predicate from `Model.lean` for every `H`, `D`, input
trace, and output trace. No assumption such as `0 < H`, nonempty input, or
positive delay is hidden in that theorem.

The formal exchange proof covers the occupied-earlier-slot case explicitly;
it is not relying on a mistaken assumption that the earliest greedy slot is
unused. The remaining limitation is an interface obligation: the current
`Execution.lean` has FIFO queue invariants but no theorem yet identifying its
schedule-mode service pairs with the recursive `greedy` relation. Thus the
matching theorem is sound as a standalone feasibility result, while its use in
the switch-to-service proof still needs that bridge.

## Definition and correspondence

`candidates` and `greedyStep` (`Matching.lean:15–23`) implement exactly the
manuscript rule: filter `y` to slots `s` with `a ≤ s`, choose the least such
slot, and fail if there is no candidate or the selected slot exceeds
`a + D`. `greedy` (`Matching.lean:25–39`) processes the least arrival in `x`,
erases that arrival and selected service slot, and returns `true` exactly when
all arrivals are matched.

The upper bound uses `s.val ≤ a.val + D` rather than the manuscript's clipped
`s ≤ min(a + D, H - 1)`. This is semantically equivalent because the selected
service has type `Fin H`, hence `s.val < H`; the same equivalence is used by
`Model.Feasible`. The release inequality is retained directly by the
candidate filter.

The local theorems `mem_candidates`, `earliest_available_mem`, and
`earliest_available_le` (`Matching.lean:41–54`) establish membership,
release-time validity, and minimality. `greedyStep_some_spec`
(`Matching.lean:84–100`) packages the complete one-step specification. The
failure lemmas (`Matching.lean:112–141`) show respectively that a feasible
assignment must give the least arrival a candidate slot, and that if the least
candidate misses the deadline then no feasible assignment exists.

## Exchange case: occupied greedy slot

The key equivalence is `feasible_erase_min_iff`
(`Matching.lean:143–310`). Let `a` be the least arrival, let `s` be the least
candidate slot for `a`, and let `s₀` be the slot assigned to `a` by an arbitrary
feasible assignment. Minimality gives `s ≤ s₀`.

* If `s = s₀`, the proof restricts the assignment to `x.erase a`. Injectivity
  proves that no residual arrival uses the erased slot `s`, so all residual
  assignments land in `y.erase s`.
* If `s ≠ s₀`, the proof defines the residual assignment
  `g b := if f (emb b) = s then s₀ else f (emb b)` (`Matching.lean:201–202`).
  This covers both subcases: if `s` was unused, no value changes; if `s` was
  occupied, the later packet using `s` is exchanged onto `s₀`.
* Injectivity is checked by all four cases of whether two residual assignments
  equal `s` (`Matching.lean:204–228`). A mixed case would force a residual
  input to be the erased head `a`, contradicting membership in `x.erase a`.
* For the exchanged packet, `a ≤ b` because `a` is the least input slot, and
  `b ≤ s` because its old assignment was `s`. Since `s ≤ s₀`, its release
  inequality transfers to `s₀`; since `s₀ ≤ a + D` and `a ≤ b`, its deadline
  inequality transfers to `s₀ ≤ b + D` (`Matching.lean:230–252`). The head
  packet receives `s`, whose membership, release, and deadline facts come from
  the candidate and `hs` hypotheses.
* The reverse direction constructs an assignment for the original input by
  assigning `a` to `s` and lifting the residual assignment from
  `x.erase a`/`y.erase s` (`Matching.lean:263–310`). The residual output
  membership in `y.erase s` excludes a collision with the head assignment.

This is the same exchange required by the manuscript proof
(`manuscript.md:75–77`): an earlier greedy slot that is occupied by a later
arrival is exchanged with that later arrival's former slot. The Lean proof
uses the unclipped natural deadline inequalities; because all service values
are in `Fin H`, this is sufficient for the clipped deadline in the manuscript.

The final strong induction on the input trace (`Matching.lean:311–356`) applies
this erase equivalence in the successful branch and the two failure lemmas in
the other branches. Therefore the direction from an arbitrary injective
matching to greedy success is not merely asserted by a greedy-choice
heuristic; it is discharged by the explicit finite exchange.

## Empty and `Fin 0` cases

The empty-input branch is explicit: `greedy_empty` (`Matching.lean:56–58`)
returns `true` for every output trace, and the final induction branch uses
`Model.feasible_empty` (`Matching.lean:354–356`). If the output trace is empty
and the input is nonempty, `candidates_nonempty_of_feasible` makes feasibility
impossible, so the no-candidate branch returns `false` as required.

For `H = 0`, `Fin 0` has no elements, so every trace is empty. The nonempty
input branch is unreachable; both sides reduce to the empty case. A separate
Lean check instantiated the theorem at `H = 0`, and the examples for arbitrary
empty inputs and outputs compile. The theorem also handles `D = 0` without a
special case. The manuscript itself assumes `H ≥ 1` and `1 ≤ m`, but the
matching theorem is correctly more general rather than relying on those
assumptions.

## FIFO execution interface and limits

There is no semantic mismatch in the intended schedule-mode interpretation:
`Execution.step` reads the current arrival before transmission, appends it to
the queue, and processes slots in increasing order (`Execution.lean:35–81`).
The queue invariant records increasing arrival order and exactly the unseen,
unserved input prefix (`Execution.lean:123–128`). Consequently, when schedule
mode is active, a `y` slot with a nonempty queue is the chronological earliest
available slot for the FIFO head; a `y` slot used while the queue is empty is
earlier than every future arrival and cannot be a feasible candidate later.

That correspondence is currently an informal semantic observation, not a
proved theorem in `Execution.lean`. The available execution invariant
`executeState_queueInvariant` (`Execution.lean:358–367`) tracks queue contents,
but it does not state that schedule-mode served packet/slot pairs equal the
prefix of the `greedy` assignment. The execution proof should add or use such
an invariant before importing `greedy_true_iff_feasible` to prove deadline
preservation or schedule preservation. This is an outstanding bridge, not a
counterexample to `Matching.lean`.

The manuscript also states an `O(H)` implementation cost for sorted binary
traces (`manuscript.md:75`). `Matching.lean` proves semantic correctness but
does not prove a complexity bound. Its `Finset.filter`, `min'`, and `erase`
definition is a finite reference predicate; a linear-time implementation claim
needs a separate representation or complexity argument.

## Independent checks

The module was built independently with:

```text
/private/tmp/lean-4.33.1-darwin_aarch64/bin/lake build TrafficShaping.Matching
```

The build completed successfully without diagnostics. A direct source scan
found no `sorry`, `sorryAx`, `axiom`, `unsafe`, or `native_decide` in
`Matching.lean`.

The following declarations were checked with `#print axioms`:

```text
greedy
greedyStep
candidates_nonempty_of_feasible
not_feasible_of_greedy_deadline
feasible_erase_min_iff
greedy_true_iff_feasible
```

Each reports only the ordinary dependencies `propext`, `Classical.choice`, and
`Quot.sound`; no project-specific axiom or unfinished-proof dependency is
present.

Finally, an independent exhaustive checker compared greedy matching with all
injective assignments for every `H ≤ 6`, every `D ≤ H + 2`, and every pair of
traces. It checked 47,331 cases, including `H = 0`, and found no mismatch.
