# Matching proof record

`TrafficShaping/Matching.lean` proves the FIFO earliest-slot greedy
criterion against the concrete finite model in `TrafficShaping/Model.lean`.
The model uses `Trace H = Finset (Fin H)`, so the proof does not rely on an
equivalent binary-function encoding.

## Exported algorithm

For an arrival slot `a` and an output trace `y`,

```text
candidates a y = y.filter (fun s => a.val ≤ s.val)
```

is the set of available transmission slots that are not before the packet.
`greedyStep D a y` takes its least element and returns it exactly when the
deadline `s.val ≤ a.val + D` holds.  The recursive Boolean `greedy D x y`
takes the least arrival in `x`, applies `greedyStep`, erases both the arrival
and selected slot, and recurses.  Its termination measure is `x.card`; the
recursive branch erases `x.min' hx` and uses
`Finset.card_erase_lt_of_mem`.

The primary theorem is

```text
greedy D x y = true ↔ Feasible D x y.
```

It has no restrictions on `H` or `D`; empty traces and `Fin 0` are covered by
the empty branch.

## Proof structure

The proof first exposes the local greedy facts:

* `mem_candidates` characterizes membership as `s ∈ y ∧ a.val ≤ s.val`.
* `earliest_available_mem` proves that the selected slot is available and not
  before the packet.
* `earliest_available_le` proves that it is no later than every other
  candidate.
* `greedyStep_some_spec` packages availability, release time, deadline, and
  earliest-slot choice for a successful step.

The reverse matching direction is handled by
`feasible_erase_min_iff`.  Let `a` be the least arrival and `s` the least
candidate slot.  Given a feasible assignment, let `s₀` be the slot assigned to
`a`; minimality gives `s ≤ s₀`.

* If `s = s₀`, restrict the assignment to `x.erase a`.
* If `s < s₀` and `s` is already assigned, swap the assignments: the packet
  using `s` receives `s₀`.  Its release constraint holds because it was
  released no later than `s`, and its deadline holds because
  `s₀ ≤ deadline(a) ≤ deadline(packet)`.  If `s` was unused, the same update
  simply leaves all residual assignments unchanged.

The update is represented explicitly as a dependent function on the erased
arrival subtype.  Injectivity is checked by cases on whether an assignment
equals `s`; a residual packet cannot map to `s` after the update.  The forward
construction assigns `a` to `s` and uses the residual assignment elsewhere;
the erased output slot prevents collisions.

The two failure cases are proved independently:

* no candidate implies no feasible assignment, because the assignment of the
  least arrival would itself be a candidate;
* a least candidate after the deadline implies no feasible assignment,
  because every feasible assignment sends the least arrival to a candidate at
  least as large as the greedy one.

Finally, strong induction on `x.card` applies `feasible_erase_min_iff` to the
successful recursive branch and the two failure lemmas to the failing
branches.  The empty branch uses `Model.feasible_empty`.

## FIFO/execution interface

The execution implementation can import the following facts without opening
private definitions:

```text
greedy_true_iff_feasible
greedyStep_some_spec
greedy_head_some
earliest_available_mem
earliest_available_le
mem_candidates
```

`greedyStep_some_spec` is the direct earliest-service lemma needed by a FIFO
queue: the chosen slot is a one of `y`, is not before the head arrival, meets
the deadline, and is no later than every available slot after that arrival.
`greedy_head_some` exposes the first recursive service and leaves the exact
residual input and output traces for induction.  Thus a schedule-mode FIFO
execution can be related to the same recursive greedy relation used by the
feasibility theorem, rather than assuming an informal equivalence.

## Build status

The module was compiled from the formal project root with

```text
/private/tmp/lean-4.33.1-darwin_aarch64/bin/lake build TrafficShaping.Matching
```

The build succeeds without diagnostics; the file contains no `sorry`, `admit`,
`axiom`, `unsafe`, or `native_decide`.
