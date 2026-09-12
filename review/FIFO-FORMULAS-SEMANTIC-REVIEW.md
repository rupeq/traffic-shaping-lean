# FIFO formulas and actual service events: semantic review

Audit date: 2026-09-11. This review covers
`formal/TrafficShaping/QueueCorollaries.lean`,
`formal/TrafficShaping/QueueServiceTimes.lean`,
`formal/TrafficShaping/QueueSuffixInstances.lean`, and
`formal/TrafficShaping/QueueArticleFormulas.lean`. It compares the source with
the r9 manuscript's Eqs. (12) and (13). The review does not edit the Lean
proofs and does not run a repository-wide build.

## Verdict

**PASS for the semantic content of Eqs. (12) and (13).** The public wrappers
`terminal_actual_fifo_eq12` and `switch_actual_fifo_eq13` state the closed FIFO
service slot as a maximum, bound it by the clipped deadline used by the
execution, and identify the actual transition that first inserts each packet
into `executeState.served`. Their suffix lists are computed from the actual
input and actual served set; they are not supplied as an unrelated schedule.

**PASS for the operational bridge.** The final wrappers construct their
`FifoSuffixBase` and `WorkConservingSuffix` premises internally. They do not
take a `FifoHeadSchedule`, a `FifoSuffixWitness`, a future mode schedule, or a
future head schedule as an assumption. The only switch-specific assumptions in
Eq. (13) describe the observed trigger at `tau`: schedule mode, the actual
enqueued queue head, and the actual predicate `tau ∉ y ∧ deadline = tau`.

The remaining qualification is about the theorem interfaces: Eq. (13) is
conditional on an actual switch trigger and does not claim that a switch must
occur for an arbitrary input and trace. That is the correct scope for a formula
describing the post-switch branch.

## Indexing and the service-time meaning

The model uses slots `0, ..., H-1`. `executeState n` is the state after the
first `n` slot transitions, and `executeState_succ_step` in
`QueueCorollaries.lean` identifies the transition from state `n` to state
`n+1` with the actual call to `step` at slot `n`.

The article numbers packets one-based. The Lean list index `i` is zero-based,
so the formal expressions

```text
max a.val (H - m + i)
max ai.val (tau.val + i)
```

are exactly the manuscript's `max(a_i, r+i-1)` and `max(a_i, tau+i-1)` when
the paper's `i` is the formal `i+1`. There is no extra `+1` in either wrapper;
the `+1` appears only in the state index that records the result of the
service transition.

For either wrapper, the conjunction

```text
a ∉ (executeState ... si).served ∧
a ∈ (executeState ... (si + 1)).served
```

means that `a` is served exactly at slot `si`: it has not been inserted into
the monotone served set before the transition, and the transition at `si`
inserts it. The event theorems derive this from the actual queue head and the
actual `step` transition, rather than merely asserting a numerical service
list.

The suffix base also proves each computed service slot is `< H`. Thus the
transition at `si` is a real in-horizon transition even though the wrapper
uses `si + 1` to expose its post-transition state.

## Clipped deadlines and Eq. (12)

`deadline H D a` is defined by

```text
min (a.val + D) (H - 1).
```

`fifoSuffixBase_first_deadline` obtains the first-arrival condition from the
actual queue head and `executeState_headSafe`. The generic FIFO bound in
`fifoSuffixBase_service_le_deadline` combines the arrival-plus-delay bound
with the actual suffix horizon, producing the clipped deadline inequality.

`terminal_actual_fifo_eq12` then follows this chain:

1. `canonicalRemainingArrivals_fifoSuffixBase` constructs a
   `FifoSuffixBase` at `r = H-m` from the actual unserved input, actual queue,
   actual served set, FIFO order invariant, and the horizon bound.
2. `terminal_workConservingSuffix` proves that every slot from `H-m` through
   the end is work-conserving because every terminal slot belongs to `y` in
   schedule mode; service mode is handled directly.
3. `fifoSuffix_service_events_of_base` recursively follows the actual queue
   transition and proves first insertion into `served` at every computed FIFO
   service slot.
4. `fifoServices_get_eq_max` rewrites the recurrence to the zero-based closed
   form, and `fifoSuffixBase_service_le_deadline` supplies the clipped bound.

The theorem therefore establishes the actual counterpart of Eq. (12):

```text
s_i = max(a_i, r+i-1),
s_i ≤ min(a_i+D, H-1),
```

with the event identity attached to the concrete `executeState` run. The
article's terminal reserve is represented by `hterminal : terminal H m ⊆ y`;
no independently postulated list of service slots is used.

## Clipped deadlines and Eq. (13)

`switch_actual_fifo_eq13` starts with `tau < H-m`, the actual schedule-mode
state at `tau`, the head of `suffixQueueAt tau` after the current arrival has
been enqueued, and the actual switch predicate. The source definition of
`step` uses this same queue and predicate, so these assumptions describe the
observed trigger rather than a second switching machine.

The post-switch chain is concrete:

1. `canonicalRemainingArrivals_fifoSuffixBase` gives the actual suffix base at
   `tau`.
2. `canonicalRemainingArrivals_eq_cons_of_head` proves that the actual head
   `a` is the first element of the canonical remaining-arrival list. It uses
   the queue invariant, the sorted canonical list, and the actual enqueue
   operation; it does not assume the list's head identity.
3. `executeState_switch_step_mode_service` derives service mode at `tau+1`
   from the actual trigger. `executeState_service_mode_persists` then derives
   service mode at every later in-horizon state.
4. `executeState_switch_workConservingSuffix` packages that derived mode
   persistence as the actual work-conserving suffix needed by
   `fifoSuffix_service_events_of_switch`.
5. `fifoSuffix_service_events_of_switch` handles the first transition at the
   switch directly, removes the actual head, constructs the actual tail base,
   and invokes the base event theorem recursively for all later packets.
6. The same closed recurrence and clipped deadline theorem used by Eq. (12)
   rewrites the event result to `max(ai, tau+i)` and
   `si ≤ min(ai+D,H-1)`.

Consequently, future service mode and all later head positions are derived
from the operational transition and queue invariant. They are not premises of
the final Eq. (13) wrapper. The switch assumptions remain intentionally
conditional: the theorem verifies the service-time formula after a specified
actual trigger, rather than proving existence of such a trigger.

## Canonical list and absence of circular assumptions

`canonicalRemainingArrivals` is the increasing sort of

```text
x \ (executeState D x y start).served.
```

`canonicalRemainingArrivals_remaining` proves the exact set identity. The
queue-to-filter theorem identifies the actual queue with the part of that list
whose arrival value is `< start`; both directions use
`executeState_queueInvariant`. Strict sorting then turns equality of finite
sets into equality of lists. The horizon proof uses the input cardinality bound
and `fifoServices_get_lt_horizon`.

This establishes all three fields used by `FifoSuffixBase` from the actual
execution. `FifoSuffixBase` deliberately contains no service-event or head
position field. The stronger `FifoSuffixWitness` and `FifoHeadSchedule` APIs
remain available in `QueueServiceTimes.lean`, but neither final article wrapper
uses them. In particular, the final path does not smuggle in a precomputed
head schedule under a different name.

There are no `sorry`, `admit`, or user-declared axioms in the four reviewed
files. A targeted `#print axioms` check for both final wrappers and their event
bridges reports only Lean's standard foundational axioms:
`propext`, `Classical.choice`, and `Quot.sound`.

## Scope conditions to retain in the article map

* Eq. (12) requires the terminal all-one condition on `y` and is quantified
  over actual canonical remaining arrivals at `r=H-m`.
* Eq. (13) requires a specified actual switching slot `tau<H-m`, schedule mode
  at that slot, the actual post-enqueue head, and the actual switch predicate.
* Both equations use binary, strictly ordered arrivals represented by a
  `Finset` trace and one dequeue per work-conserving slot, exactly as in the
  execution model.
* The formal inequalities are clipped by `H-1`, which is stronger and more
  explicit than quoting only the un-clipped `a_i+D` inequality in the middle
  of the manuscript's Eq. (13) discussion.

No semantic defect was found in the current Eq. (12)/(13) source chain. The
integrated build remains the coordinator's release gate; this review itself
does not run that build.
