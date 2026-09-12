# Semantic review of matching and execution-cost claims

This review compares `formal/TrafficShaping/MatchingComplexity.lean`,
`formal/TrafficShaping/QueueCorollaries.lean`, and the completed actual FIFO
wrappers in `QueueArticleFormulas.lean`, `QueueSuffixInstances.lean`, and
`QueueServiceTimes.lean` with Lemma 1, Eqs. (12)--(13), and the execution
paragraph in the r9 English manuscript
(work/new-topic-2026-09-09/article-1-final-2026-09-11-r9/international-en/manuscript.md,
lines 77, 151--161, and 173). The semantic feasibility predicate in this
checkout is `TrafficShaping.Feasible` (`Model.lean:23--26`); there is no
separate `actualFeasible` declaration. The arithmetic FIFO helpers and the
actual execution wrappers are assessed separately so that their interfaces
are not conflated.

## Verdict

**PASS, with a representation qualification, for Lemma 1's sorted scan.**
scan is a genuine monotone two-pointer traversal over strictly increasing
arrival and service lists. scan_true_iff_feasible proves that its Boolean
result is equivalent to the injective, release-and-deadline predicate, and
fastMatch_iff_feasible transports that result to arbitrary finite traces by
enumerating the horizon and filtering it by membership. The operation theorem
is an explicit bound on the scan counter, not an unqualified claim about all
work performed by fastMatch.

**QUALIFIED for end-to-end running time.** fastMatch_ops_le_five_mul_H counts
only the scan phase after `fastSortedTrace` enumerates `List.finRange H` and
filters it by finite-set membership. The horizon enumeration, membership
tests, finite-set/list conversion, natural-number arithmetic, and recursion
overhead are outside `ScanResult.ops`. Therefore the current Lean theorem
supports the manuscript's statement when sorted one-slot lists are supplied,
but it does not prove that public fastMatch or articleScanFeasible, including
their bounded preprocessing, runs in O(H) under a complete machine-cost model.

**PASS at the transition and queue-size level for the execution paragraph.**
execute_exactly_H_steps records one step transition for each horizon slot, and
executeState_queue_length_le proves the queue contains at most m packets. These
are the formal counterparts of one horizon pass and the queue capacity bound.
They are not a machine-cost theorem: the current state representation leaves
the cost of each transition unmodelled.

**PASS for the arithmetic helpers and the actual Eqs. (12) and (13) wrappers.**
The generic `terminal_fifo_service_formula` and
`switch_fifo_service_formula` lemmas establish the recurrence arithmetic for
strict `List Nat` inputs. The completed `terminal_actual_fifo_eq12` and
`switch_actual_fifo_eq13` wrappers then build their suffix premises from the
actual input, served set, queue, mode transition, and `executeState` events.
They return both the clipped deadline bound and the before/after served-set
membership for each computed service slot. The switch wrapper is correctly
conditional on an observed actual switch trigger; it does not claim that
every execution must switch.

## Matching scan and its cost counter

SortedTrace stores a strict, increasing list of Fin H slots and
SortedTrace.toTrace is its finite-set interpretation. In advance, the service
pointer moves past slots earlier than the current arrival, accepts the first
slot in the interval [a,a+D], or stops at the first candidate that misses the
deadline. A successful call returns the suffix after the consumed slot; a
failed call retains the candidate and scan stops. Consequently a service-list
cell is never revisited after a successful pointer advance, and an arrival cell
is processed at most once.

The cost model is clearly stated in the source (MatchingComplexity.lean:13–17):
one unit covers one list/pointer inspection, including the comparison and a
constant state update. The counter also charges the terminal empty-list
inspection performed when no service slot remains, and charges one arrival
dispatch in scan. It does not count Lean recursion fuel, so the bound is about
the declared list model rather than a proof artifact.

The proved bounds are:

    advance.ops ≤ 2 * (|ys| - |remaining|) + 2
    scan.ops    ≤ 3 * |arrivals| + 2 * |services|
    scan.ops    ≤ 5 * H       when both list lengths are at most H.

Thus scan_ops_le_five_mul_H is a valid, deliberately loose O(H) bound for
already sorted binary traces. The semantic theorem is also aligned with the
article predicate: the upper test s.val ≤ a.val + D is equivalent to the
clipped deadline in the manuscript because s : Fin H already gives s.val < H.
Empty traces and H = 0 are covered by the list definitions.

`fastSortedTrace` changes the cost interpretation. `fastMatchRun` first
enumerates the horizon and filters membership for both finite traces, then
calls `scan`; the `ops` field contains no charge for that preprocessing.
`fastMatch_ops_le_five_mul_H` proves a bound on the resulting scan counter,
not on the complete function. `articleScanFeasible` has the same bounded
enumeration and sorted-list preprocessing, and coverage sums can invoke it
repeatedly. If the intended claim is the article's “with sorted binary
traces” claim, the precise API is `scan`/`scanBool` on a `SortedTrace`, or a
caller must provide a separately costed sorted representation. A full claim
for arbitrary `Trace H` needs a cost theorem for the `List.finRange` traversal,
finite-set membership and conversion (or a pre-sorted input contract), in
addition to the scan theorem. The current source supplies no such combined
counter.

The same distinction applies to cost units. The scan theorem treats list-cell
inspections, comparisons, state updates, and Nat arithmetic as unit-cost and
says nothing about bit complexity when D is large. It also does not assign a
cost to the membership predicate used by the bounded preprocessing. That is a
reasonable RAM-style scan contract, but it should accompany any prose that
presents `5*H` as an implementation bound.

## Queue pass and operational work

ExecStepRun and runN_execStepRun expose the actual calls to step, and
execute_exactly_H_steps specializes this relation to exactly H calls. The queue
invariant gives strict FIFO order, and executeState_queue_length_le derives the
cardinality bound from the input partition. These results are enough to state
structurally that the machine walks slots 0, ..., H-1 and stores at most m
queued arrivals.

They do not establish an O(H) runtime for the current Lean data structures.
In particular, enqueue is defined as q ++ [a] (ExecutionCore.lean:33), so a
direct singly linked-list evaluation can traverse the existing queue on each
arrival. The transition also performs trace membership tests and Finset
insertions, none of which are charged by ExecStepRun. A literal implementation
using these definitions may therefore take more than constant work per slot
even though it makes exactly one step call per slot. The article execution-cost
sentence is sound as a pass-count and queue-capacity statement; reading it as a
proved machine-runtime bound requires an explicit deque/tail-pointer cost
model (and charged trace operations), or a separate amortized-cost theorem.

The transition theorem also does not count transmissions. A call to step can
emit no slot, a dummy, or a real service, so “H transitions” should not be read
as “H service operations.” execute_exactly_H_steps is intentionally limited
to the former, as its source comment says.

## Arithmetic correspondence with Eqs. (12) and (13)

`fifoServices` is the FIFO recurrence

    s₀ = max(a₀, start)
    sᵢ = max(aᵢ, sᵢ₋₁ + 1).

`fifoServices_get_eq_max` proves, for a strict arrival list, the closed form
`sᵢ = max(aᵢ, start+i)`. This is exactly the manuscript's one-based
`max(aᵢ, start+i-1)` after the documented zero-based index shift.

The generic `terminal_fifo_service_formula` and
`switch_fifo_service_formula` remain useful arithmetic helpers. Their
hypotheses describe an arbitrary strict `List Nat`, its length and horizon,
and the first-deadline condition; they prove the corresponding unclipped and
horizon bounds. These helper theorems are deliberately more abstract than an
execution trace, but they are no longer the endpoint of the formal argument.

`terminal_actual_fifo_eq12` is the actual execution wrapper for Eq. (12). It
takes `x : Input H m`, the concrete trace `y`, the terminal-reserve inclusion,
and an index into
`canonicalRemainingArrivals x y (H - m)`. For the resulting arrival `a` and
slot `sᵢ = max a.val (H - m + i)`, it proves all three concrete facts:

```text
sᵢ ≤ deadline H D a,
a ∉ (executeState ... sᵢ).served,
a ∈ (executeState ... (sᵢ + 1)).served.
```

Its proof constructs `FifoSuffixBase` from the actual unserved set and queue,
derives work conservation on the actual terminal suffix, follows the actual
`step` transitions with `fifoSuffix_service_events_of_base`, and then applies
the recurrence and clipped-deadline lemmas. The service events therefore refer
to `executeState`, not to an independently supplied schedule.

`switch_actual_fifo_eq13` is the corresponding post-switch wrapper. It takes
an actual `tau : Fin H` with `tau < H-m`, actual schedule mode at `tau`, the
head of the actual post-enqueue `suffixQueueAt`, and the actual trigger
`tau ∉ y ∧ deadline H D a = tau`. It proves the same three facts for
`sᵢ = max ai.val (tau.val+i)` for every indexed element of the canonical
remaining-arrival list. The wrapper derives the canonical list decomposition
from the actual queue head, derives service-mode persistence and
work-conservation after the switch from the operational transition, and then
uses the actual service-event theorem. Thus the former arithmetic helper's
`a :: as` is connected to the concrete queue and future service events.

The switch theorem is intentionally conditional on an observed actual trigger;
it verifies the service-time formula after a switch and does not claim that an
arbitrary run must switch. Both wrappers use the clipped deadline
`min (a.val + D) (H - 1)` and expose the zero-based indexing explicitly.

## Review conclusion

The sorted matcher is semantically correct and has a real linear scan bound
under its declared sorted-list/list-inspection contract. The queue results
prove the article's structural H-transition and m-capacity facts, and the
actual Eq. (12)/(13) wrappers connect the FIFO service formulas to the
concrete queue run. The remaining scope is computational: bounded
enumeration, membership and finite-set work are not included in the matching
counter, and queue transitions are not machine-costed.
