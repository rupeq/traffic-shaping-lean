# Execution preservation review

## Scope

`formal/TrafficShaping/ExecutionPreservation.lean` proves preservation for the
actual queue based switch-to-service machine in `ExecutionCore.lean`.  It does
not replace the operational transition with a search over future traces.

The public result is:

```lean
theorem execute_eq_of_feasible {H D : ℕ} {x y : Trace H}
    (hxy : Feasible D x y) : execute D x y = y
```

The file imports `TrafficShaping.ExecutionCore` and
`TrafficShaping.Matching`.

## Proof invariant

After the first `n` slots, the induction invariant states that:

1. the machine is still in schedule mode;
2. its public output is `tracePrefix n y`; and
3. the unserved arrivals still have an injective deadline respecting matching
   into the residual output slots `y \ tracePrefix n y`.

The queue invariant from `ExecutionCore.lean` supplies FIFO order, disjointness
from served arrivals, and the fact that the queue contains exactly the
processed arrivals that have not been served.  Consequently, the queue head is
the least unserved arrival after the current arrival is enqueued.

At a scheduled one-slot, the FIFO matching lemma removes the queue head and
that slot from the residual matching.  At an empty scheduled slot, the queue
head cannot have the current deadline: any feasible assignment would have to
map it to the current slot, which is absent from the residual output.  If the
queue is empty, every unserved arrival is strictly future, so a scheduled
one-slot can be removed from the matching without changing the input side.

The induction therefore rules out every switch and establishes the output
equality at the horizon using `tracePrefix_horizon`.

## Verification

The pinned Lean 4.33.1 toolchain builds the target successfully:

```text
lake build TrafficShaping.ExecutionPreservation
```

The source contains no `sorry` declarations.
