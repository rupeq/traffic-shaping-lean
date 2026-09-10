# Operational execution proof record

`formal/TrafficShaping/ExecutionCore.lean` defines the causal switch-to-service
state machine.  At slot `t` it first appends the current arrival, then checks
the schedule-mode deadline trigger.  A trigger at a silent slot enters
permanent service mode in that same slot; service mode transmits the FIFO head
and never emits a dummy.  Schedule mode follows the sampled base trace and
emits a dummy only when its queue is empty.

The checked queue invariant records four facts at every processed prefix:
the queue is duplicate-free and strictly arrival-ordered, queue plus served
arrivals is exactly the input prefix, queue and served are disjoint, and every
queued arrival is earlier than the next slot.  `HeadSafe` is propagated up to
the final pre-horizon state: the FIFO head is never beyond its clipped
deadline.  `OutputPast` proves that every emitted slot is earlier than the
current slot.  For an on-schedule base trace, `OutputModeInvariant` records
that schedule mode has emitted exactly its base prefix; after switching at
`τ`, the switch is before `H-m` and the output cardinality is bounded by the
base prefix before `τ` plus the number of served packets.

`formal/TrafficShaping/Execution.lean` proves the matching side of the
operational argument.  `feasible_insert_of_feasible` explicitly extends an
injective assignment when the FIFO head is served: the head is released by
the current slot, the propagated deadline bound supplies its upper bound, and
the output-prefix invariant supplies a fresh service slot.  The induction
`executeState_servedFeasible` therefore proves feasibility of every served
prefix for the concrete transition relation, including both schedule and
service branches.  The final delivery lemma supplies `served = x` for an
admissible input and an on-schedule base trace; composing it with this prefix
theorem yields feasibility of the complete `execute` output.  The cap theorem
is maintained separately from this matching proof and uses the terminal
reserve cardinality together with the mode invariant.

## Verification

The modules build with Lean 4.33.1 and the pinned Mathlib cache:

```text
cd /Users/artem.derevago/master_thesis/traffic-shaping-lean/formal
/private/tmp/lean-4.33.1-darwin_aarch64/bin/lake build TrafficShaping.ExecutionCore
/private/tmp/lean-4.33.1-darwin_aarch64/bin/lake build TrafficShaping.Execution
```

Both commands exit successfully.  The remaining linter output is limited to
unused simp arguments and section-variable warnings; there are no `sorry`,
`admit`, `axiom`, `unsafe`, or `native_decide` declarations in these files.
