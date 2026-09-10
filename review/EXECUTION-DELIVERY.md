# Operational execution delivery proof

`formal/TrafficShaping/ExecutionDelivery.lean` proves final delivery for the
concrete queue machine defined in `ExecutionCore.lean`.  The main public
theorem is:

```lean
theorem executeState_served_eq {H m D : ℕ} (hm : m ≤ H)
    {x y : Trace H} (hx : x.card ≤ m) (hterminal : terminal H m ⊆ y) :
    (executeState D x y H).served = x
```

The proof uses the actual `step` transition and its checked
`executeState_queueInvariant`; it does not assume an abstract final-delivery
property.  The queue invariant says that queue plus served arrivals is exactly
the processed input prefix.  To show that the queue is empty at the horizon,
the proof defines the unprocessed tail
`future n x = x \ tracePrefix n x` and proves, from the beginning of the
terminal reserve, the quantitative bound

```text
queue.length + (future n x).card ≤ H - n.
```

At the first reserve slot this follows from the queue invariant, because the
input has at most `m` arrivals.  At each subsequent slot, the concrete queue
transition removes one queued head when the current slot is not a new arrival;
when the slot is an arrival, that arrival is removed from `future` instead.
The terminal-subset hypothesis ensures that every slot in this induction is
present in `y`, so schedule mode cannot retain a dummy slot at the reserve
boundary.  The two cases are formalized by `step_queue_tail`, `future_succ`,
and the private induction `pending_tail`.

At `n = H`, the right side is zero.  Nonnegativity therefore forces the final
queue length to zero, and `executeState_queue_empty` turns that into an empty
list.  Rewriting the queue invariant at the horizon with
`tracePrefix H x = x` then gives the stated equality of the actual served set
and the input trace.

## Verification

The module was checked with Lean 4.33.1 and the pinned Mathlib cache:

```text
cd /Users/artem.derevago/master_thesis/traffic-shaping-lean/formal
/private/tmp/lean-4.33.1-darwin_aarch64/bin/lake build TrafficShaping.ExecutionDelivery
```

The command exits successfully.  The output contains only linter warnings
about unused local names or simp arguments; the proof has no `sorry`, `admit`,
`axiom`, `unsafe`, or `native_decide` declarations.
