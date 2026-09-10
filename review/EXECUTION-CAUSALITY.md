# Semantic audit of execution causality

This audit covers the operational execution in
`formal/TrafficShaping/ExecutionCore.lean` (re-exported by the execution
interface) and the proof in `formal/TrafficShaping/ExecutionCausality.lean`.
The claim is
pointwise causality for the concrete `execute` function, with the public
schedule `y` and delay bound `D` fixed.

## Verdict

**PASS for the stated finite-session causality claim.** The dedicated Lean
module proves that, for every `H`, `D`, and `t ≤ H`, equality of the input
prefixes through slot `t` gives equality of the output prefixes through slot
`t`:

```lean
tracePrefix t x = tracePrefix t x' →
  tracePrefix t (execute D x y) = tracePrefix t (execute D x' y)
```

It also proves the useful empty-input identity
`execute D ∅ y = y`.

## Why the concrete rule is causal

* `ExecState` stores only the queue, served arrivals, output trace, and the
  current mode (`ExecutionCore.lean:14–23`). `step` reads the input trace only
  at its current slot `t` (`ExecutionCore.lean:35–72`). Its other inputs are the
  already accumulated state, the fixed public schedule `y`, and `D`.
* `runN` calls `step` at slot `n` after the first `n` calls and does so in
  increasing slot order (`ExecutionCore.lean:74–78`). `execute` is the output
  of the `H`-step run (`ExecutionCore.lean:80–84`). It does not search over a
  future feasible trace.
* `tracePrefix_succ` exposes the only new input fact at step `n`: membership
  of the current slot, together with the earlier prefix
  (`ExecutionCore.lean:90–121`). The proof of
  `executeState_eq_of_prefix_eq` in `ExecutionCausality.lean:58–80` inducts on
  the number of executed slots and applies this fact to both branches of the
  current `step`.
* A later step can only leave the output unchanged or insert its current slot.
  The local `step_output_shape_local` lemma and
  `tracePrefix_insert_current` (`ExecutionCausality.lean:82–123`) formalize
  that an insertion at slot `k ≥ t` does not change the prefix below `t`.
  `executeState_output_prefix_stable` (`ExecutionCausality.lean:133–155`)
  then transports the state equality at `t` to the final output at `H`.
* `execute_causal` (`ExecutionCausality.lean:180–198`) combines those two
  facts. `executeState_empty_state` and `execute_empty`
  (`ExecutionCausality.lean:157–203`) give the empty-input identity by the
  same operational induction.

## Scope and limits

1. The theorem is pointwise for deterministic `execute`, with `D` and `y`
   fixed. It does not assert privacy, a distributional coupling, or any
   property of an arbitrary randomized mechanism.
2. The theorem uses the finite binary trace model from `Model.lean`: input and
   output traces are finite sets of one-slot events. Packet identities,
   variable service times, and simultaneous arrivals are outside this model.
3. Causality is independent of feasibility and the hard cap. The execution
   invariant and preservation proofs must separately establish that every
   real arrival is served within its deadline and that the output cardinality
   stays within the mechanism budget.
4. The boundary `t = H` is included: `tracePrefix H x = x` in the finite model,
   so the result covers the complete final output as well as proper prefixes.

## Verification

The proof module was checked with Lean 4.33.1 and the pinned mathlib
environment (`lake build TrafficShaping.ExecutionCausality`, exit 0). Its
causality theorem uses the standard finite-library axioms reported by Lean
(`propext`, `Classical.choice`, and `Quot.sound`); it adds no axiom or `sorry`
of its own.
