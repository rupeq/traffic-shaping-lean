# Achievability and main-theorem semantic audit

This audit covers `formal/TrafficShaping/Achievability.lean` and
`formal/TrafficShaping/MainTheorem.lean` against Theorem 1 and its
noncausal construction in the r4 manuscript.  It is intentionally bounded to
the current proof stage.  The noncausal optimum is complete and checked.  The
causal optimum is not yet proved.

## Noncausal construction

The generic `repairMechanism` has the right semantic shape.  Its law is the
push-forward of an input-independent schedule law `q` through a repair
function.  The hypotheses require every repaired trace to be feasible and to
have cardinality at most `B`, so the hard delivery and hard per-execution cap
are properties of the mechanism itself rather than privacy allowances.

The exact TV claim is proved as an equality in
`repairMechanism_tv`, not merely as a coupling upper bound.  The proof uses
`Law.repair_tv_identity` with the base map `embed` and the active repair map.
It checks both facts needed for the identity:

```text
repair x s ∈ inputFeasibleEvent x
embed s ∈ inputFeasibleEvent x → repair x s = embed s.
```

The complement of `inputFeasibleEvent` is then identified with the complement
of `inputScheduleEvent`, and `Law.mass_compl` gives exactly

```text
TV(law x, law empty) = 1 - q.mass(inputScheduleEvent embed x).
```

This is the complete-trace identity required by the manuscript.  It does not
condition on a fixed output cardinality and it includes fallback outputs.

`input_coverage_lower` correctly lifts a row lower bound from exact weight-m
inputs to every admissible input.  It uses
`exists_fullInput_superset hm x` to choose `z` with `x ⊆ z` and `|z| = m`,
then applies `Feasible.mono_input` to show

```text
feasible schedules for z ⊆ feasible schedules for x.
```

Monotonicity of law mass completes the inequality.  The argument includes the
empty input and all smaller inputs, so the construction does not silently
restrict privacy to full inputs.

The concrete fallback is `offRepair`:

```text
if Feasible D x y then y else x.1
```

The first branch preserves the sampled schedule.  The fallback `x.1` is
feasible by `feasible_self` and has at most `m ≤ B` slots.  On the empty input,
every schedule is feasible, so the fallback is never taken and
`repairMechanism_empty` proves that the empty-input law is exactly the base
law `q`.  `offMechanism_private` then applies the exact TV identity and the
finite-game row bound.

The epsilon lifting is explicit.  `repairMechanism_private` obtains an
`(0, 1-v)` TV bound and calls `Law.privatePair_of_tv` with the hypothesis
`0 ≤ ε`.  `noncausal_attainment` accepts an arbitrary real `ε` together with
`hε : 0 ≤ ε`, and `noncausal_optimum_isLeast` carries the same hypotheses.
Thus the checked result covers every finite nonnegative epsilon, including
epsilon zero, without claiming that a negative epsilon is meaningful.

## Noncausal optimum and infimum claims

`noncausalLosses` quantifies over every `Mechanism H m B D` satisfying
`Private M ε δ`; feasibility and the cap are already fields of `Mechanism`.
The set additionally requires `0 ≤ δ ≤ 1`, matching the manuscript's
parameter domain.

`noncausal_optimum_isLeast` has both required directions of a minimum:

1. `offGameValue_bounds` supplies `0 ≤ 1 - v ≤ 1`, and
   `noncausal_attainment` supplies an actual mechanism at that value.
2. The lower direction destructures an arbitrary
   `δ ∈ noncausalLosses` and an arbitrary witness mechanism `M`, then applies
   `noncausal_converse_bound`.  It is therefore not a proof only for the
   constructed mechanism or for an optimizer already assumed in advance.

The theorem `noncausal_optimum_eq` derives the `sInf` equality from this
`IsLeast` statement.  Under the stated parameter and epsilon hypotheses the
loss set is nonempty and bounded below because the proof has already supplied
the least element; the use of `csInf_eq` is consequently justified.  The
epsilon-independence theorem rewrites both sides with the same game value at
the requested epsilon and at zero.  This is an equality of the defined
infima, not just an informal statement that the construction happens to work
for more than one epsilon.

## Causal status

The causal definitions are present but the causal optimum is not yet a proved
theorem.  `causalLosses`, `causalOptimum`, `onGameValue`, and
`onGameValue_bounds` define and bound the relevant objects, but
`MainTheorem.lean` contains no causal analogue of:

```text
causal_attainment
causal_optimum_isLeast
causal_optimum_eq
causal_optimum_epsilon_independent
```

`repairMechanism_causal` is a generic sufficient lemma: it would prove
semantic causality from pointwise same-seed prefix agreement.  No concrete
`OnSchedule` repair is supplied to it yet.  The current `Execution.lean`
contains an operational `execute` function and queue invariants, but it is not
connected to `Achievability.lean` or `MainTheorem.lean` by proofs of all of the
properties needed for Theorem 1: hard feasibility and deadline delivery,
the per-execution cap, same-seed prefix agreement, and preservation of every
feasible terminal-reserve schedule.  Consequently the manuscript's causal
equality in (9), and the statement that both mechanism classes attain their
minima at epsilon zero, must remain marked incomplete until those lemmas and
the causal `IsLeast` proof are added.

This is a proof-coverage limitation rather than a defect in the completed
noncausal argument.  The current files must not be cited as a completed
formal proof of the causal half of Theorem 1.

## Verification

After the local `Nonempty` witnesses were added to both converse theorem
bodies, the relevant target was checked directly with Lean 4.33.1 and
mathlib v4.33.1:

```text
cd /Users/artem.derevago/master_thesis/traffic-shaping-lean/formal
/private/tmp/lean-4.33.1-darwin_aarch64/bin/lake build TrafficShaping.Converse
/private/tmp/lean-4.33.1-darwin_aarch64/bin/lake build TrafficShaping.MainTheorem
```

Both commands exit successfully.  The output contains only existing style and
unused-variable linter warnings.  The successful `MainTheorem` build verifies
the current noncausal achievability and `IsLeast` declarations; it does not
turn the still-absent causal theorem into a proved result.
