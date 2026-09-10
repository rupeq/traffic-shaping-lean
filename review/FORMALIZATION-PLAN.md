# Formal proof map

The main optimum theorem is implemented for all natural `H, m, B, D` with
`1 ≤ m ≤ B ≤ H` and all real `ε ≥ 0`. The proof includes universal lower
bounds over the semantic mechanism classes and actual attaining mechanisms.
The cap boundary `B < m` is a separate impossibility result.

## Model and probability

`Model.lean` represents binary traces by finite sets of slots in `Fin H`.
An input has at most `m` arrivals. `Feasible D x y` is an injective assignment
from the arrivals of `x` to transmission slots of `y`, with release and delay
inequalities. The codomain `Fin H` enforces delivery before the public horizon.

`Law.lean` uses finite real probability vectors. It defines event masses,
push-forwards, total variation, and both event inequalities of participation
privacy. The exact repair identity is proved by combining a common-seed
coupling with the forbidden-output event; it is not an assumed bound.

`Mechanism.lean` quantifies over arbitrary finite output laws for each
admissible input. Every positive-mass output satisfies feasibility and the cap.
Causality means equality of output-prefix laws whenever arrival prefixes
agree. No sampled-schedule representation is assumed in the converse.

## Matching and finite games

`Matching.lean` proves `greedy_true_iff_feasible` by an exchange argument.
`Saturation.lean` proves monotone input/output extensions, exact cardinality
saturation, and the terminal-input argument. Nonempty row and schedule types
are supplied from the parameter inequalities, not from unconditional
instances.

`Game.lean` proves existence of a maximizing law by compactness of the finite
simplex and continuity of the minimum row coverage. The general optimum
proof uses this primal attainment theorem. The separate certificate theorems
check finite primal/dual inequalities directly; no unproved LP-duality
assumption enters the optimum theorem.

## Universal converse

`Converse.lean` bounds the empty-input mass of the outputs forbidden by each
active input using the second privacy inequality. Saturation maps this law to
full-budget schedules without reducing coverage. In the causal case, the
terminal full input and equal-prefix laws first force the empty-prefix cap
`B-m`. This supports the terminal-reserve saturation and the causal lower
bound for every semantic causal mechanism.

## Concrete causal execution

`ExecutionCore.lean` contains the actual queue transition: observe the arrival,
check the oldest deadline, switch irreversibly when needed, and transmit
according to the current mode. It proves queue partition and ordering,
output-prefix support, deadline safety, and the mode-dependent output bound.

`Execution.lean` proves feasibility of the actual served-packet set.
`ExecutionDelivery.lean` proves that the queue is empty at the horizon and
that the served set equals the input. Its tail invariant counts queued and
future arrivals against the remaining service slots.

`ExecutionBudget.lean` derives the pathwise cap. `ExecutionCausality.lean`
proves pointwise equal-prefix outputs and exact preservation of the empty
input's base schedule. `ExecutionPreservation.lean` maintains a residual
matching invariant along the queue transition and proves
`execute_eq_of_feasible`. These are properties of the defined algorithm, with
no correctness oracle or unspecified repair function.

## Attainment and exact minima

`Achievability.lean` proves the generic repair composition results, including
exact TV and the reduction from full inputs to all admissible inputs. It
instantiates them with the noncausal fallback.

`OnAchievability.lean` instantiates the same results with the concrete causal
execution and its proved properties. It constructs a semantic causal
mechanism and proves `onMechanism_tv`, `onMechanism_private`, and
`causal_attainment` for an optimal base law.

`MainTheorem.lean` combines each attained upper bound with its universal
converse. It proves `IsLeast` for both loss sets; the infimum equalities and
independence of every finite nonnegative epsilon follow. The attained
minimum at epsilon zero is explicit in `both_optima_attained_at_zero`.

## Verification boundary

`Audit.lean` requests the transitive axiom dependencies of 29 critical
results, including both final equalities. The permitted dependencies are
only `propext`, `Classical.choice`, and `Quot.sound`. The source audit rejects
unfinished-proof tokens, additional axiom declarations, `unsafe`, and
`native_decide`. The verification wrapper records actual command results and
requires all formal source hashes to remain unchanged during the run.

The main theorem handles zero delay, clipped long delays, `m=1`, `m=H`,
`B=m`, `B=H`, and zero covering value through its universal parameter range.
There is no finite enumeration bound in these theorems. Secondary closed
forms, no-savings formulas, and quantitative resource-gap bounds have their
own analytical and computational records; they are not claimed as additional
Lean theorems in this inventory.
