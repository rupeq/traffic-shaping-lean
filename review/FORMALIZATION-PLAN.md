# Lean formalization plan for Theorem 1

This document specifies a Lean-friendly route to the main theorem in
`article-1-final-2026-09-10-r4/international-en/manuscript.md`.  It is a proof
plan, not a proposed Lean implementation.  The theorem is formalized for
every finite horizon and every `m, B, D` satisfying

```
0 < H,  1 ≤ m ≤ H,  m ≤ B ≤ H,  0 ≤ D.
```

The case `B < m` is proved separately as an infeasibility lemma.  No
enumeration bound, solver output, or external covering theorem is used in the
proof of the main result.  The cited finite computations can later be checked
against the definitions below.

## 1. Core representation

Use a finite, discrete model throughout.  The most convenient choices are

```text
Slot H       := {t : Nat // t < H}
Trace H      := Slot H → Bool
Input H      := Trace H
Arrivals x   := {t : Slot H // x t = true}
```

`Fin H` can be used in place of `Slot H`; a named subtype is often easier for
the arithmetic lemmas because `.val` remains a natural number.  Keep the
binary trace representation instead of representing a trace by a `Finset`:
coordinate restriction, output prefixes, and the public observation then have
direct definitions.

Define

```text
weight z       := (Finset.univ.filter (fun t => z t = true)).card
deadline D a   := min (a.val + D) (H - 1)
emptyInput     := fun _ => false
```

Every use of `H - 1` carries `hH : 0 < H`; prove once that
`deadline D a < H`.  A useful alternative is to define the clipped deadline
as a `Slot H` and keep the natural-number version as a coercion lemma.  Keep
the service-slot inequalities in natural numbers:

```text
a.val ≤ s.val ∧ s.val ≤ deadline D a
```

This avoids repeated coercion lemmas while proving FIFO arithmetic.

For an input `x` and trace `y`, define `Feasible x y` by an injective service
assignment

```text
f : Arrivals x → Slot H
```

such that every assigned slot is a one of `y` and satisfies the release-time
and clipped-deadline inequalities.  The assignment domain is a finite subtype,
so `Function.Injective f` is the exact one-packet-per-slot condition.  Define

```text
F x := {y : Trace H | Feasible x y}
```

and keep the transmission cap separate:
`Cap B y := weight y ≤ B`.  This makes it explicit that privacy slack never
permits a deadline or cap violation.

Prove these elementary facts first:

1. The arrival trace `x` itself is feasible for `x` by assigning every packet
   to its arrival slot (`D ≥ 0`).
2. If `x'` is obtained from `x` by adding arrivals, then
   `Feasible x' y → Feasible x y` by restricting an assignment.
3. If `y` is obtained from `y'` by adding transmission slots, then
   `Feasible x y → Feasible x y'` by reusing the assignment.
4. There is an admissible `x⁺` of weight exactly `m` extending every
   admissible `x` of weight at most `m`.  Prove this by selecting `m - weight x`
   points from the complement of the arrival set.  Consequently, for every
   fixed schedule law, the least coverage over all nonempty inputs is attained
   among inputs of weight exactly `m`.
5. If `B < m`, the input with `m` arrivals cannot be served under `Cap B`.

The fourth fact is the reduction used everywhere the manuscript writes
`min_{|x|=m}`.  Do not silently replace the full input class by weight-
`m` inputs; expose this monotonicity lemma in the dependency graph.

## 2. Greedy feasibility and the matching lemma

For a trace `y`, enumerate its one-slots in increasing order.  For an input,
enumerate its arrivals in increasing order.  Define the FIFO greedy procedure
recursively: for the next arrival, choose the least unused one-slot of `y`
whose value is not before the arrival.  It fails if there is no such slot or if
the chosen slot is after the packet deadline.

Formalize the procedure as a result type such as

```text
GreedyResult x y := Fail | Success (assignment : Arrivals x → Slot H)
```

with predicates for order, injectivity, and deadline validity.  The key lemma
is the exact equivalence

```text
greedySucceeds x y ↔ Feasible x y.
```

The forward implication is immediate from the recursive construction.  For
the reverse implication, use induction over the sorted arrivals and an
exchange argument, rather than invoking a general matching theorem:

* Assume a valid assignment for the already processed arrivals that agrees
  with greedy on their slots.
* Let `a` be the next arrival, let `s` be its slot in that assignment, and
  let `s' ≤ s` be the greedy slot.
* If `s'` is unused, move `a` to `s'`.
* If `s'` is assigned to a later arrival `a'`, exchange the assignments of
  `a` and `a'`.

The exchange is valid because `a ≤ a'`, `s' ≤ s`, and
`deadline D a ≤ deadline D a'`.  The earlier packet receives the earlier slot
`s'`.  The later packet moves from `s'` to `s`; its release-time inequality
`a' ≤ s` was already true, and its deadline remains valid because
`s ≤ deadline D a ≤ deadline D a'` (the original assignment served `a` at
`s`).  Previously fixed assignments are unchanged.  This gives the induction
step.

State separately the natural-number lemma that clipped deadlines are
nondecreasing in arrival time.  It is the only deadline-order fact needed in
the exchange.

The greedy theorem should also expose the algorithmic invariant used later:
before a switch, the queue assignment made by the causal rule is exactly the
prefix of this greedy assignment.  A separate theorem proves that inserting
additional one-slots or deleting arrivals cannot turn a successful greedy
assignment into a failure.

## 3. Schedule classes and the finite game

For `m ≤ B ≤ H`, define finite sets of traces

```text
Soff B := {y | weight y = B}
Son  B := {y | weight y = B ∧
               ∀ t, H - m ≤ t.val → t.val < H → y t = true}
```

The second class has exactly `B - m` one-slots in the prefix and all `m`
terminal slots.  Prove nonemptiness constructively by taking the first
`B - m` prefix slots.  Prove the cardinalities only if needed for the later
combinatorial propositions; Theorem 1 needs finiteness and nonemptiness.

For any nonempty finite schedule set `S`, use a finite probability law
(`Law S`) whose mass function has nonnegative real values summing to one.  A
custom finite law structure is preferable to introducing general measure
theory: all domains here are finite, and all push-forwards and event masses
are finite sums.  Define

```text
coverage q x := ∑ y : S, q y * (if Feasible x y then 1 else 0)
worst q     := min' (all admissible weight-m inputs) (coverage q x)
v S         := sSup {z | ∃ q : Law S, z = worst q}
```

Then prove that the supremum is a maximum.  A robust finite-dimensional proof
is:

1. View `Law S` as the set of vectors `q : S → ℝ` with `q y ≥ 0` and
   `∑ y, q y = 1`.
2. Show it is closed and bounded in the finite product space, hence compact
   by Heine–Borel.  The uniform law supplies nonemptiness.
3. `coverage q x` is a finite linear sum and therefore continuous.
4. The minimum over the finite set of weight-`m` inputs is continuous (or,
   equivalently, introduce an auxiliary scalar `z` with constraints
   `z ≤ coverage q x` for every input).
5. Apply the extreme-value theorem to obtain `q*` with
   `worst q* = v S`.

The theorem should be stated explicitly as

```text
∃ qStar : Law S, ∀ q, worst q ≤ worst qStar ∧ worst qStar = v S.
```

This is the finite-simplex attainment needed by the construction.  It is
independent of the later rational-certificate computations.  A later module
may add the finite LP dual and the direct certificate checker; Theorem 1
should depend only on the primal maximizer.  For a candidate rational primal
and dual certificate, checking normalization, nonnegativity, and every matrix
inequality directly is sufficient and avoids making the main theorem depend
on a general LP formalization.

## 4. Finite laws, prefixes, and privacy

Use a semantic mechanism class.  This is broad enough for every randomized
stateful implementation and keeps the converse independent of a particular
randomness or state representation:

```text
Mechanism H m B D :=
  law       : Input H → Law (Trace H)
  feasible  : ∀ x, weight x ≤ m → ∀ y, law x y > 0 → Feasible x y
  budget    : ∀ x, weight x ≤ m → ∀ y, law x y > 0 → weight y ≤ B
```

A mechanism is `Causal` when equal prefixes of two *admissible* inputs induce
equal output-prefix laws.  For `t ≤ H`, define `prefix t z : Fin t → Bool` by
restriction.  Define `samePrefix t x x'` coordinatewise and define `Causal M`
by

```text
weight x ≤ m → weight x' ≤ m → samePrefix t x x' →
  map (prefix t) (M.law x) = map (prefix t) (M.law x')
```

for every `t` and every pair of inputs.  The empty input and `tailInput` used
in the converse are admissible, so this is exactly the causality instance the
lower bound needs.  If the law field is defined on all binary inputs, retain
the two weight premises; do not silently strengthen the theorem to a class
causal on inadmissible inputs.  An operational state machine will be shown to
induce this semantic property by induction on slots.

Represent a finite law by a nonnegative real mass function with total mass
one.  Define push-forward mass by summing over the finite preimage.  Define
event mass for a `Finset (Trace H)` and

```text
TV P Q := (1 / 2) * ∑ y, |P y - Q y|.
```

The finite-law library should establish:

* event monotonicity: `|P E - Q E| ≤ TV P Q`;
* the shared-seed coupling bound
  `TV (map f q) (map g q) ≤ q {u | f u ≠ g u}`;
* the reverse event lower bound
  `TV P Q ≥ |P E - Q E|`;
* at `ε = 0`, the two event-wise DP inequalities are equivalent to
  `TV P Q ≤ δ`;
* if `ε ≥ 0`, an `(0, δ)` pair is also an `(ε, δ)` pair because
  `1 ≤ exp ε` and event masses are nonnegative.

Use real `ε` with the assumption `0 ≤ ε`; “finite ε” means exactly that no
extended-real value is admitted.  Define privacy for an admissible nonempty
input `x` and every output event `E` by both inequalities

```text
P_x(E) ≤ exp ε * P_0(E) + δ
P_0(E) ≤ exp ε * P_x(E) + δ.
```

Define the optimum as an `IsLeast` statement over `δ ∈ [0,1]`, rather than as
an unproved infimum over the infinite space of mechanisms.  The converse
proves a lower bound for every member of this set, and the construction gives
an element attaining that lower bound.

## 5. The converse: no repair or representation assumption

Let `M` be any valid mechanism and put `Q := M.law emptyInput`.  For every
admissible active input `x`, apply the reverse privacy inequality to the event
`F xᶜ`.  Feasibility gives `P_x(F xᶜ) = 0`, so

```text
Q(F xᶜ) ≤ δ.                                      (C)
```

This is the only privacy step and is independent of `ε`.  The rest is a
finite support transformation of `Q`; it must not be described as an online
repair and it must not assume that `Q` came from a fixed schedule.

### 5.1 Noncausal support transformation

For every trace `z` with `weight z ≤ B`, define `saturateOff z` by adding the
first `B - weight z` zero-slots.  Prove it has weight `B`, contains all
one-slots of `z`, and therefore preserves every feasible input.  Make the
function total by mapping the (zero-mass) `weight z > B` branch to one fixed
element of `Soff B`; the cap makes that branch null under `Q`.

Push `Q` forward through `saturateOff` to a law `q` on `Soff B`.  Since the
cap holds almost surely,

```text
q(F x) ≥ Q(F x) ≥ 1 - δ.
```

Take the minimum over weight-`m` inputs and use the finite-simplex definition
of `v` to obtain `v (Soff B) ≥ 1 - δ`, hence
`δ ≥ 1 - v (Soff B)`.

### 5.2 Empty-prefix lemma for causal mechanisms

Put `r := H - m`.  Define `tailInput` by ones exactly on slots
`r, ..., H - 1`.  Prove in this order:

1. Every feasible trace for `tailInput` has one on each terminal slot.  The
   assignment maps `m` packets injectively into the `m` terminal slots; the
   release-time constraints force the range to be contained in those slots,
   so finite cardinality gives equality.
2. Consequently, the cap implies that every trace in the support of
   `M.law tailInput` has at most `B - m` ones in the prefix
   `0, ..., r - 1`.
3. `tailInput` and the empty input have the same prefix of length `r`.
   Causality transfers the prefix-law event of probability one to `Q`:

   ```text
   Q(prefixWeight ≤ B - m) = 1.                 (P)
   ```

The statement remains valid for `r = 0`: then `m = H` and the prefix count is
zero.  This explicit edge case prevents accidental use of a positive-prefix
assumption.

### 5.3 Causal support transformation

For every trace satisfying the event in (P), define `saturateOn z` by adding
prefix zeros until the prefix has `B - m` ones and setting all terminal slots
to one.  Prove that it is in `Son B`, contains `z`, and preserves feasibility.

Make the function total by mapping traces outside the event to one fixed
element of `Son B`; the outside branch has `Q`-mass zero by (P).  Push `Q`
forward and use the same monotonicity argument as in the noncausal case.  It
gives

```text
v (Son B) ≥ 1 - δ,
```

and therefore the causal lower bound.  This proof covers arbitrary semantic
causal laws, so it does not assume a fixed schedule, a repair operation, or a
particular kernel/state realization.

## 6. Achievability: noncausal and causal mechanisms

Choose an optimal law `qStar` from the finite-simplex lemma.

### 6.1 Noncausal rule

Sample `y` from `qStar` independently of `x` before the session.  Define

```text
Roff x y := if Feasible x y then y else arrivalTrace x.
```

This is a full-input rule, so it is a valid noncausal mechanism.  The fallback
is feasible and has at most `m ≤ B` transmissions.  On the empty input every
schedule is feasible, so the empty-input output law is exactly `qStar`.

For an active input, `Roff x y = y` whenever `y ∈ F x`, and every produced
trace is feasible.  The shared-seed coupling and the event `F xᶜ` give the
exact identity

```text
TV(law (Roff x), qStar) = qStar(F xᶜ).             (TV-off)
```

The upper inequality is the coupling bound.  The reverse inequality uses
that the active law gives `F xᶜ` mass zero while the empty law gives it mass
`qStar(F xᶜ)`.  At the optimal law, the right side is at most
`1 - v (Soff B)` for every input.

### 6.2 Operational switch-to-service rule

Sample `y` from an optimal law on `Son B`.  The state is a mode (`Schedule` or
`Service`) and a FIFO list of arrival slots.  The step at slot `t` is ordered
as follows:

1. Read `x t`; append `t` to the queue when it is one.
2. In schedule mode, if the queue is nonempty, `y t = 0`, and the oldest
   packet has deadline `t`, switch to service mode immediately.
3. In service mode, transmit the oldest real packet when the queue is
   nonempty; otherwise stay silent.
4. If still in schedule mode, transmit at a one of `y` (the oldest real
   packet if available, otherwise a dummy), and stay silent at a zero of `y`.

Implement this as a recursion over `t < H`; do not define it by looking at a
future arrival.  Prove the following state invariants by induction:

* the queue is sorted, has no duplicate slots, and contains exactly the
  arrivals seen so far that have not been served;
* while in schedule mode, the served packet/slot pairs agree with the FIFO
  greedy matching of the prefix of `y`;
* once service mode is entered it is permanent and no dummy is ever sent.

The core feasibility proof is split into two cases, with all arithmetic made
explicit in natural numbers.

**No switch before `r = H - m`.**  If the queue at `r` is nonempty, list the
unserved and future arrivals as `a₁ < ... < a_k`.  Each has
`a₁ + D ≥ r`; otherwise its deadline would have forced a service or a switch
before `r`.  The terminal reserve gives a one in every slot from `r` onward.
The FIFO service times satisfy

```text
s₁ = max(r, a₁)
sᵢ = max(aᵢ, sᵢ₋₁ + 1)
sᵢ = max(aᵢ, r + i - 1).
```

Distinct integer arrivals give `aᵢ ≥ a₁ + i - 1`, hence
`r + i - 1 ≤ aᵢ + D`.  Because `i ≤ m`, `r + i - 1 ≤ H - 1`, so the clipped
deadline is respected.  The same argument includes `r = 0`.

**A first switch at `τ < r`.**  Before the switch, at most `B - m` base
transmissions occurred because all `B - m` nonterminal schedule ones lie in
the prefix.  The oldest queued arrival is `a₁ = τ - D`: the deadline check is
at an untruncated slot `τ < H - 1`.  For the queued and future arrivals,

```text
sᵢ = max(aᵢ, τ + i - 1),
aᵢ ≥ a₁ + i - 1,
τ + i - 1 ≤ aᵢ + D.
```

There are at most `m` packets in this list, and `τ + i - 1 ≤ H - 2` for
`i ≤ m`; together with `aᵢ ≤ H - 1` this proves both service completion and
the clipped deadline.  After the switch there are no dummy transmissions and
at most `m` real transmissions, so the total cap is at most
`(B - m) + m = B`.

If no switch occurs, the output is exactly `y` and has weight `B`.  These two
cases establish delivery, no duplicate service, the hard cap, and the absence
of loss for every admissible input.  They cover `D = 0`, `B = m`, `B = H`,
and `m = H`; no strict inequality such as `r > 0` may be inserted.

### 6.3 Causality and schedule preservation

Prove by induction that equal input prefixes produce equal transducer states
and output prefixes for every fixed sampled schedule `y`.  Since `y` is
sampled independently of the input, pushing any common law `q` through the
transducer preserves the prefix-law equality.  This proves `Causal` for the
constructed mechanism.

If `y ∈ F x`, the greedy/matching equivalence implies that the deadline check
never triggers.  The rule therefore remains in schedule mode and emits
exactly `y`:

```text
Feasible x y → R_on x y = y.                       (Preserve)
```

The output is always feasible by the two-case argument above.  On the empty
input the queue stays empty, so the rule never switches and emits the sampled
schedule; hence `P₀ = qStar`.

The same-seed argument as in (TV-off) gives the exact causal identity

```text
TV(law (Ron x), qStar) = qStar(F xᶜ).              (TV-on)
```

This is an identity for the complete public trace, including a change in the
number or positions of transmissions after a switch.  It must not be replaced
by an argument that only compares timing while conditioning on a fixed count.

At `qStar`, (TV-on) satisfies privacy with `ε = 0` and
`δ = 1 - v (Son B)`, and therefore with every finite `ε ≥ 0` at the same
`δ`.

## 7. Main theorem statement and dependency order

State the result as two `IsLeast` theorems.  For every finite `ε ≥ 0`, define
`PrivacySet_off ε` and `PrivacySet_on ε` as the `δ ∈ [0,1]` for which an
appropriate mechanism exists.  Then prove

```text
IsLeast (PrivacySet_off ε) (1 - v (Soff B))
IsLeast (PrivacySet_on  ε) (1 - v (Son  B))
```

and separately

```text
∃ Moff, Privacy Moff 0 (1 - v (Soff B))
∃ Mon,  Privacy Mon  0 (1 - v (Son  B)).
```

The recommended proof order is:

1. finite arithmetic, arrivals, deadlines, trace weights;
2. feasibility monotonicity and weight-`m` reduction;
3. greedy success iff injective matching;
4. finite laws, prefix maps, event mass, TV lemmas;
5. finite simplex compactness and an optimal `qStar`;
6. support cap saturation and the empty-prefix lemma;
7. arbitrary-mechanism noncausal and causal converses;
8. noncausal fallback rule and exact TV identity;
9. switch-to-service recursion, invariants, feasibility, and causality;
10. causal preservation and exact TV identity;
11. the two `IsLeast` statements and the `ε = 0` attainment corollary.

This order ensures that neither the converse nor achievability assumes the
conclusion of the other direction.

## 8. Secondary results and their status

These are not prerequisites for Theorem 1.  They can be added after the core
module, reusing the same finite game and schedule transformations.

### Theorem 2: additional budget at a privacy threshold

Define

```text
B_g δ := min {B ∈ Nat | m ≤ B ∧ B ≤ H ∧ δ_g B ≤ δ}.
```

First prove that the set is nonempty because `B = H` gives the all-one
schedule and value one.  Prove monotonicity in `B` by adding schedule slots.
The lower bound `B_on δ ≥ B_off δ` follows because every causal mechanism is a
noncausal mechanism.  For the upper bound, transform each noncausal schedule
of weight `B_off δ` by adding the terminal `m` slots and padding to
`min(H, B_off δ + m)`.  This is the same monotone support transformation as in
the converse, now applied to an optimal schedule law.  The sharp example uses
`D = 0`, `H ≥ 2m`, and
`δ = 1 - 1/C(H,m)`; it needs the elementary zero-delay formula or a direct
subset-counting argument.

### Theorem 3: privacy gap at a fixed budget

For `B ≥ 2m`, start with an optimal noncausal law.  Independently retain a
uniform `B - m` subset of its `B` one-slots, add the terminal reserve, and pad
to weight `B`.  For a fixed matching of an input to `m` original slots, the
probability all `m` slots survive the deletion is

```text
C(B - m, m) / C(B, m).
```

Adding terminal slots and padding can only help.  Average over the original
law and minimize over inputs to get the covering-value inequality.  Translate
it to the privacy-gap inequality using Theorem 1.  The final union bound is
`1 - rho ≤ m^2 / B`.  Formalize the hypergeometric count separately; it is
the only new probability calculation.

### Proposition 1: perfect privacy budget

Let `H = a(D+m) + b` with `0 ≤ b < D+m`.  The lower bound uses `K` separate
test inputs: `m` arrivals in the first `m` slots of each full block and
`min(m,b)` arrivals at the beginning of the remainder.  Every trace feasible
for a test must use the corresponding service slots inside that block, and
these service blocks are disjoint.  At `δ = 0`, the converse event bound makes
the empty-input trace feasible for all tests outside one null set; therefore it
has at least

```text
B0 = m*a + min(m,b)
```

ones almost surely.  The union of the test inputs is not an input and must not
be used in this argument.

For sufficiency, use the fixed schedule consisting of the last `m` slots of
each full block and the last `min(m,b)` slots of the remainder.  Prove by a
block induction that the queue is empty at every block boundary and that a
packet waits at most `D` slots.  The same fixed trace is emitted for every
input, so it gives `δ = 0` in both classes for every finite `ε`.  This last
sentence concerns this particular fixed mechanism; it is not a claim that an
arbitrary positive-`ε` optimum has the same output law as the empty input.

### Proposition 2: zero-delay closed forms

For `D = 0`, prove `Feasible x y ↔ support x ⊆ support y`.  Then use uniform
subset laws and uniform input laws as matching primal and dual certificates.
For the noncausal class this gives

```text
v_off(B) = C(B,m) / C(H,m).
```

For the causal class, put `n = H-m`, `k = B-m`, `j = min(m,n)`.  The terminal
reserve is automatic, and an input with `c` prefix arrivals is covered with
probability `C(k,c)/C(n,c)`.  This decreases in `c`, so the worst case is
`c = j`; a dual law with `j` uniformly chosen prefix arrivals and fixed
terminal arrivals proves equality:

```text
v_on(B) = C(k,j) / C(n,j).
```

Use the convention `C(0,0) = 1` and prove the `H = m` case explicitly.

### Proposition 3: no-savings threshold

Reuse the `K = ceil(H/(D+m))` disjoint block tests from Proposition 1.  If
`B < B0`, every trace with cap `B` fails at least one test.  The union bound
and the event bound (C) give

```text
1 ≤ K * δ,  hence  δ ≥ 1/K.
```

At `B = B0`, Proposition 1 supplies `δ = 0`, so both threshold budgets equal
`B0` whenever `0 ≤ δ < 1/K`.  Keep the inequality strict.  The point
`δ = 1/K` cannot be included in general; formalize the small boundary example
`H = 2, m = 1, D = 0, B = 1` using the zero-delay formula.

The secondary propositions therefore need no new mechanism model.  Proposition
1 adds a block-scheduling proof, Proposition 2 adds finite subset counting,
and Proposition 3 adds a finite union-bound argument.  Theorem 2 and Theorem 3
add only monotone schedule transformations and hypergeometric counting.

## 9. Edge-case checklist

The formal development should include explicit lemmas or test cases for:

* `D = 0` (deadline equals arrival; switch may occur in the arrival slot);
* `D ≥ H` (clipped deadlines are still `< H`);
* `m = 1`;
* `m = H`, hence `r = 0` and necessarily `B = H`;
* `B = m` (no spare schedule slots beyond the terminal reserve);
* `B = H` (the all-one trace);
* `H = 1`;
* empty prefix/suffix in the causal support transformation;
* `v(S) = 0` (the construction still has `δ = 1`);
* empty-input budget and feasibility, since the cap is required there too.

Avoid hidden assumptions that the first switch exists, that a prefix has a
positive length, or that a mechanism emits exactly `B` transmissions.  The
base schedule has weight `B`; a repaired causal output may have fewer.

## 10. Suggested module layout and validation

The eventual Lean project can be split as follows:

```text
TrafficShaping/FiniteModel.lean       slots, traces, inputs, deadlines
TrafficShaping/Matching.lean          assignments, greedy, monotonicity
TrafficShaping/Law.lean               finite laws, maps, events, TV, prefixes
TrafficShaping/Game.lean              schedule sets, simplex, value attainment
TrafficShaping/Converse.lean          cap saturation, empty-prefix bound
TrafficShaping/Construction.lean      noncausal fallback and causal transducer
TrafficShaping/MainTheorem.lean       Theorem 1 and epsilon corollaries
TrafficShaping/ClosedForms.lean       Theorems 2–3 and Propositions 1–3
```

Before proving the full theorem, compile small lemmas for `H = 1`, `m = H`,
and `D = 0`; these expose `Fin` subtraction and empty-prefix issues early.
Then prove the greedy equivalence independently of probability.  Next test
the finite-law lemmas on a two-element output type.  Only after the semantic
converse and switch construction are complete should the finite-game value be
connected to the privacy optimum.

The machine-readable certificate files in `traffic-shaping-lean/computations`
can be used as regression data, but their numerical values are not premises of
the theorem.  A certificate checker should validate a proposed rational
primal/dual pair against the exact feasibility matrix and should remain
separate from the all-parameter proof.
