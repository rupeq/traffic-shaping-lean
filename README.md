# The cost of causality in privacy-preserving traffic shaping

Source code, exact rational certificates, and a Lean formalization for the finite-session traffic-shaping model studied by Artem Dereviago.

Repository: [rupeq/traffic-shaping-lean](https://github.com/rupeq/traffic-shaping-lean). This repository is private while the manuscript and formalization are being prepared. A private GitHub URL does not provide public access; access must be granted separately, or the supplementary archive must accompany a submission.

## Computational materials

The `computations/` directory contains the original optimization code, 95 positive-delay primal/dual certificates, independent certificate checkers, exhaustive algorithm checks, and zero-delay and no-savings checks. See [the computational instructions](computations/README.md). A clean verification and full regeneration of all 95 LP values completed successfully; the fresh reports record the checked domains and environment. The GitHub workflow repeats the full reproduction on changes to these materials. The [first clean Linux reproduction](https://github.com/rupeq/traffic-shaping-lean/actions/runs/34526555754) also passed for all 95 values.

## Formalization status

Lean work is in progress. The default `lake build` now checks the finite foundations, the equivalence of greedy matching and feasibility, both universal converse bounds, the repair total-variation identity, and the **complete noncausal optimum**, including attainment and independence of every finite nonnegative epsilon. The least-element and infimum statements are `noncausal_optimum_isLeast` and `noncausal_optimum_eq` in [MainTheorem.lean](formal/TrafficShaping/MainTheorem.lean).

The causal construction and causal optimum are not yet complete. They are the remaining formalization task; the verified causal converse alone does not establish causal attainment. The [current verification record](verification/NONCAUSAL-OPTIMUM-CHECK.json) and [semantic audit](review/ACHIEVABILITY-SEMANTIC-AUDIT.md) state this scope explicitly. All 13 audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`, with no unfinished-proof dependency or additional axiom.

Use the [pinned environment](docs/TOOLCHAIN.md), run `lake build` in `formal/`, then run `lake env lean AuditNoncausal.lean` to inspect the dependencies of the principal checked results. Finite numerical checks and a successful build of a subset of modules are not treated as a proof of the full causal theorem.

## Mathematical scope

Inputs have publicly known finite duration, at most one arrival per slot, at most `m` real packets in total, a hard per-packet delay bound, and a cap counting all real and dummy transmissions on every execution. Privacy compares each admissible input with the empty input through the complete binary output trace. Broader traffic or observation models require separate arguments.
