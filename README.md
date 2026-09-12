# The cost of causality in privacy-preserving traffic shaping

Source code, exact rational certificates, and a Lean formalization for the finite-session traffic-shaping model studied by Artem Dereviago.

Repository: [rupeq/traffic-shaping-lean](https://github.com/rupeq/traffic-shaping-lean).

## Computational materials

The `computations/` directory contains the original optimization code, 95 positive-delay primal/dual certificates, independent certificate checkers, exhaustive algorithm checks, and zero-delay and no-savings checks. See [the computational instructions](computations/README.md). The archived baseline verification and full regeneration of all 95 LP values completed successfully; those reports record their own source versions, checked domains, and environment. The GitHub workflow repeats the full reproduction on changes to these materials. The [first clean Linux reproduction](https://github.com/rupeq/traffic-shaping-lean/actions/runs/34526555754) also passed for all 95 values.

## Formalization status

The **complete optimum theorem for both mechanism classes** is formalized in Lean 4.33.1. For every `1 ≤ m ≤ B ≤ H`, every natural delay bound `D`, and every real `ε ≥ 0`, the minimum additive loss equals one minus the corresponding finite covering-game value. Both minima are attained already at `ε = 0`. The separate theorem `mechanism_impossible_of_budget_lt` rules out a cap below the admissible workload.

The declarations `noncausal_optimum_isLeast`, `causal_optimum_isLeast`, `noncausal_optimum_eq`, and `causal_optimum_eq` are in [MainTheorem.lean](formal/TrafficShaping/MainTheorem.lean). The causal attainment proof uses the [actual queue execution](formal/TrafficShaping/ExecutionCore.lean), with delivery, delay, cap, prefix causality, and schedule preservation proved from that execution. The [proof map](review/FORMALIZATION-PLAN.md) identifies the corresponding modules.

The five corollaries now have Lean proofs: the additive budget bound and sharpness, the thinning comparison and asymptotic privacy gap, the exact perfect-privacy budget with an explicit feasible schedule, both zero-delay formulas, and the strict no-savings interval. They use the same semantic mechanism classes as the main theorem. The [article inventory](formal/article-coverage.json) and [complete map](review/ARTICLE-FORMALIZATION-MAP.md) now name source declarations for all 67 required items, including actual FIFO service-time formulas and every numerical table row. The [complete article check](verification/article-complete/ARTICLE-CHECK.json) passed for the recorded source snapshot, including 257 kernel-axiom reports, all 95 certificate proofs, independent exact computations, and all 17 numerical table rows. This report records local verification of the source snapshot; GitHub Actions checks each pushed revision separately.

Use the [pinned environment](docs/TOOLCHAIN.md), then run `python3 verify_article.py` from the repository root. It combines the complete Lean build and kernel audit with independent exact computational checks. Use `--lake /path/to/lake` for an explicit compiler installation. The [article verification instructions](docs/ARTICLE-VERIFICATION.md) explain the evidence and completeness gates; the [CI instructions](docs/CI.md) describe the corresponding GitHub checks.

The earlier [optimum verification record](verification/FULL-OPTIMUM-CHECK.json), its 29-declaration audit, and the older semantic reviews remain historical checkpoints of the main theorem. The current audit derives its required declarations from the complete article inventory and accepts only `propext`, `Classical.choice`, and `Quot.sound`. A recorded check applies to its recorded source hashes; historical reports do not certify later additions.

## Mathematical scope

Inputs have publicly known finite duration, at most one arrival per slot, at most `m` real packets in total, a hard per-packet delay bound, and a cap counting all real and dummy transmissions on every execution. Privacy compares each admissible input with the empty input through the complete binary output trace. Broader traffic or observation models require separate arguments.

The manuscript text in either language is maintained outside this repository.
