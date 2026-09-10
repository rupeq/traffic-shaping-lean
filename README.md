# The cost of causality in privacy-preserving traffic shaping

Source code, exact rational certificates, and a Lean formalization for the finite-session traffic-shaping model studied by Artem Dereviago.

Repository: [rupeq/traffic-shaping-lean](https://github.com/rupeq/traffic-shaping-lean). This repository is private while the manuscript and formalization are being prepared. A private GitHub URL does not provide public access; access must be granted separately, or the supplementary archive must accompany a submission.

## Computational materials

The `computations/` directory contains the original optimization code, 95 positive-delay primal/dual certificates, independent certificate checkers, exhaustive algorithm checks, and zero-delay and no-savings checks. See [the computational instructions](computations/README.md). A clean verification and full regeneration of all 95 LP values completed successfully; the fresh reports record the checked domains and environment. The GitHub workflow repeats the full reproduction on changes to these materials. The [first clean Linux reproduction](https://github.com/rupeq/traffic-shaping-lean/actions/runs/34526555754) also passed for all 95 values.

## Formalization status

The **complete optimum theorem for both mechanism classes** is formalized in Lean 4.33.1. For every `1 ≤ m ≤ B ≤ H`, every natural delay bound `D`, and every real `ε ≥ 0`, the minimum additive loss equals one minus the corresponding finite covering-game value. Both minima are attained already at `ε = 0`. The separate theorem `mechanism_impossible_of_budget_lt` rules out a cap below the admissible workload.

The declarations `noncausal_optimum_isLeast`, `causal_optimum_isLeast`, `noncausal_optimum_eq`, and `causal_optimum_eq` are in [MainTheorem.lean](formal/TrafficShaping/MainTheorem.lean). The causal attainment proof uses the [actual queue execution](formal/TrafficShaping/ExecutionCore.lean), with delivery, delay, cap, prefix causality, and schedule preservation proved from that execution. The [proof map](review/FORMALIZATION-PLAN.md) identifies the corresponding modules.

The [complete local verification record](verification/FULL-OPTIMUM-CHECK.json) includes command exit codes, the pinned versions, and the before/after hashes of all formal sources. All 29 declarations in [Audit.lean](formal/Audit.lean) use only `propext`, `Classical.choice`, and `Quot.sound`. The source and kernel audits reject unfinished proofs and additional axioms. Earlier verification records remain as dated checkpoints with their original, narrower scope.

Use the [pinned environment](docs/TOOLCHAIN.md), then run `python3 verify_formal.py` from the repository root. It runs `lake build`, `lake env lean Audit.lean`, and the strict source/kernel audit, and writes fresh logs and a JSON record. Use `--lake /path/to/lake` for an explicit compiler installation. The [CI instructions](docs/CI.md) describe the corresponding GitHub checks.

The Lean inventory covers the main optimum theorem, its algorithm, and the supporting lemmas. The secondary closed forms and quantitative resource-gap bounds are outside this formal inventory; their computational checks remain in `computations/`.

## Mathematical scope

Inputs have publicly known finite duration, at most one arrival per slot, at most `m` real packets in total, a hard per-packet delay bound, and a cap counting all real and dummy transmissions on every execution. Privacy compares each admissible input with the empty input through the complete binary output trace. Broader traffic or observation models require separate arguments.

The manuscript text in either language is maintained outside this repository.
