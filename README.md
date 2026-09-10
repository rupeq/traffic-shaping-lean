# The cost of causality in privacy-preserving traffic shaping

Source code, exact rational certificates, and a Lean formalization for the finite-session traffic-shaping model studied by Artem Dereviago.

Repository: [rupeq/traffic-shaping-lean](https://github.com/rupeq/traffic-shaping-lean). This repository is private while the manuscript and formalization are being prepared. A private GitHub URL does not provide public access; access must be granted separately, or the supplementary archive must accompany a submission.

## Computational materials

The `computations/` directory contains the original optimization code, 95 positive-delay primal/dual certificates, independent certificate checkers, exhaustive algorithm checks, and zero-delay and no-savings checks. See [the computational instructions](computations/README.md). A clean verification and full regeneration of all 95 LP values completed successfully; the fresh reports record the checked domains and environment. The GitHub workflow repeats the full reproduction on changes to these materials. The [first clean Linux reproduction](https://github.com/rupeq/traffic-shaping-lean/actions/runs/34526555754) also passed for all 95 values.

## Formalization status

Lean work is in progress. The finite model, probability and total-variation lemmas, finite-game attainment and certificate theorem, and terminal saturation lemmas compile successfully. Their [axiom audit](verification/FOUNDATIONS-CHECK.json) uses only the standard logical axioms of Lean. No complete Lean verification of the manuscript is claimed at this stage. The intended sequence is reproducible computations, proofs of the service lemmas and algorithm, and the full optimality theorem over causal and noncausal mechanisms. Finite numerical checks alone do not prove the general theorem.

The formal development pins Lean and mathlib versions and will record the correspondence between manuscript claims and checked theorem declarations. The final verification will reject unfinished proofs and inspect the axioms used by the principal results. See [the pinned environment](docs/TOOLCHAIN.md).

## Mathematical scope

Inputs have publicly known finite duration, at most one arrival per slot, at most `m` real packets in total, a hard per-packet delay bound, and a cap counting all real and dummy transmissions on every execution. Privacy compares each admissible input with the empty input through the complete binary output trace. Broader traffic or observation models require separate arguments.
