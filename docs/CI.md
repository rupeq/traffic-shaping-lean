# Continuous integration checks

The repository has separate workflows for the finite computations and the
Lean formalization. Both use read-only repository permissions and run only
when their inputs change.

`computations.yml` verifies `computations/SHA256SUMS`, installs the pinned
Python requirements, runs the clean standard-library checks, and regenerates
all 95 saved positive-delay linear programs. Its reports are written below
`.check-output/` and are not treated as source inputs.

`formal.yml` checks the Lean toolchain declaration and the mathlib revision in
`formal/lake-manifest.json`. It installs the official elan v4.2.3 installer
from immutable `leanprover/elan` commit
`b6cec7e10fe4965a605aaf60d1cb4a5837f0462b`, then lets the existing
`formal/lean-toolchain` select Lean 4.33.1. It fetches the cache selected by the
existing manifest with `lake exe cache get` and runs `lake build`. It does not
run `lake update`, so CI does not silently move a dependency revision.

The final build step runs `lake env lean Audit.lean` and saves its output. The
following audit enforces two independent conditions:

1. It scans `formal/TrafficShaping.lean`, every Lean file below
   `formal/TrafficShaping/`, and `formal/Audit.lean` after removing nested
   block comments, line comments, string literals, and quoted identifiers.
   Exact source tokens `axiom`, `sorry`, `sorryAx`, `admit`, `unsafe`, and
   `native_decide` fail the check. This avoids treating prose or commented
   examples as declarations.
2. It extracts every active `#print axioms` command from `formal/Audit.lean`
   and matches it against the kernel's `depends on axioms: [...]` lines in the
   saved Lean output. Duplicate, missing, or extra commands/reports fail the
   check. The final inventory must include both
   `TrafficShaping.noncausal_optimum_eq` and
   `TrafficShaping.causal_optimum_eq`. Only Lean's standard logical axioms
   `propext`, `Classical.choice`, and `Quot.sound` are allowed. Missing axiom
   reports, `sorryAx`, `sorry`, `admit`, or any other axiom name fail the job.

`formal/Audit.lean` is the final 29-declaration theorem inventory and is a
required CI input. It includes both complete optimum theorems, their
least-element and epsilon-independence statements, and the concrete causal
execution results. Run `python3 verify_formal.py` from the repository root for
the equivalent local build and audit sequence. The wrapper writes all command
logs and `FULL-OPTIMUM-CHECK.json`, including before/after source hashes. It
returns a nonzero exit status if any command fails, any pinned input differs,
or the formal sources change during verification.

The saved `verification/full-optimum-axioms.log` contains the 29 actual kernel
reports from the complete local verification. A successful remote CI run is
recorded separately after GitHub finishes checking the committed sources.

The workflow follows the Lean installation/build flow and GitHub's action
security guidance:

- <https://lean-lang.org/install/manual/>
- <https://lean-lang.org/doc/reference/latest/Axioms/>
- <https://github.com/leanprover/elan/releases/tag/v4.2.3>
- <https://github.com/leanprover/elan/commit/b6cec7e10fe4965a605aaf60d1cb4a5837f0462b>
- <https://github.com/leanprover/lean4/releases/tag/v4.33.1>

The checkout action is pinned to the verified official commit
<https://github.com/actions/checkout/commit/11d5960a326750d5838078e36cf38b85af677262>.
