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

The main verification step runs `python3 verify_article.py`. It checks the
regression tests, reproduction of the Lean certificates from the rational
inputs, the full Lean build and axiom audit, the independent exact
corollary checks, and the saved rational certificates and table derivations.
The [article verification guide](ARTICLE-VERIFICATION.md) describes the
combined evidence record.

The formal audit enforces three separate conditions:

1. Every Lean source in the proof tree and all top-level Lean files are
   scanned after removing comments, strings, and quoted identifiers. Exact
   source tokens `axiom`, `sorry`, `sorryAx`, `admit`, `unsafe`, and
   `native_decide` fail the check. Every proof module must be reachable from
   the root import; unexpected scratch modules also fail the check.
2. The 67 required article items must each have named declarations in
   `formal/article-coverage.json`, and every declaration must appear in the
   active `#print axioms` commands in `formal/Audit.lean`. A missing formula,
   corollary, supporting consequence, or table row fails the check. The
   inventory tests presence; the accompanying semantic reviews check that
   the propositions express the intended article statements.
3. Every audit command must have exactly one matching kernel report. Both
   `depends on axioms: [...]` and `does not depend on any axioms` are parsed.
   Duplicate, missing, or extra reports fail the check. Only `propext`,
   `Classical.choice`, and `Quot.sound` are allowed.

The wrapper writes a fresh run directory and records the before/after hashes
of the proof sources, audit and checker code, and saved certificate inputs.
The combined record remains `RUNNING` until it is replaced by `PASS` or
`FAIL`; source changes or incomplete subreports prevent a pass. The older
`verification/FULL-OPTIMUM-CHECK.json` and its 29 kernel reports remain a
historical checkpoint for the source revision that they record.

The workflow definition is prepared locally. A successful remote run for the
article-completion revision must be recorded separately after GitHub checks
that revision; the earlier main-theorem CI run does not certify new sources.

The workflow follows the Lean installation/build flow and GitHub's action
security guidance:

- <https://lean-lang.org/install/manual/>
- <https://lean-lang.org/doc/reference/latest/Axioms/>
- <https://github.com/leanprover/elan/releases/tag/v4.2.3>
- <https://github.com/leanprover/elan/commit/b6cec7e10fe4965a605aaf60d1cb4a5837f0462b>
- <https://github.com/leanprover/lean4/releases/tag/v4.33.1>

The checkout action is pinned to the verified official commit
<https://github.com/actions/checkout/commit/11d5960a326750d5838078e36cf38b85af677262>.
