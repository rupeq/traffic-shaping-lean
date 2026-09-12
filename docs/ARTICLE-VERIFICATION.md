# Verifying the article

The full check uses the pinned Lean 4.33.1 environment and Python's standard
library. Run it from the repository root:

```sh
python3 verify_article.py --output-dir .check-output/article
```

An explicit compiler installation can be selected with `--lake /path/to/lake`.
Each invocation creates a new run directory. The top-level `ARTICLE-CHECK.json`
identifies that run and remains `RUNNING` until a final result is written.
Earlier run directories are retained.

The command checks five independently relevant parts:

1. Regression tests for the audit, inventory, evidence gate, and rejection of
   corrupted rational certificates or missing table rows.
2. Reproduction of the 95 Lean certificate statements, finite supports and
   integer weights from the saved rational inputs. The generated proof source
   must match the imported module, allowing comments and whitespace to differ.
3. The root Lean build and kernel-axiom audit. The
   [article inventory](../formal/article-coverage.json) requires an audited
   declaration for every numbered formula, all four lemmas, the main theorem,
   five corollaries, the mathematical prose consequences, and every numeric
   row of Tables 2 and 3. An empty inventory item fails the check. Every proof
   module must be reachable from the root import. Temporary proof files,
   unapproved axioms, and unfinished proofs fail the check.
4. Independent exact finite checks of the five corollaries, random thinning,
   boundary cases, the explicit example and its two queue executions, and the
   privacy interpretation. The matcher uses augmenting paths and all
   probabilities use `fractions.Fraction`.
5. Fresh rational checks of the 95 saved positive-delay certificates and
   exact derivation of the two tables, including the minimum-budget columns.
   This step does not rerun the optimizer.

The result records before/after hashes of the proof sources, gate and checker
implementations, and saved certificate inputs. Changed sources, missing
reports, a narrowed finite check domain, or a nonzero subprocess exit make
the combined result fail. The Lean audit accepts only `propext`,
`Classical.choice`, and `Quot.sound`; it also handles declarations that use no
axioms. Both `ARTICLE-FORMAL-CHECK.json` and the compatible
`FULL-OPTIMUM-CHECK.json` are written by the formal sub-check.

The machine-readable inventory verifies the presence of the declared
anchors. Semantic reviews separately check that each proposition has the
article's intended quantifiers and meaning. A Lean theorem with an extra
unproved mathematical hypothesis does not close the corresponding inventory
item merely because the theorem compiles.

The formal complexity statement counts list inspections for the matcher on
already sorted traces. It does not count sorting or finite-set preprocessing.
The execution result counts exactly `H` transitions and bounds the queue by
`m`; it does not assign machine costs to a transition. These are the two cost
claims made in the article.

`computations/generate_lean_certificates.py` reproduces the 95 certificate
proofs from `FRONTIERS.json` and `EXTRA-CERTIFICATES.json`. Use `--output` to
write an inspection copy. It clears rational denominators into natural-number
weights; the imported Lean helpers prove normalization, every primal row,
every dual column, and the exact game value over the complete finite types.
Compilation uses kernel-checked `decide` proofs and can take substantially
longer than the independent Python certificate check.
The generated module elaborates certificates sequentially. Its finite checks
use bounded finite-set quantifiers, and complementary partitions keep each
closed reduction small. The partition lemmas prove that every original row
and column remains covered. Causal schedules are enumerated by adding the
mandatory terminal reserve to a subset of the remaining slots. These changes
affect evaluation cost; the certificate equalities still concern the original
complete input and schedule types. The library configuration uses one compiler
worker and a memory cap of 8192 MiB per process.

The older `verification/FULL-OPTIMUM-CHECK.json` and its logs retain their
original scope and source hashes. They are historical checkpoints. The
current source tree must be checked with the current inventory and gate.

Archived reports retain the original absolute compiler, artifact, and log
paths as run provenance. Their bytes are preserved for checksum verification.
To reproduce the check after extracting the supplement elsewhere, run
`verify_article.py` from that copy; it writes a fresh report with local paths.

For a local release audit, the optional pair `--protected-manifest` and
`--protected-root` verifies the hashes of the previous manuscript release.
Manuscripts and their baseline manifest are maintained outside this repository.
