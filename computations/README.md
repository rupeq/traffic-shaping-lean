# Computational materials for Supplement S1

Revision r5 — Artem Dereviago, 10 September 2026.
Repository: `https://github.com/rupeq/traffic-shaping-lean`.
This release accompanies the same study in either journal version. All data are
generated finite combinatorial instances, not captured network traffic. The
proofs in the manuscript establish the general claims; the computations below
check stated finite domains and numerical examples.

## Run the clean reproducibility driver

`run_checks.py` is the entry point for this package. It copies `computations/`
to a temporary directory, runs every checker there, and writes fresh reports
and command logs to the requested output directory. It hashes every ordinary
source file before and after the run, excluding only `.venv/`, `__pycache__/`,
and bytecode files. The driver never reads the historical PASS logs as
evidence and refuses optimized Python (`-O` or `PYTHONOPTIMIZE`).

Create an isolated environment for the LP solver and install the pinned
requirements without changing a global Python installation:

```sh
python3.12 -m venv ../traffic-shaping-computations-venv
. ../traffic-shaping-computations-venv/bin/activate
python -m pip install -r requirements.txt
```

Run the standard-library checks in a clean copy:

```sh
python -S run_checks.py \
  --outputdir ../traffic-shaping-computations-checks
```

This independently checks all 79 `FRONTIERS.json` certificates and all 16
r4 certificates, the finite fallback algorithm, the 240 exact zero-delay
games, and the 375-instance no-savings domain. It expects 95 positive-delay
certificates, 10,356 primal rows, 39,931 schedule columns, 4,518 zero-delay
primal rows, and 2,295 zero-delay schedule columns.

For a complete fresh LP reproduction in the same clean temporary copy, add
`--full-regenerate`:

```sh
python run_checks.py \
  --outputdir ../traffic-shaping-computations-full \
  --full-regenerate
```

The fresh run solves and independently checks all 95 LPs, then compares their
exact rational coverage and delta values with the saved reports. A linear
solver may choose different optimal supports; support sets and elapsed times
are deliberately not compared. A successful run writes
`REPRODUCIBILITY-CHECK.json` and `FULL-REGENERATION.json` in the requested
output directory.

`NEGATIVE-CHECKS.json` records two adversarial checks run in temporary copies:
the independent checker rejects a non-normalized primal distribution and a
changed claimed certificate value. The saved certificate files remain
unchanged.

## Run the exact checks

Use Python 3.12 or a compatible newer version, from this extracted directory.
Do not run with `python -O`: the verification assertions must remain enabled.

```sh
python independent_certificate_check.py
python fallback_check.py
```

These two commands use only the Python standard library. The first checks all
79 stored primal/dual certificates with an independent augmenting-path matching
algorithm; it also checks the explicit 28-by-15 example and writes TABLE-1.csv.
The second exhaustively checks the actual queue rule in `execute`: delivery,
the transmission cap, preservation of feasible schedules, common prefixes and
exact total variation for uniform base distributions. Its scope is H=1..7,
1<=m<=B<=H and D=0..H, with every admissible input and reserve schedule.

Expected fallback counts: 546 parameter tuples; 45,622 input/schedule pairs;
4,069 switches; 347,870 prefix comparisons; 20,532 exact TV comparisons.
The uniform-law checks do not replace the proof for arbitrary base laws.

## Reproduce the optimization checks

Create an isolated Python environment, then install the pinned dependencies:

```sh
python -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
python quantitative_check.py
```

This runs 240 zero-delay games (H=1..8, all 1<=m<=B<=H, both classes), checking
their exact primal/dual witnesses against the closed forms. It also checks 43
budget comparisons on paired saved frontiers and 66 fixed-budget privacy-gap
comparisons, and writes QUANTITATIVE-CHECK.json. The saved frontier is only an
illustration grid: m=2, H in {8,12}, D in {1,2,3}, both classes, and H=16 with
the same delays for the causal class. Each family includes all B from m to B0.

For one fresh LP and an exact rational certificate:

```sh
python covering.py --horizon 8 --delay 1 --arrivals 2 --cap 4 --output example.json
```

Add `--offline` for the noncausal comparison. Optional `python
regenerate_frontiers.py` recomputes all 79 saved instances and independently
checks each fresh witness. It can take substantially longer. A solver version
may select different optimal strategies: compare certified values, not the
particular support or elapsed time. Exact reconstruction failure is reported
as a failed assertion, never silently accepted as an approximate certificate.

The optimizer proposes strategies with floating point arithmetic. Acceptance
uses rational normalization, nonnegativity, every primal/dual inequality and
equality of values. The independent saved-certificate checker imports neither
the optimizer nor its greedy feasibility predicate. The execution rule is the
stop-dummy rule in `fallback_check.execute`, rather than the older research
prototype that maintained an exactly saturated transmission count.

The historical check artifacts are retained in `verification.log`,
`verification-final.log`, and the original CHECK JSON files. They are
provenance records; the clean driver above is the current entry point. See
`ENVIRONMENT.json` for the original solver environment and
`SOURCE-PROVENANCE.json` for lineage. `SHA256SUMS` lists the files in this
release.

## Для русскоязычного читателя

Архив является общим приложением к двум альтернативным версиям одной статьи.
Первые две команды проверяют готовые сертификаты и причинный алгоритм без
внешних библиотек. Последующие команды воспроизводят решения линейных программ.
TABLE-1.csv содержит значения таблицы 2 редакции r4 (историческое имя файла сохранено). TABLE-3.csv соответствует таблице 3; таблица 1 сравнивает литературу и не является вычислительной. Конечная проверка не заменяет
доказательство и не является экспериментом на реальном сетевом трафике.


## Additional independent zero-delay certificates

Run `python zero_delay_independent_check.py` using only the Python standard
library. For every H=1,...,8 and every 1<=m<=B<=H in both mechanism classes,
it constructs zero-delay feasibility directly as subset containment. It checks
explicit uniform primal and dual strategies with exact rational arithmetic,
including all 4518 primal rows and 2295 dual columns across 240 games. It does
not import the optimizer or its feasibility predicate. Full witnesses and
checks are written to ZERO-DELAY-EXACT-CHECK.json. This independently certifies
the reported finite zero-delay values; the general causal characterization
still rests on the manuscript's proof.

## Additional positive-delay certificates for r4

`EXTRA-CERTIFICATES.json` stores sixteen exact reports, all added in r4.
The first and second batches contain eight reports each. The first-batch tuples
are `(8,1,3,5),(8,2,3,4),(10,1,4,7),(10,2,4,7)`. The second-batch tuples are
`(10,1,3,7),(12,2,3,7),(12,1,4,9),(14,2,4,9)`, each in causal and offline
classes. The independent augmenting-path checker verifies every stored primal
and dual witness.

The `selection` column uses the historical labels `original` and `added` for
these two r4 batches; neither label refers to the 79 pre-r4 certificates.
`TABLE-3.csv` has one row per tuple and keeps the two values visible as
`delta_off` and `delta_on`. Its four second-batch rows are informative: their
`delta_on` values are `1/2, 1/2, 2/3, 2/3`, all below one, with causal
coverages `1/2, 1/2, 1/3, 1/3`. The first-batch rows remain visible: all four
have `delta_on=1` and `delta_off=1/2`.

Across all sixteen checks there are 4,736 primal rows and 4,024 dual columns:
the first batch contributes 1,064 rows and 421 columns, while the second batch
contributes 3,672 rows and 3,603 columns. For one class, rows are the
`C(H,m)` maximal arrival inputs. Offline columns are `C(H,B)` schedules;
causal columns are `C(H-m,B-m)` schedules with the final `m` service slots
reserved. These are finite combinatorial examples used to check the
manuscript's exact values, not scalability benchmarks.

`regenerate_extra.py` preserves and rechecks the stored first eight, then
solves only the eight added LPs. Run `verify_extra.py` with the Python standard
library to verify all sixteen and write `EXTRA-CERTIFICATE-CHECK.json`.

## New no-savings bound

Run `python no_savings_check.py > NO-SAVINGS-CHECK.json` using only the Python
standard library. This checks the new block argument for H=1,...,9, all
1<=m<=H, and D=0,...,H+1: 375 parameter sets. It checks that every test
input forces the required service count in its own block, that no trace
with budget below B0 can cover all tests, and that the fixed B0 schedule
covers every admissible input. The example showing why the threshold
delta<1/K must be strict is evaluated with exact fractions.

## Historical provenance

The stored original 79 positive-delay certificates and prior algorithm and
zero-delay results retain their earlier provenance. The r4 work added 16
positive-delay certificates and this targeted no-savings check; it did not
rerun the earlier 79 LPs or the prior exhaustive algorithm and zero-delay
grids. All 95 positive-delay certificates are available for independent
checking.

The historical source archive was
`dereviago-supplement-S1-r4-2026-09-10.zip`. Its r4 labels remain in the
certificate metadata and file names so that those records remain traceable.

For a quick check of just the r4 additions:

```sh
python verify_extra.py
python no_savings_check.py > NO-SAVINGS-CHECK.json
```

The original `TABLE-1.csv` is the numeric Table 2 in both r4 manuscripts.
`TABLE-3.csv` is Table 3. The original filename and checker are retained to
preserve compatibility. To regenerate all sixteen added-in-r4 LPs from
scratch, work in a copy of this release, remove `EXTRA-CERTIFICATES.json`
from that copy, and run `python regenerate_extra.py`. With that file present,
the command reuses and rechecks the first eight and solves the next eight.
