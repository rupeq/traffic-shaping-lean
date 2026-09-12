# Certificate evaluation review

## Bounded finite checks

The closed row and column predicates are evaluated through `finiteChecked`,
whose elaborated body uses `Finset.decidableDforallFinset`. This is the
relevant kernel-level property: evaluation traverses the explicitly supplied
`Finset` and does not first enumerate the ambient subtype `Fintype`.

`rowsCheckedOnFinset` therefore visits only its supplied row set, while
`colsCheckedOnFinset` visits only its supplied schedule set. The soundness
lemmas recover the corresponding bounded universal propositions through
`finiteChecked_true_iff`; the partition lemmas combine complementary filtered
sets by ordinary case analysis. The checks remain ordinary `by decide +kernel`
proofs, with no `native_decide` or trusted native evaluator.

`rowsCheckedEnum` also uses `finiteChecked`, with `fullInputEnum` as its
explicit finite set. Its soundness theorem then uses
`fullInputEnum_eq_univ` to obtain the complete input domain.

## Causal schedule enumeration

`optimizedOnScheduleEnum` chooses `B - m` slots from the prefix of length
`H - m` and adjoins `terminal H m`. Its equality theorem proves that this is the full
`OnSchedule H m B` subtype under `m ≤ H` and `m ≤ B` (including
the article domain `B ≤ H`).
This avoids constructing all `B`-subsets of the horizon before filtering for
the terminal reserve.

## Validation boundary

The bounded-decider elaboration has been checked with Lean's printed
definition, and `CertificateOnEnumeration.lean` typechecks with the pinned
Lean 4.33.1 toolchain. The subsequent complete kernel build and combined check passed for all
95 generated certificates after these changes; see the separate integration
evidence below.

## Integration evidence appended by the coordinating task

Run `20260912T134526Z-0bf54535` completed at `2026-09-12T13:47:31.281731+00:00` with PASS. The [complete report](../verification/article-complete/ARTICLE-CHECK.json) SHA-256 is `80fde35447373f7816ce8e141a8f1c7b7371c62358074a97ba654d3733f1e116`. The formal gate emitted 257 reports for 257 requested declarations and accepted all 67 inventory items. The combined gate also passed the regression tests, source regeneration of all 95 certificates, exact corollary checks, and table checks. This subsequent integration evidence is distinct from the source reviewer's work.
