# Verification work plan

1. Reproduce the computations in a clean environment. Independently verify all 95 positive-delay certificates, the finite algorithm checks, zero-delay certificates, and the no-savings checks. Verify that full LP regeneration is documented and compare exact regenerated values when the run completes.
2. Create the requested private GitHub repository and upload only the reviewed source and reproducibility materials. Record its actual URL and private-access status.
3. Formalize the model, matching/greedy lemmas, empty-prefix restriction, and the switch-to-service algorithm with causal execution, hard delivery, cap, and schedule preservation proved from their definitions.
4. Prove the complete covering characterization of the optimum, including arbitrary causal output kernels, attainable optimal base distributions, both privacy inequalities, and independence from every finite nonnegative epsilon. No repair-correctness or converse-lifting assumption may substitute for a missing concrete-model proof.
5. Check the correspondence with the manuscript and state the precise coverage of secondary results. Build from a fresh checkout and inspect proof axioms.
6. Prepare revision r5 of all three manuscript editions: retain the titles, apply the local abstract/algorithm/reserve clarifications, restore an accurately identified data-and-code section, and reflect only actually completed formal verification. Preserve earlier final editions.
