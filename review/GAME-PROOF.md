# Finite-game proof record

`formal/TrafficShaping/Game.lean` contains the scheduling-independent finite
matrix game used by the later off/on coverage matrices.  It uses the subtype
`stdSimplex ℝ S` directly.  This is definitionally the same law type as the
root module's `TrafficShaping.Law` abbreviation.

The matrix is `A : I → S → ℝ`, with `[Fintype I] [Nonempty I]` and
`[Fintype S] [Nonempty S]`.  The checked definitions are:

```text
coverage A q i = ∑ s, q s * A i s
worst A q       = Finset.univ.inf' Finset.univ_nonempty (coverage A q)
value A         = sSup (Set.range (worst A))
```

The compactness proof establishes continuity of every row coverage and of
the finite infimum (`coverage_continuous`, `worst_continuous`), then applies
`isCompact_univ.exists_isMaxOn` to the simplex.  `exists_optimal` gives a
law `qStar` such that every law has no larger worst coverage and
`worst A qStar = value A`; `value_attained`, `worst_le_value`, and
`optimal_coverage_ge_value` expose the corresponding corollaries.

For entrywise bounds, `coverage_nonneg`, `coverage_le_one`, `worst_nonneg`,
and `worst_le_one` prove the pointwise estimates.  `value_nonneg` and
`value_le_one` lift them through the attained maximum, while
`value_mem_Icc` gives `0 ≤ value A ≤ 1` from
`∀ i s, A i s ∈ Set.Icc 0 1`.

The certificate part contains two layers.  `weak_duality_certificate` takes
plain vectors `q : S → ℝ` and `w : I → ℝ`, checks nonnegativity and unit sums,
and proves `v ≤ u` from row lower bounds and column weighted upper bounds.
`worst_le_of_column_certificate` and `value_le_of_column_certificate` turn
the dual column certificate into an upper bound on the game value.
`matching_certificate` takes simplex laws, a matching common scalar `v`, and
the same row/column inequalities, and proves both `value A = v` and
`worst A q = v`.

## Verification

The file compiles with Lean 4.33.1 and mathlib v4.33.1 using:

```text
cd /Users/artem.derevago/master_thesis/traffic-shaping-lean/formal
/private/tmp/lean-4.33.1-darwin_aarch64/bin/lake env lean TrafficShaping/Game.lean
```

The command exits successfully.  The only output is the standard unused
section-variable linter warning for lemmas whose statements do not need every
ambient nonempty instance.

The module contains no unfinished proof placeholders or unsafe evaluation
shortcuts.  An auxiliary `#print axioms` check reports only the ordinary
logical/mathlib dependencies `propext`, `Classical.choice`, and `Quot.sound`
for the compactness and finite-supremum proofs.
