import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Lattice

/-!
# A finite zero-sum coverage game

This module isolates the finite game used by the traffic-shaping development.
A law is represented directly as a point of `stdSimplex ℝ S`; the common
`TrafficShaping.Law` abbreviation can be introduced by a later root module.
The matrix `A` is deliberately independent of scheduling, so the same
lemmas apply to both the noncausal and causal coverage matrices.
-/

open scoped BigOperators
open Set

namespace TrafficShaping

variable {I S : Type*} [Fintype I] [Nonempty I] [Fintype S] [Nonempty S]

/-- Coverage of an input row by a simplex law on schedules. -/
def coverage (A : I → S → ℝ) (q : stdSimplex ℝ S) (i : I) : ℝ :=
  ∑ s, (q : S → ℝ) s * A i s

/-- The least row coverage of a law.  The `inf'` is over all rows. -/
def worst (A : I → S → ℝ) (q : stdSimplex ℝ S) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (coverage A q)

/-- The value of the finite game, as the supremum of the attainable worst
coverages. -/
noncomputable def value (A : I → S → ℝ) : ℝ :=
  sSup (Set.range (worst A))

lemma simplex_nonempty : Nonempty (stdSimplex ℝ S) := by
  classical
  exact ⟨⟨Pi.single (Classical.arbitrary S) 1, single_mem_stdSimplex ℝ _⟩⟩

lemma coverage_continuous (A : I → S → ℝ) (i : I) :
    Continuous (fun q : stdSimplex ℝ S => coverage A q i) := by
  unfold coverage
  apply continuous_finsetSum Finset.univ
  intro s hs
  exact ((continuous_apply s).comp continuous_subtype_val).mul continuous_const

lemma worst_continuous (A : I → S → ℝ) :
    Continuous (worst A) := by
  unfold worst
  apply Continuous.finset_inf'_apply Finset.univ_nonempty
  intro i hi
  exact coverage_continuous A i

/-- A maximum of the continuous worst-coverage function realizes the `sSup`
used in `value`. -/
lemma value_eq_worst_of_max
    (A : I → S → ℝ) (q : stdSimplex ℝ S)
    (hmax : ∀ q', worst A q' ≤ worst A q) :
    value A = worst A q := by
  have hne : (Set.range (worst A)).Nonempty := Set.range_nonempty _
  have hbdd : BddAbove (Set.range (worst A)) := by
    refine ⟨worst A q, ?_⟩
    rintro _ ⟨q', rfl⟩
    exact hmax q'
  apply le_antisymm
  · exact csSup_le hne (by
      rintro _ ⟨q', rfl⟩
      exact hmax q')
  · exact le_csSup hbdd ⟨q, rfl⟩

/-- The finite simplex game has an optimal law. -/
lemma exists_optimal (A : I → S → ℝ) :
    ∃ qStar : stdSimplex ℝ S,
      ∀ q, worst A q ≤ worst A qStar ∧ worst A qStar = value A := by
  have hcompact : IsCompact (Set.univ : Set (stdSimplex ℝ S)) := isCompact_univ
  have hne : (Set.univ : Set (stdSimplex ℝ S)).Nonempty := Set.univ_nonempty
  obtain ⟨qStar, hqStar, hmax⟩ :=
    hcompact.exists_isMaxOn hne (worst_continuous A).continuousOn
  refine ⟨qStar, ?_⟩
  intro q
  refine ⟨?_, ?_⟩
  · exact hmax (Set.mem_univ q)
  · exact (value_eq_worst_of_max A qStar
      (fun q' => hmax (Set.mem_univ q'))).symm

/-- A convenient one-line attainment statement. -/
theorem value_attained (A : I → S → ℝ) :
    ∃ qStar : stdSimplex ℝ S, worst A qStar = value A := by
  obtain ⟨qStar, hqStar⟩ := exists_optimal A
  exact ⟨qStar, (hqStar qStar).2⟩

/-- Every law has worst coverage at most the game value. -/
lemma worst_le_value (A : I → S → ℝ) (q : stdSimplex ℝ S) :
    worst A q ≤ value A := by
  obtain ⟨qStar, hqStar⟩ := exists_optimal A
  calc
    worst A q ≤ worst A qStar := (hqStar q).1
    _ = value A := (hqStar qStar).2

/-- An optimal law covers every row at least at the game value. -/
lemma optimal_coverage_ge_value (A : I → S → ℝ) (qStar : stdSimplex ℝ S)
    (hopt : worst A qStar = value A) (i : I) :
    value A ≤ coverage A qStar i := by
  calc
    value A = worst A qStar := hopt.symm
    _ ≤ coverage A qStar i := by
      unfold worst
      exact Finset.inf'_le _ (Finset.mem_univ i)

lemma coverage_nonneg {A : I → S → ℝ} (hA : ∀ i s, 0 ≤ A i s)
    (q : stdSimplex ℝ S) (i : I) :
    0 ≤ coverage A q i := by
  unfold coverage
  apply Finset.sum_nonneg
  intro s hs
  exact mul_nonneg (stdSimplex.zero_le q s) (hA i s)

lemma coverage_le_one {A : I → S → ℝ} (hA : ∀ i s, A i s ≤ 1)
    (q : stdSimplex ℝ S) (i : I) :
    coverage A q i ≤ 1 := by
  unfold coverage
  calc
    (∑ s, (q : S → ℝ) s * A i s) ≤ ∑ s, (q : S → ℝ) s * 1 := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (hA i s) (stdSimplex.zero_le q s)
    _ = 1 := by simpa only [mul_one] using stdSimplex.sum_eq_one q

lemma worst_nonneg {A : I → S → ℝ} (hA : ∀ i s, 0 ≤ A i s)
    (q : stdSimplex ℝ S) :
    0 ≤ worst A q := by
  unfold worst
  apply Finset.le_inf' Finset.univ_nonempty
  intro i hi
  exact coverage_nonneg hA q i

lemma worst_le_one {A : I → S → ℝ} (hA : ∀ i s, A i s ≤ 1)
    (q : stdSimplex ℝ S) :
    worst A q ≤ 1 := by
  unfold worst
  calc
    Finset.univ.inf' Finset.univ_nonempty (coverage A q) ≤
        coverage A q (Classical.arbitrary I) :=
      Finset.inf'_le _ (Finset.mem_univ _)
    _ ≤ 1 := coverage_le_one hA q _

lemma value_nonneg (A : I → S → ℝ) (hA : ∀ i s, 0 ≤ A i s) :
    0 ≤ value A := by
  obtain ⟨qStar, hqStar⟩ := exists_optimal A
  have hbdd : BddAbove (Set.range (worst A)) := by
    refine ⟨worst A qStar, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact (hqStar q).1
  apply le_csSup_of_le hbdd ⟨qStar, rfl⟩
  exact worst_nonneg hA qStar

lemma value_le_one (A : I → S → ℝ) (hA : ∀ i s, A i s ≤ 1) :
    value A ≤ 1 := by
  obtain ⟨qStar, hqStar⟩ := exists_optimal A
  rw [← (hqStar qStar).2]
  exact worst_le_one hA qStar

/-- If every matrix entry lies in `[0,1]`, then so does the game value. -/
theorem value_mem_Icc (A : I → S → ℝ)
    (hA : ∀ i s, A i s ∈ Set.Icc (0 : ℝ) 1) :
    value A ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨value_nonneg A (fun i s => (hA i s).1),
    value_le_one A (fun i s => (hA i s).2)⟩

/-- Weak duality for a finite matrix.  The hypotheses explicitly expose the
nonnegativity and normalization of both certificate vectors.  `hrow` is a
primal lower certificate and `hcol` is a dual upper certificate. -/
lemma weak_duality_certificate
    (A : I → S → ℝ) (q : S → ℝ) (w : I → ℝ) (v u : ℝ)
    (hq_nonneg : ∀ s, 0 ≤ q s) (hq_sum : ∑ s, q s = 1)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (hrow : ∀ i, v ≤ ∑ s, q s * A i s)
    (hcol : ∀ s, ∑ i, w i * A i s ≤ u) :
    v ≤ u := by
  have hweighted :
      (∑ i, w i * v) ≤ ∑ i, w i * (∑ s, q s * A i s) := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hrow i) (hw_nonneg i)
  calc
    v = ∑ i, w i * v := by
      rw [← Finset.sum_mul, hw_sum, one_mul]
    _ ≤ ∑ i, w i * (∑ s, q s * A i s) := hweighted
    _ = ∑ s, q s * (∑ i, w i * A i s) := by
      calc
        (∑ i, w i * (∑ s, q s * A i s)) =
            ∑ i, ∑ s, w i * (q s * A i s) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mul_sum]
        _ = ∑ s, ∑ i, w i * (q s * A i s) := by
              rw [Finset.sum_comm]
        _ = ∑ s, q s * (∑ i, w i * A i s) := by
              apply Finset.sum_congr rfl
              intro s hs
              calc
                (∑ i, w i * (q s * A i s)) =
                    ∑ i, q s * (w i * A i s) := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      ring
                _ = q s * (∑ i, w i * A i s) := by
                      rw [Finset.mul_sum]
    _ ≤ ∑ s, q s * u := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (hcol s) (hq_nonneg s)
    _ = u := by
      rw [← Finset.sum_mul, hq_sum, one_mul]

lemma worst_le_weighted (A : I → S → ℝ)
    (q : stdSimplex ℝ S) (w : stdSimplex ℝ I) :
    worst A q ≤ ∑ i, (w : I → ℝ) i * coverage A q i := by
  have hweighted :
      (∑ i, (w : I → ℝ) i * worst A q) ≤
        ∑ i, (w : I → ℝ) i * coverage A q i := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left
      (by
        unfold worst
        exact Finset.inf'_le _ (Finset.mem_univ i))
      (stdSimplex.zero_le w i)
  calc
    worst A q = ∑ i, (w : I → ℝ) i * worst A q := by
      rw [← Finset.sum_mul, stdSimplex.sum_eq_one w, one_mul]
    _ ≤ ∑ i, (w : I → ℝ) i * coverage A q i := hweighted

lemma weighted_coverage_eq (A : I → S → ℝ)
    (q : stdSimplex ℝ S) (w : stdSimplex ℝ I) :
    (∑ i, (w : I → ℝ) i * coverage A q i) =
      ∑ s, (q : S → ℝ) s * (∑ i, (w : I → ℝ) i * A i s) := by
  unfold coverage
  calc
    (∑ i, (w : I → ℝ) i * ∑ s, (q : S → ℝ) s * A i s) =
        ∑ i, ∑ s, (w : I → ℝ) i * ((q : S → ℝ) s * A i s) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    _ = ∑ s, ∑ i, (w : I → ℝ) i * ((q : S → ℝ) s * A i s) := by
          rw [Finset.sum_comm]
    _ = ∑ s, (q : S → ℝ) s * (∑ i, (w : I → ℝ) i * A i s) := by
          apply Finset.sum_congr rfl
          intro s hs
          calc
            (∑ i, (w : I → ℝ) i * ((q : S → ℝ) s * A i s)) =
                ∑ i, (q : S → ℝ) s * ((w : I → ℝ) i * A i s) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
            _ = (q : S → ℝ) s * (∑ i, (w : I → ℝ) i * A i s) := by
                  rw [Finset.mul_sum]

lemma worst_le_of_column_certificate (A : I → S → ℝ)
    (w : stdSimplex ℝ I) (u : ℝ)
    (hcol : ∀ s, ∑ i, (w : I → ℝ) i * A i s ≤ u) :
    ∀ q : stdSimplex ℝ S, worst A q ≤ u := by
  intro q
  calc
    worst A q ≤ ∑ i, (w : I → ℝ) i * coverage A q i := worst_le_weighted A q w
    _ = ∑ s, (q : S → ℝ) s * (∑ i, (w : I → ℝ) i * A i s) :=
      weighted_coverage_eq A q w
    _ ≤ ∑ s, (q : S → ℝ) s * u := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (hcol s) (stdSimplex.zero_le q s)
    _ = u := by
      rw [← Finset.sum_mul, stdSimplex.sum_eq_one q, one_mul]

lemma value_le_of_column_certificate (A : I → S → ℝ)
    (w : stdSimplex ℝ I) (u : ℝ)
    (hcol : ∀ s, ∑ i, (w : I → ℝ) i * A i s ≤ u) :
    value A ≤ u := by
  apply csSup_le (Set.range_nonempty (worst A))
  rintro z ⟨q, rfl⟩
  exact worst_le_of_column_certificate A w u hcol q

/-- A matching primal/dual certificate pins down both the value and the
certified primal law.  The common scalar is the `v = u` of weak duality. -/
theorem matching_certificate (A : I → S → ℝ)
    (q : stdSimplex ℝ S) (w : stdSimplex ℝ I) (v : ℝ)
    (hrow : ∀ i, v ≤ coverage A q i)
    (hcol : ∀ s, ∑ i, (w : I → ℝ) i * A i s ≤ v) :
    value A = v ∧ worst A q = v := by
  have hq_lower : v ≤ worst A q := by
    unfold worst
    apply Finset.le_inf' Finset.univ_nonempty
    intro i hi
    exact hrow i
  have hvalue_upper : value A ≤ v := value_le_of_column_certificate A w v hcol
  have hvalue_lower : v ≤ value A :=
    hq_lower.trans (worst_le_value A q)
  have hq_upper : worst A q ≤ v := by
    exact (worst_le_value A q).trans hvalue_upper
  exact ⟨le_antisymm hvalue_upper hvalue_lower, le_antisymm hq_upper hq_lower⟩

end TrafficShaping
