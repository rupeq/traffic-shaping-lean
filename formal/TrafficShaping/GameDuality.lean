import TrafficShaping.Game
import Mathlib.Topology.Sion

/-!
# Strong duality for finite coverage games

This file adds the dual side of the finite matrix game from `Game.lean`.
The proof uses Sion's minimax theorem on the two standard simplices; no
assumption is made on the entries of the matrix.
-/

open scoped BigOperators
open Set

namespace TrafficShaping

variable {I S : Type*} [Fintype I] [Nonempty I] [Fintype S] [Nonempty S]

/-- The weighted payoff of a row law `w` against a schedule law `q`. -/
def payoff (A : I → S → ℝ) (w : I → ℝ) (q : S → ℝ) : ℝ :=
  ∑ i, w i * (∑ s, q s * A i s)

/-- The largest column payoff of a row law. -/
def dualWorst (A : I → S → ℝ) (w : stdSimplex ℝ I) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun s => ∑ i, (w : I → ℝ) i * A i s)

/-- The dual value, written as the infimum of the attainable largest columns. -/
noncomputable def dualValue (A : I → S → ℝ) : ℝ :=
  sInf (Set.range (dualWorst A))

private lemma payoff_eq_weighted_coverage (A : I → S → ℝ)
    (w : stdSimplex ℝ I) (q : stdSimplex ℝ S) :
    payoff A (w : I → ℝ) (q : S → ℝ) =
      ∑ i, (w : I → ℝ) i * coverage A q i := by
  rfl

private lemma payoff_eq_weighted_columns (A : I → S → ℝ)
    (w : stdSimplex ℝ I) (q : stdSimplex ℝ S) :
    payoff A (w : I → ℝ) (q : S → ℝ) =
      ∑ s, (q : S → ℝ) s * (∑ i, (w : I → ℝ) i * A i s) := by
  unfold payoff
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

private lemma payoff_continuous_left (A : I → S → ℝ) (q : S → ℝ) :
    Continuous (fun w : I → ℝ => payoff A w q) := by
  unfold payoff
  apply continuous_finsetSum
  intro i hi
  exact (continuous_apply i).mul continuous_const

private lemma payoff_continuous_right (A : I → S → ℝ) (w : I → ℝ) :
    Continuous (fun q : S → ℝ => payoff A w q) := by
  unfold payoff
  apply continuous_finsetSum
  intro i hi
  apply continuous_const.mul
  apply continuous_finsetSum
  intro s hs
  exact (continuous_apply s).mul continuous_const

private lemma payoff_quasiconvex_left (A : I → S → ℝ) (q : S → ℝ) :
    QuasiconvexOn ℝ (stdSimplex ℝ I) (fun w : I → ℝ => payoff A w q) := by
  rw [quasiconvexOn_iff_le_max]
  refine ⟨convex_stdSimplex ℝ I, ?_⟩
  intro w hw z hz a b ha hb hab
  have hlin :
      payoff A (a • w + b • z) q =
        a • payoff A w q + b • payoff A z q := by
    unfold payoff
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      (∑ i, (a * w i + b * z i) * (∑ s, q s * A i s)) =
          ∑ i, (a * (w i * (∑ s, q s * A i s)) +
            b * (z i * (∑ s, q s * A i s))) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, a * (w i * (∑ s, q s * A i s))) +
            ∑ i, b * (z i * (∑ s, q s * A i s)) := by
        rw [Finset.sum_add_distrib]
      _ = a * (∑ i, w i * (∑ s, q s * A i s)) +
            b * (∑ i, z i * (∑ s, q s * A i s)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [hlin]
  calc
    a • payoff A w q + b • payoff A z q ≤
        a • max (payoff A w q) (payoff A z q) +
          b • max (payoff A w q) (payoff A z q) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
    _ = max (payoff A w q) (payoff A z q) := by
      rw [← add_smul, hab, one_smul]

private lemma payoff_quasiconcave_right (A : I → S → ℝ) (w : I → ℝ) :
    QuasiconcaveOn ℝ (stdSimplex ℝ S) (fun q : S → ℝ => payoff A w q) := by
  rw [quasiconcaveOn_iff_min_le]
  refine ⟨convex_stdSimplex ℝ S, ?_⟩
  intro q hq r hr a b ha hb hab
  have hlin :
      payoff A w (a • q + b • r) =
        a • payoff A w q + b • payoff A w r := by
    unfold payoff
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      (∑ i, w i * ∑ s, (a * q s + b * r s) * A i s) =
          ∑ i, w i *
            (a * (∑ s, q s * A i s) + b * (∑ s, r s * A i s)) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        calc
          (∑ s, (a * q s + b * r s) * A i s) =
              ∑ s, (a * (q s * A i s) + b * (r s * A i s)) := by
            apply Finset.sum_congr rfl
            intro s hs
            ring
          _ = (∑ s, a * (q s * A i s)) +
                ∑ s, b * (r s * A i s) := by
            rw [Finset.sum_add_distrib]
          _ = a * (∑ s, q s * A i s) + b * (∑ s, r s * A i s) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ = ∑ i, (a * (w i * (∑ s, q s * A i s)) +
            b * (w i * (∑ s, r s * A i s))) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, a * (w i * (∑ s, q s * A i s))) +
            ∑ i, b * (w i * (∑ s, r s * A i s)) := by
        rw [Finset.sum_add_distrib]
      _ = a * (∑ i, w i * (∑ s, q s * A i s)) +
            b * (∑ i, w i * (∑ s, r s * A i s)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [hlin]
  calc
    min (payoff A w q) (payoff A w r) ≤
        a • payoff A w q + b • payoff A w r := by
      rw [smul_eq_mul, smul_eq_mul]
      have hq' : min (payoff A w q) (payoff A w r) ≤ payoff A w q := min_le_left _ _
      have hr' : min (payoff A w q) (payoff A w r) ≤ payoff A w r := min_le_right _ _
      calc
        min (payoff A w q) (payoff A w r) =
            (a + b) * min (payoff A w q) (payoff A w r) := by rw [hab, one_mul]
        _ = a * min (payoff A w q) (payoff A w r) +
              b * min (payoff A w q) (payoff A w r) := by ring
        _ ≤ a * payoff A w q + b * payoff A w r := add_le_add
          (mul_le_mul_of_nonneg_left hq' ha)
          (mul_le_mul_of_nonneg_left hr' hb)

private lemma exists_saddle (A : I → S → ℝ) :
    ∃ w : stdSimplex ℝ I, ∃ q : stdSimplex ℝ S,
      IsSaddlePointOn (stdSimplex ℝ I) (stdSimplex ℝ S)
        (fun w q => payoff A w q) w q := by
  classical
  have hI : (stdSimplex ℝ I).Nonempty := by
    exact ⟨Pi.single (Classical.arbitrary I) 1, single_mem_stdSimplex ℝ _⟩
  have hS : (stdSimplex ℝ S).Nonempty := by
    exact ⟨Pi.single (Classical.arbitrary S) 1, single_mem_stdSimplex ℝ _⟩
  obtain ⟨w, hw, q, hq, hs⟩ :=
    Sion.exists_isSaddlePointOn
      (X := stdSimplex ℝ I) (Y := stdSimplex ℝ S)
      (f := fun w q => payoff A w q)
      hI (convex_stdSimplex ℝ I) (isCompact_stdSimplex ℝ I)
      (fun q hq => (payoff_continuous_left A q).continuousOn.lowerSemicontinuousOn)
      (fun q hq => payoff_quasiconvex_left A q)
      (convex_stdSimplex ℝ S) hS (isCompact_stdSimplex ℝ S)
      (fun w hw => (payoff_continuous_right A w).continuousOn.upperSemicontinuousOn)
      (fun w hw => payoff_quasiconcave_right A w)
  exact ⟨⟨w, hw⟩, ⟨q, hq⟩, hs⟩

/-- The feasible scalars in the dual linear program. -/
def dualFeasible (A : I → S → ℝ) : Set ℝ :=
  {u | ∃ w : stdSimplex ℝ I,
    ∀ s, ∑ i, (w : I → ℝ) i * A i s ≤ u}

private lemma saddle_payoff_le_row
    (A : I → S → ℝ) (w : stdSimplex ℝ I) (q : stdSimplex ℝ S)
    (hs : IsSaddlePointOn (stdSimplex ℝ I) (stdSimplex ℝ S)
      (fun w q => payoff A w q) w q) (i : I) :
    payoff A (w : I → ℝ) (q : S → ℝ) ≤ coverage A q i := by
  classical
  have hi : (Pi.single i (1 : ℝ) : I → ℝ) ∈ stdSimplex ℝ I :=
    single_mem_stdSimplex ℝ i
  have h := hs (Pi.single i (1 : ℝ)) hi (q : S → ℝ) q.2
  simpa [payoff, coverage, Pi.single_apply] using h

private lemma saddle_column_le_payoff
    (A : I → S → ℝ) (w : stdSimplex ℝ I) (q : stdSimplex ℝ S)
    (hs : IsSaddlePointOn (stdSimplex ℝ I) (stdSimplex ℝ S)
      (fun w q => payoff A w q) w q) (s : S) :
    ∑ i, (w : I → ℝ) i * A i s ≤
      payoff A (w : I → ℝ) (q : S → ℝ) := by
  classical
  have hs' : (Pi.single s (1 : ℝ) : S → ℝ) ∈ stdSimplex ℝ S :=
    single_mem_stdSimplex ℝ s
  have h := hs (w : I → ℝ) w.2 (Pi.single s (1 : ℝ)) hs'
  simpa [payoff, Pi.single_apply] using h

private lemma saddle_payoff_le_value
    (A : I → S → ℝ) (w : stdSimplex ℝ I) (q : stdSimplex ℝ S)
    (hs : IsSaddlePointOn (stdSimplex ℝ I) (stdSimplex ℝ S)
      (fun w q => payoff A w q) w q) :
    payoff A (w : I → ℝ) (q : S → ℝ) ≤ value A := by
  have hrow : ∀ i, payoff A (w : I → ℝ) (q : S → ℝ) ≤ coverage A q i :=
    fun i => saddle_payoff_le_row A w q hs i
  have hworst : payoff A (w : I → ℝ) (q : S → ℝ) ≤ worst A q := by
    unfold worst
    apply Finset.le_inf' Finset.univ_nonempty
    intro i hi
    exact hrow i
  exact hworst.trans (worst_le_value A q)

private lemma dualWorst_le_value_of_saddle
    (A : I → S → ℝ) (w : stdSimplex ℝ I) (q : stdSimplex ℝ S)
    (hs : IsSaddlePointOn (stdSimplex ℝ I) (stdSimplex ℝ S)
      (fun w q => payoff A w q) w q) :
    dualWorst A w ≤ value A := by
  unfold dualWorst
  apply Finset.sup'_le
  intro s hmem
  exact (saddle_column_le_payoff A w q hs s).trans (saddle_payoff_le_value A w q hs)

private lemma value_le_dualWorst (A : I → S → ℝ) (w : stdSimplex ℝ I) :
    value A ≤ dualWorst A w := by
  apply value_le_of_column_certificate A w (dualWorst A w)
  intro s
  unfold dualWorst
  exact Finset.le_sup'
    (fun s => ∑ i, (w : I → ℝ) i * A i s) (Finset.mem_univ s)

private lemma value_le_worst_of_saddle
    (A : I → S → ℝ) (w : stdSimplex ℝ I) (q : stdSimplex ℝ S)
    (hs : IsSaddlePointOn (stdSimplex ℝ I) (stdSimplex ℝ S)
      (fun w q => payoff A w q) w q) :
    value A ≤ worst A q := by
  have hq (q' : stdSimplex ℝ S) : worst A q' ≤
      payoff A (w : I → ℝ) (q' : S → ℝ) := by
    exact (worst_le_weighted A q' w).trans_eq
      (payoff_eq_weighted_coverage A w q').symm
  have hmax : ∀ q' : stdSimplex ℝ S, payoff A (w : I → ℝ) (q' : S → ℝ) ≤
      payoff A (w : I → ℝ) (q : S → ℝ) := by
    intro q'
    exact hs (w : I → ℝ) w.2 (q' : S → ℝ) q'.2
  have hsup : value A ≤ payoff A (w : I → ℝ) (q : S → ℝ) := by
    apply csSup_le (Set.range_nonempty (worst A))
    rintro z ⟨q', rfl⟩
    exact (hq q').trans (hmax q')
  exact hsup.trans ((by
    unfold worst
    apply Finset.le_inf' Finset.univ_nonempty
    intro i hi
    exact saddle_payoff_le_row A w q hs i) )

theorem exists_dual_optimal (A : I → S → ℝ) :
    ∃ w : stdSimplex ℝ I,
      ∀ s, ∑ i, (w : I → ℝ) i * A i s ≤ value A := by
  obtain ⟨w, q, hs⟩ := exists_saddle A
  exact ⟨w, fun s =>
    (by
      have h := saddle_column_le_payoff A w q hs s
      exact h.trans (saddle_payoff_le_value A w q hs))⟩

theorem exists_dual_optimal_exact (A : I → S → ℝ) :
    ∃ w : stdSimplex ℝ I,
      dualWorst A w = value A ∧
      ∀ s, ∑ i, (w : I → ℝ) i * A i s ≤ value A := by
  obtain ⟨w, q, hs⟩ := exists_saddle A
  have hupper : dualWorst A w ≤ value A :=
    dualWorst_le_value_of_saddle A w q hs
  have hlower : value A ≤ dualWorst A w := value_le_dualWorst A w
  refine ⟨w, le_antisymm hupper hlower, ?_⟩
  intro s
  exact (saddle_column_le_payoff A w q hs s).trans (saddle_payoff_le_value A w q hs)

theorem exists_strongly_optimal (A : I → S → ℝ) :
    ∃ q : stdSimplex ℝ S, ∃ w : stdSimplex ℝ I,
      (∀ i, value A ≤ coverage A q i) ∧
      (∀ s, ∑ i, (w : I → ℝ) i * A i s ≤ value A) ∧
      worst A q = value A := by
  obtain ⟨w, q, hs⟩ := exists_saddle A
  have hq_lower : value A ≤ worst A q := value_le_worst_of_saddle A w q hs
  have hq_upper : worst A q ≤ value A := worst_le_value A q
  have hq_eq : worst A q = value A := le_antisymm hq_upper hq_lower
  refine ⟨q, w, ?_, ?_, hq_eq⟩
  · intro i
    exact optimal_coverage_ge_value A q hq_eq i
  · intro s
    exact (saddle_column_le_payoff A w q hs s).trans (saddle_payoff_le_value A w q hs)

theorem dual_value_isLeast (A : I → S → ℝ) :
    IsLeast (dualFeasible A) (value A) := by
  obtain ⟨w, hw⟩ := exists_dual_optimal A
  refine ⟨⟨w, hw⟩, ?_⟩
  rintro u ⟨w', hw'⟩
  exact value_le_of_column_certificate A w' u hw'

theorem strong_duality (A : I → S → ℝ) :
    value A = dualValue A := by
  obtain ⟨w, q, hs⟩ := exists_saddle A
  have hlow : BddBelow (Set.range (dualWorst A)) := by
    refine ⟨value A, ?_⟩
    rintro z ⟨w', rfl⟩
    exact value_le_dualWorst A w'
  have hne : (Set.range (dualWorst A)).Nonempty := Set.range_nonempty _
  apply le_antisymm
  · exact (Real.isGLB_sInf hne hlow).2 (by
      intro z hz
      rcases hz with ⟨w', rfl⟩
      exact value_le_dualWorst A w')
  · exact (csInf_le hlow ⟨w, rfl⟩).trans
      (dualWorst_le_value_of_saddle A w q hs)

theorem dual_optimum_eq_value (A : I → S → ℝ) :
    dualValue A = value A := (strong_duality A).symm

end TrafficShaping
