import TrafficShaping.Corollary3
import TrafficShaping.BudgetCertificates
import TrafficShaping.PrivacyInterpretation

/-!
The table statements concern minimum budgets and minima over every budget
below the perfect-privacy reserve.  These bridges derive those conclusions
from exact game values, monotonicity, and the analytic no-savings theorem.
-/

namespace TrafficShaping

theorem small_threshold_budgets_of_six_tests {H m D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H)
    (hK : testBlockCount H m D ≤ 6) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 10) :
    noncausalBudget H m D δ hm1 hm hδ0 (by linarith) = perfectBudget H m D ∧
      causalBudget H m D δ hm1 hm hδ0 (by linarith) = perfectBudget H m D := by
  apply corollary5_eq25_unconditional hm1 hm δ hδ0 (by linarith)
  have hKr : (0 : ℝ) < testBlockCount H m D := by
    exact_mod_cast testBlockCount_pos (D := D) hm1 hm
  have hK6 : (testBlockCount H m D : ℝ) ≤ 6 := by exact_mod_cast hK
  apply (lt_div_iff₀ hKr).2
  nlinarith

/-- Every numerical column of one Table 2 row, with the minimum interpreted
over all admissible budgets below the exact perfect-privacy budget. -/
def ArticleTable2Row (H D R C : ℕ) (μ : ℝ) (hm : 2 ≤ H) : Prop :=
  perfectBudget H 2 D = R ∧
    testBlockCount H 2 D ≤ 6 ∧
    noncausalBudget H 2 D (1 / 10) (by norm_num) hm
        (by norm_num) (by norm_num) = R ∧
    causalBudget H 2 D (1 / 10) (by norm_num) hm
        (by norm_num) (by norm_num) = R ∧
    causalBudget H 2 D (1 / 2) (by norm_num) hm
        (by norm_num) (by norm_num) = C ∧
    0 < μ ∧
    ∀ ε : ℝ, 0 ≤ ε →
      IsLeast {δ : ℝ | ∃ B : ℕ, 2 ≤ B ∧ B < R ∧
        δ = causalOptimum H 2 B D ε} μ

theorem article_table2_row_of_values {H D R C : ℕ} (μ : ℝ)
    (hm : 2 ≤ H) (hmR : 2 < R) (hRH : R ≤ H)
    (hmC : 2 ≤ C) (hCH : C ≤ H)
    (hreserve : perfectBudget H 2 D = R)
    (hK : testBlockCount H 2 D ≤ 6) (hμ : 0 < μ)
    (hlast : onGameValue H 2 (R - 1) D hm (by omega) (by omega) = 1 - μ)
    (hfit : 1 - onGameValue H 2 C D hm hmC hCH ≤ 1 / 2)
    (hfail : C = 2 ∨ ∃ hprev : 2 ≤ C - 1,
      (1 : ℝ) / 2 < 1 - onGameValue H 2 (C - 1) D hm hprev (by omega)) :
    ArticleTable2Row H D R C μ hm := by
  have hsmall := small_threshold_budgets_of_six_tests
    (D := D) (by norm_num : 1 ≤ 2) hm hK (1 / 10) (by norm_num) le_rfl
  rw [hreserve] at hsmall
  refine ⟨hreserve, hK, hsmall.1, hsmall.2, ?_, hμ, ?_⟩
  · exact causalBudget_eq_of_adjacent_certificates
      (D := D) (by norm_num) hm hmC hCH (1 / 2)
      (by norm_num) (by norm_num) hfit hfail
  · intro ε hε
    have hleast := causal_subreserve_loss_isLeast
      (D := D) (by norm_num : 1 ≤ 2) hm hmR hRH ε hε
    have heq : causalOptimum H 2 (R - 1) D ε = μ := by
      rw [causal_optimum_eq (by norm_num) hm (by omega) (by omega) ε hε,
        hlast]
      ring
    rwa [heq] at hleast

theorem table2_H16_half_privacy_accuracy {M : Mechanism 16 2 8 1}
    (hprivacy : Private M 0 (1 / 2)) (x : Input 16 2) (hx : x.1 ≠ ∅)
    (d : Trace 16 → ℝ) (hd : ∀ y, d y ∈ Set.Icc (0 : ℝ) 1) :
    Law.testSuccess (M.law x) (M.law (emptyInput 16 2)) d ≤ 3 / 4 := by
  have h := participation_accuracy_bound hprivacy x hx d hd
  norm_num at h ⊢
  exact h

end TrafficShaping
