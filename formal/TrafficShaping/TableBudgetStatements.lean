import TrafficShaping.TableCertificates
import TrafficShaping.ArticleTableBounds

/-! Exact statements for every numerical row of Tables 2 and 3. The values
come from kernel-checked matching certificates; minimum-budget and minimum-loss
claims additionally use the universal monotonicity and no-savings proofs. -/

namespace TrafficShaping

theorem table2_row_1 :
    ArticleTable2Row 8 1 6 5 (1/2 : ℝ) (by decide) := by
  refine article_table2_row_of_values (H := 8) (D := 1)
    (R := 6) (C := 5) (1/2 : ℝ)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by norm_num) ?_ ?_ ?_
  · rw [certificate_value_on_H8_m2_B5_D1]
    norm_num
  · rw [certificate_value_on_H8_m2_B5_D1]
    norm_num
  · right
    refine ⟨by decide, ?_⟩
    rw [certificate_value_on_H8_m2_B4_D1]
    norm_num

theorem table2_row_2 :
    ArticleTable2Row 8 2 4 4 (1 : ℝ) (by decide) := by
  refine article_table2_row_of_values (H := 8) (D := 2)
    (R := 4) (C := 4) (1 : ℝ)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by norm_num) ?_ ?_ ?_
  · rw [certificate_value_on_H8_m2_B3_D2]
    norm_num
  · rw [certificate_value_on_H8_m2_B4_D2]
    norm_num
  · right
    refine ⟨by decide, ?_⟩
    rw [certificate_value_on_H8_m2_B3_D2]
    norm_num

theorem table2_row_3 :
    ArticleTable2Row 8 3 4 4 (1 : ℝ) (by decide) := by
  refine article_table2_row_of_values (H := 8) (D := 3)
    (R := 4) (C := 4) (1 : ℝ)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by norm_num) ?_ ?_ ?_
  · rw [certificate_value_on_H8_m2_B3_D3]
    norm_num
  · rw [certificate_value_on_H8_m2_B4_D3]
    norm_num
  · right
    refine ⟨by decide, ?_⟩
    rw [certificate_value_on_H8_m2_B3_D3]
    norm_num

theorem table2_row_4 :
    ArticleTable2Row 12 1 8 7 (1/3 : ℝ) (by decide) := by
  refine article_table2_row_of_values (H := 12) (D := 1)
    (R := 8) (C := 7) (1/3 : ℝ)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by norm_num) ?_ ?_ ?_
  · rw [certificate_value_on_H12_m2_B7_D1]
    norm_num
  · rw [certificate_value_on_H12_m2_B7_D1]
    norm_num
  · right
    refine ⟨by decide, ?_⟩
    rw [certificate_value_on_H12_m2_B6_D1]
    norm_num

theorem table2_row_5 :
    ArticleTable2Row 12 2 6 5 (1/2 : ℝ) (by decide) := by
  refine article_table2_row_of_values (H := 12) (D := 2)
    (R := 6) (C := 5) (1/2 : ℝ)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by norm_num) ?_ ?_ ?_
  · rw [certificate_value_on_H12_m2_B5_D2]
    norm_num
  · rw [certificate_value_on_H12_m2_B5_D2]
    norm_num
  · right
    refine ⟨by decide, ?_⟩
    rw [certificate_value_on_H12_m2_B4_D2]
    norm_num

theorem table2_row_6 :
    ArticleTable2Row 12 3 6 5 (1/2 : ℝ) (by decide) := by
  refine article_table2_row_of_values (H := 12) (D := 3)
    (R := 6) (C := 5) (1/2 : ℝ)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by norm_num) ?_ ?_ ?_
  · rw [certificate_value_on_H12_m2_B5_D3]
    norm_num
  · rw [certificate_value_on_H12_m2_B5_D3]
    norm_num
  · right
    refine ⟨by decide, ?_⟩
    rw [certificate_value_on_H12_m2_B4_D3]
    norm_num

theorem table2_row_7 :
    ArticleTable2Row 16 1 11 8 (2/9 : ℝ) (by decide) := by
  refine article_table2_row_of_values (H := 16) (D := 1)
    (R := 11) (C := 8) (2/9 : ℝ)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by norm_num) ?_ ?_ ?_
  · rw [certificate_value_on_H16_m2_B10_D1]
    norm_num
  · rw [certificate_value_on_H16_m2_B8_D1]
    norm_num
  · right
    refine ⟨by decide, ?_⟩
    rw [certificate_value_on_H16_m2_B7_D1]
    norm_num

theorem table2_row_8 :
    ArticleTable2Row 16 2 8 7 (1/3 : ℝ) (by decide) := by
  refine article_table2_row_of_values (H := 16) (D := 2)
    (R := 8) (C := 7) (1/3 : ℝ)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by norm_num) ?_ ?_ ?_
  · rw [certificate_value_on_H16_m2_B7_D2]
    norm_num
  · rw [certificate_value_on_H16_m2_B7_D2]
    norm_num
  · right
    refine ⟨by decide, ?_⟩
    rw [certificate_value_on_H16_m2_B6_D2]
    norm_num

theorem table2_row_9 :
    ArticleTable2Row 16 3 7 6 (2/5 : ℝ) (by decide) := by
  refine article_table2_row_of_values (H := 16) (D := 3)
    (R := 7) (C := 6) (2/5 : ℝ)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by norm_num) ?_ ?_ ?_
  · rw [certificate_value_on_H16_m2_B6_D3]
    norm_num
  · rw [certificate_value_on_H16_m2_B6_D3]
    norm_num
  · right
    refine ⟨by decide, ?_⟩
    rw [certificate_value_on_H16_m2_B5_D3]
    norm_num

theorem table3_row_1 (ε : ℝ) (hε : 0 ≤ ε) :
    perfectBudget 8 3 1 = 6 ∧
      noncausalOptimum 8 3 5 1 ε = (1/2 : ℝ) ∧
      causalOptimum 8 3 5 1 ε = (1 : ℝ) := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [noncausal_optimum_eq (by decide) (by decide) (by decide)
      (by decide) ε hε, certificate_value_off_H8_m3_B5_D1]
    norm_num
  · rw [causal_optimum_eq (by decide) (by decide) (by decide)
      (by decide) ε hε, certificate_value_on_H8_m3_B5_D1]
    norm_num

theorem table3_row_2 (ε : ℝ) (hε : 0 ≤ ε) :
    perfectBudget 8 3 2 = 6 ∧
      noncausalOptimum 8 3 4 2 ε = (1/2 : ℝ) ∧
      causalOptimum 8 3 4 2 ε = (1 : ℝ) := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [noncausal_optimum_eq (by decide) (by decide) (by decide)
      (by decide) ε hε, certificate_value_off_H8_m3_B4_D2]
    norm_num
  · rw [causal_optimum_eq (by decide) (by decide) (by decide)
      (by decide) ε hε, certificate_value_on_H8_m3_B4_D2]
    norm_num

theorem table3_row_3 (ε : ℝ) (hε : 0 ≤ ε) :
    perfectBudget 10 4 1 = 8 ∧
      noncausalOptimum 10 4 7 1 ε = (1/2 : ℝ) ∧
      causalOptimum 10 4 7 1 ε = (1 : ℝ) := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [noncausal_optimum_eq (by decide) (by decide) (by decide)
      (by decide) ε hε, certificate_value_off_H10_m4_B7_D1]
    norm_num
  · rw [causal_optimum_eq (by decide) (by decide) (by decide)
      (by decide) ε hε, certificate_value_on_H10_m4_B7_D1]
    norm_num

theorem table3_row_4 (ε : ℝ) (hε : 0 ≤ ε) :
    perfectBudget 10 4 2 = 8 ∧
      noncausalOptimum 10 4 7 2 ε = (1/2 : ℝ) ∧
      causalOptimum 10 4 7 2 ε = (1 : ℝ) := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [noncausal_optimum_eq (by decide) (by decide) (by decide)
      (by decide) ε hε, certificate_value_off_H10_m4_B7_D2]
    norm_num
  · rw [causal_optimum_eq (by decide) (by decide) (by decide)
      (by decide) ε hε, certificate_value_on_H10_m4_B7_D2]
    norm_num

theorem table3_row_5 (ε : ℝ) (hε : 0 ≤ ε) :
    perfectBudget 10 3 1 = 8 ∧
      noncausalOptimum 10 3 7 1 ε = (1/3 : ℝ) ∧
      causalOptimum 10 3 7 1 ε = (1/2 : ℝ) := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [noncausal_optimum_eq (by decide) (by decide) (by decide)
      (by decide) ε hε, certificate_value_off_H10_m3_B7_D1]
    norm_num
  · rw [causal_optimum_eq (by decide) (by decide) (by decide)
      (by decide) ε hε, certificate_value_on_H10_m3_B7_D1]
    norm_num

theorem table3_row_6 (ε : ℝ) (hε : 0 ≤ ε) :
    perfectBudget 12 3 2 = 8 ∧
      noncausalOptimum 12 3 7 2 ε = (1/3 : ℝ) ∧
      causalOptimum 12 3 7 2 ε = (1/2 : ℝ) := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [noncausal_optimum_eq (by decide) (by decide) (by decide)
      (by decide) ε hε, certificate_value_off_H12_m3_B7_D2]
    norm_num
  · rw [causal_optimum_eq (by decide) (by decide) (by decide)
      (by decide) ε hε, certificate_value_on_H12_m3_B7_D2]
    norm_num

theorem table3_row_7 (ε : ℝ) (hε : 0 ≤ ε) :
    perfectBudget 12 4 1 = 10 ∧
      noncausalOptimum 12 4 9 1 ε = (2/5 : ℝ) ∧
      causalOptimum 12 4 9 1 ε = (2/3 : ℝ) := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [noncausal_optimum_eq (by decide) (by decide) (by decide)
      (by decide) ε hε, certificate_value_off_H12_m4_B9_D1]
    norm_num
  · rw [causal_optimum_eq (by decide) (by decide) (by decide)
      (by decide) ε hε, certificate_value_on_H12_m4_B9_D1]
    norm_num

theorem table3_row_8 (ε : ℝ) (hε : 0 ≤ ε) :
    perfectBudget 14 4 2 = 10 ∧
      noncausalOptimum 14 4 9 2 ε = (2/5 : ℝ) ∧
      causalOptimum 14 4 9 2 ε = (2/3 : ℝ) := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [noncausal_optimum_eq (by decide) (by decide) (by decide)
      (by decide) ε hε, certificate_value_off_H14_m4_B9_D2]
    norm_num
  · rw [causal_optimum_eq (by decide) (by decide) (by decide)
      (by decide) ε hε, certificate_value_on_H14_m4_B9_D2]
    norm_num

theorem qualitative_causality_gap (ε : ℝ) (hε : 0 ≤ ε) :
    noncausalOptimum 8 2 3 2 ε = (1 / 2 : ℝ) ∧
      causalOptimum 8 2 3 2 ε = 1 := by
  constructor
  · rw [noncausal_optimum_eq (by decide) (by decide) (by decide)
      (by decide) ε hε, certificate_value_off_H8_m2_B3_D2]
    norm_num
  · rw [causal_optimum_eq (by decide) (by decide) (by decide)
      (by decide) ε hε, certificate_value_on_H8_m2_B3_D2]
    norm_num

theorem qualitative_causal_loss_lower (M : Mechanism 8 2 3 2)
    (ε δ : ℝ) (hprivacy : Private M ε δ) (hcausal : Causal M) :
    1 ≤ δ := by
  have h := causal_converse_bound (by decide) (by decide) (by decide)
    (by decide) M ε δ hprivacy hcausal
  change 1 - onGameValue 8 2 3 2 (by decide) (by decide) (by decide) ≤ δ at h
  rw [certificate_value_on_H8_m2_B3_D2] at h
  simpa using h

/-- The H=16 table row has an attaining causal mechanism with the stated
equal-prior testing guarantee, including all randomized tests. -/
theorem table2_H16_half_attainable_accuracy :
    ∃ M : Mechanism 16 2 8 1, Causal M ∧ Private M 0 (1 / 2) ∧
      ∀ (x : Input 16 2), x.1 ≠ ∅ →
        ∀ (d : Trace 16 → ℝ), (∀ y, d y ∈ Set.Icc (0 : ℝ) 1) →
          Law.testSuccess (M.law x) (M.law (emptyInput 16 2)) d ≤ 3 / 4 := by
  have hB : causalBudget 16 2 1 (1 / 2) (by norm_num) (by decide)
      (by norm_num) (by norm_num) = 8 := table2_row_7.2.2.2.2.1
  have hex := causalBudget_attainable (H := 16) (m := 2) (D := 1)
    (1 / 2) (by norm_num) (by decide) (by norm_num) (by norm_num)
    0 (by norm_num)
  rw [hB] at hex
  obtain ⟨M, hcausal, hprivate⟩ := hex
  refine ⟨M, hcausal, hprivate, ?_⟩
  intro x hx d hd
  exact table2_H16_half_privacy_accuracy hprivate x hx d hd

end TrafficShaping
