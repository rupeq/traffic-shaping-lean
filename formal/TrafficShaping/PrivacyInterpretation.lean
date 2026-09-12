import TrafficShaping.Mechanism

/-!
# Operational meaning of the article's privacy guarantee

The decision rule may itself be randomized: `d a` is the probability of
guessing the first input after observing output `a`. The two hypotheses
have equal prior probabilities. These statements cover the unnumbered
consequences following equation (3).
-/

namespace TrafficShaping
namespace Law

variable {α : Type*} [Fintype α]

theorem tv_triangle (p q r : Law α) : p.tv r ≤ p.tv q + q.tv r := by
  classical
  rw [tv_eq_event_difference]
  have h₁ := p.event_difference_le_tv q (positiveEvent p r)
  have h₂ := q.event_difference_le_tv r (positiveEvent p r)
  linarith

/-- Success probability of a randomized binary test with equal priors. -/
noncomputable def testSuccess (p q : Law α) (d : α → ℝ) : ℝ :=
  (∑ a, (p.val a * d a + q.val a * (1 - d a))) / 2

theorem testSuccess_eq (p q : Law α) (d : α → ℝ) :
    testSuccess p q d = (1 + ∑ a, (p.val a - q.val a) * d a) / 2 := by
  unfold testSuccess
  have h : (∑ a, (p.val a * d a + q.val a * (1 - d a))) =
      (∑ a, q.val a) + ∑ a, (p.val a - q.val a) * d a := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [h, q.total]

theorem testSuccess_le (p q : Law α) (d : α → ℝ)
    (hd : ∀ a, d a ∈ Set.Icc (0 : ℝ) 1) :
    testSuccess p q d ≤ (1 + p.tv q) / 2 := by
  classical
  have h : (∑ a, (p.val a - q.val a) * d a) ≤ p.tv q := by
    rw [tv_eq_sum_pos]
    apply Finset.sum_le_sum
    intro a _
    split_ifs with ha
    · nlinarith [(hd a).2]
    · have hdiff : p.val a - q.val a ≤ 0 := by linarith
      exact mul_nonpos_of_nonpos_of_nonneg hdiff (hd a).1
  rw [testSuccess_eq]
  linarith

/-- The deterministic likelihood comparison attains the upper bound. -/
noncomputable def positiveTest (p q : Law α) : α → ℝ := by
  classical
  exact fun a => if q.val a ≤ p.val a then 1 else 0

theorem positiveTest_mem (p q : Law α) (a : α) :
    positiveTest p q a ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  unfold positiveTest
  split_ifs <;> constructor <;> norm_num

theorem positiveTest_success (p q : Law α) :
    testSuccess p q (positiveTest p q) = (1 + p.tv q) / 2 := by
  classical
  rw [testSuccess_eq, tv_eq_sum_pos]
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  unfold positiveTest
  split_ifs <;> simp

/-- Exact best discrimination accuracy, including all randomized tests. -/
theorem optimal_equal_prior_accuracy (p q : Law α) :
    IsGreatest {s : ℝ | ∃ d : α → ℝ,
      (∀ a, d a ∈ Set.Icc (0 : ℝ) 1) ∧ s = testSuccess p q d}
      ((1 + p.tv q) / 2) := by
  constructor
  · exact ⟨positiveTest p q, positiveTest_mem p q, (positiveTest_success p q).symm⟩
  · rintro s ⟨d, hd, rfl⟩
    exact testSuccess_le p q d hd

theorem testSuccess_le_of_tv_le (p q : Law α) (d : α → ℝ)
    (hd : ∀ a, d a ∈ Set.Icc (0 : ℝ) 1) {δ : ℝ} (hδ : p.tv q ≤ δ) :
    testSuccess p q d ≤ (1 + δ) / 2 := by
  have h := testSuccess_le p q d hd
  linarith

end Law

/-- Two active inputs are compared through the common empty-input law. -/
theorem active_pair_tv_bound {H m B D : ℕ} {M : Mechanism H m B D} {δ : ℝ}
    (hM : Private M 0 δ) (x x' : Input H m) (hx : x.1 ≠ ∅) (hx' : x'.1 ≠ ∅) :
    (M.law x).tv (M.law x') ≤ min 1 (2 * δ) := by
  classical
  have h₁ := (Law.privatePair_zero_iff_tv _ _ δ).mp (hM x hx)
  have h₂ := (Law.privatePair_zero_iff_tv _ _ δ).mp (hM x' hx')
  apply le_min (Law.tv_le_one _ _)
  have h := Law.tv_triangle (M.law x) (M.law (emptyInput H m)) (M.law x')
  rw [Law.tv_symm (M.law (emptyInput H m)) (M.law x')] at h
  linarith

/-- The privacy bound applies to the best equal-prior observer in the model. -/
theorem participation_accuracy_bound {H m B D : ℕ} {M : Mechanism H m B D} {δ : ℝ}
    (hM : Private M 0 δ) (x : Input H m) (hx : x.1 ≠ ∅)
    (d : Trace H → ℝ) (hd : ∀ y, d y ∈ Set.Icc (0 : ℝ) 1) :
    Law.testSuccess (M.law x) (M.law (emptyInput H m)) d ≤ (1 + δ) / 2 := by
  exact Law.testSuccess_le_of_tv_le _ _ d hd
    ((Law.privatePair_zero_iff_tv _ _ δ).mp (hM x hx))

end TrafficShaping
