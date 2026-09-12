import TrafficShaping.Corollary1

/-!
Monotonicity turns certificates at adjacent budgets into certificates of the
minimum budget.  Thus a table threshold is a statement about all smaller
budgets, even when only its last failing budget needs a numerical witness.
-/

namespace TrafficShaping

theorem causalOptimum_antitone_budget {H m B₁ B₂ D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb₁ : m ≤ B₁)
    (hB₁₂ : B₁ ≤ B₂) (hB₂ : B₂ ≤ H) (ε : ℝ) (hε : 0 ≤ ε) :
    causalOptimum H m B₂ D ε ≤ causalOptimum H m B₁ D ε := by
  rw [causal_optimum_eq hm1 hm (hmb₁.trans hB₁₂) hB₂ ε hε,
    causal_optimum_eq hm1 hm hmb₁ (hB₁₂.trans hB₂) ε hε]
  exact sub_le_sub_left (onGameValue_mono_budget hm hmb₁ hB₁₂ hB₂) 1

theorem noncausalOptimum_antitone_budget {H m B₁ B₂ D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb₁ : m ≤ B₁)
    (hB₁₂ : B₁ ≤ B₂) (hB₂ : B₂ ≤ H) (ε : ℝ) (hε : 0 ≤ ε) :
    noncausalOptimum H m B₂ D ε ≤ noncausalOptimum H m B₁ D ε := by
  rw [noncausal_optimum_eq hm1 hm (hmb₁.trans hB₁₂) hB₂ ε hε,
    noncausal_optimum_eq hm1 hm hmb₁ (hB₁₂.trans hB₂) ε hε]
  exact sub_le_sub_left (offGameValue_mono_budget hm hmb₁ hB₁₂ hB₂) 1

theorem causalBudget_eq_of_adjacent_certificates {H m B D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hfit : 1 - onGameValue H m B D hm hmb hB ≤ δ)
    (hfail : B = m ∨ ∃ hprev : m ≤ B - 1,
      δ < 1 - onGameValue H m (B - 1) D hm hprev (by omega)) :
    causalBudget H m D δ hm1 hm hδ0 hδ1 = B := by
  have hupper := causalBudget_minimal (D := D) δ hm1 hm hmb hB hδ0 hδ1 hfit
  have hbounds := causalBudget_bounds (D := D) δ hm1 hm hδ0 hδ1
  apply Nat.le_antisymm hupper
  by_contra hnot
  have hsmall : causalBudget H m D δ hm1 hm hδ0 hδ1 ≤ B - 1 := by omega
  rcases hfail with heq | ⟨hprev, hfail⟩
  · omega
  · have hmono := onGameValue_mono_budget (D := D) hm hbounds.1 hsmall
      (show B - 1 ≤ H by omega)
    have hthreshold := causalBudget_threshold (D := D) δ hm1 hm hδ0 hδ1
    linarith

theorem noncausalBudget_eq_of_adjacent_certificates {H m B D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hfit : 1 - offGameValue H m B D hm hB ≤ δ)
    (hfail : B = m ∨
      δ < 1 - offGameValue H m (B - 1) D hm (by omega)) :
    noncausalBudget H m D δ hm1 hm hδ0 hδ1 = B := by
  have hupper := noncausalBudget_minimal (D := D) δ hm1 hm hmb hB hδ0 hδ1 hfit
  have hbounds := noncausalBudget_bounds (D := D) δ hm1 hm hδ0 hδ1
  apply Nat.le_antisymm hupper
  by_contra hnot
  have hsmall : noncausalBudget H m D δ hm1 hm hδ0 hδ1 ≤ B - 1 := by omega
  rcases hfail with heq | hfail
  · omega
  · have hmono := offGameValue_mono_budget (D := D) hm hbounds.1 hsmall
      (show B - 1 ≤ H by omega)
    have hthreshold := noncausalBudget_threshold (D := D) δ hm1 hm hδ0 hδ1
    linarith

/-- The last budget below a reserve has the least loss among all sub-reserve
budgets.  Instantiating its exact value proves the table's minimum column. -/
theorem causal_subreserve_loss_isLeast {H m R D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hmR : m < R) (hR : R ≤ H)
    (ε : ℝ) (hε : 0 ≤ ε) :
    IsLeast {δ : ℝ | ∃ B : ℕ, m ≤ B ∧ B < R ∧
        δ = causalOptimum H m B D ε}
      (causalOptimum H m (R - 1) D ε) := by
  constructor
  · exact ⟨R - 1, by omega, by omega, rfl⟩
  · rintro δ ⟨B, hBm, hBR, rfl⟩
    exact causalOptimum_antitone_budget hm1 hm hBm (by omega) (by omega) ε hε

end TrafficShaping
