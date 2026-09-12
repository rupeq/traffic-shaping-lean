import TrafficShaping.PrivacyGap
import TrafficShaping.GapAsymptoticsCore

/-!
The asymptotic statements concern the actual minimum privacy losses of the
two mechanism classes.  The uniform bound quantifies over every delay and
every nonnegative finite epsilon, with a constant independent of both.
-/

namespace TrafficShaping

open Filter Asymptotics
open scoped Topology

theorem eventually_twice_workload_le_budget (m : ℕ) (B : ℕ → ℕ)
    (c : ℝ) (hc : 0 < c)
    (hB : ∀ᶠ (H : ℕ) in atTop, c * (H : ℝ) ≤ (B H : ℝ)) :
    ∀ᶠ (H : ℕ) in atTop, 2 * m ≤ B H := by
  filter_upwards [hB, eventually_ge_atTop (Nat.ceil ((2 * (m : ℝ)) / c))]
    with H hBH hH
  have hceil : (2 * (m : ℝ)) / c ≤ (H : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast hH)
  have hlarge : 2 * (m : ℝ) ≤ c * H := by
    simpa [mul_comm] using (div_le_iff₀ hc).mp hceil
  exact_mod_cast hlarge.trans hBH

theorem privacy_gap_uniform_inverse_bound (m : ℕ) (hm1 : 1 ≤ m)
    (B : ℕ → ℕ) (c : ℝ) (hc : 0 < c)
    (hB : ∀ᶠ (H : ℕ) in atTop, c * (H : ℝ) ≤ (B H : ℝ) ∧ B H ≤ H) :
    ∀ᶠ (H : ℕ) in atTop, ∀ (D : ℕ) (ε : ℝ), 0 ≤ ε →
      0 ≤ causalOptimum H m (B H) D ε - noncausalOptimum H m (B H) D ε ∧
      causalOptimum H m (B H) D ε - noncausalOptimum H m (B H) D ε ≤
        ((m : ℝ) ^ 2 / c) / H := by
  have hlarge := eventually_twice_workload_le_budget m B c hc
    (hB.mono fun _ h => h.1)
  filter_upwards [hB, hlarge, eventually_ge_atTop 1] with H hBH h2 hH
  intro D ε hε
  have hgap := privacy_gap_bounds (D := D) hm1 h2 hBH.2 ε hε
  exact ⟨hgap.1, (hgap.2.1.trans hgap.2.2).trans
    (square_div_budget_le_inverse_horizon hc (by omega) hBH.1)⟩

theorem privacy_gap_isBigO_inverse (m : ℕ) (hm1 : 1 ≤ m)
    (B D : ℕ → ℕ) (ε : ℕ → ℝ)
    (hε : ∀ᶠ (H : ℕ) in atTop, 0 ≤ ε H)
    (c : ℝ) (hc : 0 < c)
    (hB : ∀ᶠ (H : ℕ) in atTop, c * (H : ℝ) ≤ (B H : ℝ) ∧ B H ≤ H) :
    (fun H => causalOptimum H m (B H) (D H) (ε H) -
      noncausalOptimum H m (B H) (D H) (ε H)) =O[atTop]
        (fun H : ℕ => (H : ℝ)⁻¹) := by
  apply gap_isBigO_inverse_of_budget_bound m B _ ?_ c hc
    (hB.mono fun _ h => h.1)
  have hlarge := eventually_twice_workload_le_budget m B c hc
    (hB.mono fun _ h => h.1)
  filter_upwards [hB, hlarge, hε] with H hBH h2 hεH
  have hgap := privacy_gap_bounds (D := D H) hm1 h2 hBH.2 (ε H) hεH
  exact ⟨hgap.1, hgap.2.1.trans hgap.2.2⟩

/-- Workload, budget, horizon, delay and epsilon may all vary in this limit. -/
theorem privacy_gap_tendsto_zero {α : Type*} {l : Filter α}
    (H m B D : α → ℕ) (ε : α → ℝ)
    (hdomain : ∀ᶠ i in l,
      1 ≤ m i ∧ 2 * m i ≤ B i ∧ B i ≤ H i ∧ 0 ≤ ε i)
    (hratio : Tendsto (fun i => (m i : ℝ) ^ 2 / B i) l (𝓝 0)) :
    Tendsto (fun i => causalOptimum (H i) (m i) (B i) (D i) (ε i) -
      noncausalOptimum (H i) (m i) (B i) (D i) (ε i)) l (𝓝 0) := by
  apply gap_tendsto_zero_of_ratio_bound _ _ ?_ hratio
  filter_upwards [hdomain] with i hi
  have hgap := privacy_gap_bounds (D := D i) hi.1 hi.2.1 hi.2.2.1
    (ε i) hi.2.2.2
  exact ⟨hgap.1, hgap.2.1.trans hgap.2.2⟩

end TrafficShaping
