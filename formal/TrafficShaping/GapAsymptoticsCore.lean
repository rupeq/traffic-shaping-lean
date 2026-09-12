import Mathlib

/-! Analytic implications of a nonnegative gap bounded by `m² / B`. -/

namespace TrafficShaping

open Filter Asymptotics
open scoped Topology

theorem square_div_budget_le_inverse_horizon {m B H : ℕ} {c : ℝ}
    (hc : 0 < c) (hH : 0 < H) (hB : c * (H : ℝ) ≤ (B : ℝ)) :
    (m : ℝ) ^ 2 / B ≤ ((m : ℝ) ^ 2 / c) / H := by
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    (m : ℝ) ^ 2 / B ≤ (m : ℝ) ^ 2 / (c * H) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hc hH') hB
    _ = ((m : ℝ) ^ 2 / c) / H := by ring

/-- The constant is independent of any delay sequence hidden in `g`. -/
theorem gap_isBigO_inverse_of_budget_bound (m : ℕ) (B : ℕ → ℕ) (g : ℕ → ℝ)
    (hgap : ∀ᶠ (H : ℕ) in atTop, 0 ≤ g H ∧ g H ≤ (m : ℝ) ^ 2 / B H)
    (c : ℝ) (hc : 0 < c)
    (hB : ∀ᶠ (H : ℕ) in atTop, c * (H : ℝ) ≤ (B H : ℝ)) :
    g =O[atTop] (fun H : ℕ => (H : ℝ)⁻¹) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨(m : ℝ) ^ 2 / c, ?_⟩
  filter_upwards [hgap, hB, eventually_ge_atTop 1] with H hg hBH hH
  have hHpos : 0 < H := by omega
  have hHi : (0 : ℝ) ≤ (H : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg H)
  rw [Real.norm_eq_abs, abs_of_nonneg hg.1, Real.norm_eq_abs, abs_of_nonneg hHi]
  calc
    g H ≤ (m : ℝ) ^ 2 / B H := hg.2
    _ ≤ ((m : ℝ) ^ 2 / c) / H :=
      square_div_budget_le_inverse_horizon hc hHpos hBH
    _ = ((m : ℝ) ^ 2 / c) * (H : ℝ)⁻¹ := div_eq_mul_inv _ _

theorem gap_tendsto_zero_of_ratio_bound {α : Type*} {l : Filter α}
    (g ratio : α → ℝ) (hgap : ∀ᶠ i in l, 0 ≤ g i ∧ g i ≤ ratio i)
    (hratio : Tendsto ratio l (𝓝 0)) : Tendsto g l (𝓝 0) := by
  exact squeeze_zero' (hgap.mono fun _ h => h.1) (hgap.mono fun _ h => h.2) hratio

end TrafficShaping
