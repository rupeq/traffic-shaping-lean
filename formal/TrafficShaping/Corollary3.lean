import TrafficShaping.Corollary5
import TrafficShaping.BlockArithmetic

/-!
The exact perfect-privacy budget combines the explicit universal schedule
with the disjoint block tests.  The no-savings proof uses those ingredients
directly, so specializing its strict interval to zero is non-circular.
-/

namespace TrafficShaping

theorem corollary3_perfect_privacy_budgets {H m D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) :
    noncausalBudget H m D 0 hm1 hm (by norm_num) (by norm_num) =
        perfectBudget H m D ∧
      causalBudget H m D 0 hm1 hm (by norm_num) (by norm_num) =
        perfectBudget H m D := by
  apply corollary5_eq25_unconditional hm1 hm 0 (by norm_num) (by norm_num)
  have hK : (0 : ℝ) < testBlockCount H m D := by
    exact_mod_cast testBlockCount_pos (D := D) hm1 hm
  exact one_div_pos.mpr hK

theorem corollary3_eq20 {H m D a b : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H)
    (hH : H = a * (D + m) + b) (hb : b < D + m) :
    noncausalBudget H m D 0 hm1 hm (by norm_num) (by norm_num) =
        m * a + min m b ∧
      causalBudget H m D 0 hm1 hm (by norm_num) (by norm_num) =
        m * a + min m b := by
  have h := corollary3_perfect_privacy_budgets (D := D) hm1 hm
  rw [perfectBudget_eq_quotient_remainder hH hb] at h
  exact h

/-- The lower bound concerns every semantic mechanism, at every finite
epsilon, and does not require a causal implementation. -/
theorem perfect_privacy_mechanism_budget_lower {H m B D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H)
    (M : Mechanism H m B D) (ε : ℝ) (hε : 0 ≤ ε)
    (hprivacy : Private M ε 0) : perfectBudget H m D ≤ B := by
  by_contra hnot
  have hlower := block_noSavings_delta_lower hm1 hm M ε 0
    (Nat.lt_of_not_ge hnot) hprivacy
  have hK : (0 : ℝ) < testBlockCount H m D := by
    exact_mod_cast testBlockCount_pos (D := D) hm1 hm
  have hpositive := one_div_pos.mpr hK
  linarith

theorem perfect_privacy_causal_attainable {H m D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ M : Mechanism H m (perfectBudget H m D) D,
      Causal M ∧ Private M ε 0 := by
  have h := causalBudget_attainable (D := D) 0 hm1 hm
    (by norm_num) (by norm_num) ε hε
  rw [(corollary3_perfect_privacy_budgets (D := D) hm1 hm).2] at h
  exact h

theorem perfect_privacy_both_attainable {H m D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) (ε : ℝ) (hε : 0 ≤ ε) :
    (∃ M : Mechanism H m (perfectBudget H m D) D, Private M ε 0) ∧
      ∃ M : Mechanism H m (perfectBudget H m D) D,
        Causal M ∧ Private M ε 0 := by
  obtain ⟨M, hcausal, hprivate⟩ := perfect_privacy_causal_attainable hm1 hm ε hε
  exact ⟨⟨M, hprivate⟩, ⟨M, hcausal, hprivate⟩⟩

end TrafficShaping
