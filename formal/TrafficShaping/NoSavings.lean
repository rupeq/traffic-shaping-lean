import TrafficShaping.NoSavingsCore
import TrafficShaping.CorollaryDefinitions
import TrafficShaping.Budgets

/-!
# Corollary 5: the finite-test no-savings threshold

The block-test construction is intentionally supplied as a hypothesis here.
This keeps the privacy argument independent of the concrete arithmetic proof
and lets the latter be checked in a small, dedicated module.
-/

namespace TrafficShaping

open scoped BigOperators

/-! A support point that is feasible for every test must meet the block lower
bound.  The mechanism cap turns this into a missing test whenever `B` is
strictly below `perfectBudget`. -/
theorem noSavings_union_bound
    {H m B D : ℕ} {I : Type*} [Fintype I]
    (M : Mechanism H m B D) (tests : I → Input H m)
    (htest_nonempty : ∀ i, (tests i).1 ≠ ∅)
    (hall_lower : ∀ y : Trace H,
      (∀ i, Feasible D (tests i).1 y) → perfectBudget H m D ≤ y.card)
    (hB : B < perfectBudget H m D)
    (ε δ : ℝ) (hprivacy : Private M ε δ) :
    1 ≤ (Fintype.card I : ℝ) * δ := by
  apply finite_test_privacy_bound M tests ε δ hprivacy htest_nonempty
  intro y hy
  by_contra hnone
  push Not at hnone
  have hlow := hall_lower y hnone
  have hcap := M.cap (emptyInput H m) y hy
  omega

theorem noSavings_delta_lower
    {H m B D : ℕ} {I : Type*} [Fintype I]
    [Nonempty I]
    (M : Mechanism H m B D) (tests : I → Input H m)
    (htest_nonempty : ∀ i, (tests i).1 ≠ ∅)
    (hall_lower : ∀ y : Trace H,
      (∀ i, Feasible D (tests i).1 y) → perfectBudget H m D ≤ y.card)
    (hB : B < perfectBudget H m D)
    (ε δ : ℝ) (hprivacy : Private M ε δ) :
    (1 : ℝ) / Fintype.card I ≤ δ := by
  have hK : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos
  have hu := noSavings_union_bound M tests htest_nonempty hall_lower hB ε δ hprivacy
  apply (div_le_iff₀ hK).2
  nlinarith [hu]

/-!
Budget-level corollary.  The two value hypotheses are the zero-loss
achievability facts proved by the explicit perfect schedule.  The theorem
then uses the `Nat.find` budget definitions from `Budgets.lean`.
-/
theorem noncausalBudget_eq_perfectBudget_of_noSavings
    {H m D : ℕ} {I : Type*} [Fintype I] [Nonempty I]
    (hm1 : 1 ≤ m) (hm : m ≤ H)
    (tests : I → Input H m)
    (htest_nonempty : ∀ i, (tests i).1 ≠ ∅)
    (hall_lower : ∀ y : Trace H,
      (∀ i, Feasible D (tests i).1 y) → perfectBudget H m D ≤ y.card)
    (hB0H : perfectBudget H m D ≤ H)
    (hB0m : m ≤ perfectBudget H m D)
    (hvalue : offGameValue H m (perfectBudget H m D) D hm hB0H = 1)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδsmall : δ < 1 / (Fintype.card I : ℝ)) :
    noncausalBudget H m D δ hm1 hm hδ0 hδ1 = perfectBudget H m D := by
  let B0 := perfectBudget H m D
  have hupper : noncausalBudget H m D δ hm1 hm hδ0 hδ1 ≤ B0 := by
    apply noncausalBudget_minimal δ hm1 hm hB0m hB0H hδ0 hδ1
    rw [hvalue]
    linarith
  have hlower : B0 ≤ noncausalBudget H m D δ hm1 hm hδ0 hδ1 := by
    by_contra hnot
    have hlt : noncausalBudget H m D δ hm1 hm hδ0 hδ1 < B0 := by omega
    obtain ⟨hNB, hNm, hthreshold⟩ :=
      noncausalBudget_spec δ hm1 hm hδ0 hδ1
    let B := noncausalBudget H m D δ hm1 hm hδ0 hδ1
    obtain ⟨M, hM⟩ := noncausal_attainment (D := D) hm hNm hNB 0 le_rfl
    have hlow := noSavings_delta_lower M tests htest_nonempty hall_lower hlt
      0 (1 - offGameValue H m B D hm hNB) hM
    have hsmall : 1 / (Fintype.card I : ℝ) >
        1 - offGameValue H m B D hm hNB := by
      exact lt_of_le_of_lt hthreshold hδsmall
    linarith
  exact Nat.le_antisymm hupper hlower

theorem causalBudget_eq_perfectBudget_of_noSavings
    {H m D : ℕ} {I : Type*} [Fintype I] [Nonempty I]
    (hm1 : 1 ≤ m) (hm : m ≤ H)
    (tests : I → Input H m)
    (htest_nonempty : ∀ i, (tests i).1 ≠ ∅)
    (hall_lower : ∀ y : Trace H,
      (∀ i, Feasible D (tests i).1 y) → perfectBudget H m D ≤ y.card)
    (hB0H : perfectBudget H m D ≤ H)
    (hB0m : m ≤ perfectBudget H m D)
    (hvalue : onGameValue H m (perfectBudget H m D) D hm hB0m hB0H = 1)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδsmall : δ < 1 / (Fintype.card I : ℝ)) :
    causalBudget H m D δ hm1 hm hδ0 hδ1 = perfectBudget H m D := by
  let B0 := perfectBudget H m D
  have hupper : causalBudget H m D δ hm1 hm hδ0 hδ1 ≤ B0 := by
    apply causalBudget_minimal δ hm1 hm hB0m hB0H hδ0 hδ1
    rw [hvalue]
    linarith
  have hlower : B0 ≤ causalBudget H m D δ hm1 hm hδ0 hδ1 := by
    by_contra hnot
    have hlt : causalBudget H m D δ hm1 hm hδ0 hδ1 < B0 := by omega
    obtain ⟨hNB, hNm, hthreshold⟩ :=
      causalBudget_spec δ hm1 hm hδ0 hδ1
    let B := causalBudget H m D δ hm1 hm hδ0 hδ1
    have hH : 0 < H := by omega
    obtain ⟨M, hC, hM⟩ := causal_attainment
      (H := H) (m := m) (B := B) (D := D) hm hH hNm hNB 0 le_rfl
    have hlow := noSavings_delta_lower M tests htest_nonempty hall_lower hlt
      0 (1 - onGameValue H m B D hm hNm hNB) hM
    have hsmall : 1 / (Fintype.card I : ℝ) >
        1 - onGameValue H m B D hm hNm hNB := by
      exact lt_of_le_of_lt hthreshold hδsmall
    linarith
  exact Nat.le_antisymm hupper hlower

end TrafficShaping
