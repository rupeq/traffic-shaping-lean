import TrafficShaping.BlockTests
import TrafficShaping.NoSavings

/-!
  Instantiation of the generic finite-test bound with the block inputs.
-/

namespace TrafficShaping

theorem perfectBudget_lower {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H) :
    m ≤ perfectBudget H m D := by
  let q := H / (D + m)
  let r := H % (D + m)
  by_cases hq : q = 0
  · have hlt : H < D + m := by
      have hL : 0 < D + m := by omega
      dsimp [q] at hq
      exact (Nat.div_eq_zero_iff_lt hL).mp hq
    have hrem : r = H := by
      dsimp [r]
      exact Nat.mod_eq_of_lt hlt
    have hmin : min m r = m := by
      rw [hrem, min_eq_left hm]
    change m ≤ m * q + min m r
    rw [hmin]
    simp [hq]
  · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq
    have hmul : m ≤ m * q := by
      simpa [Nat.mul_comm] using (Nat.le_mul_of_pos_left m hq1)
    exact hmul.trans (Nat.le_add_right _ _)

theorem perfectBudget_upper {H m D : ℕ} (hm : m ≤ H) :
    perfectBudget H m D ≤ H := by
  let L := D + m
  let q := H / L
  let r := H % L
  have hdecomp : q * L + r = H := by
    dsimp [q, r]
    simpa [Nat.mul_comm] using Nat.div_add_mod H L
  have hmL : m ≤ L := by
    dsimp [L]
    omega
  have hq : m * q ≤ q * L := by
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left q hmL
  have hr : min m r ≤ r := min_le_right _ _
  have hsum : m * q + min m r ≤ q * L + r := Nat.add_le_add hq hr
  calc
    perfectBudget H m D = m * q + min m r := by rfl
    _ ≤ q * L + r := hsum
    _ = H := hdecomp

theorem blockTests_nonempty
    {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (i : Fin (testBlockCount H m D)) :
    (blockTests hm1 hm i).1 ≠ ∅ := by
  intro hzero
  have hcard0 : (blockTests hm1 hm i).1.card = 0 := by simp [hzero]
  have hcard : (blockTests hm1 hm i).1.card =
      blockArrivalCount H m D i.val := by
    simpa [blockTests] using blockTest_card hm1 hm i
  rw [hcard] at hcard0
  have hpos := blockArrivalCount_pos hm1 hm i
  omega

theorem block_noSavings_union_bound
    {H m B D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (M : Mechanism H m B D) (ε δ : ℝ)
    (hB : B < perfectBudget H m D)
    (hprivacy : Private M ε δ) :
    1 ≤ (testBlockCount H m D : ℝ) * δ := by
  have h := noSavings_union_bound (I := Fin (testBlockCount H m D)) M
    (blockTests hm1 hm)
    (fun i => blockTests_nonempty hm1 hm i)
    (fun y hfeas => block_tests_lower_bound hm1 hm y hfeas)
    hB ε δ hprivacy
  simpa using h

theorem block_noSavings_union_equation
    {H m B D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (M : Mechanism H m B D) (ε δ : ℝ)
    (hB : B < perfectBudget H m D)
    (hprivacy : Private M ε δ) :
    (∀ i : Fin (testBlockCount H m D), (M.law (emptyInput H m)).mass
      (feasibleInputEvent (D := D) (blockTests hm1 hm i))ᶜ ≤ δ) ∧
    (∀ y, 0 < (M.law (emptyInput H m)).val y →
      ∃ i : Fin (testBlockCount H m D),
        y ∈ (feasibleInputEvent (D := D) (blockTests hm1 hm i))ᶜ) ∧
    1 ≤ (testBlockCount H m D : ℝ) * δ := by
  have h := finite_test_union_equation
    (H := H) (m := m) (B := B) (D := D)
    (I := Fin (testBlockCount H m D)) M
    (blockTests hm1 hm) ε δ hprivacy
    (fun i => blockTests_nonempty hm1 hm i)
    (by
      intro y hy
      by_contra hnone
      push Not at hnone
      have hlow := block_tests_lower_bound hm1 hm y hnone
      have hcap := M.cap (emptyInput H m) y hy
      omega)
  simpa using h

theorem block_noSavings_delta_lower
    {H m B D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (M : Mechanism H m B D) (ε δ : ℝ)
    (hB : B < perfectBudget H m D)
    (hprivacy : Private M ε δ) :
    (1 : ℝ) / testBlockCount H m D ≤ δ := by
  letI : Nonempty (Fin (testBlockCount H m D)) :=
    ⟨⟨0, testBlockCount_pos hm1 hm⟩⟩
  have h := noSavings_delta_lower (I := Fin (testBlockCount H m D)) M
    (blockTests hm1 hm)
    (fun i => blockTests_nonempty hm1 hm i)
    (fun y hfeas => block_tests_lower_bound hm1 hm y hfeas)
    hB ε δ hprivacy
  simpa using h

theorem corollary5_eq24
    {H m B D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B)
    (M : Mechanism H m B D) (ε δ : ℝ)
    (hB : B < perfectBudget H m D)
    (hprivacy : Private M ε δ) :
    (1 : ℝ) / testBlockCount H m D ≤ δ := by
  exact block_noSavings_delta_lower hm1 hm M ε δ hB hprivacy

theorem corollary5_eq25
    {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (hoff : offGameValue H m (perfectBudget H m D) D hm
        (perfectBudget_upper hm) = 1)
    (hon : onGameValue H m (perfectBudget H m D) D hm
        (perfectBudget_lower hm1 hm) (perfectBudget_upper hm) = 1)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδsmall : δ < 1 / (testBlockCount H m D : ℝ)) :
    noncausalBudget H m D δ hm1 hm hδ0 hδ1 = perfectBudget H m D ∧
      causalBudget H m D δ hm1 hm hδ0 hδ1 = perfectBudget H m D := by
  letI : Nonempty (Fin (testBlockCount H m D)) :=
    ⟨⟨0, testBlockCount_pos hm1 hm⟩⟩
  have hnc := noncausalBudget_eq_perfectBudget_of_noSavings
    (I := Fin (testBlockCount H m D)) hm1 hm (blockTests hm1 hm)
    (fun i => blockTests_nonempty hm1 hm i)
    (fun y hfeas => block_tests_lower_bound hm1 hm y hfeas)
    (perfectBudget_upper hm) (perfectBudget_lower hm1 hm) hoff
    δ hδ0 hδ1 (by simpa using hδsmall)
  have hc := causalBudget_eq_perfectBudget_of_noSavings
    (I := Fin (testBlockCount H m D)) hm1 hm (blockTests hm1 hm)
    (fun i => blockTests_nonempty hm1 hm i)
    (fun y hfeas => block_tests_lower_bound hm1 hm y hfeas)
    (perfectBudget_upper hm) (perfectBudget_lower hm1 hm) hon
    δ hδ0 hδ1 (by simpa using hδsmall)
  exact ⟨hnc, hc⟩

theorem corollary5_eq25_of_zero_witnesses
    {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (hoff_zero : ∃ M : Mechanism H m (perfectBudget H m D) D,
      Private M 0 0)
    (hon_zero : ∃ M : Mechanism H m (perfectBudget H m D) D,
      Causal M ∧ Private M 0 0)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδsmall : δ < 1 / (testBlockCount H m D : ℝ)) :
    noncausalBudget H m D δ hm1 hm hδ0 hδ1 = perfectBudget H m D ∧
      causalBudget H m D δ hm1 hm hδ0 hδ1 = perfectBudget H m D := by
  have hB0H := perfectBudget_upper (D := D) hm
  have hB0m := perfectBudget_lower (D := D) hm1 hm
  have hoff_bound := offGameValue_bounds (D := D) hm hB0H
  have hon_bound := onGameValue_bounds (D := D) hm hB0m hB0H
  have hoff_value : offGameValue H m (perfectBudget H m D) D hm hB0H = 1 := by
    obtain ⟨M, hM⟩ := hoff_zero
    have hleast := noncausal_optimum_isLeast (D := D) hm1 hm hB0m hB0H 0 le_rfl
    have hzero : (0 : ℝ) ∈ noncausalLosses H m (perfectBudget H m D) D 0 := by
      exact ⟨by norm_num, by norm_num, M, hM⟩
    have hle := hleast.2 hzero
    linarith [hoff_bound.2]
  have hon_value : onGameValue H m (perfectBudget H m D) D hm hB0m hB0H = 1 := by
    obtain ⟨M, hC, hM⟩ := hon_zero
    have hleast := causal_optimum_isLeast (D := D) hm1 hm hB0m hB0H 0 le_rfl
    have hzero : (0 : ℝ) ∈ causalLosses H m (perfectBudget H m D) D 0 := by
      exact ⟨by norm_num, by norm_num, M, hC, hM⟩
    have hle := hleast.2 hzero
    linarith [hon_bound.2]
  exact corollary5_eq25 hm1 hm hoff_value hon_value δ hδ0 hδ1
    (by simpa using hδsmall)

end TrafficShaping
