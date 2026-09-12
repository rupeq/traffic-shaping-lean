import TrafficShaping.MainTheorem

/-!
# Budget thresholds

This module turns the exact optimum statements into genuine minimum-budget
definitions.  The predicates below quantify over natural budgets in the
feasible interval and use the actual finite-game values; the `Nat.find`
witnesses are therefore tied to the semantic mechanism classes by the
attainment and converse theorems from `MainTheorem`.
-/

namespace TrafficShaping

open scoped BigOperators

private theorem offSchedule_full {H : ℕ} (s : OffSchedule H H) :
    s.1 = (Finset.univ : Trace H) := by
  apply Finset.eq_univ_of_card
  simpa [Fintype.card_fin] using s.2

private theorem onSchedule_full {H m : ℕ} (s : OnSchedule H m H) :
    s.1 = (Finset.univ : Trace H) := by
  apply Finset.eq_univ_of_card
  simpa [Fintype.card_fin] using s.2.1

private theorem offMatrix_full_entry {H m D : ℕ} (hm : m ≤ H)
    (x : FullInput H m) (s : OffSchedule H H) :
    offMatrix H m H D x s = 1 := by
  have hs := offSchedule_full s
  simp only [offMatrix, coverageMatrix]
  have hfeas : Feasible D x.1 (Finset.univ : Trace H) :=
    Feasible.mono_output (feasible_self D x.1) (Finset.subset_univ _)
  simp [hs, hfeas]

private theorem onMatrix_full_entry {H m D : ℕ} (hm : m ≤ H)
    (x : FullInput H m) (s : OnSchedule H m H) :
    onMatrix H m H D x s = 1 := by
  have hs := onSchedule_full s
  simp only [onMatrix, coverageMatrix]
  have hfeas : Feasible D x.1 (Finset.univ : Trace H) :=
    Feasible.mono_output (feasible_self D x.1) (Finset.subset_univ _)
  simp [hs, hfeas]

private theorem value_one_of_all_one
    {I S : Type*} [Fintype I] [Nonempty I] [Fintype S] [Nonempty S]
    (A : I → S → ℝ) (hA : ∀ i s, A i s = 1) : value A = 1 := by
  obtain ⟨q⟩ := simplex_nonempty (S := S)
  have hcov : ∀ i, coverage A q i = 1 := by
    intro i
    unfold coverage
    calc
      (∑ s, (q : S → ℝ) s * A i s) = ∑ s, (q : S → ℝ) s * 1 := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [hA i s]
      _ = 1 := by simpa only [mul_one] using stdSimplex.sum_eq_one q
  have hworst : worst A q = 1 := by
    unfold worst
    apply le_antisymm
    · calc
        Finset.univ.inf' Finset.univ_nonempty (coverage A q) ≤
            coverage A q (Classical.arbitrary I) :=
          Finset.inf'_le (coverage A q) (Finset.mem_univ (Classical.arbitrary I))
        _ = 1 := hcov _
    · apply Finset.le_inf' Finset.univ_nonempty (coverage A q)
      intro i hi
      rw [hcov i]
  have hmax : ∀ q', worst A q' ≤ worst A q := by
    intro q'
    calc
      worst A q' ≤ 1 := worst_le_one (fun i s => by rw [hA i s]) q'
      _ = worst A q := hworst.symm
  exact value_eq_worst_of_max A q hmax |>.trans hworst

theorem offGameValue_full {H m D : ℕ} (hm : m ≤ H) :
    offGameValue H m H D hm le_rfl = 1 := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OffSchedule H H) := exists_offSchedule H H le_rfl
  change value (offMatrix H m H D) = 1
  apply value_one_of_all_one
  exact offMatrix_full_entry hm

theorem onGameValue_full {H m D : ℕ} (hm : m ≤ H) :
    onGameValue H m H D hm hm le_rfl = 1 := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OnSchedule H m H) := exists_onSchedule hm hm le_rfl
  change value (onMatrix H m H D) = 1
  apply value_one_of_all_one
  exact onMatrix_full_entry hm

def offBudgetGood (H m D : ℕ) (δ : ℝ) (hm : m ≤ H) (B : ℕ) : Prop :=
  ∃ hB : B ≤ H, m ≤ B ∧
    1 - offGameValue H m B D hm hB ≤ δ

def onBudgetGood (H m D : ℕ) (δ : ℝ) (hm : m ≤ H) (B : ℕ) : Prop :=
  ∃ hB : B ≤ H, ∃ hmb : m ≤ B,
    1 - onGameValue H m B D hm hmb hB ≤ δ

noncomputable def noncausalBudget (H m D : ℕ) (δ : ℝ)
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) : ℕ := by
  classical
  exact Nat.find (show ∃ B, offBudgetGood H m D δ hm B from by
    refine ⟨H, ?_⟩
    refine ⟨le_rfl, hm, ?_⟩
    rw [offGameValue_full hm]
    linarith)

noncomputable def causalBudget (H m D : ℕ) (δ : ℝ)
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) : ℕ := by
  classical
  exact Nat.find (show ∃ B, onBudgetGood H m D δ hm B from by
    refine ⟨H, ?_⟩
    refine ⟨le_rfl, hm, ?_⟩
    rw [onGameValue_full hm]
    linarith)

theorem noncausalBudget_spec {H m D : ℕ} (δ : ℝ)
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    offBudgetGood H m D δ hm
      (noncausalBudget H m D δ hm1 hm hδ0 hδ1) := by
  classical
  exact Nat.find_spec (show ∃ B, offBudgetGood H m D δ hm B from by
    refine ⟨H, ?_⟩
    refine ⟨le_rfl, hm, ?_⟩
    rw [offGameValue_full hm]
    linarith)

theorem causalBudget_spec {H m D : ℕ} (δ : ℝ)
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    onBudgetGood H m D δ hm
      (causalBudget H m D δ hm1 hm hδ0 hδ1) := by
  classical
  exact Nat.find_spec (show ∃ B, onBudgetGood H m D δ hm B from by
    refine ⟨H, ?_⟩
    refine ⟨le_rfl, hm, ?_⟩
    rw [onGameValue_full hm]
    linarith)

theorem noncausalBudget_bounds {H m D : ℕ} (δ : ℝ)
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    m ≤ noncausalBudget H m D δ hm1 hm hδ0 hδ1 ∧
      noncausalBudget H m D δ hm1 hm hδ0 hδ1 ≤ H := by
  obtain ⟨hB, hmb, _⟩ := noncausalBudget_spec δ hm1 hm hδ0 hδ1
  exact ⟨hmb, hB⟩

theorem causalBudget_bounds {H m D : ℕ} (δ : ℝ)
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    m ≤ causalBudget H m D δ hm1 hm hδ0 hδ1 ∧
      causalBudget H m D δ hm1 hm hδ0 hδ1 ≤ H := by
  obtain ⟨hB, hmb, _⟩ := causalBudget_spec δ hm1 hm hδ0 hδ1
  exact ⟨hmb, hB⟩

theorem noncausalBudget_threshold {H m D : ℕ} (δ : ℝ)
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    1 - offGameValue H m (noncausalBudget H m D δ hm1 hm hδ0 hδ1) D hm
        (noncausalBudget_bounds δ hm1 hm hδ0 hδ1).2 ≤ δ := by
  obtain ⟨hB, _, hv⟩ := noncausalBudget_spec δ hm1 hm hδ0 hδ1
  simpa using hv

theorem causalBudget_threshold {H m D : ℕ} (δ : ℝ)
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    1 - onGameValue H m (causalBudget H m D δ hm1 hm hδ0 hδ1) D hm
        (causalBudget_bounds δ hm1 hm hδ0 hδ1).1
        (causalBudget_bounds δ hm1 hm hδ0 hδ1).2 ≤ δ := by
  obtain ⟨hB, hmb, hv⟩ := causalBudget_spec δ hm1 hm hδ0 hδ1
  simpa using hv

theorem noncausalBudget_minimal {H m D B : ℕ} (δ : ℝ)
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hthreshold : 1 - offGameValue H m B D hm hB ≤ δ) :
    noncausalBudget H m D δ hm1 hm hδ0 hδ1 ≤ B := by
  classical
  apply Nat.find_min'
  exact ⟨hB, hmb, hthreshold⟩

theorem causalBudget_minimal {H m D B : ℕ} (δ : ℝ)
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hthreshold : 1 - onGameValue H m B D hm hmb hB ≤ δ) :
    causalBudget H m D δ hm1 hm hδ0 hδ1 ≤ B := by
  classical
  apply Nat.find_min'
  exact ⟨hB, hmb, hthreshold⟩

theorem noncausalBudget_attainable {H m D : ℕ} (δ : ℝ)
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ M : Mechanism H m (noncausalBudget H m D δ hm1 hm hδ0 hδ1) D,
      Private M ε δ := by
  have hb := noncausalBudget_bounds (D := D) δ hm1 hm hδ0 hδ1
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OffSchedule H (noncausalBudget H m D δ hm1 hm hδ0 hδ1)) :=
    exists_offSchedule H _ hb.2
  obtain ⟨M, hM⟩ := noncausal_attainment (D := D) hm hb.1 hb.2 ε hε
  refine ⟨M, ?_⟩
  have hthreshold := noncausalBudget_threshold (D := D) δ hm1 hm hδ0 hδ1
  have hthreshold' :
      1 - value (offMatrix H m (noncausalBudget H m D δ hm1 hm hδ0 hδ1) D) ≤ δ := by
    simpa [offGameValue] using hthreshold
  intro x hx E
  obtain ⟨hleft, hright⟩ := hM x hx E
  exact ⟨by linarith, by linarith⟩

theorem causalBudget_attainable {H m D : ℕ} (δ : ℝ)
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ∃ M : Mechanism H m (causalBudget H m D δ hm1 hm hδ0 hδ1) D,
      Causal M ∧ Private M ε δ := by
  have hb := causalBudget_bounds (D := D) δ hm1 hm hδ0 hδ1
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OnSchedule H m (causalBudget H m D δ hm1 hm hδ0 hδ1)) :=
    exists_onSchedule hm hb.1 hb.2
  obtain ⟨M, hC, hM⟩ := causal_attainment (D := D) hm (by omega) hb.1 hb.2 ε hε
  refine ⟨M, hC, ?_⟩
  have hthreshold := causalBudget_threshold (D := D) δ hm1 hm hδ0 hδ1
  have hthreshold' :
      1 - value (onMatrix H m (causalBudget H m D δ hm1 hm hδ0 hδ1) D) ≤ δ := by
    simpa [onGameValue] using hthreshold
  intro x hx E
  obtain ⟨hleft, hright⟩ := hM x hx E
  exact ⟨by linarith, by linarith⟩

theorem noncausalBudget_minimal_of_mechanism {H m D B : ℕ} (δ : ℝ)
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (ε : ℝ) (hε : 0 ≤ ε)
    (M : Mechanism H m B D) (hM : Private M ε δ) :
    noncausalBudget H m D δ hm1 hm hδ0 hδ1 ≤ B := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OffSchedule H B) := exists_offSchedule H B hB
  have hleast := noncausal_optimum_isLeast (D := D) hm1 hm hmb hB ε hε
  have hmem : δ ∈ noncausalLosses H m B D ε := ⟨hδ0, hδ1, M, hM⟩
  apply noncausalBudget_minimal δ hm1 hm hmb hB hδ0 hδ1
  exact hleast.2 hmem

theorem causalBudget_minimal_of_mechanism {H m D B : ℕ} (δ : ℝ)
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (ε : ℝ) (hε : 0 ≤ ε)
    (M : Mechanism H m B D) (hC : Causal M) (hM : Private M ε δ) :
    causalBudget H m D δ hm1 hm hδ0 hδ1 ≤ B := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OnSchedule H m B) := exists_onSchedule hm hmb hB
  have hleast := causal_optimum_isLeast (D := D) hm1 hm hmb hB ε hε
  have hmem : δ ∈ causalLosses H m B D ε := ⟨hδ0, hδ1, M, hC, hM⟩
  apply causalBudget_minimal δ hm1 hm hmb hB hδ0 hδ1
  exact hleast.2 hmem

end TrafficShaping
