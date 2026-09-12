import TrafficShaping.Budgets

/-!
# Corollary 1: the budget price of causality

The padding map in this file is a fixed transformation of a distribution on
noncausal base schedules.  It depends on the public parameters and on the
sampled base schedule only; it never inspects an input trace.  The resulting
coverage comparison is therefore a game statement, after which the exact
attainment and converse theorems turn it into a statement about the true
minimum budgets.
-/

namespace TrafficShaping

open scoped BigOperators

private theorem prefix_card_le_horizon {H m : ℕ} (hm : m ≤ H) (y : Trace H) :
    (tracePrefix (H - m) y).card ≤ H - m := by
  let f : (tracePrefix (H - m) y) → Fin (H - m) :=
    fun a => ⟨a.1.1, (mem_prefix.mp a.2).2⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Fin.ext
    simpa [f] using congrArg Fin.val hab
  have hc := Fintype.card_le_of_injective f hf
  have hcard : Fintype.card (tracePrefix (H - m) y) =
      (tracePrefix (H - m) y).card := Fintype.card_coe _
  rw [hcard] at hc
  simpa [Fintype.card_fin] using hc

private theorem prefix_card_le_base {H m B : ℕ} (hm : m ≤ H)
    (y : OffSchedule H B) :
    (tracePrefix (H - m) y.1).card ≤ B := by
  have hs : tracePrefix (H - m) y.1 ⊆ y.1 := by
    intro a ha
    exact (mem_prefix.mp ha).1
  exact (Finset.card_le_card hs).trans_eq y.2

private theorem padded_prefix_bound {H m B : ℕ} (hm : m ≤ H)
    (hmb : m ≤ B) (hB : B ≤ H) (y : OffSchedule H B) :
    (tracePrefix (H - m) y.1).card ≤ min H (B + m) - m := by
  have hpB := prefix_card_le_base hm y
  have hpH := prefix_card_le_horizon hm y.1
  by_cases hsum : B + m ≤ H
  · rw [Nat.min_eq_right hsum]
    omega
  · rw [Nat.min_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hsum))]
    omega

private theorem padded_budget_lower {H m B : ℕ} (hm : m ≤ H)
    (hmb : m ≤ B) : m ≤ min H (B + m) := by
  rw [Nat.le_min]
  exact ⟨hm, le_trans hmb (Nat.le_add_right B m)⟩

private noncomputable def paddedOnSchedule {H m B : ℕ}
    (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (y : OffSchedule H B) : OnSchedule H m (min H (B + m)) :=
  saturateOn hm (padded_budget_lower hm hmb)
    (Nat.min_le_left H (B + m)) y.1 (padded_prefix_bound hm hmb hB y)

private theorem paddedOnSchedule_superset {H m B : ℕ}
    (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (y : OffSchedule H B) :
    y.1 ⊆ (paddedOnSchedule hm hmb hB y).1 := by
  exact saturateOn_subset hm (padded_budget_lower hm hmb)
    (Nat.min_le_left H (B + m)) y.1 (padded_prefix_bound hm hmb hB y)

private noncomputable def paddedOnLaw {H m B : ℕ}
    (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (q : Law (OffSchedule H B)) : Law (OnSchedule H m (min H (B + m))) :=
  q.map (paddedOnSchedule hm hmb hB)

private theorem padded_coverage_ge {H m B D : ℕ}
    (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (q : Law (OffSchedule H B)) (x : FullInput H m) :
    coverage (offMatrix H m B D) q x ≤
      coverage (onMatrix H m (min H (B + m)) D)
        (paddedOnLaw hm hmb hB q) x := by
  let Eoff : Finset (OffSchedule H B) :=
    feasibleScheduleEvent (D := D) (fun s : OffSchedule H B => s.1) x
  let Eon : Finset (OnSchedule H m (min H (B + m))) :=
    feasibleScheduleEvent
      (D := D) (fun s : OnSchedule H m (min H (B + m)) => s.1) x
  have hmass : q.mass Eoff ≤
      (q.map (paddedOnSchedule hm hmb hB)).mass Eon := by
    apply Law.mass_map_ge q (paddedOnSchedule hm hmb hB) Eoff Eon
    intro y hypos hyE
    have hyfeasible : Feasible D x.1 y.1 := by
      simpa [Eoff, feasibleScheduleEvent] using hyE
    have hsup := paddedOnSchedule_superset hm hmb hB y
    have hfeasible := Feasible.mono_output hyfeasible hsup
    simpa [Eon, feasibleScheduleEvent] using hfeasible
  calc
    coverage (offMatrix H m B D) q x = q.mass Eoff := by
      change coverage (coverageMatrix (D := D)
        (fun s : OffSchedule H B => s.1)) q x = q.mass Eoff
      rw [coverageMatrix_eq_mass]
    _ ≤ (q.map (paddedOnSchedule hm hmb hB)).mass Eon := hmass
    _ = coverage (onMatrix H m (min H (B + m)) D)
        (paddedOnLaw hm hmb hB q) x := by
      change (paddedOnLaw hm hmb hB q).mass Eon =
        coverage (coverageMatrix (D := D)
          (fun s : OnSchedule H m (min H (B + m)) => s.1))
          (paddedOnLaw hm hmb hB q) x
      rw [coverageMatrix_eq_mass]

theorem onGameValue_ge_offGameValue_padded {H m B D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H) :
    offGameValue H m B D hm hB ≤
      onGameValue H m (min H (B + m)) D hm
        (padded_budget_lower hm hmb) (Nat.min_le_left H (B + m)) := by
  let B' := min H (B + m)
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OffSchedule H B) := exists_offSchedule H B hB
  letI : Nonempty (OnSchedule H m B') :=
    exists_onSchedule hm (padded_budget_lower hm hmb) (Nat.min_le_left H (B + m))
  obtain ⟨q, hq⟩ := value_attained (offMatrix H m B D)
  have hcov : ∀ x : FullInput H m,
      coverage (offMatrix H m B D) q x ≤
        coverage (onMatrix H m B' D) (paddedOnLaw hm hmb hB q) x := by
    intro x
    exact padded_coverage_ge hm hmb hB q x
  have hworst : worst (offMatrix H m B D) q ≤
      worst (onMatrix H m B' D) (paddedOnLaw hm hmb hB q) := by
    unfold worst
    apply Finset.le_inf' Finset.univ_nonempty
      (coverage (onMatrix H m B' D) (paddedOnLaw hm hmb hB q))
    intro x hx
    exact (Finset.inf'_le (coverage (offMatrix H m B D) q)
      (Finset.mem_univ x)).trans (hcov x)
  change value (offMatrix H m B D) ≤ value (onMatrix H m B' D)
  calc
    value (offMatrix H m B D) = worst (offMatrix H m B D) q :=
      (hq).symm
    _ ≤ worst (onMatrix H m B' D) (paddedOnLaw hm hmb hB q) := hworst
    _ ≤ value (onMatrix H m B' D) :=
      worst_le_value (onMatrix H m B' D) _

private noncomputable def offBudgetPad {H B₁ B₂ : ℕ}
    (hB₁₂ : B₁ ≤ B₂) (hB₂ : B₂ ≤ H)
    (y : OffSchedule H B₁) : OffSchedule H B₂ :=
  saturateOff y.1 (by simpa [y.2] using hB₁₂) hB₂

private theorem offBudgetPad_superset {H B₁ B₂ : ℕ}
    (hB₁₂ : B₁ ≤ B₂) (hB₂ : B₂ ≤ H)
    (y : OffSchedule H B₁) : y.1 ⊆ (offBudgetPad hB₁₂ hB₂ y).1 := by
  exact saturateOff_subset y.1 (by simpa [y.2] using hB₁₂) hB₂

private theorem off_coverage_mono {H m B₁ B₂ D : ℕ}
    (hm : m ≤ H) (hmb₁ : m ≤ B₁) (hB₁₂ : B₁ ≤ B₂) (hB₂ : B₂ ≤ H)
    (q : Law (OffSchedule H B₁)) (x : FullInput H m) :
    coverage (offMatrix H m B₁ D) q x ≤
      coverage (offMatrix H m B₂ D) (Law.map (offBudgetPad hB₁₂ hB₂) q) x := by
  let E₁ : Finset (OffSchedule H B₁) :=
    feasibleScheduleEvent (D := D) (fun s : OffSchedule H B₁ => s.1) x
  let E₂ : Finset (OffSchedule H B₂) :=
    feasibleScheduleEvent (D := D) (fun s : OffSchedule H B₂ => s.1) x
  have hmass : q.mass E₁ ≤
      (Law.map (offBudgetPad hB₁₂ hB₂) q).mass E₂ := by
    apply Law.mass_map_ge q (offBudgetPad hB₁₂ hB₂) E₁ E₂
    intro y hypos hyE
    have hyfeasible : Feasible D x.1 y.1 := by
      simpa [E₁, feasibleScheduleEvent] using hyE
    have hfeasible := Feasible.mono_output hyfeasible
      (offBudgetPad_superset hB₁₂ hB₂ y)
    simpa [E₂, feasibleScheduleEvent] using hfeasible
  calc
    coverage (offMatrix H m B₁ D) q x = q.mass E₁ := by
      change coverage (coverageMatrix (D := D)
        (fun s : OffSchedule H B₁ => s.1)) q x = q.mass E₁
      rw [coverageMatrix_eq_mass]
    _ ≤ (Law.map (offBudgetPad hB₁₂ hB₂) q).mass E₂ := hmass
    _ = coverage (offMatrix H m B₂ D)
        (Law.map (offBudgetPad hB₁₂ hB₂) q) x := by
      change (Law.map (offBudgetPad hB₁₂ hB₂) q).mass E₂ =
        coverage (coverageMatrix (D := D)
          (fun s : OffSchedule H B₂ => s.1))
          (Law.map (offBudgetPad hB₁₂ hB₂) q) x
      rw [coverageMatrix_eq_mass]

theorem offGameValue_mono_budget {H m B₁ B₂ D : ℕ}
    (hm : m ≤ H) (hmb₁ : m ≤ B₁) (hB₁₂ : B₁ ≤ B₂) (hB₂ : B₂ ≤ H) :
    offGameValue H m B₁ D hm (hB₁₂.trans hB₂) ≤
      offGameValue H m B₂ D hm hB₂ := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OffSchedule H B₁) := exists_offSchedule H B₁ (hB₁₂.trans hB₂)
  letI : Nonempty (OffSchedule H B₂) := exists_offSchedule H B₂ hB₂
  obtain ⟨q, hq⟩ := value_attained (offMatrix H m B₁ D)
  have hcov : ∀ x : FullInput H m,
      coverage (offMatrix H m B₁ D) q x ≤
      coverage (offMatrix H m B₂ D)
        (Law.map (offBudgetPad hB₁₂ hB₂) q) x := by
    intro x
    exact off_coverage_mono hm hmb₁ hB₁₂ hB₂ q x
  have hworst : worst (offMatrix H m B₁ D) q ≤
      worst (offMatrix H m B₂ D)
        (Law.map (offBudgetPad hB₁₂ hB₂) q) := by
    unfold worst
    apply Finset.le_inf' Finset.univ_nonempty
      (coverage (offMatrix H m B₂ D)
        (Law.map (offBudgetPad hB₁₂ hB₂) q))
    intro x hx
    exact (Finset.inf'_le (coverage (offMatrix H m B₁ D) q)
      (Finset.mem_univ x)).trans (hcov x)
  change value (offMatrix H m B₁ D) ≤ value (offMatrix H m B₂ D)
  calc
    value (offMatrix H m B₁ D) = worst (offMatrix H m B₁ D) q := hq.symm
    _ ≤ worst (offMatrix H m B₂ D)
        (Law.map (offBudgetPad hB₁₂ hB₂) q) := hworst
    _ ≤ value (offMatrix H m B₂ D) := worst_le_value _ _

private noncomputable def onBudgetPad {H m B₁ B₂ : ℕ}
    (hm : m ≤ H) (hB₁₂ : B₁ ≤ B₂) (hmb₂ : m ≤ B₂) (hB₂ : B₂ ≤ H)
    (y : OnSchedule H m B₁) : OnSchedule H m B₂ := by
  apply saturateOn hm hmb₂ hB₂ y.1
  have hpart := prefix_terminal_card_of_subset hm y.2.2
  rw [terminal_card hm, y.2.1] at hpart
  have hB₁ : B₁ ≤ B₂ := hB₁₂
  omega

private theorem onBudgetPad_superset {H m B₁ B₂ : ℕ}
    (hm : m ≤ H) (hmb₁ : m ≤ B₁) (hB₁₂ : B₁ ≤ B₂)
    (hmb₂ : m ≤ B₂) (hB₂ : B₂ ≤ H)
    (y : OnSchedule H m B₁) :
    y.1 ⊆ (onBudgetPad hm hB₁₂ hmb₂ hB₂ y).1 := by
  apply saturateOn_subset hm hmb₂ hB₂ y.1

private theorem on_coverage_mono {H m B₁ B₂ D : ℕ}
    (hm : m ≤ H) (hmb₁ : m ≤ B₁) (hB₁₂ : B₁ ≤ B₂)
    (hmb₂ : m ≤ B₂) (hB₂ : B₂ ≤ H)
    (q : Law (OnSchedule H m B₁)) (x : FullInput H m) :
    coverage (onMatrix H m B₁ D) q x ≤
      coverage (onMatrix H m B₂ D)
        (Law.map (onBudgetPad hm hB₁₂ hmb₂ hB₂) q) x := by
  let E₁ : Finset (OnSchedule H m B₁) :=
    feasibleScheduleEvent (D := D) (fun s : OnSchedule H m B₁ => s.1) x
  let E₂ : Finset (OnSchedule H m B₂) :=
    feasibleScheduleEvent (D := D) (fun s : OnSchedule H m B₂ => s.1) x
  have hmass : q.mass E₁ ≤
      (Law.map (onBudgetPad hm hB₁₂ hmb₂ hB₂) q).mass E₂ := by
    apply Law.mass_map_ge q (onBudgetPad hm hB₁₂ hmb₂ hB₂) E₁ E₂
    intro y hypos hyE
    have hyfeasible : Feasible D x.1 y.1 := by
      simpa [E₁, feasibleScheduleEvent] using hyE
    have hfeasible := Feasible.mono_output hyfeasible
      (onBudgetPad_superset hm hmb₁ hB₁₂ hmb₂ hB₂ y)
    simpa [E₂, feasibleScheduleEvent] using hfeasible
  calc
    coverage (onMatrix H m B₁ D) q x = q.mass E₁ := by
      change coverage (coverageMatrix (D := D)
        (fun s : OnSchedule H m B₁ => s.1)) q x = q.mass E₁
      rw [coverageMatrix_eq_mass]
    _ ≤ (Law.map (onBudgetPad hm hB₁₂ hmb₂ hB₂) q).mass E₂ := hmass
    _ = coverage (onMatrix H m B₂ D)
        (Law.map (onBudgetPad hm hB₁₂ hmb₂ hB₂) q) x := by
      change (Law.map (onBudgetPad hm hB₁₂ hmb₂ hB₂) q).mass E₂ =
        coverage (coverageMatrix (D := D)
          (fun s : OnSchedule H m B₂ => s.1))
          (Law.map (onBudgetPad hm hB₁₂ hmb₂ hB₂) q) x
      rw [coverageMatrix_eq_mass]

theorem onGameValue_mono_budget {H m B₁ B₂ D : ℕ}
    (hm : m ≤ H) (hmb₁ : m ≤ B₁) (hB₁₂ : B₁ ≤ B₂) (hB₂ : B₂ ≤ H) :
    onGameValue H m B₁ D hm hmb₁ (hB₁₂.trans hB₂) ≤
      onGameValue H m B₂ D hm (by omega) hB₂ := by
  let hmb₂ : m ≤ B₂ := by omega
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OnSchedule H m B₁) := exists_onSchedule hm hmb₁ (hB₁₂.trans hB₂)
  letI : Nonempty (OnSchedule H m B₂) := exists_onSchedule hm hmb₂ hB₂
  obtain ⟨q, hq⟩ := value_attained (onMatrix H m B₁ D)
  have hcov : ∀ x : FullInput H m,
    coverage (onMatrix H m B₁ D) q x ≤
        coverage (onMatrix H m B₂ D)
          (Law.map (onBudgetPad hm hB₁₂ hmb₂ hB₂) q) x := by
    intro x
    exact on_coverage_mono hm hmb₁ hB₁₂ hmb₂ hB₂ q x
  have hworst : worst (onMatrix H m B₁ D) q ≤
      worst (onMatrix H m B₂ D)
        (Law.map (onBudgetPad hm hB₁₂ hmb₂ hB₂) q) := by
    unfold worst
    apply Finset.le_inf' Finset.univ_nonempty
      (coverage (onMatrix H m B₂ D)
        (Law.map (onBudgetPad hm hB₁₂ hmb₂ hB₂) q))
    intro x hx
    exact (Finset.inf'_le (coverage (onMatrix H m B₁ D) q)
      (Finset.mem_univ x)).trans (hcov x)
  change value (onMatrix H m B₁ D) ≤ value (onMatrix H m B₂ D)
  calc
    value (onMatrix H m B₁ D) = worst (onMatrix H m B₁ D) q := hq.symm
    _ ≤ worst (onMatrix H m B₂ D)
        (Law.map (onBudgetPad hm hB₁₂ hmb₂ hB₂) q) := hworst
    _ ≤ value (onMatrix H m B₂ D) := worst_le_value _ _

theorem noncausalBudget_le_causalBudget {H m D : ℕ} (δ : ℝ)
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    noncausalBudget H m D δ hm1 hm hδ0 hδ1 ≤
      causalBudget H m D δ hm1 hm hδ0 hδ1 := by
  have hbc := causalBudget_bounds (D := D) δ hm1 hm hδ0 hδ1
  obtain ⟨M, hC, hM⟩ :=
    causalBudget_attainable (D := D) δ hm1 hm hδ0 hδ1 0 le_rfl
  exact noncausalBudget_minimal_of_mechanism (D := D) δ hm1 hm
    hbc.1 hbc.2 hδ0 hδ1 0 le_rfl M hM

theorem corollary1_budget_bounds {H m D : ℕ} (δ : ℝ)
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    let Boff := noncausalBudget H m D δ hm1 hm hδ0 hδ1
    let Bon := causalBudget H m D δ hm1 hm hδ0 hδ1
    0 ≤ Bon - Boff ∧ Bon - Boff ≤ m ∧ Bon ≤ min H (Boff + m) := by
  let Boff := noncausalBudget H m D δ hm1 hm hδ0 hδ1
  let Bon := causalBudget H m D δ hm1 hm hδ0 hδ1
  have hbo := noncausalBudget_bounds (D := D) δ hm1 hm hδ0 hδ1
  have hbc := causalBudget_bounds (D := D) δ hm1 hm hδ0 hδ1
  have hBonThreshold := causalBudget_threshold (D := D) δ hm1 hm hδ0 hδ1
  have hBoff_le_Bon : Boff ≤ Bon := by
    exact noncausalBudget_le_causalBudget (D := D) δ hm1 hm hδ0 hδ1
  have hpadValue :
      offGameValue H m Boff D hm hbo.2 ≤
        onGameValue H m (min H (Boff + m)) D hm
          (padded_budget_lower hm hbo.1) (Nat.min_le_left H (Boff + m)) := by
    exact onGameValue_ge_offGameValue_padded hm1 hm hbo.1 hbo.2
  have hpadThreshold :
      1 - onGameValue H m (min H (Boff + m)) D hm
          (padded_budget_lower hm hbo.1) (Nat.min_le_left H (Boff + m)) ≤ δ := by
    have hoff := noncausalBudget_threshold (D := D) δ hm1 hm hδ0 hδ1
    linarith
  have hBon_le : Bon ≤ min H (Boff + m) := by
    exact causalBudget_minimal (D := D) δ hm1 hm
      (padded_budget_lower hm hbo.1) (Nat.min_le_left H (Boff + m))
      hδ0 hδ1 hpadThreshold
  dsimp [Boff, Bon] at hBoff_le_Bon hBon_le hbo hbc
  omega

theorem corollary1_real_difference_bounds {H m D : ℕ} (δ : ℝ)
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    0 ≤
        (causalBudget H m D δ hm1 hm hδ0 hδ1 : ℝ) -
          (noncausalBudget H m D δ hm1 hm hδ0 hδ1 : ℝ) ∧
      (causalBudget H m D δ hm1 hm hδ0 hδ1 : ℝ) -
          (noncausalBudget H m D δ hm1 hm hδ0 hδ1 : ℝ) ≤ m := by
  have horder := noncausalBudget_le_causalBudget (D := D) δ hm1 hm hδ0 hδ1
  have hbounds := corollary1_budget_bounds (D := D) δ hm1 hm hδ0 hδ1
  constructor
  · rw [← Nat.cast_sub horder]
    exact_mod_cast (Nat.zero_le
      (causalBudget H m D δ hm1 hm hδ0 hδ1 -
        noncausalBudget H m D δ hm1 hm hδ0 hδ1))
  · rw [← Nat.cast_sub horder]
    exact_mod_cast hbounds.2.1

theorem corollary1_ratio_le_two {H m D : ℕ} (δ : ℝ)
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (causalBudget H m D δ hm1 hm hδ0 hδ1 : ℝ) /
        (noncausalBudget H m D δ hm1 hm hδ0 hδ1 : ℝ) ≤ 2 := by
  have hb := corollary1_budget_bounds (D := D) δ hm1 hm hδ0 hδ1
  have hbo := noncausalBudget_bounds (D := D) δ hm1 hm hδ0 hδ1
  have hden : 0 < (noncausalBudget H m D δ hm1 hm hδ0 hδ1 : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le hm1 hbo.1)
  have hnat :
      causalBudget H m D δ hm1 hm hδ0 hδ1 ≤
        2 * noncausalBudget H m D δ hm1 hm hδ0 hδ1 := by
    omega
  exact (div_le_iff₀ hden).2 (by exact_mod_cast hnat)

end TrafficShaping
