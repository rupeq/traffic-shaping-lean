import TrafficShaping.NoSavingsBlocks
import TrafficShaping.PerfectPrivacy

/-!
# Corollary 5: the finite-test no-savings threshold

The fixed schedule from `PerfectPrivacy` is a zero-loss witness at the
budget in (20).  This file turns that witness into the two semantic
mechanisms needed by the budget theorem, so the article statement has no
remaining game-value or mechanism hypotheses.
-/

namespace TrafficShaping

private theorem coverage_dirac {I S : Type*} [Fintype I] [Fintype S] [DecidableEq S]
    (A : I → S → ℝ) (q : S) (i : I) :
    coverage A (Law.dirac q) i = A i q := by
  classical
  unfold coverage
  change (∑ s, (if s = q then 1 else 0) * A i s) = A i q
  simp

private noncomputable def perfectOffSchedule {H m D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) :
    OffSchedule H (perfectBudget H m D) :=
  ⟨perfectSchedule H m D, perfectSchedule_card hm1 hm⟩

private noncomputable def perfectOnSchedule {H m D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) :
    OnSchedule H m (perfectBudget H m D) :=
  ⟨perfectSchedule H m D, perfectSchedule_card hm1 hm,
    perfectSchedule_terminal_subset hm1 hm⟩

private theorem perfectBudget_hmb {H m D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) :
    m ≤ perfectBudget H m D :=
  perfectBudget_lower hm1 hm

private noncomputable def perfectOffMechanism {H m D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) :
    Mechanism H m (perfectBudget H m D) D :=
  offMechanism (D := D) (perfectBudget_hmb hm1 hm)
    (Law.dirac (perfectOffSchedule hm1 hm))

private noncomputable def perfectOnMechanism {H m D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) :
    Mechanism H m (perfectBudget H m D) D :=
  onMechanism (D := D) hm (by omega) (perfectBudget_hmb hm1 hm)
    (Law.dirac (perfectOnSchedule hm1 hm))

private theorem perfect_off_private_zero {H m D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) :
    Private (perfectOffMechanism (D := D) hm1 hm) 0 0 := by
  classical
  unfold perfectOffMechanism
  have hrow : ∀ z : FullInput H m,
      (1 : ℝ) ≤ coverage (offMatrix H m (perfectBudget H m D) D)
        (Law.dirac (perfectOffSchedule hm1 hm)) z := by
    intro z
    have hfeas : Feasible D z.1 (perfectSchedule H m D) :=
      perfectSchedule_feasible hm1 hm (by omega)
    rw [coverage_dirac (A := offMatrix H m (perfectBudget H m D) D)
      (q := perfectOffSchedule hm1 hm) (i := z)]
    unfold offMatrix coverageMatrix
    change (1 : ℝ) ≤ if Feasible D z.1 (perfectSchedule H m D) then 1 else 0
    simp [hfeas]
  have h := offMechanism_private (D := D) hm (perfectBudget_hmb hm1 hm)
    (Law.dirac (perfectOffSchedule hm1 hm)) 1 hrow 0 (by norm_num)
  simpa using h

private theorem perfect_on_private_zero {H m D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) :
    Private (perfectOnMechanism (D := D) hm1 hm) 0 0 := by
  classical
  unfold perfectOnMechanism
  have hrow : ∀ z : FullInput H m,
      (1 : ℝ) ≤ coverage (onMatrix H m (perfectBudget H m D) D)
        (Law.dirac (perfectOnSchedule hm1 hm)) z := by
    intro z
    have hfeas : Feasible D z.1 (perfectSchedule H m D) :=
      perfectSchedule_feasible hm1 hm (by omega)
    rw [coverage_dirac (A := onMatrix H m (perfectBudget H m D) D)
      (q := perfectOnSchedule hm1 hm) (i := z)]
    unfold onMatrix coverageMatrix
    change (1 : ℝ) ≤ if Feasible D z.1 (perfectSchedule H m D) then 1 else 0
    simp [hfeas]
  have h := onMechanism_private (D := D) hm (by omega)
    (perfectBudget_hmb hm1 hm)
    (Law.dirac (perfectOnSchedule hm1 hm)) 1 hrow 0 (by norm_num)
  simpa using h

private theorem perfect_off_zero_witness {H m D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) :
    ∃ M : Mechanism H m (perfectBudget H m D) D, Private M 0 0 :=
  ⟨perfectOffMechanism (D := D) hm1 hm, perfect_off_private_zero hm1 hm⟩

private theorem perfect_on_zero_witness {H m D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) :
    ∃ M : Mechanism H m (perfectBudget H m D) D,
      Causal M ∧ Private M 0 0 := by
  refine ⟨perfectOnMechanism (D := D) hm1 hm, ?_, perfect_on_private_zero hm1 hm⟩
  exact onMechanism_causal hm (by omega) (perfectBudget_hmb hm1 hm)
    (Law.dirac (perfectOnSchedule hm1 hm))

theorem corollary5_eq25_unconditional {H m D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδsmall : δ < 1 / (testBlockCount H m D : ℝ)) :
    noncausalBudget H m D δ hm1 hm hδ0 hδ1 = perfectBudget H m D ∧
      causalBudget H m D δ hm1 hm hδ0 hδ1 = perfectBudget H m D := by
  exact corollary5_eq25_of_zero_witnesses hm1 hm
    (perfect_off_zero_witness hm1 hm)
    (perfect_on_zero_witness hm1 hm)
    δ hδ0 hδ1 hδsmall

end TrafficShaping
