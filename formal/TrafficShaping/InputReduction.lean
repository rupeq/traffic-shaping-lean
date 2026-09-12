import TrafficShaping.Achievability

/-! The full-weight rows represent the worst nonempty input exactly. -/

namespace TrafficShaping

variable {H m D : ℕ} {S : Type*} [Fintype S]

/-- The two sets of lower bounds coincide, not just their optimal values. -/
theorem full_row_reduction (hm1 : 1 ≤ m) (hm : m ≤ H)
    (q : Law S) (embed : S → Trace H) (v : ℝ) :
    (∀ x : Input H m, x.1 ≠ ∅ →
      v ≤ q.mass (inputScheduleEvent (D := D) embed x)) ↔
    (∀ z : FullInput H m, v ≤ coverage (coverageMatrix (m := m) (D := D) embed) q z) := by
  classical
  constructor
  · intro h z
    let x : Input H m := ⟨z.1, z.2.le⟩
    have hx : x.1 ≠ ∅ := by
      intro he
      have hz := z.2
      change z.1 = ∅ at he
      rw [he] at hz
      simp only [Finset.card_empty] at hz
      omega
    have hp := h x hx
    rw [coverageMatrix_eq_mass]
    simpa only [inputScheduleEvent, feasibleScheduleEvent] using hp
  · intro h x _
    exact input_coverage_lower hm q embed v h x

abbrev ActiveInput (H m : ℕ) := {x : Input H m // x.1 ≠ ∅}

def terminalActiveInput (hm1 : 1 ≤ m) (hm : m ≤ H) : ActiveInput H m :=
  ⟨⟨terminal H m, (terminal_card hm).le⟩, by
    intro h
    change terminal H m = ∅ at h
    have hc := terminal_card hm
    rw [h] at hc
    simp only [Finset.card_empty] at hc
    omega⟩

noncomputable def activeRowMinimum (hm1 : 1 ≤ m) (hm : m ≤ H)
    (q : Law S) (embed : S → Trace H) : ℝ := by
  classical
  letI : Nonempty (ActiveInput H m) := ⟨terminalActiveInput hm1 hm⟩
  exact Finset.univ.inf' Finset.univ_nonempty
    (fun x : ActiveInput H m => q.mass (inputScheduleEvent (D := D) embed x.1))

/-- The minimum over all nonempty admissible inputs equals the full-row minimum. -/
theorem activeRowMinimum_eq_worst (hm1 : 1 ≤ m) (hm : m ≤ H)
    [Nonempty (FullInput H m)] (q : Law S) (embed : S → Trace H) :
    activeRowMinimum (D := D) hm1 hm q embed = worst (coverageMatrix (m := m) (D := D) embed) q := by
  classical
  letI : Nonempty (ActiveInput H m) := ⟨terminalActiveInput hm1 hm⟩
  have hrow : ∀ z : FullInput H m,
      worst (coverageMatrix (m := m) (D := D) embed) q ≤
        coverage (coverageMatrix (m := m) (D := D) embed) q z := by
    intro z
    exact Finset.inf'_le _ (Finset.mem_univ z)
  apply le_antisymm
  · unfold worst
    apply Finset.le_inf' Finset.univ_nonempty
    intro z _
    let x : ActiveInput H m := ⟨⟨z.1, z.2.le⟩, by
      intro he
      have hz := z.2
      rw [he] at hz
      simp only [Finset.card_empty] at hz
      omega⟩
    have hx : activeRowMinimum (D := D) hm1 hm q embed ≤
        q.mass (inputScheduleEvent (D := D) embed x.1) :=
      Finset.inf'_le _ (Finset.mem_univ x)
    rw [coverageMatrix_eq_mass]
    simpa only [inputScheduleEvent, feasibleScheduleEvent] using hx
  · unfold activeRowMinimum
    apply Finset.le_inf' Finset.univ_nonempty
    intro x _
    exact input_coverage_lower hm q embed _ hrow x.1

end TrafficShaping
