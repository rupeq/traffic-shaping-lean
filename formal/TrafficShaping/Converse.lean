import TrafficShaping.Mechanism
import TrafficShaping.Saturation

/-!
# Support-based converse bounds

The converse uses only the semantic mechanism interface.  Privacy forces the
empty-input law to put enough mass on every full-input feasible event.  Finite
support saturation moves that mass to the exact-cap schedule family without
losing feasibility, after which the finite-game value gives the bound.
-/

namespace TrafficShaping

open scoped BigOperators

private noncomputable def offSaturator {H B : ℕ} (hB : B ≤ H) :
    Trace H → OffSchedule H B := by
  classical
  exact fun y => if hy : y.card ≤ B then
    saturateOff y hy hB
  else Classical.choice (exists_offSchedule H B hB)

private noncomputable def onSaturator {H m B : ℕ}
    (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H) :
    Trace H → OnSchedule H m B := by
  classical
  exact fun y => if hy : (tracePrefix (H - m) y).card ≤ B - m then
    saturateOn hm hmb hB y hy
  else Classical.choice (exists_onSchedule hm hmb hB)

private lemma fullInput_nonempty {H m : ℕ} (hm1 : 1 ≤ m)
    (x : FullInput H m) : x.1 ≠ ∅ := by
  intro hx
  have hcard : x.1.card = 0 := by simp [hx]
  omega

private lemma active_feasible_mass_lower {H m B D : ℕ}
    (hm1 : 1 ≤ m) (M : Mechanism H m B D) (ε δ : ℝ)
    (hprivacy : Private M ε δ) (x : FullInput H m) :
    1 - δ ≤ (M.law (emptyInput H m)).mass (feasibleEvent (D := D) x) := by
  let xi : Input H m := ⟨x.1, le_of_eq x.2⟩
  have hxi : xi.1 ≠ ∅ := fullInput_nonempty hm1 x
  let E : Finset (Trace H) := feasibleEvent (D := D) x
  have hzero : (M.law xi).mass Eᶜ = 0 := by
    apply (Law.mass_zero_iff (M.law xi) Eᶜ).2
    intro y hybad
    have hynot : ¬ Feasible D x.1 y := by
      simpa [E, feasibleEvent] using (Finset.mem_compl.mp hybad)
    have hnotpos : ¬ 0 < (M.law xi).val y := by
      intro hypos
      exact hynot (M.feasible xi y hypos)
    exact le_antisymm (le_of_not_gt hnotpos) ((M.law xi).nonneg y)
  have hbad : (M.law (emptyInput H m)).mass Eᶜ ≤ δ :=
    Law.forbidden_event (M.law xi) (M.law (emptyInput H m))
      (hprivacy xi hxi) Eᶜ hzero
  have hcomp := Law.mass_compl (M.law (emptyInput H m)) E
  have hgood : 1 - δ ≤ (M.law (emptyInput H m)).mass E := by
    linarith
  simpa [E] using hgood

private lemma coverage_lower_after_map
    {H m D : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    (embed : S → Trace H) (p : Law (Trace H)) (sat : Trace H → S)
    (x : FullInput H m) (δ : ℝ) (E : Finset (Trace H))
    (hprob : 1 - δ ≤ p.mass E)
    (hpreserve : ∀ y, 0 < p.val y → y ∈ E →
      Feasible D x.1 (embed (sat y))) :
    1 - δ ≤ coverage (coverageMatrix (D := D) embed) (p.map sat) x := by
  classical
  let F : Finset S := Finset.univ.filter
    (fun s => Feasible D x.1 (embed s))
  have hmap : p.mass E ≤ (p.map sat).mass F := by
    apply Law.mass_map_ge p sat E F
    intro y hypos hyE
    simpa [F] using hpreserve y hypos hyE
  calc
    1 - δ ≤ p.mass E := hprob
    _ ≤ (p.map sat).mass F := hmap
    _ = coverage (coverageMatrix (D := D) embed) (p.map sat) x := by
      have hF : F = feasibleScheduleEvent (D := D) embed x := by
        ext s
        simp [F, feasibleScheduleEvent]
      rw [coverageMatrix_eq_mass]
      rw [← hF]

private lemma empty_prefix_cap
    {H m B D : ℕ} (hm : m ≤ H) (hmb : m ≤ B)
    (M : Mechanism H m B D) (hcausal : Causal M) :
    ∀ y, 0 < (M.law (emptyInput H m)).val y →
      (tracePrefix (H - m) y).card ≤ B - m := by
  let terminalInput : Input H m :=
    ⟨terminal H m, le_of_eq (terminal_card hm)⟩
  let pref : Trace H → Trace H := tracePrefix (H - m)
  have hprefix_eq : tracePrefix (H - m) terminalInput.1 =
      tracePrefix (H - m) (emptyInput H m).1 := by
    ext a
    simp [terminalInput, emptyInput, mem_prefix, mem_terminal]
  have hmap_eq : (M.law terminalInput).map pref =
      (M.law (emptyInput H m)).map pref := by
    exact hcausal (H - m) (Nat.sub_le H m) terminalInput
      (emptyInput H m) hprefix_eq
  let bad : Finset (Trace H) := Finset.univ.filter
    (fun z => z.card > B - m)
  have hterminal_zero : ((M.law terminalInput).map pref).mass bad = 0 := by
    apply Law.mass_zero_of_support
    intro z hzpos hbad
    obtain ⟨y, hypos, hyeq⟩ :=
      Law.exists_of_map_pos (M.law terminalInput) pref z hzpos
    have hycap := M.support_cap terminalInput y hypos
    have hyfeasible := M.feasible terminalInput y hypos
    have hprefixcap := prefix_card_le_sub_of_terminal_feasible hm hmb hycap hyfeasible
    have hzlarge : z.card > B - m := by simpa [bad] using hbad
    rw [← hyeq] at hzlarge
    have hzlarge' : (tracePrefix (H - m) y).card > B - m := by
      simpa [pref] using hzlarge
    exact (not_lt_of_ge hprefixcap) hzlarge'
  have hempty_zero : ((M.law (emptyInput H m)).map pref).mass bad = 0 := by
    rw [← hmap_eq]
    exact hterminal_zero
  intro y hypos
  by_contra hnot
  have hlarge : B - m < (tracePrefix (H - m) y).card := by omega
  have hbad : pref y ∈ bad := by simp [bad, pref, hlarge]
  have hpoint_zero :=
    (Law.mass_zero_iff ((M.law (emptyInput H m)).map pref) bad).mp
      hempty_zero (pref y) hbad
  have hpoint_pos := Law.map_pos_of_pos (M.law (emptyInput H m)) pref y hypos
  linarith

private lemma off_row_lower
    {H m B D : ℕ} (hm1 : 1 ≤ m) (hB : B ≤ H)
    (M : Mechanism H m B D) (ε δ : ℝ) (hprivacy : Private M ε δ)
    (x : FullInput H m) :
    1 - δ ≤ coverage (offMatrix H m B D)
      ((M.law (emptyInput H m)).map (offSaturator hB)) x := by
  let p0 : Law (Trace H) := M.law (emptyInput H m)
  let sat : Trace H → OffSchedule H B := offSaturator hB
  let E : Finset (Trace H) := feasibleEvent (D := D) x
  have hprob : 1 - δ ≤ p0.mass E := by
    simpa [p0, E] using active_feasible_mass_lower hm1 M ε δ hprivacy x
  have hpreserve : ∀ y, 0 < p0.val y → y ∈ E →
      Feasible D x.1 (sat y).1 := by
    intro y hypos hyE
    have hcap := M.support_cap (emptyInput H m) y hypos
    have hyfeasible : Feasible D x.1 y := by simpa [E, feasibleEvent] using hyE
    have hsateq : sat y = saturateOff y hcap hB := by simp [sat, offSaturator, hcap]
    rw [hsateq]
    exact Feasible.mono_output hyfeasible (saturateOff_subset y hcap hB)
  change 1 - δ ≤ coverage (coverageMatrix (D := D)
    (fun s : OffSchedule H B => s.1)) (p0.map sat) x
  exact coverage_lower_after_map (D := D)
    (fun s : OffSchedule H B => s.1) p0 sat x δ E hprob hpreserve

private lemma on_row_lower
    {H m B D : ℕ} (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (hm1 : 1 ≤ m) (M : Mechanism H m B D) (ε δ : ℝ)
    (hprivacy : Private M ε δ) (hcausal : Causal M) (x : FullInput H m) :
    1 - δ ≤ coverage (onMatrix H m B D)
      ((M.law (emptyInput H m)).map (onSaturator hm hmb hB)) x := by
  let p0 : Law (Trace H) := M.law (emptyInput H m)
  let sat : Trace H → OnSchedule H m B := onSaturator hm hmb hB
  let E : Finset (Trace H) := feasibleEvent (D := D) x
  have hprob : 1 - δ ≤ p0.mass E := by
    simpa [p0, E] using active_feasible_mass_lower hm1 M ε δ hprivacy x
  have hprefix := empty_prefix_cap hm hmb M hcausal
  have hpreserve : ∀ y, 0 < p0.val y → y ∈ E →
      Feasible D x.1 (sat y).1 := by
    intro y hypos hyE
    have hprefixcap := hprefix y (by simpa [p0] using hypos)
    have hyfeasible : Feasible D x.1 y := by simpa [E, feasibleEvent] using hyE
    have hsateq : sat y = saturateOn hm hmb hB y hprefixcap := by
      simp [sat, onSaturator, hprefixcap]
    rw [hsateq]
    exact Feasible.mono_output hyfeasible
      (saturateOn_subset hm hmb hB y hprefixcap)
  change 1 - δ ≤ coverage (coverageMatrix (D := D)
    (fun s : OnSchedule H m B => s.1)) (p0.map sat) x
  exact coverage_lower_after_map (D := D)
    (fun s : OnSchedule H m B => s.1) p0 sat x δ E hprob hpreserve

theorem noncausal_converse_bound
    {H m B D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (M : Mechanism H m B D) (ε δ : ℝ) (hprivacy : Private M ε δ) :
    letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
    letI : Nonempty (OffSchedule H B) := exists_offSchedule H B hB
    1 - value (offMatrix H m B D) ≤ δ := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OffSchedule H B) := exists_offSchedule H B hB
  let q : Law (OffSchedule H B) :=
    (M.law (emptyInput H m)).map (offSaturator hB)
  have hrow : ∀ x : FullInput H m, 1 - δ ≤ coverage (offMatrix H m B D) q x := by
    intro x
    exact off_row_lower hm1 hB M ε δ hprivacy x
  have hworst : 1 - δ ≤ worst (offMatrix H m B D) q := by
    unfold worst
    apply Finset.le_inf' Finset.univ_nonempty
    intro x hx
    exact hrow x
  have hvalue := hworst.trans (worst_le_value (offMatrix H m B D) q)
  linarith

theorem causal_converse_bound
    {H m B D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (M : Mechanism H m B D) (ε δ : ℝ) (hprivacy : Private M ε δ)
    (hcausal : Causal M) :
    letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
    letI : Nonempty (OnSchedule H m B) := exists_onSchedule hm hmb hB
    1 - value (onMatrix H m B D) ≤ δ := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OnSchedule H m B) := exists_onSchedule hm hmb hB
  let q : Law (OnSchedule H m B) :=
    (M.law (emptyInput H m)).map (onSaturator hm hmb hB)
  have hrow : ∀ x : FullInput H m, 1 - δ ≤ coverage (onMatrix H m B D) q x := by
    intro x
    exact on_row_lower hm hmb hB hm1 M ε δ hprivacy hcausal x
  have hworst : 1 - δ ≤ worst (onMatrix H m B D) q := by
    unfold worst
    apply Finset.le_inf' Finset.univ_nonempty
    intro x hx
    exact hrow x
  have hvalue := hworst.trans (worst_le_value (onMatrix H m B D) q)
  linarith

end TrafficShaping
