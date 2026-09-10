import TrafficShaping.Mechanism
import TrafficShaping.Saturation

/-!
# From a schedule law to an attaining mechanism

The general repair lemmas below are intermediate composition results.  Their
feasibility, cap, preservation and causality hypotheses must be discharged by
the concrete repairs: the noncausal fallback in this file and the causal
queue algorithm in `Execution`.
-/

namespace TrafficShaping

variable {H m B D : ℕ} {S : Type*} [Fintype S]

noncomputable def inputFeasibleEvent (x : Input H m) : Finset (Trace H) := by
  classical
  exact Finset.univ.filter (fun y => Feasible D x.1 y)

noncomputable def inputScheduleEvent (embed : S → Trace H) (x : Input H m) :
    Finset S := by
  classical
  exact Finset.univ.filter (fun s => Feasible D x.1 (embed s))

/-- A deterministic same-seed repair induces a valid finite mechanism. -/
noncomputable def repairMechanism (q : Law S) (repair : Input H m → S → Trace H)
    (hfeasible : ∀ x s, Feasible D x.1 (repair x s))
    (hcap : ∀ x s, (repair x s).card ≤ B) : Mechanism H m B D := by
  classical
  exact
    { law := fun x => q.map (repair x)
      feasible := by
        intro x y hy
        obtain ⟨s, hs, rfl⟩ := q.exists_of_map_pos (repair x) y hy
        exact hfeasible x s
      support_cap := by
        intro x y hy
        obtain ⟨s, hs, rfl⟩ := q.exists_of_map_pos (repair x) y hy
        exact hcap x s }

theorem repairMechanism_empty (q : Law S) (embed : S → Trace H)
    (repair : Input H m → S → Trace H)
    (hfeasible : ∀ x s, Feasible D x.1 (repair x s))
    (hcap : ∀ x s, (repair x s).card ≤ B)
    (hfix : ∀ x s, Feasible D x.1 (embed s) → repair x s = embed s) :
    (repairMechanism q repair hfeasible hcap).law (emptyInput H m) = q.map embed := by
  classical
  change q.map (repair (emptyInput H m)) = q.map embed
  have heq : repair (emptyInput H m) = embed := by
    funext s
    exact hfix _ s (feasible_empty D (embed s))
  rw [heq]

/-- Pointwise prefix agreement for each seed gives equality of prefix laws. -/
theorem repairMechanism_causal (q : Law S) (repair : Input H m → S → Trace H)
    (hfeasible : ∀ x s, Feasible D x.1 (repair x s))
    (hcap : ∀ x s, (repair x s).card ≤ B)
    (hprefix : ∀ t, t ≤ H → ∀ x x' : Input H m,
      tracePrefix t x.1 = tracePrefix t x'.1 →
      ∀ s, tracePrefix t (repair x s) = tracePrefix t (repair x' s)) :
    Causal (repairMechanism q repair hfeasible hcap) := by
  classical
  intro t ht x x' hx
  change (q.map (repair x)).map (tracePrefix t) =
    (q.map (repair x')).map (tracePrefix t)
  rw [Law.map_comp, Law.map_comp]
  apply congrArg (fun f : S → Trace H => q.map f)
  funext s
  exact hprefix t ht x x' hx s

/-- Exact total variation, rather than merely an upper coupling bound. -/
theorem repairMechanism_tv (q : Law S) (embed : S → Trace H)
    (repair : Input H m → S → Trace H)
    (hfeasible : ∀ x s, Feasible D x.1 (repair x s))
    (hcap : ∀ x s, (repair x s).card ≤ B)
    (hfix : ∀ x s, Feasible D x.1 (embed s) → repair x s = embed s)
    (x : Input H m) :
    ((repairMechanism q repair hfeasible hcap).law x).tv
      ((repairMechanism q repair hfeasible hcap).law (emptyInput H m)) =
      1 - q.mass (inputScheduleEvent (D := D) embed x) := by
  classical
  rw [repairMechanism_empty q embed repair hfeasible hcap hfix]
  change (q.map (repair x)).tv (q.map embed) = _
  have ht := q.repair_tv_identity embed (repair x) (inputFeasibleEvent (D := D) x)
    (fun s => by simpa [inputFeasibleEvent] using hfeasible x s)
    (fun s hs => hfix x s (by simpa [inputFeasibleEvent] using hs))
  have he : Finset.univ.filter (fun s => embed s ∉ inputFeasibleEvent (D := D) x) =
      (inputScheduleEvent (D := D) embed x)ᶜ := by
    ext s
    simp [inputFeasibleEvent, inputScheduleEvent]
  rw [ht, he, Law.mass_compl]

/-- Coverage of all full inputs implies coverage of every smaller input. -/
theorem input_coverage_lower (hm : m ≤ H) (q : Law S) (embed : S → Trace H)
    (v : ℝ) (hrow : ∀ z : FullInput H m, v ≤ coverage (coverageMatrix (D := D) embed) q z)
    (x : Input H m) : v ≤ q.mass (inputScheduleEvent (D := D) embed x) := by
  classical
  obtain ⟨z, hxz⟩ := exists_fullInput_superset hm x
  have he : feasibleScheduleEvent (D := D) embed z ⊆
      inputScheduleEvent (D := D) embed x := by
    intro s hs
    have hf : Feasible D z.1 (embed s) := by
      simpa [feasibleScheduleEvent] using hs
    simpa [inputScheduleEvent] using hf.mono_input hxz
  calc
    v ≤ coverage (coverageMatrix (D := D) embed) q z := hrow z
    _ = q.mass (feasibleScheduleEvent (D := D) embed z) :=
      coverageMatrix_eq_mass embed q z
    _ ≤ q.mass (inputScheduleEvent (D := D) embed x) := q.mass_mono he

theorem repairMechanism_private (hm : m ≤ H) (q : Law S) (embed : S → Trace H)
    (repair : Input H m → S → Trace H)
    (hfeasible : ∀ x s, Feasible D x.1 (repair x s))
    (hcap : ∀ x s, (repair x s).card ≤ B)
    (hfix : ∀ x s, Feasible D x.1 (embed s) → repair x s = embed s)
    (v : ℝ) (hrow : ∀ z : FullInput H m, v ≤ coverage (coverageMatrix (D := D) embed) q z)
    (ε : ℝ) (hε : 0 ≤ ε) :
    Private (repairMechanism q repair hfeasible hcap) ε (1 - v) := by
  classical
  intro x hx
  apply Law.privatePair_of_tv _ _ hε
  rw [repairMechanism_tv q embed repair hfeasible hcap hfix]
  have hc := input_coverage_lower hm q embed v hrow x
  linarith

/-- Concrete noncausal repair: keep a feasible base, otherwise transmit
exactly at arrival slots.  The latter is always feasible and uses at most m. -/
noncomputable def offRepair (x : Input H m) (y : OffSchedule H B) : Trace H := by
  classical
  exact if Feasible D x.1 y.1 then y.1 else x.1

theorem offRepair_feasible (x : Input H m) (y : OffSchedule H B) :
    Feasible D x.1 (offRepair (D := D) x y) := by
  classical
  unfold offRepair
  split_ifs with h
  · exact h
  · exact feasible_self D x.1

theorem offRepair_cap (hmb : m ≤ B) (x : Input H m) (y : OffSchedule H B) :
    (offRepair (D := D) x y).card ≤ B := by
  classical
  unfold offRepair
  split_ifs
  · exact y.2.le
  · exact x.2.trans hmb

theorem offRepair_fixes (x : Input H m) (y : OffSchedule H B)
    (h : Feasible D x.1 y.1) : offRepair (D := D) x y = y.1 := by
  classical
  simp [offRepair, h]

noncomputable def offMechanism (hmb : m ≤ B) (q : Law (OffSchedule H B)) :
    Mechanism H m B D :=
  repairMechanism q (offRepair (D := D)) offRepair_feasible (offRepair_cap hmb)

theorem offMechanism_private (hm : m ≤ H) (hmb : m ≤ B)
    (q : Law (OffSchedule H B)) (v : ℝ)
    (hrow : ∀ z : FullInput H m, v ≤ coverage (offMatrix H m B D) q z)
    (ε : ℝ) (hε : 0 ≤ ε) : Private (offMechanism (D := D) hmb q) ε (1 - v) := by
  exact repairMechanism_private hm q (fun y => y.1) (offRepair (D := D))
    offRepair_feasible (offRepair_cap hmb) offRepair_fixes v hrow ε hε

/-- An optimizer of the finite noncausal game gives a concrete private
mechanism.  Nonempty witnesses come only from the stated parameter bounds. -/
theorem noncausal_attainment (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (ε : ℝ) (hε : 0 ≤ ε) :
    letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
    letI : Nonempty (OffSchedule H B) := exists_offSchedule H B hB
    ∃ M : Mechanism H m B D, Private M ε (1 - value (offMatrix H m B D)) := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OffSchedule H B) := exists_offSchedule H B hB
  obtain ⟨q, hq⟩ := value_attained (offMatrix H m B D)
  refine ⟨offMechanism hmb q, ?_⟩
  exact offMechanism_private hm hmb q _
    (optimal_coverage_ge_value _ q hq) ε hε

end TrafficShaping
