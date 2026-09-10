import TrafficShaping.Model
import TrafficShaping.Law
import TrafficShaping.Game

/-!
# Semantic finite mechanisms

This file gives the broad mechanism interface used by the converse.  A
mechanism is a law on complete binary traces for every admissible input.  Its
support is required to satisfy feasibility and the hard cap; no sampled
policy, state representation, or operational scheduling rule is assumed.
-/

namespace TrafficShaping

structure Mechanism (H m B D : ℕ) where
  law : Input H m → Law (Trace H)
  feasible : ∀ x y, 0 < (law x).val y → Feasible D x.1 y
  support_cap : ∀ x y, 0 < (law x).val y → y.card ≤ B

namespace Mechanism

theorem cap (M : Mechanism H m B D) (x : Input H m) (y : Trace H)
    (hy : 0 < (M.law x).val y) : y.card ≤ B :=
  M.support_cap x y hy

end Mechanism

/-- Causality is equality of the complete output-prefix laws for any two
valid inputs with equal arrival prefixes. -/
def Causal {H m B D : ℕ} (M : Mechanism H m B D) : Prop :=
  ∀ (t : ℕ), t ≤ H → ∀ x x' : Input H m,
    tracePrefix t x.1 = tracePrefix t x'.1 →
      (M.law x).map (tracePrefix t) = (M.law x').map (tracePrefix t)

/-- Two-sided finite-parameter event privacy against the empty input. -/
def Private {H m B D : ℕ} (M : Mechanism H m B D) (ε δ : ℝ) : Prop :=
  ∀ x : Input H m, x.1 ≠ ∅ →
    Law.PrivatePair (M.law x) (M.law (emptyInput H m)) ε δ

/-- The output event of traces feasible for a full input. -/
noncomputable def feasibleEvent {H m D : ℕ} (x : FullInput H m) : Finset (Trace H) := by
  classical
  exact Finset.univ.filter (fun y => Feasible D x.1 y)

/-- Matrix obtained from any finite schedule family embedded into traces. -/
noncomputable def coverageMatrix {H m D : ℕ} {S : Type*} [Fintype S]
    (embed : S → Trace H) : FullInput H m → S → ℝ := by
  classical
  exact fun x s => if Feasible D x.1 (embed s) then 1 else 0

noncomputable def feasibleScheduleEvent {H m D : ℕ} {S : Type*} [Fintype S]
    (embed : S → Trace H) (x : FullInput H m) : Finset S := by
  classical
  exact Finset.univ.filter (fun s => Feasible D x.1 (embed s))

/-- Noncausal schedule matrix: rows are full inputs and columns are exact-cap
output traces. -/
noncomputable def offMatrix (H m B D : ℕ) :
    FullInput H m → OffSchedule H B → ℝ :=
  coverageMatrix (D := D) (fun s : OffSchedule H B => s.1)

/-- Causal schedule matrix: rows are full inputs and columns are exact-cap
traces containing the terminal reserve. -/
noncomputable def onMatrix (H m B D : ℕ) :
    FullInput H m → OnSchedule H m B → ℝ :=
  coverageMatrix (D := D) (fun s : OnSchedule H m B => s.1)

lemma coverageMatrix_eq_mass {H m D : ℕ} {S : Type*} [Fintype S]
    (embed : S → Trace H) (q : Law S) (x : FullInput H m) :
    coverage (coverageMatrix (D := D) embed) q x =
      q.mass (feasibleScheduleEvent (D := D) embed x) := by
  classical
  unfold feasibleScheduleEvent
  rw [Law.mass_filter]
  unfold coverage coverageMatrix
  apply Finset.sum_congr rfl
  intro s hs
  split_ifs with h
  · change q.val s * 1 = q.val s
    simp
  · simp

end TrafficShaping
