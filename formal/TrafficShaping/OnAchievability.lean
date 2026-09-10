import TrafficShaping.Achievability
import TrafficShaping.ExecutionBudget
import TrafficShaping.ExecutionCausality
import TrafficShaping.Execution
import TrafficShaping.ExecutionDelivery
import TrafficShaping.ExecutionPreservation

/-! The schedule law is implemented by the concrete causal queue algorithm. -/

namespace TrafficShaping

def onRepair {H m B D : ℕ} (x : Input H m) (y : OnSchedule H m B) : Trace H :=
  execute D x.1 y.1

theorem onRepair_cap {H m B D : ℕ} (hm : m ≤ H) (hmb : m ≤ B)
    (x : Input H m) (y : OnSchedule H m B) :
    (onRepair (D := D) x y).card ≤ B :=
  execute_cap hm hmb x y

theorem onRepair_prefix {H m B D t : ℕ} (ht : t ≤ H)
    (x x' : Input H m) (hprefix : tracePrefix t x.1 = tracePrefix t x'.1)
    (y : OnSchedule H m B) :
    tracePrefix t (onRepair (D := D) x y) = tracePrefix t (onRepair (D := D) x' y) :=
  execute_causal ht D x.1 x'.1 y.1 hprefix

theorem onRepair_empty {H m B D : ℕ} (y : OnSchedule H m B) :
    onRepair (D := D) (emptyInput H m) y = y.1 :=
  execute_empty D y.1

/-- All arrivals are served by the concrete execution, each within its delay
bound.  This combines the actual served-packet invariant with final delivery. -/
theorem onRepair_feasible {H m B D : ℕ} (hm : m ≤ H) (hH : 0 < H)
    (x : Input H m) (y : OnSchedule H m B) :
    Feasible D x.1 (onRepair (D := D) x y) := by
  have hf := executeState_servedFeasible hH le_rfl D x.1 y.1
  rw [executeState_served_eq hm x.2 y.2.2] at hf
  exact hf

noncomputable def onMechanism {H m B D : ℕ} (hm : m ≤ H) (hH : 0 < H)
    (hmb : m ≤ B) (q : Law (OnSchedule H m B)) : Mechanism H m B D :=
  repairMechanism q (onRepair (D := D)) (onRepair_feasible hm hH) (onRepair_cap hm hmb)

theorem onMechanism_causal {H m B D : ℕ} (hm : m ≤ H) (hH : 0 < H)
    (hmb : m ≤ B) (q : Law (OnSchedule H m B)) :
    Causal (onMechanism (D := D) hm hH hmb q) := by
  apply repairMechanism_causal
  intro t ht x x' hx s
  exact onRepair_prefix ht x x' hx s

theorem onRepair_fixes {H m B D : ℕ} (x : Input H m) (y : OnSchedule H m B)
    (h : Feasible D x.1 y.1) : onRepair (D := D) x y = y.1 :=
  execute_eq_of_feasible h

/-- Exact full-trace total variation for the actual causal execution. -/
theorem onMechanism_tv {H m B D : ℕ} (hm : m ≤ H) (hH : 0 < H)
    (hmb : m ≤ B) (q : Law (OnSchedule H m B)) (x : Input H m) :
    ((onMechanism (D := D) hm hH hmb q).law x).tv
      ((onMechanism (D := D) hm hH hmb q).law (emptyInput H m)) =
      1 - q.mass (inputScheduleEvent (D := D) (fun y => y.1) x) := by
  exact repairMechanism_tv q (fun y => y.1) (onRepair (D := D))
    (onRepair_feasible hm hH) (onRepair_cap hm hmb) onRepair_fixes x

theorem onMechanism_private {H m B D : ℕ} (hm : m ≤ H) (hH : 0 < H)
    (hmb : m ≤ B) (q : Law (OnSchedule H m B)) (v : ℝ)
    (hrow : ∀ z : FullInput H m, v ≤ coverage (onMatrix H m B D) q z)
    (ε : ℝ) (hε : 0 ≤ ε) :
    Private (onMechanism (D := D) hm hH hmb q) ε (1 - v) := by
  exact repairMechanism_private hm q (fun y => y.1) (onRepair (D := D))
    (onRepair_feasible hm hH) (onRepair_cap hm hmb) onRepair_fixes v hrow ε hε

/-- A game optimizer is attained by the concrete causal algorithm. -/
theorem causal_attainment {H m B D : ℕ} (hm : m ≤ H) (hH : 0 < H)
    (hmb : m ≤ B) (hB : B ≤ H) (ε : ℝ) (hε : 0 ≤ ε) :
    letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
    letI : Nonempty (OnSchedule H m B) := exists_onSchedule hm hmb hB
    ∃ M : Mechanism H m B D, Causal M ∧ Private M ε (1 - value (onMatrix H m B D)) := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OnSchedule H m B) := exists_onSchedule hm hmb hB
  obtain ⟨q, hq⟩ := value_attained (onMatrix H m B D)
  refine ⟨onMechanism hm hH hmb q, onMechanism_causal hm hH hmb q, ?_⟩
  exact onMechanism_private hm hH hmb q _
    (optimal_coverage_ge_value _ q hq) ε hε

end TrafficShaping
