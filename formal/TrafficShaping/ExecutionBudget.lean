import TrafficShaping.ExecutionCore
import TrafficShaping.Saturation

/-! The pathwise cap of the concrete queue algorithm. -/

namespace TrafficShaping

/-- Every run of the queue algorithm stays within the hard cap.  In service
mode all later transmissions are real, and the pre-switch base prefix uses
at most `B-m` slots because the base contains the terminal reserve. -/
theorem execute_cap {H m B D : ℕ} (hm : m ≤ H) (hmb : m ≤ B)
    (x : Input H m) (y : OnSchedule H m B) :
    (execute D x.1 y.1).card ≤ B := by
  classical
  let s := executeState D x.1 y.1 H
  change s.output.card ≤ B
  have ho : OutputModeInvariant m y.1 H s :=
    executeState_outputModeInvariant hm le_rfl D x.1 y.1 y.2.2
  have hq : QueueInvariant x.1 H s := executeState_queueInvariant le_rfl D x.1 y.1
  have hserved : s.served ⊆ x.1 := by
    intro a ha
    have hmem : a ∈ s.queue.toFinset ∪ s.served := Finset.mem_union_right _ ha
    rw [hq.2.2.1, prefix_horizon] at hmem
    exact hmem
  have hserved_card : s.served.card ≤ m := (Finset.card_le_card hserved).trans x.2
  cases hs : s.mode with
  | schedule =>
      have hout : s.output = y.1 := by
        simpa [OutputModeInvariant, hs, prefix_horizon] using ho
      rw [hout, y.2.1]
  | service serviceAt =>
      have hmode : serviceAt.val < H - m ∧
          s.output.card ≤ (tracePrefix serviceAt.val y.1).card + s.served.card := by
        simpa [OutputModeInvariant, hs] using ho
      have hpref : tracePrefix serviceAt.val y.1 ⊆ tracePrefix (H - m) y.1 := by
        intro a ha
        simp only [mem_prefix] at ha ⊢
        exact ⟨ha.1, ha.2.trans hmode.1⟩
      have hprefix_card := Finset.card_le_card hpref
      have hpartition := prefix_terminal_card_of_subset hm y.2.2
      rw [terminal_card hm, y.2.1] at hpartition
      omega

end TrafficShaping
