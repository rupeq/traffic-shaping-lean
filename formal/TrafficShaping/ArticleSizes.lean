import TrafficShaping.Saturation

/-! Exact row and column counts for the explicit matrix in the article. -/

namespace TrafficShaping

theorem fullInput_card (H m : ℕ) : Fintype.card (FullInput H m) = H.choose m := by
  classical
  let e : FullInput H m ≃ ↥((Finset.univ : Trace H).powersetCard m) :=
    Equiv.subtypeEquivRight (fun x => by simp)
  have h := Fintype.card_congr e
  simpa using h

theorem offSchedule_card (H B : ℕ) : Fintype.card (OffSchedule H B) = H.choose B :=
  fullInput_card H B

theorem onSchedule_card {H m B : ℕ} (hm : m ≤ H) (hmb : m ≤ B) :
    Fintype.card (OnSchedule H m B) = (H - m).choose (B - m) := by
  classical
  let s := ((Finset.univ : Trace H).powersetCard B).filter (terminal H m ⊆ ·)
  let e : OnSchedule H m B ≃ ↥s :=
    Equiv.subtypeEquivRight (fun x => by simp [s])
  have h := Fintype.card_congr e
  have hcard : s.card = (H - m).choose (B - m) := by
    dsimp [s]
    rw [Finset.card_filter_powersetCard_subset _ _ _ (Finset.subset_univ _)]
    · simp [terminal_card hm]
    · simpa [terminal_card hm] using hmb
  simpa only [Fintype.card_coe, hcard] using h

/-- Concrete design-space size quoted after the causal algorithm. -/
theorem onSchedule_card_fifty : Fintype.card (OnSchedule 50 2 10) = 377348994 := by
  rw [onSchedule_card (by omega) (by omega)]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

end TrafficShaping
