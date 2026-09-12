import TrafficShaping.RationalCertificates
import TrafficShaping.ArticleSizes

namespace TrafficShaping

open scoped BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

def offScheduleEnum (H B : ℕ) : Finset (OffSchedule H B) :=
  cardEnum B (Finset.univ : Finset (Fin H))

lemma offScheduleEnum_eq_univ (H B : ℕ) :
    offScheduleEnum H B = (Finset.univ : Finset (OffSchedule H B)) := by
  apply Finset.eq_univ_of_card
  unfold offScheduleEnum
  rw [card_cardEnum]
  simp [Fintype.card_finset_len]

def onScheduleEnum (H m B : ℕ) : Finset (OnSchedule H m B) :=
  ((Finset.powersetCard B (Finset.univ : Trace H)).filter
      (fun y => terminal H m ⊆ y)).attach.map
    { toFun := fun t =>
        ⟨t.1, ⟨(Finset.mem_powersetCard.mp
            (Finset.mem_filter.mp t.2).1).2,
          (Finset.mem_filter.mp t.2).2⟩⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : OnSchedule H m B => z.1) hab }

lemma onScheduleEnum_eq_univ {H m B : ℕ} (hm : m ≤ H) (hmb : m ≤ B) :
    onScheduleEnum H m B = (Finset.univ : Finset (OnSchedule H m B)) := by
  apply Finset.eq_univ_of_card
  unfold onScheduleEnum
  simp only [Finset.card_map, Finset.card_attach]
  rw [onSchedule_card hm hmb]
  rw [Finset.card_filter_powersetCard_subset _ _ _ (Finset.subset_univ _)]
  · simp [terminal_card hm]
  · simpa [terminal_card hm] using hmb

theorem off_certificate_value
    {H m B D : ℕ} (hm : m ≤ H) (hB : B ≤ H)
    (schedules : Finset (OffSchedule H B × ℕ)) (scale : ℕ)
    (hsum : (∑ p ∈ schedules, p.2) = scale) (hscale : 0 < scale)
    (v : ℕ)
    (inputs : Finset (FullInput H m × ℕ))
    (isum : (∑ p ∈ inputs, p.2) = scale)
    (rows : Finset (FullInput H m))
    (hrows : rows = (Finset.univ : Finset (FullInput H m)))
    (hrow : rowsCheckedOnFinset (m := m) (D := D) rows
      (fun s : OffSchedule H B => s.1) schedules v = true)
    (cols : Finset (OffSchedule H B))
    (hcols : cols = (Finset.univ : Finset (OffSchedule H B)))
    (hcol : colsCheckedOnFinset (m := m) (D := D) cols
      (fun s : OffSchedule H B => s.1) inputs v = true) :
    offGameValue H m B D hm hB = (v : ℝ) / (scale : ℝ) := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OffSchedule H B) := exists_offSchedule H B hB
  let q : Law (OffSchedule H B) := sparseLaw schedules scale hsum hscale
  let w : Law (FullInput H m) := sparseLaw inputs scale isum hscale
  have hr : ∀ x : FullInput H m,
      (v : ℝ) / scale ≤ coverage (offMatrix H m B D) q x := by
    simpa [q, offMatrix] using
      (row_ineq_of_finset_checked (m := m) (D := D) rows
        (fun s : OffSchedule H B => s.1) schedules scale v hscale hsum hrows hrow)
  have hc : ∀ s : OffSchedule H B,
      (∑ x : FullInput H m, w.val x * offMatrix H m B D x s) ≤
        (v : ℝ) / scale := by
    simpa [w, offMatrix] using
      (col_ineq_of_finset_checked (m := m) (D := D) cols
        (fun s : OffSchedule H B => s.1) inputs scale v hscale isum hcols hcol)
  have hmcert := matching_certificate (offMatrix H m B D) q w ((v : ℝ) / scale) hr hc
  have hvalue := hmcert.1
  norm_num [offGameValue] at hvalue ⊢
  exact hvalue

theorem on_certificate_value
    {H m B D : ℕ} (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (schedules : Finset (OnSchedule H m B × ℕ)) (scale : ℕ)
    (hsum : (∑ p ∈ schedules, p.2) = scale) (hscale : 0 < scale)
    (v : ℕ)
    (inputs : Finset (FullInput H m × ℕ))
    (isum : (∑ p ∈ inputs, p.2) = scale)
    (rows : Finset (FullInput H m))
    (hrows : rows = (Finset.univ : Finset (FullInput H m)))
    (hrow : rowsCheckedOnFinset (m := m) (D := D) rows
      (fun s : OnSchedule H m B => s.1) schedules v = true)
    (cols : Finset (OnSchedule H m B))
    (hcols : cols = (Finset.univ : Finset (OnSchedule H m B)))
    (hcol : colsCheckedOnFinset (m := m) (D := D) cols
      (fun s : OnSchedule H m B => s.1) inputs v = true) :
    onGameValue H m B D hm hmb hB = (v : ℝ) / (scale : ℝ) := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OnSchedule H m B) := exists_onSchedule hm hmb hB
  let q : Law (OnSchedule H m B) := sparseLaw schedules scale hsum hscale
  let w : Law (FullInput H m) := sparseLaw inputs scale isum hscale
  have hr : ∀ x : FullInput H m,
      (v : ℝ) / scale ≤ coverage (onMatrix H m B D) q x := by
    simpa [q, onMatrix] using
      (row_ineq_of_finset_checked (m := m) (D := D) rows
        (fun s : OnSchedule H m B => s.1) schedules scale v hscale hsum hrows hrow)
  have hc : ∀ s : OnSchedule H m B,
      (∑ x : FullInput H m, w.val x * onMatrix H m B D x s) ≤
        (v : ℝ) / scale := by
    simpa [w, onMatrix] using
      (col_ineq_of_finset_checked (m := m) (D := D) cols
        (fun s : OnSchedule H m B => s.1) inputs scale v hscale isum hcols hcol)
  have hmcert := matching_certificate (onMatrix H m B D) q w ((v : ℝ) / scale) hr hc
  have hvalue := hmcert.1
  norm_num [onGameValue] at hvalue ⊢
  exact hvalue

end TrafficShaping
