import TrafficShaping.CertificateHelpers

/-! Complementary finite partitions bound the size of each closed certificate
calculation. Every original row and column remains covered. -/

namespace TrafficShaping

theorem forall_mem_of_partition {α : Type*} [DecidableEq α]
    (s : Finset α) (p q : α → Prop) [DecidablePred p]
    (hyes : ∀ x ∈ s.filter p, q x)
    (hno : ∀ x ∈ s.filter (fun x => ¬ p x), q x) :
    ∀ x ∈ s, q x := by
  intro x hx
  by_cases hp : p x
  · exact hyes x (Finset.mem_filter.mpr ⟨hx, hp⟩)
  · exact hno x (Finset.mem_filter.mpr ⟨hx, hp⟩)

theorem rowsCheckedOnFinset_partition {H m D : ℕ} {S : Type*}
    (rows : Finset (FullInput H m)) (embed : S → Trace H)
    (items : Finset (S × ℕ)) (v : ℕ)
    (p : FullInput H m → Prop) [DecidablePred p]
    (hyes : rowsCheckedOnFinset (m := m) (D := D)
      (rows.filter p) embed items v = true)
    (hno : rowsCheckedOnFinset (m := m) (D := D)
      (rows.filter (fun x => ¬ p x)) embed items v = true) :
    rowsCheckedOnFinset (m := m) (D := D) rows embed items v = true := by
  unfold rowsCheckedOnFinset
  apply (finiteChecked_true_iff _ _).mpr
  exact forall_mem_of_partition rows p
    (fun x => v ≤ rowCoverNum (D := D) embed items x.1)
    (rowsCheckedOnFinset_sound _ embed items v hyes)
    (rowsCheckedOnFinset_sound _ embed items v hno)

theorem colsCheckedOnFinset_partition {H m D : ℕ} {S : Type*} [DecidableEq S]
    (cols : Finset S) (embed : S → Trace H)
    (items : Finset (FullInput H m × ℕ)) (v : ℕ)
    (p : S → Prop) [DecidablePred p]
    (hyes : colsCheckedOnFinset (m := m) (D := D)
      (cols.filter p) embed items v = true)
    (hno : colsCheckedOnFinset (m := m) (D := D)
      (cols.filter (fun x => ¬ p x)) embed items v = true) :
    colsCheckedOnFinset (m := m) (D := D) cols embed items v = true := by
  unfold colsCheckedOnFinset
  apply (finiteChecked_true_iff _ _).mpr
  exact forall_mem_of_partition cols p
    (fun x => colCoverNum (D := D) embed items x ≤ v)
    (colsCheckedOnFinset_sound _ embed items v hyes)
    (colsCheckedOnFinset_sound _ embed items v hno)

end TrafficShaping
