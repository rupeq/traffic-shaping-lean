import TrafficShaping.MainTheorem
import TrafficShaping.CertificateMatcher
import TrafficShaping.Mechanism

/-!
# Kernel-checked sparse rational certificates

This module is deliberately independent of any optimizer.  A certificate is
stored as finite sets of natural numerators with one common positive scale.
The two Boolean checks below evaluate the FIFO matcher over every finite row
and column in the kernel; the soundness lemmas turn successful checks into
the real inequalities consumed by `TrafficShaping.matching_certificate`.
-/

namespace TrafficShaping

open scoped BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-! A binary trace uses the manuscript's left-to-right slot convention. -/

def bitTrace (H mask : ℕ) : Trace H :=
  Finset.univ.filter (fun a => mask.testBit (H - 1 - a.val))

@[simp] theorem bitTrace_mem {H mask : ℕ} {a : Fin H} :
    a ∈ bitTrace H mask ↔ mask.testBit (H - 1 - a.val) := by
  simp [bitTrace]

def sparseWeight {S : Type*} [DecidableEq S]
    (items : Finset (S × ℕ)) (s : S) : ℝ :=
  ∑ p ∈ items, if s = p.1 then (p.2 : ℝ) else 0

lemma sparseWeight_sum {S : Type*} [Fintype S] [DecidableEq S]
    (items : Finset (S × ℕ)) :
    (∑ s, sparseWeight items s) = (∑ p ∈ items, (p.2 : ℝ)) := by
  classical
  unfold sparseWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  simp

noncomputable def sparseLaw {S : Type*} [Fintype S] [DecidableEq S]
    (items : Finset (S × ℕ)) (scale : ℕ)
    (hitems : (∑ p ∈ items, p.2) = scale) (hscale : 0 < scale) : Law S :=
  ⟨fun s => sparseWeight items s / (scale : ℝ),
    by
      intro s
      apply div_nonneg
      · apply Finset.sum_nonneg
        intro p hp
        split_ifs <;> positivity
      · positivity,
    by
      rw [← Finset.sum_div, sparseWeight_sum]
      rw [← Nat.cast_sum, hitems]
      exact by field_simp⟩

def rowCoverNum {H D : ℕ} {S : Type*} (embed : S → Trace H)
    (items : Finset (S × ℕ)) (x : Trace H) : ℕ :=
  ∑ p ∈ items, if certificateScanFeasible D x (embed p.1) then p.2 else 0

def colCoverNum {H m D : ℕ} {S : Type*} (embed : S → Trace H)
    (items : Finset (FullInput H m × ℕ)) (s : S) : ℕ :=
  ∑ p ∈ items, if certificateScanFeasible D p.1.1 (embed s) then p.2 else 0

/-! Enumerating `powersetCard` avoids reducing the generic subtype `Fintype`
instance (which is implemented through the full powerset) during certificate
checking. -/

def cardEnum {α : Type*} [DecidableEq α] (k : ℕ) (u : Finset α) :
    Finset {s : Finset α // s.card = k} :=
  (Finset.powersetCard k u).attach.map
    { toFun := fun t =>
        ⟨t.1, (Finset.mem_powersetCard.mp t.2).2⟩
      inj' := by
        intro a b hab
        exact Subtype.ext (congrArg
          (fun z : {s : Finset α // s.card = k} => z.1) hab) }

lemma card_cardEnum {α : Type*} [DecidableEq α] (k : ℕ) (u : Finset α) :
    (cardEnum k u).card = u.card.choose k := by
  unfold cardEnum
  simp [Finset.card_powersetCard]

def fullInputEnum (H m : ℕ) : Finset (FullInput H m) :=
  cardEnum m (Finset.univ : Finset (Fin H))

lemma fullInputEnum_eq_univ (H m : ℕ) :
    fullInputEnum H m = (Finset.univ : Finset (FullInput H m)) := by
  apply Finset.eq_univ_of_card
  unfold fullInputEnum
  rw [card_cardEnum]
  simp [fullInputEnum, Fintype.card_finset_len]

/-- Keep the bounded finite-set decider independent of any ambient `Fintype`.
In particular, a concrete `FullInput H m` must not make Lean enumerate the
generic subtype instance before inspecting the explicitly supplied rows. -/
def finiteChecked {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → Prop) [DecidablePred p] : Bool :=
  decide (∀ x ∈ s, p x)

theorem finiteChecked_true_iff {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → Prop) [DecidablePred p] :
    finiteChecked s p = true ↔ ∀ x ∈ s, p x := by
  simp [finiteChecked]

def rowsChecked {H m D : ℕ} {S : Type*} [Fintype (FullInput H m)]
    (embed : S → Trace H) (items : Finset (S × ℕ)) (v : ℕ) : Bool :=
  decide (∀ x : FullInput H m, v ≤ rowCoverNum (D := D) embed items x.1)

def colsChecked {H m B D : ℕ} {S : Type*} [Fintype S]
    (embed : S → Trace H) (items : Finset (FullInput H m × ℕ)) (v : ℕ) : Bool :=
  decide (∀ s : S, colCoverNum (D := D) embed items s ≤ v)

def rowsCheckedEnum {H m D : ℕ} {S : Type*}
    (embed : S → Trace H) (items : Finset (S × ℕ)) (v : ℕ) : Bool :=
  finiteChecked (fullInputEnum H m)
    (fun x => v ≤ rowCoverNum (D := D) embed items x.1)

/-! A caller may provide an explicit row enumeration.  This is useful for
small certificates: reducing a literal finite set is substantially cheaper
than reducing the generic subtype `Fintype` instance for `FullInput`. -/

def rowsCheckedOnFinset {H m D : ℕ} {S : Type*}
    (rows : Finset (FullInput H m)) (embed : S → Trace H)
    (items : Finset (S × ℕ)) (v : ℕ) : Bool :=
  finiteChecked rows (fun x => v ≤ rowCoverNum (D := D) embed items x.1)

def colsCheckedOnFinset {H m D : ℕ} {S : Type*} [DecidableEq S]
    (schedules : Finset S) (embed : S → Trace H)
    (items : Finset (FullInput H m × ℕ)) (v : ℕ) : Bool :=
  finiteChecked schedules (fun s => colCoverNum (D := D) embed items s ≤ v)

lemma rowsChecked_sound {H m D : ℕ} {S : Type*} [Fintype (FullInput H m)]
    (embed : S → Trace H) (items : Finset (S × ℕ)) (v : ℕ)
    (h : rowsChecked (m := m) (D := D) embed items v = true) :
    ∀ x : FullInput H m, v ≤ rowCoverNum (D := D) embed items x.1 := by
  simpa [rowsChecked] using of_decide_eq_true h

lemma colsChecked_sound {H m B D : ℕ} {S : Type*} [Fintype S]
    (embed : S → Trace H) (items : Finset (FullInput H m × ℕ)) (v : ℕ)
    (h : colsChecked (B := B) (D := D) embed items v = true) :
    ∀ s : S, colCoverNum (D := D) embed items s ≤ v := by
  simpa [colsChecked] using of_decide_eq_true h

lemma rowsCheckedEnum_sound {H m D : ℕ} {S : Type*}
    (embed : S → Trace H) (items : Finset (S × ℕ)) (v : ℕ)
    (h : rowsCheckedEnum (m := m) (D := D) embed items v = true) :
    ∀ x : FullInput H m, v ≤ rowCoverNum (D := D) embed items x.1 := by
  have hh := (finiteChecked_true_iff (fullInputEnum H m)
    (fun x => v ≤ rowCoverNum (D := D) embed items x.1)).mp h
  intro x
  apply hh x
  rw [fullInputEnum_eq_univ]
  exact Finset.mem_univ x

lemma rowsCheckedOnFinset_sound {H m D : ℕ} {S : Type*}
    (rows : Finset (FullInput H m)) (embed : S → Trace H)
    (items : Finset (S × ℕ)) (v : ℕ)
    (h : rowsCheckedOnFinset (m := m) (D := D)
      rows embed items v = true) :
    ∀ x ∈ rows, v ≤ rowCoverNum (D := D) embed items x.1 := by
  exact (finiteChecked_true_iff rows
    (fun x => v ≤ rowCoverNum (D := D) embed items x.1)).mp h

lemma colsCheckedOnFinset_sound {H m D : ℕ} {S : Type*} [DecidableEq S]
    (schedules : Finset S) (embed : S → Trace H)
    (items : Finset (FullInput H m × ℕ)) (v : ℕ)
    (h : colsCheckedOnFinset (m := m) (D := D)
      schedules embed items v = true) :
    ∀ s ∈ schedules, colCoverNum (D := D) embed items s ≤ v := by
  exact (finiteChecked_true_iff schedules
    (fun s => colCoverNum (D := D) embed items s ≤ v)).mp h

lemma sparse_dot {S : Type*} [Fintype S] [DecidableEq S]
    (items : Finset (S × ℕ)) (f : S → ℝ) :
    (∑ s, sparseWeight items s * f s) =
      (∑ p ∈ items, (p.2 : ℝ) * f p.1) := by
  classical
  unfold sparseWeight
  simp_rw [Finset.sum_mul]
  calc
    (∑ s, ∑ p ∈ items, (if s = p.1 then (p.2 : ℝ) else 0) * f s) =
        ∑ p ∈ items, ∑ s, (if s = p.1 then (p.2 : ℝ) else 0) * f s := by
          rw [Finset.sum_comm]
    _ = ∑ p ∈ items, (p.2 : ℝ) * f p.1 := by
      apply Finset.sum_congr rfl
      intro p hp
      simp

lemma sparse_dot_bool_indicator {S : Type*} [Fintype S] [DecidableEq S]
    (items : Finset (S × ℕ)) (P : S → Bool) :
    (∑ p ∈ items, (p.2 : ℝ) * (if P p.1 then 1 else 0)) =
      ((∑ p ∈ items, if P p.1 then p.2 else 0 : ℕ) : ℝ) := by
  simp only [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : P p.1
  · simp [h]
  · simp [h]

lemma coverageMatrix_entry_eq_greedy {H m D : ℕ} {S : Type*} [Fintype S]
    (embed : S → Trace H) (x : FullInput H m) (s : S) :
    coverageMatrix (D := D) embed x s =
      (if certificateScanFeasible D x.1 (embed s) then 1 else 0) := by
  classical
  unfold coverageMatrix
  by_cases h : Feasible D x.1 (embed s)
  · have hg : certificateScanFeasible D x.1 (embed s) = true :=
      (certificateScanFeasible_true_iff _ _).mpr h
    simp [h, hg]
  · have hg : certificateScanFeasible D x.1 (embed s) ≠ true := by
      intro hh
      exact h ((certificateScanFeasible_true_iff _ _).mp hh)
    simp [h, hg]

lemma sparse_row_coverage {H m D : ℕ} {S : Type*} [Fintype S]
    [DecidableEq S] (embed : S → Trace H)
    (items : Finset (S × ℕ)) (scale : ℕ) (hscale : 0 < scale)
    (x : FullInput H m) (hitems : (∑ p ∈ items, p.2) = scale) :
    coverage (coverageMatrix (D := D) embed)
        (sparseLaw items scale hitems hscale) x =
      (rowCoverNum (D := D) embed items x.1 : ℝ) / (scale : ℝ) := by
  classical
  unfold coverage
  change (∑ s, sparseWeight items s / (scale : ℝ) *
      coverageMatrix (D := D) embed x s) = _
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  rw [sparse_dot]
  simp_rw [coverageMatrix_entry_eq_greedy]
  have hnum :
        (∑ p ∈ items, (p.2 : ℝ) *
          (if certificateScanFeasible D x.1 (embed p.1) then 1 else 0)) =
        ((∑ p ∈ items, if certificateScanFeasible D x.1 (embed p.1) then p.2 else 0 : ℕ) : ℝ) :=
    sparse_dot_bool_indicator items (fun s => certificateScanFeasible D x.1 (embed s))
  rw [hnum]
  unfold rowCoverNum
  rfl

lemma sparse_col_coverage {H m D : ℕ} {S : Type*} [Fintype S]
    [DecidableEq S] (embed : S → Trace H)
    (items : Finset (FullInput H m × ℕ)) (scale : ℕ) (hscale : 0 < scale)
    (s : S) (hitems : (∑ p ∈ items, p.2) = scale) :
    (∑ x : FullInput H m,
      ((sparseLaw items scale hitems hscale).val x) *
        coverageMatrix (D := D) embed x s) =
      (colCoverNum (D := D) embed items s : ℝ) / (scale : ℝ) := by
  classical
  change (∑ x : FullInput H m, sparseWeight items x / (scale : ℝ) *
      coverageMatrix (D := D) embed x s) = _
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  rw [sparse_dot]
  simp_rw [coverageMatrix_entry_eq_greedy]
  have hnum :
      (∑ p ∈ items, (p.2 : ℝ) *
          (if certificateScanFeasible D p.1.1 (embed s) then 1 else 0)) =
        ((∑ p ∈ items, if certificateScanFeasible D p.1.1 (embed s) then p.2 else 0 : ℕ) : ℝ) :=
    sparse_dot_bool_indicator items (fun x => certificateScanFeasible D x.1 (embed s))
  rw [hnum]
  unfold colCoverNum
  rfl

lemma row_ineq_of_checked {H m D : ℕ} {S : Type*} [Fintype S]
    [DecidableEq S] (embed : S → Trace H)
    (items : Finset (S × ℕ)) (scale v : ℕ) (hscale : 0 < scale)
    (hitems : (∑ p ∈ items, p.2) = scale)
    (hcheck : rowsChecked (m := m) (D := D) embed items v = true) :
    ∀ x : FullInput H m,
      (v : ℝ) / (scale : ℝ) ≤
        coverage (coverageMatrix (D := D) embed)
          (sparseLaw items scale hitems hscale) x := by
  intro x
  rw [sparse_row_coverage embed items scale hscale x hitems]
  have hn := rowsChecked_sound (m := m) (D := D) embed items v hcheck x
  exact (div_le_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hn)

lemma col_ineq_of_checked {H m B D : ℕ} {S : Type*} [Fintype S]
    [DecidableEq S] (embed : S → Trace H)
    (items : Finset (FullInput H m × ℕ)) (scale v : ℕ) (hscale : 0 < scale)
    (hitems : (∑ p ∈ items, p.2) = scale)
    (hcheck : colsChecked (m := m) (B := B) (D := D) embed items v = true) :
    ∀ s : S,
      (∑ x : FullInput H m,
        ((sparseLaw items scale hitems hscale).val x) *
          coverageMatrix (D := D) embed x s) ≤ (v : ℝ) / (scale : ℝ) := by
  intro s
  rw [sparse_col_coverage embed items scale hscale s hitems]
  have hn := colsChecked_sound (m := m) (B := B) (D := D) embed items v hcheck s
  exact (div_le_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hn)

lemma row_ineq_of_enum_checked {H m D : ℕ} {S : Type*} [Fintype S]
    [DecidableEq S] (embed : S → Trace H)
    (items : Finset (S × ℕ)) (scale v : ℕ) (hscale : 0 < scale)
    (hitems : (∑ p ∈ items, p.2) = scale)
    (hcheck : rowsCheckedEnum (m := m) (D := D) embed items v = true) :
    ∀ x : FullInput H m,
      (v : ℝ) / (scale : ℝ) ≤
        coverage (coverageMatrix (D := D) embed)
          (sparseLaw items scale hitems hscale) x := by
  intro x
  rw [sparse_row_coverage embed items scale hscale x hitems]
  have hn := rowsCheckedEnum_sound (m := m) (D := D) embed items v hcheck x
  exact (div_le_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hn)

lemma row_ineq_of_finset_checked {H m D : ℕ} {S : Type*} [Fintype S]
    [DecidableEq S] (rows : Finset (FullInput H m))
    (embed : S → Trace H) (items : Finset (S × ℕ))
    (scale v : ℕ) (hscale : 0 < scale)
    (hitems : (∑ p ∈ items, p.2) = scale)
    (hcomplete : rows = (Finset.univ : Finset (FullInput H m)))
    (hcheck : rowsCheckedOnFinset (m := m) (D := D)
      rows embed items v = true) :
    ∀ x : FullInput H m,
      (v : ℝ) / (scale : ℝ) ≤
        coverage (coverageMatrix (D := D) embed)
          (sparseLaw items scale hitems hscale) x := by
  intro x
  rw [sparse_row_coverage embed items scale hscale x hitems]
  have hx : x ∈ rows := by simpa [hcomplete]
  have hn := rowsCheckedOnFinset_sound (m := m) (D := D)
    rows embed items v hcheck x hx
  exact (div_le_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hn)

lemma col_ineq_of_finset_checked {H m D : ℕ} {S : Type*} [Fintype S]
    [DecidableEq S] (schedules : Finset S) (embed : S → Trace H)
    (items : Finset (FullInput H m × ℕ)) (scale v : ℕ) (hscale : 0 < scale)
    (hitems : (∑ p ∈ items, p.2) = scale)
    (hcomplete : schedules = Finset.univ)
    (hcheck : colsCheckedOnFinset (m := m) (D := D)
      schedules embed items v = true) :
    ∀ s : S,
      (∑ x : FullInput H m,
        ((sparseLaw items scale hitems hscale).val x) *
          coverageMatrix (D := D) embed x s) ≤ (v : ℝ) / (scale : ℝ) := by
  intro s
  rw [sparse_col_coverage embed items scale hscale s hitems]
  have hn := colsCheckedOnFinset_sound (m := m) (D := D)
    schedules embed items v hcheck s
  have hs : s ∈ schedules := by simpa [hcomplete]
  have hn' := hn hs
  exact (div_le_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hn')

end TrafficShaping
