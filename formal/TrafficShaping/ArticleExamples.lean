import TrafficShaping.CorollaryDefinitions
import TrafficShaping.Matching
import TrafficShaping.MatchingComplexity
import TrafficShaping.Execution
import TrafficShaping.ExecutionDelivery
import TrafficShaping.ExecutionCausality
import TrafficShaping.RationalCertificates
import TrafficShaping.InputReduction
import TrafficShaping.Corollary3
import TrafficShaping.BudgetCertificates
import TrafficShaping.ZeroDelay

namespace TrafficShaping

open scoped BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/- The sorted representation used to run the linear matcher on a finite trace. -/
def articleTraceList {H : ℕ} (x : Trace H) : List (Fin H) :=
  (List.finRange H).filter (fun a => decide (a ∈ x))

def articleSortedTrace {H : ℕ} (x : Trace H) : SortedTrace H :=
  ⟨articleTraceList x,
    (List.sortedLT_finRange H).pairwise.filter (fun a => decide (a ∈ x))⟩

/- A structurally recursive wrapper around the scan.  The fuel is the
   horizon, which is enough for every trace in `Fin H`. -/
def articleAdvanceFuel {H D : ℕ} (a : Fin H) : List (Fin H) → Option (List (Fin H))
  | [] => none
  | s :: ys =>
      if h₁ : a.val ≤ s.val then
        if h₂ : s.val ≤ a.val + D then some ys else none
      else articleAdvanceFuel (D := D) a ys

def articleScanFuel {H D : ℕ} : ℕ → List (Fin H) → List (Fin H) → Bool
  | 0, [], _ => true
  | 0, _ :: _, _ => false
  | fuel + 1, [], _ => true
  | fuel + 1, a :: xs, ys =>
      match articleAdvanceFuel (D := D) a ys with
      | some rem => articleScanFuel (D := D) fuel xs rem
      | none => false

lemma articleAdvanceFuel_spec {H D : ℕ} (a : Fin H) (ys : List (Fin H)) :
    (articleAdvanceFuel (D := D) a ys).isSome =
        (advance D a ys).accepted := by
  induction ys with
  | nil => simp [articleAdvanceFuel, advance]
  | cons s ys ih =>
      by_cases h₁ : a.val ≤ s.val
      · by_cases h₂ : s.val ≤ a.val + D
        · simp [articleAdvanceFuel, advance, h₁, h₂]
        · simp [articleAdvanceFuel, advance, h₁, h₂]
      · simp [articleAdvanceFuel, advance, h₁, ih]

lemma articleAdvanceFuel_spec_full {H D : ℕ} (a : Fin H) (ys : List (Fin H))
    (rem : List (Fin H)) :
    articleAdvanceFuel (D := D) a ys = some rem ↔
      (advance D a ys).accepted = true ∧ (advance D a ys).remaining = rem := by
  induction ys with
  | nil => simp [articleAdvanceFuel, advance]
  | cons s ys ih =>
      by_cases h₁ : a.val ≤ s.val
      · by_cases h₂ : s.val ≤ a.val + D
        · simp [articleAdvanceFuel, advance, h₁, h₂]
        · simp [articleAdvanceFuel, advance, h₁, h₂]
      · simp [articleAdvanceFuel, advance, h₁, ih]

lemma articleScanFuel_eq_scanBool {H D : ℕ} :
    ∀ (fuel : ℕ) (xs ys : List (Fin H)), xs.length ≤ fuel →
      articleScanFuel (D := D) fuel xs ys = scanBool D xs ys := by
  intro fuel
  induction fuel with
  | zero =>
      intro xs ys hlen
      have hnil : xs = [] := by simpa using hlen
      subst hnil
      simp [articleScanFuel, scanBool, scan]
  | succ fuel ih =>
      intro xs
      cases xs with
      | nil =>
          intro ys _
          simp [articleScanFuel, scanBool, scan]
      | cons a xs =>
          intro ys hlen
          have hxs : xs.length ≤ fuel := by simp at hlen; omega
          let r := advance D a ys
          cases ha : articleAdvanceFuel (D := D) a ys with
          | none =>
              have hr : r.accepted = false := by
                have hs := articleAdvanceFuel_spec (D := D) a ys
                simpa [ha, r] using hs
              simp [articleScanFuel, scanBool, scan, r, ha, hr]
          | some rem =>
              have hfull := (articleAdvanceFuel_spec_full (D := D) a ys rem).mp ha
              have hr : r.accepted = true := by simpa [r] using hfull.1
              have hrem : r.remaining = rem := by simpa [r] using hfull.2
              simp [articleScanFuel, scanBool, scan, r, ha, hr, hrem,
                ih xs rem hxs]

@[simp] theorem articleSortedTrace_toTrace {H : ℕ} (x : Trace H) :
    (articleSortedTrace x).toTrace = x := by
  simp [articleSortedTrace, articleTraceList, SortedTrace.toTrace]

lemma articleSortedTrace_length_le {H : ℕ} (x : Trace H) :
    (articleSortedTrace x).slots.length ≤ H := by
  simpa [articleSortedTrace, articleTraceList] using
    (List.length_filter_le (fun a : Fin H => decide (a ∈ x)) (List.finRange H))

/-- Executable feasibility test, definitionally independent of finite-set search. -/
def articleScanFeasible (D : ℕ) (x y : Trace H) : Bool :=
  articleScanFuel (D := D) H (articleSortedTrace x).slots (articleSortedTrace y).slots

theorem articleScanFeasible_true_iff {H D : ℕ} (x y : Trace H) :
    articleScanFeasible D x y = true ↔ Feasible D x y := by
  unfold articleScanFeasible
  rw [articleScanFuel_eq_scanBool (D := D) H _ _ (articleSortedTrace_length_le x)]
  rw [scan_true_iff_feasible]
  simp [articleSortedTrace_toTrace]

/-- Coverage counts evaluated by the executable sorted-list matcher. -/
def articleScanRowCoverNum {H D : ℕ} {S : Type*}
    (embed : S → Trace H) (items : Finset (S × ℕ)) (x : Trace H) : ℕ :=
  ∑ p ∈ items, if articleScanFeasible D x (embed p.1) then p.2 else 0

def articleScanColCoverNum {H m D : ℕ} {S : Type*}
    (embed : S → Trace H) (items : Finset (FullInput H m × ℕ)) (s : S) : ℕ :=
  ∑ p ∈ items, if articleScanFeasible D p.1.1 (embed s) then p.2 else 0

def articleScanRowsChecked {H m D : ℕ} [Fintype (FullInput H m)]
    (embed : S → Trace H) (items : Finset (S × ℕ)) (v : ℕ) : Bool :=
  decide (∀ x : FullInput H m, v ≤ articleScanRowCoverNum (D := D) embed items x.1)

def articleScanColsChecked {H m D : ℕ} [Fintype S]
    (embed : S → Trace H) (items : Finset (FullInput H m × ℕ)) (v : ℕ) : Bool :=
  decide (∀ s : S, articleScanColCoverNum (D := D) embed items s ≤ v)

lemma articleScanRowsChecked_sound {H m D : ℕ} {S : Type*}
    [Fintype (FullInput H m)] (embed : S → Trace H)
    (items : Finset (S × ℕ)) (v : ℕ)
    (h : articleScanRowsChecked (m := m) (D := D) embed items v = true) :
    ∀ x : FullInput H m, v ≤ articleScanRowCoverNum (D := D) embed items x.1 := by
  simpa [articleScanRowsChecked] using of_decide_eq_true h

lemma articleScanColsChecked_sound {H m D : ℕ} {S : Type*} [Fintype S]
    (embed : S → Trace H) (items : Finset (FullInput H m × ℕ)) (v : ℕ)
    (h : articleScanColsChecked (m := m) (D := D) embed items v = true) :
    ∀ s : S, articleScanColCoverNum (D := D) embed items s ≤ v := by
  simpa [articleScanColsChecked] using of_decide_eq_true h

lemma coverageMatrix_entry_eq_articleScan {H m D : ℕ} {S : Type*} [Fintype S]
    (embed : S → Trace H) (x : FullInput H m) (s : S) :
    coverageMatrix (D := D) embed x s =
      (if articleScanFeasible D x.1 (embed s) then 1 else 0) := by
  classical
  by_cases h : articleScanFeasible D x.1 (embed s) = true
  · have hf : Feasible D x.1 (embed s) :=
      (articleScanFeasible_true_iff (D := D) x.1 (embed s)).mp h
    simp [coverageMatrix, h, hf]
  · have hf : ¬Feasible D x.1 (embed s) := by
      intro hf
      exact h ((articleScanFeasible_true_iff (D := D) x.1 (embed s)).mpr hf)
    simp [coverageMatrix, h, hf]

lemma articleSparse_row_coverage {H m D : ℕ} {S : Type*} [Fintype S]
    [DecidableEq S] (embed : S → Trace H)
    (items : Finset (S × ℕ)) (scale : ℕ) (hscale : 0 < scale)
    (x : FullInput H m) (hitems : (∑ p ∈ items, p.2) = scale) :
    coverage (coverageMatrix (D := D) embed)
        (sparseLaw items scale hitems hscale) x =
      (articleScanRowCoverNum (D := D) embed items x.1 : ℝ) / (scale : ℝ) := by
  classical
  unfold coverage
  change (∑ s, sparseWeight items s / (scale : ℝ) *
      coverageMatrix (D := D) embed x s) = _
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  rw [sparse_dot]
  simp_rw [coverageMatrix_entry_eq_articleScan]
  have hnum :
      (∑ p ∈ items, (p.2 : ℝ) *
          (if articleScanFeasible D x.1 (embed p.1) then 1 else 0)) =
        ((∑ p ∈ items, if articleScanFeasible D x.1 (embed p.1) then p.2 else 0 : ℕ) : ℝ) :=
    sparse_dot_bool_indicator items (fun s => articleScanFeasible D x.1 (embed s))
  rw [hnum]
  unfold articleScanRowCoverNum
  rfl

lemma articleSparse_col_coverage {H m D : ℕ} {S : Type*} [Fintype S]
    [DecidableEq S] (embed : S → Trace H)
    (items : Finset (FullInput H m × ℕ)) (scale : ℕ) (hscale : 0 < scale)
    (s : S) (hitems : (∑ p ∈ items, p.2) = scale) :
    (∑ x : FullInput H m,
      ((sparseLaw items scale hitems hscale).val x) *
        coverageMatrix (D := D) embed x s) =
      (articleScanColCoverNum (D := D) embed items s : ℝ) / (scale : ℝ) := by
  classical
  change (∑ x : FullInput H m, sparseWeight items x / (scale : ℝ) *
      coverageMatrix (D := D) embed x s) = _
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  rw [sparse_dot]
  simp_rw [coverageMatrix_entry_eq_articleScan]
  have hnum :
      (∑ p ∈ items, (p.2 : ℝ) *
          (if articleScanFeasible D p.1.1 (embed s) then 1 else 0)) =
        ((∑ p ∈ items, if articleScanFeasible D p.1.1 (embed s) then p.2 else 0 : ℕ) : ℝ) :=
    sparse_dot_bool_indicator items (fun x => articleScanFeasible D x.1 (embed s))
  rw [hnum]
  unfold articleScanColCoverNum
  rfl

lemma article_row_ineq_of_checked {H m D : ℕ} {S : Type*} [Fintype S]
    [DecidableEq S] (embed : S → Trace H)
    (items : Finset (S × ℕ)) (scale v : ℕ) (hscale : 0 < scale)
    (hitems : (∑ p ∈ items, p.2) = scale)
    (hcheck : articleScanRowsChecked (m := m) (D := D) embed items v = true) :
    ∀ x : FullInput H m,
      (v : ℝ) / (scale : ℝ) ≤
        coverage (coverageMatrix (D := D) embed)
          (sparseLaw items scale hitems hscale) x := by
  intro x
  rw [articleSparse_row_coverage embed items scale hscale x hitems]
  have hn := articleScanRowsChecked_sound (m := m) (D := D) embed items v hcheck x
  exact (div_le_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hn)

lemma article_col_ineq_of_checked {H m D : ℕ} {S : Type*} [Fintype S]
    [DecidableEq S] (embed : S → Trace H)
    (items : Finset (FullInput H m × ℕ)) (scale v : ℕ) (hscale : 0 < scale)
    (hitems : (∑ p ∈ items, p.2) = scale)
    (hcheck : articleScanColsChecked (m := m) (D := D) embed items v = true) :
    ∀ s : S,
      (∑ x : FullInput H m,
        ((sparseLaw items scale hitems hscale).val x) *
          coverageMatrix (D := D) embed x s) ≤ (v : ℝ) / (scale : ℝ) := by
  intro s
  rw [articleSparse_col_coverage embed items scale hscale s hitems]
  have hn := articleScanColsChecked_sound (m := m) (D := D) embed items v hcheck s
  exact (div_le_div_iff_of_pos_right (by positivity)).mpr (by exact_mod_cast hn)

/-! ## The three certificates quoted in equation (23) -/

def articleCausalSchedule01100011 : OnSchedule 8 2 4 :=
  ⟨({1, 2, 6, 7} : Trace 8), by decide, by decide⟩

def articleCausalSchedule01001011 : OnSchedule 8 2 4 :=
  ⟨({1, 4, 6, 7} : Trace 8), by decide, by decide⟩

def articleCausalSchedule00011011 : OnSchedule 8 2 4 :=
  ⟨({3, 4, 6, 7} : Trace 8), by decide, by decide⟩

def articleCausalInput11000000 : FullInput 8 2 :=
  ⟨({0, 1} : Trace 8), by decide⟩

def articleCausalInput10010000 : FullInput 8 2 :=
  ⟨({0, 3} : Trace 8), by decide⟩

def articleCausalInput00110000 : FullInput 8 2 :=
  ⟨({2, 3} : Trace 8), by decide⟩

def articleCausalPolicyItems :
    Finset (OnSchedule 8 2 4 × ℕ) :=
  {(articleCausalSchedule01100011, 1),
   (articleCausalSchedule01001011, 1),
   (articleCausalSchedule00011011, 1)}

def articleCausalDualItems :
    Finset (FullInput 8 2 × ℕ) :=
  {(articleCausalInput11000000, 1),
   (articleCausalInput10010000, 1),
   (articleCausalInput00110000, 1)}

theorem articleCausalPolicyItems_sum :
    (∑ p ∈ articleCausalPolicyItems, p.2) = 3 := by decide

theorem articleCausalDualItems_sum :
    (∑ p ∈ articleCausalDualItems, p.2) = 3 := by decide

noncomputable def articleCausalPolicy : Law (OnSchedule 8 2 4) :=
  sparseLaw articleCausalPolicyItems 3 articleCausalPolicyItems_sum (by decide)

noncomputable def articleCausalDual : Law (FullInput 8 2) :=
  sparseLaw articleCausalDualItems 3 articleCausalDualItems_sum (by decide)

theorem articleCausalPolicy_rows :
    articleScanRowsChecked (m := 2) (D := 1)
      (fun s : OnSchedule 8 2 4 => s.1) articleCausalPolicyItems 1 = true := by
  norm_num [articleScanRowsChecked, articleScanRowCoverNum,
    articleScanFeasible, articleSortedTrace, articleTraceList,
    articleScanFuel, articleAdvanceFuel]
  intro a ha
  fin_cases a <;> decide +revert

theorem articleCausalDual_cols :
    articleScanColsChecked (m := 2) (D := 1)
      (fun s : OnSchedule 8 2 4 => s.1) articleCausalDualItems 1 = true := by
  norm_num [articleScanColsChecked, articleScanColCoverNum,
    articleScanFeasible, articleSortedTrace, articleTraceList,
    articleScanFuel, articleAdvanceFuel]
  intro a ha hb
  fin_cases a <;> decide +revert

/-! The corresponding noncausal certificate uses all four-slot traces. -/

def articleNoncausalSchedule11000011 : OffSchedule 8 4 :=
  ⟨({0, 1, 6, 7} : Trace 8), by decide⟩

def articleNoncausalSchedule01101100 : OffSchedule 8 4 :=
  ⟨({1, 2, 4, 5} : Trace 8), by decide⟩

def articleNoncausalSchedule01101001 : OffSchedule 8 4 :=
  ⟨({1, 2, 4, 7} : Trace 8), by decide⟩

def articleNoncausalSchedule01100011 : OffSchedule 8 4 :=
  ⟨({1, 2, 6, 7} : Trace 8), by decide⟩

def articleNoncausalSchedule01011001 : OffSchedule 8 4 :=
  ⟨({1, 3, 4, 7} : Trace 8), by decide⟩

def articleNoncausalSchedule01001011 : OffSchedule 8 4 :=
  ⟨({1, 4, 6, 7} : Trace 8), by decide⟩

def articleNoncausalSchedule00011011 : OffSchedule 8 4 :=
  ⟨({3, 4, 6, 7} : Trace 8), by decide⟩

def articleNoncausalSchedule00010111 : OffSchedule 8 4 :=
  ⟨({3, 5, 6, 7} : Trace 8), by decide⟩

def articleNoncausalInput11000000 : FullInput 8 2 :=
  ⟨({0, 1} : Trace 8), by decide⟩

def articleNoncausalInput01010000 : FullInput 8 2 :=
  ⟨({1, 3} : Trace 8), by decide⟩

def articleNoncausalInput01000001 : FullInput 8 2 :=
  ⟨({1, 7} : Trace 8), by decide⟩

def articleNoncausalInput00011000 : FullInput 8 2 :=
  ⟨({3, 4} : Trace 8), by decide⟩

def articleNoncausalInput00010001 : FullInput 8 2 :=
  ⟨({3, 7} : Trace 8), by decide⟩

def articleNoncausalInput00000011 : FullInput 8 2 :=
  ⟨({6, 7} : Trace 8), by decide⟩

def articleNoncausalPolicyItems : Finset (OffSchedule 8 4 × ℕ) :=
  {(articleNoncausalSchedule11000011, 1),
   (articleNoncausalSchedule01101100, 2),
   (articleNoncausalSchedule01101001, 1),
   (articleNoncausalSchedule01100011, 1),
   (articleNoncausalSchedule01011001, 1),
   (articleNoncausalSchedule01001011, 1),
   (articleNoncausalSchedule00011011, 1),
   (articleNoncausalSchedule00010111, 1)}

def articleNoncausalDualItems : Finset (FullInput 8 2 × ℕ) :=
  {(articleNoncausalInput11000000, 2),
   (articleNoncausalInput01010000, 1),
   (articleNoncausalInput01000001, 1),
   (articleNoncausalInput00011000, 2),
   (articleNoncausalInput00010001, 1),
   (articleNoncausalInput00000011, 2)}

theorem articleNoncausalPolicyItems_sum :
    (∑ p ∈ articleNoncausalPolicyItems, p.2) = 9 := by decide

theorem articleNoncausalDualItems_sum :
    (∑ p ∈ articleNoncausalDualItems, p.2) = 9 := by decide

theorem articleNoncausalPolicy_rows :
    articleScanRowsChecked (m := 2) (D := 1)
      (fun s : OffSchedule 8 4 => s.1) articleNoncausalPolicyItems 5 = true := by
  norm_num [articleScanRowsChecked, articleScanRowCoverNum,
    articleScanFeasible, articleSortedTrace, articleTraceList,
    articleScanFuel, articleAdvanceFuel]
  intro a ha
  fin_cases a <;> decide +revert

theorem articleNoncausalDual_cols :
    articleScanColsChecked (m := 2) (D := 1)
      (fun s : OffSchedule 8 4 => s.1) articleNoncausalDualItems 5 = true := by
  norm_num [articleScanColsChecked, articleScanColCoverNum,
    articleScanFeasible, articleSortedTrace, articleTraceList,
    articleScanFuel, articleAdvanceFuel]
  intro a ha
  fin_cases a <;> decide +revert

theorem articleCausalValue :
    onGameValue 8 2 4 1 (by decide) (by decide) (by decide) = (1 / 3 : ℝ) := by
  let hm : 2 ≤ 8 := by decide
  let hmb : 2 ≤ 4 := by decide
  let hB : 4 ≤ 8 := by decide
  letI : Nonempty (FullInput 8 2) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OnSchedule 8 2 4) := exists_onSchedule hm hmb hB
  let q : Law (OnSchedule 8 2 4) :=
    sparseLaw articleCausalPolicyItems 3 articleCausalPolicyItems_sum (by decide)
  let w : Law (FullInput 8 2) :=
    sparseLaw articleCausalDualItems 3 articleCausalDualItems_sum (by decide)
  have hrow : ∀ x : FullInput 8 2,
      (1 / 3 : ℝ) ≤ coverage (onMatrix 8 2 4 1) q x := by
    simpa [q, onMatrix] using
      (article_row_ineq_of_checked (m := 2) (D := 1)
        (fun s : OnSchedule 8 2 4 => s.1) articleCausalPolicyItems 3 1
        (by decide) articleCausalPolicyItems_sum articleCausalPolicy_rows)
  have hcol : ∀ s : OnSchedule 8 2 4,
      (∑ x : FullInput 8 2, w.val x * onMatrix 8 2 4 1 x s) ≤ (1 / 3 : ℝ) := by
    simpa [w, onMatrix] using
      (article_col_ineq_of_checked (m := 2) (D := 1)
        (fun s : OnSchedule 8 2 4 => s.1) articleCausalDualItems 3 1
        (by decide) articleCausalDualItems_sum articleCausalDual_cols)
  have hm' := matching_certificate (onMatrix 8 2 4 1) q w (1 / 3 : ℝ) hrow hcol
  change value (onMatrix 8 2 4 1) = (1 / 3 : ℝ)
  exact hm'.1

theorem articleNoncausalValue :
    offGameValue 8 2 4 1 (by decide) (by decide) = (5 / 9 : ℝ) := by
  let hm : 2 ≤ 8 := by decide
  let hB : 4 ≤ 8 := by decide
  letI : Nonempty (FullInput 8 2) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OffSchedule 8 4) := exists_offSchedule 8 4 hB
  let q : Law (OffSchedule 8 4) :=
    sparseLaw articleNoncausalPolicyItems 9 articleNoncausalPolicyItems_sum (by decide)
  let w : Law (FullInput 8 2) :=
    sparseLaw articleNoncausalDualItems 9 articleNoncausalDualItems_sum (by decide)
  have hrow : ∀ x : FullInput 8 2,
      (5 / 9 : ℝ) ≤ coverage (offMatrix 8 2 4 1) q x := by
    simpa [q, offMatrix] using
      (article_row_ineq_of_checked (m := 2) (D := 1)
        (fun s : OffSchedule 8 4 => s.1) articleNoncausalPolicyItems 9 5
        (by decide) articleNoncausalPolicyItems_sum articleNoncausalPolicy_rows)
  have hcol : ∀ s : OffSchedule 8 4,
      (∑ x : FullInput 8 2, w.val x * offMatrix 8 2 4 1 x s) ≤ (5 / 9 : ℝ) := by
    simpa [w, offMatrix] using
      (article_col_ineq_of_checked (m := 2) (D := 1)
        (fun s : OffSchedule 8 4 => s.1) articleNoncausalDualItems 9 5
        (by decide) articleNoncausalDualItems_sum articleNoncausalDual_cols)
  have hm' := matching_certificate (offMatrix 8 2 4 1) q w (5 / 9 : ℝ) hrow hcol
  change value (offMatrix 8 2 4 1) = (5 / 9 : ℝ)
  exact hm'.1

theorem articleCausalPolicy_full_rows :
    ∀ x : FullInput 8 2,
      (1 / 3 : ℝ) ≤
        coverage (onMatrix 8 2 4 1) articleCausalPolicy x := by
  let hm : 2 ≤ 8 := by decide
  let hmb : 2 ≤ 4 := by decide
  let hB : 4 ≤ 8 := by decide
  letI : Nonempty (FullInput 8 2) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OnSchedule 8 2 4) := exists_onSchedule hm hmb hB
  simpa [articleCausalPolicy, onMatrix] using
    (article_row_ineq_of_checked (m := 2) (D := 1)
      (fun s : OnSchedule 8 2 4 => s.1) articleCausalPolicyItems 3 1
      (by decide) articleCausalPolicyItems_sum articleCausalPolicy_rows)

theorem articleCausalPolicy_all_inputs :
    ∀ x : Input 8 2,
      (1 / 3 : ℝ) ≤
        articleCausalPolicy.mass
          (inputScheduleEvent (D := 1)
            (fun s : OnSchedule 8 2 4 => s.1) x) := by
  intro x
  apply input_coverage_lower (D := 1) (m := 2) (by decide)
    articleCausalPolicy (fun s : OnSchedule 8 2 4 => s.1) (1 / 3 : ℝ)
  simpa [onMatrix] using articleCausalPolicy_full_rows

theorem articleCausalPolicy_nonempty_inputs :
    ∀ x : Input 8 2, x.1 ≠ ∅ →
      (1 / 3 : ℝ) ≤
        articleCausalPolicy.mass
          (inputScheduleEvent (D := 1)
            (fun s : OnSchedule 8 2 4 => s.1) x) := by
  let hm1 : 1 ≤ 2 := by decide
  let hm : 2 ≤ 8 := by decide
  letI : Nonempty (FullInput 8 2) := ⟨terminalFullInput hm⟩
  apply (full_row_reduction (D := 1) hm1 hm articleCausalPolicy
    (fun s : OnSchedule 8 2 4 => s.1) (1 / 3 : ℝ)).mpr
  simpa [onMatrix] using articleCausalPolicy_full_rows

theorem articleCausalOptimum (ε : ℝ) (hε : 0 ≤ ε) :
    causalOptimum 8 2 4 1 ε = (2 / 3 : ℝ) := by
  rw [causal_optimum_eq (D := 1) (by decide) (by decide) (by decide)
    (by decide) ε hε, articleCausalValue]
  norm_num

theorem articleNoncausalOptimum (ε : ℝ) (hε : 0 ≤ ε) :
    noncausalOptimum 8 2 4 1 ε = (4 / 9 : ℝ) := by
  rw [noncausal_optimum_eq (D := 1) (by decide) (by decide) (by decide)
    (by decide) ε hε, articleNoncausalValue]
  norm_num

theorem articlePerfectPrivacyB6 :
    perfectBudget 8 2 1 = 6 ∧
      noncausalBudget 8 2 1 0 (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) = 6 ∧
      causalBudget 8 2 1 0 (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) = 6 := by
  have h := corollary3_perfect_privacy_budgets (H := 8) (m := 2) (D := 1)
    (by decide) (by decide)
  norm_num [perfectBudget] at h ⊢
  exact h

theorem articlePerfectScheduleB6 :
    perfectSchedule 8 2 1 = ({1, 2, 4, 5, 6, 7} : Trace 8) ∧
      (perfectSchedule 8 2 1).card = 6 ∧
      ∀ x : Trace 8, x.card ≤ 2 →
        Feasible 1 x (perfectSchedule 8 2 1) := by
  refine ⟨by decide, by decide, ?_⟩
  intro x hx
  exact perfectSchedule_feasible (by norm_num) (by norm_num) hx

theorem articleExecute_base :
    execute 1 ({0, 1} : Trace 8) ({1, 2, 6, 7} : Trace 8) =
      ({1, 2, 6, 7} : Trace 8) := by decide

theorem articleExecute_switch :
    execute 1 ({0, 1} : Trace 8) ({3, 4, 6, 7} : Trace 8) =
      ({1, 2} : Trace 8) := by decide

def articleExecute_servicePairs : List (Fin 8 × Fin 8) :=
  [ (⟨0, by decide⟩, ⟨1, by decide⟩),
    (⟨1, by decide⟩, ⟨2, by decide⟩) ]

def articleExecute_servicePairSpec (x y : Trace 8) (p : Fin 8 × Fin 8) : Prop :=
  p.1 ∉ (executeState 1 x y p.2.val).served ∧
    p.1 ∈ (executeState 1 x y (p.2.val + 1)).served

theorem articleExecute_base_servicePairs :
    List.Forall
      (articleExecute_servicePairSpec
        ({0, 1} : Trace 8) ({1, 2, 6, 7} : Trace 8))
      articleExecute_servicePairs := by
  simp only [articleExecute_servicePairs, List.forall_cons]
  unfold articleExecute_servicePairSpec
  decide

theorem articleExecute_switch_servicePairs :
    List.Forall
      (articleExecute_servicePairSpec
        ({0, 1} : Trace 8) ({3, 4, 6, 7} : Trace 8))
      articleExecute_servicePairs := by
  simp only [articleExecute_servicePairs, List.forall_cons]
  unfold articleExecute_servicePairSpec
  decide

theorem articleExecute_switch_first_activation :
    (executeState 1 ({0, 1} : Trace 8) ({3, 4, 6, 7} : Trace 8) 0).mode =
        (.schedule : ExecMode 8) ∧
      (executeState 1 ({0, 1} : Trace 8) ({3, 4, 6, 7} : Trace 8) 1).mode =
        (.schedule : ExecMode 8) ∧
      (executeState 1 ({0, 1} : Trace 8) ({3, 4, 6, 7} : Trace 8) 2).mode =
        (.service ⟨1, by decide⟩ : ExecMode 8) := by decide

theorem articleExecute_base_transmission_card :
    (execute 1 ({0, 1} : Trace 8) ({1, 2, 6, 7} : Trace 8)).card = 4 := by decide

theorem articleExecute_switch_transmission_card :
    (execute 1 ({0, 1} : Trace 8) ({3, 4, 6, 7} : Trace 8)).card = 2 := by decide

/- The strict endpoint in the threshold statement: at equality
   `δ = 1/K = 1/2`, the reserve is `B₀ = K = 2`, while the
   noncausal minimum budget has already dropped to `B = 1`. -/
theorem articleStrictThresholdEndpoint :
    perfectBudget 2 1 0 = 2 ∧
      testBlockCount 2 1 0 = 2 ∧
      1 - offGameValue 2 1 1 0 (by decide) (by decide) = (1 / 2 : ℝ) ∧
      noncausalBudget 2 1 0 (1 / 2 : ℝ)
          (by decide) (by decide) (by norm_num) (by norm_num) = 1 := by
  have hvalue :
      1 - offGameValue 2 1 1 0 (by decide) (by decide) = (1 / 2 : ℝ) := by
    rw [zero_delay_offGameValue (by decide) (by decide) (by decide) (by decide)]
    norm_num
  have hbudget :
      noncausalBudget 2 1 0 (1 / 2 : ℝ)
          (by decide) (by decide) (by norm_num) (by norm_num) = 1 := by
    apply noncausalBudget_eq_of_adjacent_certificates
      (D := 0) (by decide) (by decide) (by decide) (by decide)
      (1 / 2 : ℝ) (by norm_num) (by norm_num)
    · simpa [hvalue]
    · exact Or.inl rfl
  refine ⟨?_, ?_, hvalue, hbudget⟩
  · norm_num [perfectBudget]
  · norm_num [testBlockCount]

end TrafficShaping
