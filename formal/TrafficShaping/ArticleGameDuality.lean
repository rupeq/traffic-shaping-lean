import TrafficShaping.GameDuality
import TrafficShaping.MainTheorem

/-!
# Article-level duality for the off/on coverage games

The generic finite-game API is stated for an arbitrary matrix with explicit
finite and nonempty row and column types.  This module supplies the article's
two matrices and obtains those instances from `1 ≤ m ≤ B ≤ H` inside each
statement.  The optimal primal and dual laws are returned together from the
same saddle-point argument; no rationality claim is made about arbitrary
optimal laws.
-/

open scoped BigOperators

namespace TrafficShaping

/-- The article's noncausal (off-line) game value. -/
noncomputable def v_off (H m B D : ℕ) (hm : m ≤ H) (hB : B ≤ H) : ℝ :=
  offGameValue H m B D hm hB

/-- The article's causal (on-line) game value. -/
noncomputable def v_on (H m B D : ℕ) (hm : m ≤ H) (hmb : m ≤ B)
    (hB : B ≤ H) : ℝ :=
  onGameValue H m B D hm hmb hB

theorem off_strong_duality
    {H m B D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B)
    (hB : B ≤ H) :
    letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
    letI : Nonempty (OffSchedule H B) := exists_offSchedule H B hB
    v_off H m B D hm hB = dualValue (offMatrix H m B D) := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OffSchedule H B) := exists_offSchedule H B hB
  change value (offMatrix H m B D) = dualValue (offMatrix H m B D)
  exact strong_duality (offMatrix H m B D)

theorem on_strong_duality
    {H m B D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B)
    (hB : B ≤ H) :
    letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
    letI : Nonempty (OnSchedule H m B) := exists_onSchedule hm hmb hB
    v_on H m B D hm hmb hB = dualValue (onMatrix H m B D) := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OnSchedule H m B) := exists_onSchedule hm hmb hB
  change value (onMatrix H m B D) = dualValue (onMatrix H m B D)
  exact strong_duality (onMatrix H m B D)

theorem off_exists_strongly_optimal
    {H m B D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B)
    (hB : B ≤ H) :
    letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
    letI : Nonempty (OffSchedule H B) := exists_offSchedule H B hB
    ∃ q : Law (OffSchedule H B), ∃ w : Law (FullInput H m),
      (∀ x, v_off H m B D hm hB ≤
        coverage (offMatrix H m B D) q x) ∧
      (∀ s, ∑ x, (w : FullInput H m → ℝ) x *
        offMatrix H m B D x s ≤ v_off H m B D hm hB) ∧
      worst (offMatrix H m B D) q = v_off H m B D hm hB ∧
      dualWorst (offMatrix H m B D) w = v_off H m B D hm hB := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OffSchedule H B) := exists_offSchedule H B hB
  obtain ⟨q, w, hrow, hcol, hq⟩ :=
    exists_strongly_optimal (offMatrix H m B D)
  have hdual_le : dualWorst (offMatrix H m B D) w ≤
      value (offMatrix H m B D) := by
    unfold dualWorst
    apply Finset.sup'_le
    intro s hs
    exact hcol s
  have hvalue_le : value (offMatrix H m B D) ≤
      dualWorst (offMatrix H m B D) w := by
    apply value_le_of_column_certificate (offMatrix H m B D) w
      (dualWorst (offMatrix H m B D) w)
    intro s
    unfold dualWorst
    exact Finset.le_sup'
      (fun s => ∑ x, (w : FullInput H m → ℝ) x *
        offMatrix H m B D x s) (Finset.mem_univ s)
  refine ⟨q, w, ?_, ?_, ?_, ?_⟩
  · intro x
    change value (offMatrix H m B D) ≤
      coverage (offMatrix H m B D) q x
    exact hrow x
  · intro s
    change (∑ x, (w : FullInput H m → ℝ) x *
        offMatrix H m B D x s) ≤ value (offMatrix H m B D)
    exact hcol s
  · change worst (offMatrix H m B D) q = value (offMatrix H m B D)
    exact hq
  · change dualWorst (offMatrix H m B D) w = value (offMatrix H m B D)
    exact le_antisymm hdual_le hvalue_le

theorem on_exists_strongly_optimal
    {H m B D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B)
    (hB : B ≤ H) :
    letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
    letI : Nonempty (OnSchedule H m B) := exists_onSchedule hm hmb hB
    ∃ q : Law (OnSchedule H m B), ∃ w : Law (FullInput H m),
      (∀ x, v_on H m B D hm hmb hB ≤
        coverage (onMatrix H m B D) q x) ∧
      (∀ s, ∑ x, (w : FullInput H m → ℝ) x *
        onMatrix H m B D x s ≤ v_on H m B D hm hmb hB) ∧
      worst (onMatrix H m B D) q = v_on H m B D hm hmb hB ∧
      dualWorst (onMatrix H m B D) w = v_on H m B D hm hmb hB := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OnSchedule H m B) := exists_onSchedule hm hmb hB
  obtain ⟨q, w, hrow, hcol, hq⟩ :=
    exists_strongly_optimal (onMatrix H m B D)
  have hdual_le : dualWorst (onMatrix H m B D) w ≤
      value (onMatrix H m B D) := by
    unfold dualWorst
    apply Finset.sup'_le
    intro s hs
    exact hcol s
  have hvalue_le : value (onMatrix H m B D) ≤
      dualWorst (onMatrix H m B D) w := by
    apply value_le_of_column_certificate (onMatrix H m B D) w
      (dualWorst (onMatrix H m B D) w)
    intro s
    unfold dualWorst
    exact Finset.le_sup'
      (fun s => ∑ x, (w : FullInput H m → ℝ) x *
        onMatrix H m B D x s) (Finset.mem_univ s)
  refine ⟨q, w, ?_, ?_, ?_, ?_⟩
  · intro x
    change value (onMatrix H m B D) ≤
      coverage (onMatrix H m B D) q x
    exact hrow x
  · intro s
    change (∑ x, (w : FullInput H m → ℝ) x *
        onMatrix H m B D x s) ≤ value (onMatrix H m B D)
    exact hcol s
  · change worst (onMatrix H m B D) q = value (onMatrix H m B D)
    exact hq
  · change dualWorst (onMatrix H m B D) w = value (onMatrix H m B D)
    exact le_antisymm hdual_le hvalue_le

end TrafficShaping
