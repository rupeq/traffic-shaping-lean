import TrafficShaping.Achievability
import TrafficShaping.OnAchievability
import TrafficShaping.Converse

/-!
# Exact privacy optima

The loss sets quantify over all semantic mechanisms.  Causality, when
required, is equality of output-prefix laws under equal arrival prefixes.
The least-element statements prove both a universal lower bound and actual
attainment; the infimum equalities are consequences.
-/

namespace TrafficShaping

/-- All admissible additive losses for arbitrary finite mechanisms. -/
def noncausalLosses (H m B D : ℕ) (ε : ℝ) : Set ℝ :=
  {δ | 0 ≤ δ ∧ δ ≤ 1 ∧ ∃ M : Mechanism H m B D, Private M ε δ}

/-- All admissible additive losses for arbitrary causal finite mechanisms. -/
def causalLosses (H m B D : ℕ) (ε : ℝ) : Set ℝ :=
  {δ | 0 ≤ δ ∧ δ ≤ 1 ∧ ∃ M : Mechanism H m B D, Causal M ∧ Private M ε δ}

noncomputable def noncausalOptimum (H m B D : ℕ) (ε : ℝ) : ℝ :=
  sInf (noncausalLosses H m B D ε)

noncomputable def causalOptimum (H m B D : ℕ) (ε : ℝ) : ℝ :=
  sInf (causalLosses H m B D ε)

/-- A cap smaller than the admissible workload cannot serve a full input. -/
theorem mechanism_impossible_of_budget_lt {H m B D : ℕ}
    (hm : m ≤ H) (hBm : B < m) : IsEmpty (Mechanism H m B D) := by
  classical
  refine ⟨fun M => ?_⟩
  let x : Input H m := ⟨terminal H m, (terminal_card hm).le⟩
  have hpos : ∃ y, 0 < (M.law x).val y := by
    by_contra hn
    have hz : ∀ y, (M.law x).val y = 0 := by
      intro y
      exact le_antisymm (le_of_not_gt (fun hy => hn ⟨y, hy⟩)) ((M.law x).nonneg y)
    have ht := (M.law x).total
    simp_rw [hz] at ht
    norm_num at ht
  obtain ⟨y, hy⟩ := hpos
  have hf := (M.feasible x y hy).card_le
  have hc := M.cap x y hy
  have hx : x.1.card = m := terminal_card hm
  omega

/-- The proof arguments supply nonempty finite row and column sets. -/
noncomputable def offGameValue (H m B D : ℕ) (hm : m ≤ H) (hB : B ≤ H) : ℝ := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OffSchedule H B) := exists_offSchedule H B hB
  exact value (offMatrix H m B D)

noncomputable def onGameValue (H m B D : ℕ) (hm : m ≤ H) (hmb : m ≤ B)
    (hB : B ≤ H) : ℝ := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OnSchedule H m B) := exists_onSchedule hm hmb hB
  exact value (onMatrix H m B D)

theorem offGameValue_bounds {H m B D : ℕ} (hm : m ≤ H) (hB : B ≤ H) :
    offGameValue H m B D hm hB ∈ Set.Icc (0 : ℝ) 1 := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OffSchedule H B) := exists_offSchedule H B hB
  apply value_mem_Icc
  intro x s
  unfold offMatrix coverageMatrix
  split_ifs <;> constructor <;> norm_num

theorem onGameValue_bounds {H m B D : ℕ} (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H) :
    onGameValue H m B D hm hmb hB ∈ Set.Icc (0 : ℝ) 1 := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OnSchedule H m B) := exists_onSchedule hm hmb hB
  apply value_mem_Icc
  intro x s
  unfold onMatrix coverageMatrix
  split_ifs <;> constructor <;> norm_num

/-- Exact noncausal optimum for every finite nonnegative epsilon. -/
theorem noncausal_optimum_isLeast {H m B D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (ε : ℝ) (hε : 0 ≤ ε) :
    IsLeast (noncausalLosses H m B D ε) (1 - offGameValue H m B D hm hB) := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OffSchedule H B) := exists_offSchedule H B hB
  constructor
  · have hv := offGameValue_bounds (D := D) hm hB
    obtain ⟨M, hM⟩ := noncausal_attainment (D := D) hm hmb hB ε hε
    exact ⟨by linarith [hv.2], by linarith [hv.1], M, hM⟩
  · rintro δ ⟨hδ0, hδ1, M, hM⟩
    exact noncausal_converse_bound hm1 hm hmb hB M ε δ hM

theorem noncausal_optimum_eq {H m B D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (ε : ℝ) (hε : 0 ≤ ε) :
    noncausalOptimum H m B D ε = 1 - offGameValue H m B D hm hB :=
  (noncausal_optimum_isLeast hm1 hm hmb hB ε hε).csInf_eq

theorem noncausal_optimum_epsilon_independent {H m B D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (ε : ℝ) (hε : 0 ≤ ε) :
    noncausalOptimum H m B D ε = noncausalOptimum H m B D 0 := by
  rw [noncausal_optimum_eq hm1 hm hmb hB ε hε,
    noncausal_optimum_eq hm1 hm hmb hB 0 le_rfl]

/-- Exact causal optimum, with both the universal converse and attainment. -/
theorem causal_optimum_isLeast {H m B D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (ε : ℝ) (hε : 0 ≤ ε) :
    IsLeast (causalLosses H m B D ε) (1 - onGameValue H m B D hm hmb hB) := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OnSchedule H m B) := exists_onSchedule hm hmb hB
  have hH : 0 < H := by omega
  constructor
  · have hv := onGameValue_bounds (D := D) hm hmb hB
    obtain ⟨M, hC, hM⟩ := causal_attainment (D := D) hm hH hmb hB ε hε
    exact ⟨by linarith [hv.2], by linarith [hv.1], M, hC, hM⟩
  · rintro δ ⟨hδ0, hδ1, M, hC, hM⟩
    exact causal_converse_bound hm1 hm hmb hB M ε δ hM hC

theorem causal_optimum_eq {H m B D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (ε : ℝ) (hε : 0 ≤ ε) :
    causalOptimum H m B D ε = 1 - onGameValue H m B D hm hmb hB :=
  (causal_optimum_isLeast hm1 hm hmb hB ε hε).csInf_eq

theorem causal_optimum_epsilon_independent {H m B D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (ε : ℝ) (hε : 0 ≤ ε) :
    causalOptimum H m B D ε = causalOptimum H m B D 0 := by
  rw [causal_optimum_eq hm1 hm hmb hB ε hε,
    causal_optimum_eq hm1 hm hmb hB 0 le_rfl]

/-- The two class optima are both attained at epsilon zero. -/
theorem both_optima_attained_at_zero {H m B D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H) :
    IsLeast (noncausalLosses H m B D 0) (1 - offGameValue H m B D hm hB) ∧
    IsLeast (causalLosses H m B D 0) (1 - onGameValue H m B D hm hmb hB) :=
  ⟨noncausal_optimum_isLeast hm1 hm hmb hB 0 le_rfl,
    causal_optimum_isLeast hm1 hm hmb hB 0 le_rfl⟩

end TrafficShaping
