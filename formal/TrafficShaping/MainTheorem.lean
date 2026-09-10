import TrafficShaping.Achievability
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

end TrafficShaping
