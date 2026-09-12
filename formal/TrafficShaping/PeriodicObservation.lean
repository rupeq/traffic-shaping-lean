import TrafficShaping.Model
import TrafficShaping.Law
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A periodic-intensity observation

The two phases `10001000...` and `01000100...` have the same limiting
one-density, while their finite full-trace laws are disjoint Dirac laws.
This records the observation about the choice of output observation; it is
not a privacy theorem about the traffic-shaping mechanisms.
-/

open scoped BigOperators Topology
open Filter Set

namespace TrafficShaping

/-- The finite prefix of the phase whose one-slots satisfy `t % 4 = phase`. -/
def phaseTrace (phase : Fin 4) (H : ℕ) : Trace H :=
  Finset.univ.filter (fun t : Fin H => t.val % 4 = phase.val)

@[simp] theorem mem_phaseTrace {phase : Fin 4} {H : ℕ} {t : Fin H} :
    t ∈ phaseTrace phase H ↔ t.val % 4 = phase.val := by
  simp [phaseTrace]

/-- The indicator of a one-slot in a periodic phase. -/
def phaseBit (phase : Fin 4) (t : ℕ) : ℕ :=
  if t % 4 = phase.val then 1 else 0

/-- The number of phase-one slots in the prefix `[0,N)`. -/
def phaseCount (phase : Fin 4) (N : ℕ) : ℕ :=
  ∑ t ∈ Finset.range N, phaseBit phase t

/-- The density of the phase-one slots in the first `N` positions. -/
noncomputable def prefixDensity (phase : Fin 4) (N : ℕ) : ℝ :=
  (phaseCount phase N : ℝ) / N

private theorem phaseTrace_card_eq_filter (phase : Fin 4) (H : ℕ) :
    (phaseTrace phase H).card =
      ((Finset.range H).filter (fun t => t % 4 = phase.val)).card := by
  classical
  apply Finset.card_bij (s := phaseTrace phase H)
    (t := (Finset.range H).filter (fun t => t % 4 = phase.val))
    (fun t _ => t.val)
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨t.isLt, (mem_phaseTrace.mp ht)⟩
  · intro t₁ h₁ t₂ h₂ h
    exact Fin.ext h
  · intro b hb
    refine ⟨⟨b, Finset.mem_range.mp (Finset.mem_filter.mp hb).1⟩, ?_, rfl⟩
    exact mem_phaseTrace.mpr (Finset.mem_filter.mp hb).2

theorem phaseTrace_card_eq_count (phase : Fin 4) (H : ℕ) :
    (phaseTrace phase H).card = phaseCount phase H := by
  classical
  rw [phaseTrace_card_eq_filter]
  simp only [phaseCount, phaseBit, Finset.card_eq_sum_ones, Finset.sum_filter]

private theorem phaseCount_block (phase : Fin 4) (n : ℕ) :
    ∑ j ∈ Finset.range 4, phaseBit phase (4 * n + j) = 1 := by
  fin_cases phase <;> norm_num [phaseBit, Nat.add_mod] <;> decide

theorem phaseTrace_card_mul_four (phase : Fin 4) (n : ℕ) :
    (phaseTrace phase (4 * n)).card = n := by
  classical
  rw [phaseTrace_card_eq_count]
  induction n with
  | zero => simp [phaseCount]
  | succ n ih =>
      rw [show 4 * (Nat.succ n) = 4 * n + 4 by omega]
      calc
        phaseCount phase (4 * n + 4) =
            phaseCount phase (4 * n) +
              ∑ j ∈ Finset.range 4, phaseBit phase (4 * n + j) := by
          unfold phaseCount
          rw [Finset.sum_range_add]
        _ = n + 1 := by
          rw [ih, phaseCount_block]

private theorem phaseCount_decomposition (phase : Fin 4) (N : ℕ) :
    phaseCount phase N =
      N / 4 + ∑ j ∈ Finset.range (N % 4), phaseBit phase (4 * (N / 4) + j) := by
  have hN : N = 4 * (N / 4) + N % 4 := by omega
  calc
    phaseCount phase N = phaseCount phase (4 * (N / 4) + N % 4) := by
      exact congrArg (phaseCount phase) hN
    _ =
        phaseCount phase (4 * (N / 4)) +
          ∑ j ∈ Finset.range (N % 4), phaseBit phase (4 * (N / 4) + j) := by
      unfold phaseCount
      rw [Finset.sum_range_add]
    _ = N / 4 + ∑ j ∈ Finset.range (N % 4),
        phaseBit phase (4 * (N / 4) + j) := by
      have hcount : phaseCount phase (4 * (N / 4)) = N / 4 := by
        rw [← phaseTrace_card_eq_count, phaseTrace_card_mul_four]
      rw [hcount]

private theorem phaseCount_bounds (phase : Fin 4) (N : ℕ) :
    N / 4 ≤ phaseCount phase N ∧ phaseCount phase N ≤ N / 4 + 3 := by
  rw [phaseCount_decomposition]
  have hnonneg : 0 ≤ ∑ j ∈ Finset.range (N % 4), phaseBit phase (4 * (N / 4) + j) :=
    Nat.zero_le _
  have hbit : ∀ j, phaseBit phase (4 * (N / 4) + j) ≤ 1 := by
    intro j
    simp only [phaseBit]
    split_ifs <;> norm_num
  have htail :
      ∑ j ∈ Finset.range (N % 4), phaseBit phase (4 * (N / 4) + j) ≤ N % 4 := by
    calc
      ∑ j ∈ Finset.range (N % 4), phaseBit phase (4 * (N / 4) + j) ≤
          ∑ j ∈ Finset.range (N % 4), 1 := by
            exact Finset.sum_le_sum fun j hj => hbit j
      _ = N % 4 := by simp
  have hmod : N % 4 ≤ 3 := by omega
  omega

private theorem phase_density_bounds (phase : Fin 4) (N : ℕ) (hN : 0 < N) :
    ((N : ℝ) - 3) / (4 * N) ≤ prefixDensity phase N ∧
      prefixDensity phase N ≤ ((N : ℝ) + 12) / (4 * N) := by
  have hc := phaseCount_bounds phase N
  have hq : (N : ℝ) / 4 - 3 / 4 ≤ (phaseCount phase N : ℝ) := by
    have hmod : N % 4 ≤ 3 := by omega
    have hdecomp : N = 4 * (N / 4) + N % 4 := by omega
    have hq_nat : N / 4 ≤ phaseCount phase N := hc.1
    have hcast : (N : ℝ) = 4 * ((N / 4 : ℕ) : ℝ) + ((N % 4 : ℕ) : ℝ) := by
      exact_mod_cast hdecomp
    have hmod_real : ((N % 4 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hmod
    have hq_real : ((N / 4 : ℕ) : ℝ) ≤ (phaseCount phase N : ℝ) := by
      exact_mod_cast hq_nat
    linarith
  have hq_upper : (phaseCount phase N : ℝ) ≤ (N : ℝ) / 4 + 3 := by
    have hq_upper_nat : phaseCount phase N ≤ N / 4 + 3 := hc.2
    have hq_upper_cast : (phaseCount phase N : ℝ) ≤ ((N / 4 : ℕ) : ℝ) + 3 := by
      exact_mod_cast hq_upper_nat
    have hdiv_nat : 4 * (N / 4) ≤ N := by omega
    have hdiv_real : 4 * ((N / 4 : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hdiv_nat
    linarith
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  unfold prefixDensity
  constructor
  · apply (le_div_iff₀ hNreal).2
    calc
      ((N : ℝ) - 3) / (4 * N) * N = ((N : ℝ) - 3) / 4 := by
        field_simp [ne_of_gt hNreal]
      _ ≤ (phaseCount phase N : ℝ) := by linarith
  · apply (div_le_iff₀ hNreal).2
    calc
      (phaseCount phase N : ℝ) ≤ ((N : ℝ) + 12) / (4 * N) * N := by
        calc
          (phaseCount phase N : ℝ) ≤ ((N : ℝ) + 12) / 4 := by linarith
          _ = ((N : ℝ) + 12) / (4 * N) * N := by
            field_simp [ne_of_gt hNreal]

theorem tendsto_prefixDensity (phase : Fin 4) :
    Tendsto (prefixDensity phase) atTop (𝓝 (1 / 4 : ℝ)) := by
  have hNinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlower : Tendsto (fun N : ℕ => ((N : ℝ) - 3) / (4 * N)) atTop
      (𝓝 (1 / 4 : ℝ)) := by
    have hbase : Tendsto
        (fun N : ℕ => (1 / 4 : ℝ) - (3 / 4 : ℝ) * (N : ℝ)⁻¹) atTop
        (𝓝 (1 / 4 : ℝ)) := by
      simpa using
        (tendsto_const_nhds.sub (tendsto_const_nhds.mul hNinv) :
          Tendsto (fun N : ℕ => (1 / 4 : ℝ) - (3 / 4 : ℝ) * (N : ℝ)⁻¹)
            atTop (𝓝 ((1 / 4 : ℝ) - (3 / 4 : ℝ) * 0)))
    refine Filter.Tendsto.congr' (l₁ := atTop) ?_ hbase
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    field_simp [ne_of_gt (show (0 : ℝ) < N by exact_mod_cast hN)]
  have hupper : Tendsto (fun N : ℕ => ((N : ℝ) + 12) / (4 * N)) atTop
      (𝓝 (1 / 4 : ℝ)) := by
    have hbase : Tendsto
        (fun N : ℕ => (1 / 4 : ℝ) + (3 : ℝ) * (N : ℝ)⁻¹) atTop
        (𝓝 (1 / 4 : ℝ)) := by
      simpa using
        (tendsto_const_nhds.add (tendsto_const_nhds.mul hNinv) :
          Tendsto (fun N : ℕ => (1 / 4 : ℝ) + (3 : ℝ) * (N : ℝ)⁻¹)
            atTop (𝓝 ((1 / 4 : ℝ) + (3 : ℝ) * 0)))
    refine Filter.Tendsto.congr' (l₁ := atTop) ?_ hbase
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    field_simp [ne_of_gt (show (0 : ℝ) < N by exact_mod_cast hN)]
    norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact (phase_density_bounds phase N hN).1
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact (phase_density_bounds phase N hN).2

theorem phase_zero_density :
    Tendsto (prefixDensity (0 : Fin 4)) atTop (𝓝 (1 / 4 : ℝ)) :=
  tendsto_prefixDensity 0

theorem phase_one_density :
    Tendsto (prefixDensity (1 : Fin 4)) atTop (𝓝 (1 / 4 : ℝ)) :=
  tendsto_prefixDensity 1

/-- The deterministic output law associated with one periodic phase. -/
def phaseLaw (phase : Fin 4) (H : ℕ) : Law (Trace H) :=
  Law.dirac (phaseTrace phase H)

private theorem phaseTrace_zero_ne_one :
    phaseTrace (0 : Fin 4) 8 ≠ phaseTrace (1 : Fin 4) 8 := by
  intro h
  let t : Fin 8 := ⟨0, by omega⟩
  have ht0 : t ∈ phaseTrace (0 : Fin 4) 8 := by
    simp [t, phaseTrace]
  have ht1 : t ∉ phaseTrace (1 : Fin 4) 8 := by
    simp [t, phaseTrace]
  exact ht1 (h ▸ ht0)

theorem phase_laws_tv_one :
    (phaseLaw (0 : Fin 4) 8).tv (phaseLaw (1 : Fin 4) 8) = 1 := by
  classical
  let a : Trace 8 := phaseTrace (0 : Fin 4) 8
  let b : Trace 8 := phaseTrace (1 : Fin 4) 8
  have hab : a ≠ b := by
    simpa [a, b] using phaseTrace_zero_ne_one
  have hlower := Law.event_difference_le_tv (phaseLaw (0 : Fin 4) 8)
    (phaseLaw (1 : Fin 4) 8) ({a} : Finset (Trace 8))
  have hmass : (phaseLaw (0 : Fin 4) 8).mass {a} -
      (phaseLaw (1 : Fin 4) 8).mass {a} = 1 := by
    have hba : b ≠ a := Ne.symm hab
    simp [phaseLaw, a, b, Law.mass, Law.dirac_apply, hba]
  rw [hmass] at hlower
  exact le_antisymm (Law.tv_le_one _ _) hlower

end TrafficShaping
