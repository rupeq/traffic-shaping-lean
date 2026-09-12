import TrafficShaping.Corollary1
import TrafficShaping.ZeroDelay

/-!
# Sharpness for Corollary 1

The zero-delay closed forms identify an instance where the additive budget
bound is attained.  The proof uses the semantic minimum-budget definitions,
so both equalities concern actual admissible mechanisms rather than only the
finite-game expressions.
-/

namespace TrafficShaping

private lemma feasible_zero_subset {H : ℕ} {x y : Trace H}
    (h : Feasible 0 x y) : x ⊆ y := by
  obtain ⟨f, hf, hrel⟩ := h
  intro a ha
  let aa : {b : Fin H // b ∈ x} := ⟨a, ha⟩
  have hlow := (hrel aa).2.1
  have hupp := (hrel aa).2.2
  change a.val ≤ (f aa).val at hlow
  change (f aa).val ≤ a.val + 0 at hupp
  have hfa : (f aa).val = a.val := by omega
  have hfeq : f aa = a := Fin.ext hfa
  have hrel_aa := hrel aa
  rw [hfeq] at hrel_aa
  exact hrel_aa.1

private noncomputable def earlyTrace {H m : ℕ} (h : m ≤ H - m) : Trace H := by
  let e : Fin m ↪ Fin H :=
    ⟨fun i => ⟨i.1, by omega⟩, by
      intro i j hij
      exact Fin.ext (by simpa using congrArg Fin.val hij)⟩
  exact (Finset.univ : Finset (Fin m)).map e

private theorem earlyTrace_card {H m : ℕ} (h : m ≤ H - m) :
    (earlyTrace h).card = m := by
  simp [earlyTrace]

private theorem earlyTrace_lt {H m : ℕ} (h : m ≤ H - m)
    {a : Fin H} (ha : a ∈ earlyTrace h) : a.val < H - m := by
  change a ∈ (Finset.univ : Finset (Fin m)).map (show Fin m ↪ Fin H from
    ⟨fun i => ⟨i.1, by omega⟩, by
      intro i j hij
      exact Fin.ext (by simpa using congrArg Fin.val hij)⟩) at ha
  obtain ⟨i, hi, hia⟩ := Finset.mem_map.mp ha
  have hv : i.val = a.val := by
    have hv0 := congrArg Fin.val hia
    change i.val = a.val at hv0
    exact hv0
  have hi_lt : i.val < H - m := lt_of_lt_of_le i.isLt h
  omega

private theorem onGameValue_zero_of_budget_lt_twice {H m B : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (hBlt : B < 2 * m) (hH2m : 2 * m ≤ H) :
    onGameValue H m B 0 hm hmb hB = 0 := by
  have hsum : m + m ≤ H := by simpa [two_mul] using hH2m
  have hearly : m ≤ H - m := by omega
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OnSchedule H m B) := exists_onSchedule hm hmb hB
  let x : FullInput H m := ⟨earlyTrace hearly, earlyTrace_card hearly⟩
  have hrow : ∀ s : OnSchedule H m B, onMatrix H m B 0 x s = 0 := by
    intro s
    have hnot : ¬ Feasible 0 x.1 s.1 := by
      intro hfeasible
      have hsub := feasible_zero_subset hfeasible
      have hxs : x.1 ⊆ tracePrefix (H - m) s.1 := by
        intro a ha
        exact mem_prefix.mpr ⟨hsub ha, earlyTrace_lt hearly ha⟩
      have hcard := Finset.card_le_card hxs
      have hpart := prefix_terminal_card_of_subset hm s.2.2
      have hcard' : m ≤ (tracePrefix (H - m) s.1).card := by
        calc
          m = x.1.card := x.2.symm
          _ ≤ (tracePrefix (H - m) s.1).card := hcard
      rw [terminal_card hm, s.2.1] at hpart
      omega
    unfold onMatrix coverageMatrix
    simp [hnot]
  have hvle : value (onMatrix H m B 0) ≤ 0 := by
    apply csSup_le (Set.range_nonempty (worst (onMatrix H m B 0)))
    rintro z ⟨q, rfl⟩
    have hw : worst (onMatrix H m B 0) q ≤ 0 := by
      unfold worst
      calc
        Finset.univ.inf' Finset.univ_nonempty
            (coverage (onMatrix H m B 0) q) ≤
            coverage (onMatrix H m B 0) q x :=
          Finset.inf'_le _ (Finset.mem_univ x)
        _ = 0 := by
          unfold coverage
          apply Finset.sum_eq_zero
          intro s hs
          rw [hrow]
          simp
    exact hw
  have hvnonneg : 0 ≤ value (onMatrix H m B 0) := by
    apply value_nonneg
    intro i s
    unfold onMatrix coverageMatrix
    split_ifs <;> norm_num
  let hvalue : value (onMatrix H m B 0) = 0 := le_antisymm hvle hvnonneg
  change value (onMatrix H m B 0) = 0
  exact hvalue

private lemma choose_Hm_gt_one {H m : ℕ} (hm1 : 1 ≤ m)
    (hH2m : 2 * m ≤ H) : 1 < Nat.choose H m := by
  have hmono := Nat.choose_mono m (show m + 1 ≤ H by omega)
  change Nat.choose (m + 1) m ≤ Nat.choose H m at hmono
  rw [Nat.choose_succ_self_right] at hmono
  omega

private lemma sharp_delta_bounds {H m : ℕ} (hm1 : 1 ≤ m)
    (hH2m : 2 * m ≤ H) :
    let δ : ℝ := 1 - 1 / Nat.choose H m
    0 ≤ δ ∧ δ ≤ 1 := by
  let C : ℝ := Nat.choose H m
  have hC : 1 < C := by
    dsimp [C]
    exact_mod_cast choose_Hm_gt_one hm1 hH2m
  have hCpos : 0 < C := lt_trans (by norm_num) hC
  have hdivpos : 0 < (1 : ℝ) / C := one_div_pos.mpr hCpos
  have hdivle : (1 : ℝ) / C ≤ 1 := by
    apply (div_le_iff₀ hCpos).2
    nlinarith
  dsimp [C]
  constructor <;> linarith

theorem corollary1_sharpness {H m : ℕ} (hm1 : 1 ≤ m)
    (hm : m ≤ H) (hH2m : 2 * m ≤ H) :
    let δ : ℝ := 1 - 1 / Nat.choose H m
    noncausalBudget H m 0 δ hm1 hm (sharp_delta_bounds hm1 hH2m).1
        (sharp_delta_bounds hm1 hH2m).2 = m ∧
    causalBudget H m 0 δ hm1 hm (sharp_delta_bounds hm1 hH2m).1
        (sharp_delta_bounds hm1 hH2m).2 = 2 * m := by
  let δ : ℝ := 1 - 1 / Nat.choose H m
  have hδ := sharp_delta_bounds hm1 hH2m
  have hB2m : 2 * m ≤ H := hH2m
  have hmb2m : m ≤ 2 * m := by omega
  have hoff_threshold :
      1 - offGameValue H m m 0 hm (by omega) ≤ δ := by
    rw [zero_delay_offGameValue hm1 hm le_rfl (by omega)]
    simp [δ, Nat.choose_self]
  have hoff_upper :
      noncausalBudget H m 0 δ hm1 hm hδ.1 hδ.2 ≤ m := by
    exact noncausalBudget_minimal (D := 0) δ hm1 hm le_rfl (by omega)
      hδ.1 hδ.2 hoff_threshold
  have hoff_lower := noncausalBudget_bounds (D := 0) δ hm1 hm hδ.1 hδ.2
  have hoff_eq : noncausalBudget H m 0 δ hm1 hm hδ.1 hδ.2 = m :=
    Nat.le_antisymm hoff_upper hoff_lower.1
  have hchoose_sub_le : Nat.choose (H - m) m ≤ Nat.choose H m := by
    apply Nat.choose_mono
    exact Nat.sub_le H m
  have hchoose_sub_pos : 0 < Nat.choose (H - m) m :=
    Nat.choose_pos (by omega)
  have hrecip :
      (1 : ℝ) / Nat.choose H m ≤ 1 / Nat.choose (H - m) m := by
    apply one_div_le_one_div_of_le
    · exact_mod_cast hchoose_sub_pos
    · exact_mod_cast hchoose_sub_le
  have hon_threshold :
      1 - onGameValue H m (2 * m) 0 hm hmb2m hB2m ≤ δ := by
    have hpad := onGameValue_ge_offGameValue_padded (D := 0) hm1 hm le_rfl
      (by omega : m ≤ H)
    have hoff := zero_delay_offGameValue (H := H) (m := m) (B := m)
      hm1 hm le_rfl hm
    have hoff' : offGameValue H m m 0 hm hm =
        (1 : ℝ) / Nat.choose H m := by
      simpa [Nat.choose_self] using hoff
    have hsum : m + m ≤ H := by simpa [two_mul] using hH2m
    have hpad' :
        (1 : ℝ) / Nat.choose H m ≤
          onGameValue H m (2 * m) 0 hm hmb2m hB2m := by
      calc
        (1 : ℝ) / Nat.choose H m = offGameValue H m m 0 hm hm := hoff'.symm
        _ ≤ onGameValue H m (2 * m) 0 hm hmb2m hB2m := by
          simpa [Nat.min_eq_right hsum, two_mul] using hpad
    dsimp [δ]
    linarith
  have hcausal_upper :
      causalBudget H m 0 δ hm1 hm hδ.1 hδ.2 ≤ 2 * m := by
    exact causalBudget_minimal (D := 0) δ hm1 hm hmb2m hB2m
      hδ.1 hδ.2 hon_threshold
  have hcausal_lower :
      2 * m ≤ causalBudget H m 0 δ hm1 hm hδ.1 hδ.2 := by
    by_contra hnot
    have hlt : causalBudget H m 0 δ hm1 hm hδ.1 hδ.2 < 2 * m :=
      Nat.lt_of_not_ge hnot
    have hspec := causalBudget_spec (D := 0) δ hm1 hm hδ.1 hδ.2
    obtain ⟨hBc, hmbc, hthreshold⟩ := hspec
    have hBcz : causalBudget H m 0 δ hm1 hm hδ.1 hδ.2 - m < m := by
      omega
    have hmin : min m (H - m) = m := by omega
    have hnum :
        Nat.choose
          (causalBudget H m 0 δ hm1 hm hδ.1 hδ.2 - m)
          (min m (H - m)) = 0 := by
      rw [hmin]
      exact Nat.choose_eq_zero_of_lt hBcz
    have hvalue :
        onGameValue H m (causalBudget H m 0 δ hm1 hm hδ.1 hδ.2) 0 hm
          hmbc hBc = 0 :=
      onGameValue_zero_of_budget_lt_twice hm1 hm hmbc hBc hlt hH2m
    rw [hvalue] at hthreshold
    have hCgt : 1 < (Nat.choose H m : ℝ) := by
      exact_mod_cast choose_Hm_gt_one hm1 hH2m
    have hCpos : 0 < (Nat.choose H m : ℝ) := lt_trans (by norm_num) hCgt
    have hdelta_lt : δ < 1 := by
      dsimp [δ]
      have : 0 < (1 : ℝ) / Nat.choose H m := one_div_pos.mpr hCpos
      linarith
    linarith
  exact ⟨hoff_eq, Nat.le_antisymm hcausal_upper hcausal_lower⟩

end TrafficShaping
