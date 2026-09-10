import TrafficShaping.ExecutionCore

namespace TrafficShaping

/-!
  Causality of the operational execution rule.

  The proof is deliberately phrased through `executeState`: after `n` calls
  to `step`, the state is a deterministic function of the input prefix of
  length `n`.  The output prefix below `n` is unchanged by all later calls,
  since a call at slot `k` can only insert `k` into the output.
-/

private theorem prefix_succ_mem_iff {n : ℕ} (hn : n < H)
    {x x' : Trace H}
    (hprefix : tracePrefix (n + 1) x = tracePrefix (n + 1) x') :
    ((⟨n, hn⟩ : Fin H) ∈ x) ↔ ((⟨n, hn⟩ : Fin H) ∈ x') := by
  have hmem :
      (⟨n, hn⟩ : Fin H) ∈ tracePrefix (n + 1) x ↔
        (⟨n, hn⟩ : Fin H) ∈ tracePrefix (n + 1) x' := by
    rw [hprefix]
  simpa using hmem

private theorem prefix_of_succ_eq {n : ℕ}
    {x x' : Trace H}
    (hprefix : tracePrefix (n + 1) x = tracePrefix (n + 1) x') :
    tracePrefix n x = tracePrefix n x' := by
  ext a
  constructor
  · intro ha
    have ha_lt : a.val < n := (mem_prefix.mp ha).2
    have ha_succ : a ∈ tracePrefix (n + 1) x := by
      rw [mem_prefix]
      exact ⟨(mem_prefix.mp ha).1, by omega⟩
    rw [hprefix] at ha_succ
    exact mem_prefix.mpr ⟨(mem_prefix.mp ha_succ).1, (mem_prefix.mp ha).2⟩
  · intro ha
    have ha_lt : a.val < n := (mem_prefix.mp ha).2
    have ha_succ : a ∈ tracePrefix (n + 1) x' := by
      rw [mem_prefix]
      exact ⟨(mem_prefix.mp ha).1, by omega⟩
    rw [← hprefix] at ha_succ
    exact mem_prefix.mpr ⟨(mem_prefix.mp ha_succ).1, (mem_prefix.mp ha).2⟩

private theorem step_eq_of_prefix_succ_eq {n : ℕ} (hn : n < H)
    (D : ℕ) (x x' y : Trace H) (s : ExecState H)
    (hprefix : tracePrefix (n + 1) x = tracePrefix (n + 1) x') :
    step D x y ⟨n, hn⟩ s = step D x' y ⟨n, hn⟩ s := by
  have hmem := prefix_succ_mem_iff hn hprefix
  by_cases hx : (⟨n, hn⟩ : Fin H) ∈ x
  · have hx' : (⟨n, hn⟩ : Fin H) ∈ x' := hmem.mp hx
    simp [step, hx, hx']
  · have hx' : (⟨n, hn⟩ : Fin H) ∉ x' := by
      intro h
      exact hx (hmem.mpr h)
    simp [step, hx, hx']

theorem executeState_eq_of_prefix_eq {n : ℕ} (hn : n ≤ H)
    (D : ℕ) (x x' y : Trace H)
    (hprefix : tracePrefix n x = tracePrefix n x') :
    executeState D x y n = executeState D x' y n := by
  induction n generalizing D x x' with
  | zero =>
      rfl
  | succ n ih =>
      have hnlt : n < H := by omega
      have hprefix_n : tracePrefix n x = tracePrefix n x' :=
        prefix_of_succ_eq hprefix
      have hstate : executeState D x y n = executeState D x' y n :=
        ih (by omega) D x x' hprefix_n
      calc
        executeState D x y (n + 1) =
            step D x y ⟨n, hnlt⟩ (executeState D x y n) := by
              simp [executeState, runN, hnlt]
        _ = step D x' y ⟨n, hnlt⟩ (executeState D x' y n) := by
              rw [hstate]
              exact step_eq_of_prefix_succ_eq hnlt D x x' y
                (executeState D x' y n) hprefix
        _ = executeState D x' y (n + 1) := by
              simp [executeState, runN, hnlt]

private theorem step_output_shape_local {n : ℕ} (hn : n < H) (D : ℕ)
    (x y : Trace H) (s : ExecState H) :
    (step D x y ⟨n, hn⟩ s).output = s.output ∨
      (step D x y ⟨n, hn⟩ s).output = insert ⟨n, hn⟩ s.output := by
  classical
  let t : Fin H := ⟨n, hn⟩
  unfold step
  dsimp only
  generalize hq : (if t ∈ x then enqueue s.queue t else s.queue) = q
  cases hm : s.mode with
  | schedule =>
      cases hq' : q with
      | nil =>
          by_cases hty : t ∈ y
          · simp [t, hm, hq', hq, hty]
          · simp [t, hm, hq', hq, hty]
      | cons a qtail =>
          by_cases hswitch : decide (t ∉ y ∧ deadline H D a = t.val) = true
          · simp [t, hm, hq', hq, hswitch]
          · by_cases hty : t ∈ y
            · simp [t, hm, hq', hq, hswitch, hty]
            · by_cases hd : deadline H D a = t.val
              · simp [hty, hd] at hswitch
              · simp [t, hm, hq', hq, hswitch, hty, hd]
  | service serviceAt =>
      cases hq' : q with
      | nil =>
          simp [t, hm, hq', hq]
      | cons a qtail =>
          simp [t, hm, hq', hq]

private theorem tracePrefix_insert_current {n k : ℕ} (hnk : n ≤ k)
    (hk : k < H) (z : Trace H) :
    tracePrefix n (insert (⟨k, hk⟩ : Fin H) z) = tracePrefix n z := by
  have hnot : ¬ ((⟨k, hk⟩ : Fin H).val < n) := by
    simp only [Fin.val_mk]
    omega
  ext a
  by_cases ha : a = (⟨k, hk⟩ : Fin H)
  · subst a
    simp [tracePrefix, hnot]
  · simp [tracePrefix, ha]

private theorem step_output_prefix_stable {n k : ℕ} (hnk : n ≤ k)
    (hk : k < H) (D : ℕ) (x y : Trace H) (s : ExecState H) :
    tracePrefix n (step D x y ⟨k, hk⟩ s).output = tracePrefix n s.output := by
  rcases step_output_shape_local hk D x y s with hsame | hinsert
  · rw [hsame]
  · rw [hinsert]
    exact tracePrefix_insert_current hnk hk s.output

private theorem executeState_output_prefix_stable {n k : ℕ} (hnk : n ≤ k)
    (hk : k ≤ H) (D : ℕ) (x y : Trace H) :
    tracePrefix n (executeState D x y k).output =
      tracePrefix n (executeState D x y n).output := by
  induction k generalizing n D x y with
  | zero =>
      have hn0 : n = 0 := by omega
      subst n
      rfl
  | succ k ih =>
      have hklt : k < H := by omega
      by_cases hnk' : n ≤ k
      · calc
          tracePrefix n (executeState D x y (k + 1)).output =
              tracePrefix n (executeState D x y k).output := by
                simp only [executeState, runN, hklt]
                exact step_output_prefix_stable hnk' hklt D x y
                  (executeState D x y k)
          _ = tracePrefix n (executeState D x y n).output := by
                exact ih hnk' (by omega) D x y
      · have hnk_eq : n = k + 1 := by omega
        subst n
        rfl

private theorem executeState_empty_state {n : ℕ} (hn : n ≤ H)
    (D : ℕ) (y : Trace H) :
    executeState D ∅ y n =
      { queue := [], served := ∅, output := tracePrefix n y,
        mode := (.schedule : ExecMode H) } := by
  induction n with
  | zero =>
      simp [executeState, runN, initialState, tracePrefix_zero]
  | succ n ih =>
      have hnlt : n < H := by omega
      calc
        executeState D ∅ y (n + 1) =
            step D ∅ y ⟨n, hnlt⟩ (executeState D ∅ y n) := by
              simp [executeState, runN, hnlt]
        _ = { queue := [], served := ∅, output := tracePrefix (n + 1) y,
              mode := (.schedule : ExecMode H) } := by
              rw [ih (by omega)]
              by_cases hty : (⟨n, hnlt⟩ : Fin H) ∈ y
              · rw [tracePrefix_succ hnlt y]
                simp [step, hty]
              · rw [tracePrefix_succ hnlt y]
                simp [step, hty]

theorem execute_causal {t : ℕ} (ht : t ≤ H) (D : ℕ)
    (x x' y : Trace H)
    (hprefix : tracePrefix t x = tracePrefix t x') :
    tracePrefix t (execute D x y) = tracePrefix t (execute D x' y) := by
  have hstate : executeState D x y t = executeState D x' y t :=
    executeState_eq_of_prefix_eq ht D x x' y hprefix
  have hstable_x :
      tracePrefix t (execute D x y) =
        tracePrefix t (executeState D x y t).output := by
    simpa [execute] using
      (executeState_output_prefix_stable (H := H) (n := t) (k := H) ht
        (le_rfl) D x y)
  have hstable_x' :
      tracePrefix t (execute D x' y) =
        tracePrefix t (executeState D x' y t).output := by
    simpa [execute] using
      (executeState_output_prefix_stable (H := H) (n := t) (k := H) ht
        (le_rfl) D x' y)
  rw [hstable_x, hstable_x', hstate]

theorem execute_empty (D : ℕ) (y : Trace H) : execute D ∅ y = y := by
  change (executeState D ∅ y H).output = y
  rw [executeState_empty_state (n := H) le_rfl D y]
  exact prefix_horizon y

end TrafficShaping
