import TrafficShaping.Converse
import TrafficShaping.Achievability

/-!
# Public converse corollaries

This module exposes the two support consequences used in the article.  Eq. 10
is stated for every active admissible input, rather than only for a full input.
Eq. 11 states that a causal mechanism's empty-input law is supported on the
terminal-prefix cap.  The proofs use only the semantic mechanism interface,
privacy, and the prefix-law definition of causality.
-/

open scoped BigOperators

namespace TrafficShaping

/-- The prefix-cardinality event in the article's causal Eq. 11. -/
noncomputable def emptyPrefixCapEvent (H m B : ℕ) : Finset (Trace H) :=
  Finset.univ.filter (fun y => (tracePrefix (H - m) y).card ≤ B - m)

/-! Eq. 10: the empty-input law puts at most `δ` mass outside the outputs
feasible for any active input. -/
theorem eq10_feasible_complement_le_delta
    {H m B D : ℕ} (M : Mechanism H m B D) (ε δ : ℝ)
    (hprivacy : Private M ε δ) (x : Input H m) (hx : x.1 ≠ ∅) :
    (M.law (emptyInput H m)).mass
      (inputFeasibleEvent (D := D) x)ᶜ ≤ δ := by
  classical
  let E : Finset (Trace H) := inputFeasibleEvent (D := D) x
  have hzero : (M.law x).mass Eᶜ = 0 := by
    apply (Law.mass_zero_iff (M.law x) Eᶜ).2
    intro y hybad
    have hynot : ¬ Feasible D x.1 y := by
      simpa [E, inputFeasibleEvent] using (Finset.mem_compl.mp hybad)
    have hnotpos : ¬ 0 < (M.law x).val y := by
      intro hypos
      exact hynot (M.feasible x y hypos)
    exact le_antisymm (le_of_not_gt hnotpos) ((M.law x).nonneg y)
  have hbound := Law.forbidden_event (M.law x)
    (M.law (emptyInput H m)) (hprivacy x hx) Eᶜ hzero
  simpa [E] using hbound

/-! Eq. 11: compare the empty input with the terminal full input at the
prefix `H - m`. -/
theorem eq11_empty_prefix_cap_mass_one
    {H m B D : ℕ} (hm : m ≤ H) (hmb : m ≤ B)
    (M : Mechanism H m B D) (hcausal : Causal M) :
    (M.law (emptyInput H m)).mass (emptyPrefixCapEvent H m B) = 1 := by
  classical
  let terminalInput : Input H m :=
    ⟨terminal H m, le_of_eq (terminal_card hm)⟩
  let pref : Trace H → Trace H := tracePrefix (H - m)
  have hprefix_eq : tracePrefix (H - m) terminalInput.1 =
      tracePrefix (H - m) (emptyInput H m).1 := by
    ext a
    simp [terminalInput, emptyInput, mem_prefix, mem_terminal]
  have hmap_eq : (M.law terminalInput).map pref =
      (M.law (emptyInput H m)).map pref := by
    exact hcausal (H - m) (Nat.sub_le H m) terminalInput
      (emptyInput H m) hprefix_eq
  let E : Finset (Trace H) := emptyPrefixCapEvent H m B
  have hzero : (M.law (emptyInput H m)).mass Eᶜ = 0 := by
    apply Law.mass_zero_of_support
    intro y hypos hybad
    have hybad' : (tracePrefix (H - m) y).card > B - m := by
      simpa [E, emptyPrefixCapEvent] using hybad
    have hmap_pos : 0 <
        ((M.law (emptyInput H m)).map pref).val (pref y) :=
      Law.map_pos_of_pos (M.law (emptyInput H m)) pref y hypos
    have hterminal_map_pos : 0 <
        ((M.law terminalInput).map pref).val (pref y) := by
      rw [hmap_eq]
      exact hmap_pos
    obtain ⟨z, hzpos, hzeq⟩ :=
      Law.exists_of_map_pos (M.law terminalInput) pref (pref y) hterminal_map_pos
    have hcap := M.support_cap terminalInput z hzpos
    have hfeasible := M.feasible terminalInput z hzpos
    have hprefixcap := prefix_card_le_sub_of_terminal_feasible
      hm hmb hcap hfeasible
    have hybad'' : (pref y).card > B - m := by
      simpa [pref] using hybad'
    have hprefixcap' : (pref z).card ≤ B - m := by
      simpa [pref] using hprefixcap
    rw [← hzeq] at hybad''
    exact (not_lt_of_ge hprefixcap') hybad''
  have hcomp := Law.mass_compl (M.law (emptyInput H m)) E
  have hmass : (M.law (emptyInput H m)).mass E = 1 := by
    linarith
  simpa [E] using hmass

end TrafficShaping
