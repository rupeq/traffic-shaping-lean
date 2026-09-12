import TrafficShaping.NoSavingsBlocks

/-!
  Public Eq. (26) witness for the block-test family.

  `finite_test_union_equation` records the per-test bad-event estimates and
  the support cover, but its final conjunct hides the intermediate union
  mass.  This file exposes the instantiated chain used in the manuscript:

      1 = Q (⋃ᵢ Fᶜᵢ) ≤ ∑ᵢ Q (Fᶜᵢ) ≤ K * δ.

  The tests remain separate inputs; their union is only a union of output
  events under the empty-input law.
-/

namespace TrafficShaping

open scoped BigOperators

private theorem mass_biUnion_le_sum
    {α I : Type*} [Fintype α] [Fintype I] [DecidableEq α]
    (p : Law α) (events : I → Finset α) :
    p.mass (Finset.univ.biUnion events) ≤
      ∑ i : I, p.mass (events i) := by
  classical
  have hpoint : ∀ a : α,
      (if a ∈ Finset.univ.biUnion events then p.val a else 0) ≤
        ∑ i : I, if a ∈ events i then p.val a else 0 := by
    intro a
    by_cases hmem : a ∈ Finset.univ.biUnion events
    · obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp hmem
      have hterm : (if a ∈ events i then p.val a else 0) ≤
          ∑ j : I, if a ∈ events j then p.val a else 0 := by
        refine Finset.single_le_sum
          (f := fun j : I => if a ∈ events j then p.val a else 0) ?_
          (Finset.mem_univ i)
        intro j hj
        by_cases hja : a ∈ events j
        · simp [hja, p.nonneg a]
        · simp [hja]
      simpa [hmem, hai] using hterm
    · simp only [if_neg hmem]
      apply Finset.sum_nonneg
      intro i hi
      split_ifs
      · exact p.nonneg a
      · exact le_rfl
  calc
    p.mass (Finset.univ.biUnion events) =
        ∑ a : α, if a ∈ Finset.univ.biUnion events then p.val a else 0 :=
      p.mass_eq_sum_ite _
    _ ≤ ∑ a : α, ∑ i : I,
        if a ∈ events i then p.val a else 0 := by
      exact Finset.sum_le_sum (fun a _ => hpoint a)
    _ = ∑ i : I, ∑ a : α,
        if a ∈ events i then p.val a else 0 := by
      exact Finset.sum_comm
    _ = ∑ i : I, p.mass (events i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (p.mass_eq_sum_ite (events i)).symm

private theorem mass_biUnion_eq_one_of_support_cover
    {α I : Type*} [Fintype α] [Fintype I] [DecidableEq α]
    (p : Law α) (events : I → Finset α)
    (hcover : ∀ a, 0 < p.val a → ∃ i, a ∈ events i) :
    p.mass (Finset.univ.biUnion events) = 1 := by
  classical
  let U : Finset α := Finset.univ.biUnion events
  have hzero : p.mass Uᶜ = 0 := by
    apply p.mass_zero_of_support
    intro a hpos ha
    have ha' : a ∉ U := by simpa [U] using ha
    obtain ⟨i, hi⟩ := hcover a hpos
    apply ha'
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩
  have hcomp := p.mass_compl U
  rw [hzero] at hcomp
  have hU : p.mass U = 1 := by
    linarith
  simpa [U] using hU

theorem block_noSavings_eq26_chain
    {H m B D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (M : Mechanism H m B D) (ε δ : ℝ)
    (hB : B < perfectBudget H m D)
    (hprivacy : Private M ε δ) :
    let Q : Law (Trace H) := M.law (emptyInput H m)
    let bad : Fin (testBlockCount H m D) → Finset (Trace H) := fun i =>
      (feasibleInputEvent (D := D) (blockTests hm1 hm i))ᶜ
    Q.mass (Finset.univ.biUnion bad) = 1 ∧
      Q.mass (Finset.univ.biUnion bad) ≤
        ∑ i : Fin (testBlockCount H m D), Q.mass (bad i) ∧
      (∑ i : Fin (testBlockCount H m D), Q.mass (bad i)) ≤
        (testBlockCount H m D : ℝ) * δ := by
  classical
  let Q : Law (Trace H) := M.law (emptyInput H m)
  let bad : Fin (testBlockCount H m D) → Finset (Trace H) := fun i =>
    (feasibleInputEvent (D := D) (blockTests hm1 hm i))ᶜ
  have heq := finite_test_union_equation
    (H := H) (m := m) (B := B) (D := D)
    (I := Fin (testBlockCount H m D)) M
    (blockTests hm1 hm) ε δ hprivacy
    (fun i => blockTests_nonempty hm1 hm i)
    (by
      intro y hy
      by_contra hnone
      push Not at hnone
      have hlow := block_tests_lower_bound hm1 hm y hnone
      have hcap := M.cap (emptyInput H m) y hy
      omega)
  have hbad : ∀ i : Fin (testBlockCount H m D), Q.mass (bad i) ≤ δ := by
    intro i
    simpa [Q, bad] using heq.1 i
  have hcover : ∀ y, 0 < Q.val y →
      ∃ i : Fin (testBlockCount H m D), y ∈ bad i := by
    intro y hy
    have hy' : 0 < (M.law (emptyInput H m)).val y := by
      simpa [Q] using hy
    obtain ⟨i, hi⟩ := heq.2.1 y hy'
    exact ⟨i, by simpa [bad] using hi⟩
  have hunion : Q.mass (Finset.univ.biUnion bad) = 1 :=
    mass_biUnion_eq_one_of_support_cover Q bad hcover
  have hsum : (∑ i : Fin (testBlockCount H m D), Q.mass (bad i)) ≤
      (testBlockCount H m D : ℝ) * δ := by
    have hsum' : (∑ i : Fin (testBlockCount H m D), Q.mass (bad i)) ≤
        ∑ i : Fin (testBlockCount H m D), δ :=
      Finset.sum_le_sum (fun i _ => hbad i)
    have hcard : (∑ _i : Fin (testBlockCount H m D), δ) =
        (testBlockCount H m D : ℝ) * δ := by
      simp
    linarith
  exact ⟨hunion, mass_biUnion_le_sum Q bad, hsum⟩

end TrafficShaping
