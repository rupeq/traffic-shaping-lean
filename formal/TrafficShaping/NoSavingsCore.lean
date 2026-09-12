import TrafficShaping.Mechanism

/-!
# Finite-test lower bounds for additive privacy

This file contains the part of the no-savings argument that only uses the
finite semantic mechanism interface.  A finite family of active inputs gives
one feasible-output event per test.  If every output in the support of the
empty-input law misses at least one of those events, the complements cover
the output alphabet; the finite union bound then forces `1 ≤ |I| * δ`.

The concrete block family and its arithmetic live in later files.  Keeping
the probability argument here avoids any dependency on a particular
achievability construction.
-/

namespace TrafficShaping

open scoped BigOperators

private lemma mass_cover_le_sum
    {α I : Type*} [Fintype α] [Fintype I]
    (p : Law α) (events : I → Finset α)
    (hcover : ∀ a, 0 < p.val a → ∃ i, a ∈ events i) :
    1 ≤ ∑ i : I, p.mass (events i) := by
  classical
  have hpoint : ∀ a : α,
      p.val a ≤ ∑ i : I, if a ∈ events i then p.val a else 0 := by
    intro a
    by_cases hpos : 0 < p.val a
    · obtain ⟨i, hi⟩ := hcover a hpos
      have hterm : (if a ∈ events i then p.val a else 0) ≤
          ∑ j : I, if a ∈ events j then p.val a else 0 := by
        refine Finset.single_le_sum
          (f := fun j : I => if a ∈ events j then p.val a else 0) ?_
          (Finset.mem_univ i)
        intro j hj
        by_cases hja : a ∈ events j
        · simp [hja, p.nonneg a]
        · simp [hja]
      simpa [hi] using hterm
    · have hzero : p.val a = 0 := le_antisymm (le_of_not_gt hpos) (p.nonneg a)
      simp [hzero]
  have hsum : (∑ a : α, p.val a) ≤
      ∑ a : α, ∑ i : I, if a ∈ events i then p.val a else 0 := by
    exact Finset.sum_le_sum (fun a _ => hpoint a)
  have hswap : (∑ a : α, ∑ i : I,
      if a ∈ events i then p.val a else 0) =
      ∑ i : I, ∑ a : α, if a ∈ events i then p.val a else 0 := by
    exact Finset.sum_comm
  have hevents : (∑ i : I, ∑ a : α,
      if a ∈ events i then p.val a else 0) = ∑ i : I, p.mass (events i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (p.mass_eq_sum_ite (events i)).symm
  rw [p.total] at hsum
  rw [hswap, hevents] at hsum
  exact hsum

/-!
The preceding helper has a deliberately simple sum shape, but the public
lemma below is the useful statement: a finite family of events whose
complements cover the positive support has total bad mass at least one.
-/
theorem finite_union_bound
    {α I : Type*} [Fintype α] [Fintype I]
    (p : Law α) (events : I → Finset α)
    (hcover : ∀ a, 0 < p.val a → ∃ i, a ∈ events i)
    {δ : ℝ}
    (hbad : ∀ i, p.mass (events i) ≤ δ) :
    1 ≤ (Fintype.card I : ℝ) * δ := by
  classical
  have hsum : 1 ≤ ∑ i : I, p.mass (events i) := by
    exact mass_cover_le_sum p events hcover
  have hsum' : (∑ i : I, p.mass (events i)) ≤
      ∑ i : I, δ := Finset.sum_le_sum (fun i _ => hbad i)
  have hcard : (∑ _i : I, δ) = (Fintype.card I : ℝ) * δ := by
    simp
  linarith

noncomputable def feasibleInputEvent
    {H m D : ℕ} (x : Input H m) : Finset (Trace H) := by
  classical
  exact Finset.univ.filter (fun y => Feasible D x.1 y)

private lemma active_bad_event_bound
    {H m B D : ℕ} (M : Mechanism H m B D)
    (ε δ : ℝ) (hprivacy : Private M ε δ)
    (x : Input H m) (hx : x.1 ≠ ∅) :
    (M.law (emptyInput H m)).mass
      (feasibleInputEvent (D := D) x)ᶜ ≤ δ := by
  let E : Finset (Trace H) := feasibleInputEvent (D := D) x
  have hzero : (M.law x).mass Eᶜ = 0 := by
    apply (Law.mass_zero_iff (M.law x) Eᶜ).2
    intro y hybad
    have hynot : ¬ Feasible D x.1 y := by
      simpa [E, feasibleInputEvent] using (Finset.mem_compl.mp hybad)
    have hnotpos : ¬ 0 < (M.law x).val y := by
      intro hypos
      exact hynot (M.feasible x y hypos)
    exact le_antisymm (le_of_not_gt hnotpos) ((M.law x).nonneg y)
  exact Law.forbidden_event (M.law x) (M.law (emptyInput H m))
    (hprivacy x hx) Eᶜ hzero

/-! Equation (26), in its generic finite-test form. -/
theorem finite_test_privacy_bound
    {H m B D : ℕ} {I : Type*} [Fintype I]
    (M : Mechanism H m B D) (tests : I → Input H m)
    (ε δ : ℝ) (hprivacy : Private M ε δ)
    (htest_nonempty : ∀ i, (tests i).1 ≠ ∅)
    (hsupport_cover : ∀ y, 0 < (M.law (emptyInput H m)).val y →
      ∃ i, ¬ Feasible D (tests i).1 y) :
    1 ≤ (Fintype.card I : ℝ) * δ := by
  classical
  let p0 : Law (Trace H) := M.law (emptyInput H m)
  let events : I → Finset (Trace H) := fun i =>
    (feasibleInputEvent (D := D) (tests i))ᶜ
  have hcover : ∀ y, 0 < p0.val y → ∃ i, y ∈ events i := by
    intro y hy
    obtain ⟨i, hi⟩ := hsupport_cover y (by simpa [p0] using hy)
    exact ⟨i, by simpa [events, feasibleInputEvent] using hi⟩
  have hbad : ∀ i, p0.mass (events i) ≤ δ := by
    intro i
    simpa [p0, events] using
      (active_bad_event_bound M ε δ hprivacy (tests i) (htest_nonempty i))
  exact finite_union_bound p0 events hcover hbad

/-!
The same argument with its two measurable ingredients exposed.  The first
component is the per-test privacy estimate, the second is the support-cover
condition, and the final component is the union estimate used in (26).
-/
theorem finite_test_union_equation
    {H m B D : ℕ} {I : Type*} [Fintype I]
    (M : Mechanism H m B D) (tests : I → Input H m)
    (ε δ : ℝ) (hprivacy : Private M ε δ)
    (htest_nonempty : ∀ i, (tests i).1 ≠ ∅)
    (hsupport_cover : ∀ y, 0 < (M.law (emptyInput H m)).val y →
      ∃ i, ¬ Feasible D (tests i).1 y) :
    (∀ i, (M.law (emptyInput H m)).mass
      (feasibleInputEvent (D := D) (tests i))ᶜ ≤ δ) ∧
    (∀ y, 0 < (M.law (emptyInput H m)).val y →
      ∃ i, y ∈ (feasibleInputEvent (D := D) (tests i))ᶜ) ∧
    1 ≤ (Fintype.card I : ℝ) * δ := by
  classical
  let p0 : Law (Trace H) := M.law (emptyInput H m)
  let events : I → Finset (Trace H) := fun i =>
    (feasibleInputEvent (D := D) (tests i))ᶜ
  have hbad : ∀ i, p0.mass (events i) ≤ δ := by
    intro i
    simpa [p0, events] using
      (active_bad_event_bound M ε δ hprivacy (tests i) (htest_nonempty i))
  have hcover : ∀ y, 0 < p0.val y → ∃ i, y ∈ events i := by
    intro y hy
    obtain ⟨i, hi⟩ := hsupport_cover y (by simpa [p0] using hy)
    exact ⟨i, by simpa [events, feasibleInputEvent] using hi⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa [p0, events] using hbad i
  · intro y hy
    simpa [p0, events] using hcover y hy
  · exact finite_union_bound p0 events hcover hbad

end TrafficShaping
