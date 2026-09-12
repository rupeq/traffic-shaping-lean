import TrafficShaping.MainTheorem
import TrafficShaping.ArticleSizes
import TrafficShaping.UniformSubsets

/-!
# Corollary 4: the zero-delay games

At delay zero a feasible output contains every arrival slot.  The two finite
games can therefore be evaluated by uniform fixed-size subset laws.  The
proofs below keep the game values semantic: `offGameValue` and `onGameValue`
are identified with matching primal/dual certificates for their actual
coverage matrices.
-/

open scoped BigOperators

namespace TrafficShaping

private lemma feasible_zero_iff_subset {H : ℕ} {x y : Trace H} :
    Feasible 0 x y ↔ x ⊆ y := by
  constructor
  · rintro ⟨f, hf, hrel⟩ a ha
    let aa : {b : Fin H // b ∈ x} := ⟨a, ha⟩
    have hfa := hrel aa
    have h₁ := (hrel aa).2.1
    have h₂ := (hrel aa).2.2
    change a.val ≤ (f aa).val at h₁
    change (f aa).val ≤ a.val + 0 at h₂
    have hva : f aa = a := Fin.ext (by omega)
    rw [hva] at hfa
    exact hfa.1
  · intro hxy
    refine ⟨Subtype.val, Subtype.val_injective, ?_⟩
    intro a
    exact ⟨hxy a.property, le_rfl, by simp⟩

private lemma offMatrix_zero_apply {H m B : ℕ} (x : FullInput H m)
    (y : OffSchedule H B) :
    offMatrix H m B 0 x y = if x.1 ⊆ y.1 then 1 else 0 := by
  simp [offMatrix, coverageMatrix, feasible_zero_iff_subset]

private lemma onMatrix_zero_apply {H m B : ℕ} (x : FullInput H m)
    (y : OnSchedule H m B) :
    onMatrix H m B 0 x y = if x.1 ⊆ y.1 then 1 else 0 := by
  simp [onMatrix, coverageMatrix, feasible_zero_iff_subset]

private lemma card_fullInput (H m : ℕ) :
    Fintype.card (FullInput H m) = Nat.choose H m := by
  let e : FullInput H m ≃ Set.powersetCard (Fin H) m :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  rw [Fintype.card_congr e]
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card]
  simp [Nat.card_eq_fintype_card]

private lemma card_offSchedule (H B : ℕ) :
    Fintype.card (OffSchedule H B) = Nat.choose H B := by
  let e : OffSchedule H B ≃ Set.powersetCard (Fin H) B :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  rw [Fintype.card_congr e]
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card]
  simp [Nat.card_eq_fintype_card]

private def offSetEquiv (H B : ℕ) :
    OffSchedule H B ≃ Set.powersetCard (Fin H) B :=
  { toFun := fun x => ⟨x.1, x.2⟩
    invFun := fun x => ⟨x.1, x.2⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }

private def fullSetEquiv (H m : ℕ) :
    FullInput H m ≃ Set.powersetCard (Fin H) m :=
  { toFun := fun x => ⟨x.1, x.2⟩
    invFun := fun x => ⟨x.1, x.2⟩
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl }

private lemma card_off_containing {H m B : ℕ} (hmb : m ≤ B)
    (hB : B ≤ H) (x : FullInput H m) :
    Fintype.card {y : OffSchedule H B // x.1 ⊆ y.1} =
      Nat.choose (H - m) (B - m) := by
  let e : {y : OffSchedule H B // x.1 ⊆ y.1} ≃
      {y : Set.powersetCard (Fin H) B // x.1 ⊆ y.1} :=
    (offSetEquiv H B).subtypeEquiv (by intro y; rfl)
  rw [Fintype.card_congr e]
  let F : Finset (Finset (Fin H)) :=
    ((Finset.univ : Finset (Fin H)).powersetCard B).filter (x.1 ⊆ ·)
  let e' : {y : Set.powersetCard (Fin H) B // x.1 ⊆ y.1} ≃
      {z : Finset (Fin H) // z ∈ F} :=
    { toFun := fun y => ⟨y.1, by
          simp only [F, Finset.mem_filter]
          exact ⟨Finset.mem_powersetCard_univ.mpr y.1.2, y.2⟩⟩
      invFun := fun z => ⟨⟨z.1, Finset.mem_powersetCard_univ.mp
            (Finset.mem_filter.mp z.2).1⟩, (Finset.mem_filter.mp z.2).2⟩
      left_inv := by intro y; rfl
      right_inv := by intro z; rfl }
  rw [Fintype.card_congr e', Fintype.card_coe]
  rw [Finset.card_filter_powersetCard_subset x.1 (Finset.univ : Finset (Fin H)) B
    (Finset.subset_univ _) (by simpa [x.2] using hmb)]
  simpa [x.2]

private lemma card_full_contained {H m B : ℕ} (hm : m ≤ H)
    (y : OffSchedule H B) :
    Fintype.card {x : FullInput H m // x.1 ⊆ y.1} = Nat.choose B m := by
  let e : {x : FullInput H m // x.1 ⊆ y.1} ≃
      {x : Set.powersetCard (Fin H) m // x.1 ⊆ y.1} :=
    (fullSetEquiv H m).subtypeEquiv (by intro x; rfl)
  rw [Fintype.card_congr e]
  let F : Finset (Finset (Fin H)) := y.1.powersetCard m
  let e' : {x : Set.powersetCard (Fin H) m // x.1 ⊆ y.1} ≃
      {z : Finset (Fin H) // z ∈ F} :=
    { toFun := fun x => ⟨x.1, by
          simp only [F, Finset.mem_powersetCard]
          exact ⟨x.2, x.1.2⟩⟩
      invFun := fun z => ⟨⟨z.1, by
            simp only [F, Finset.mem_powersetCard] at z
            simpa [Set.powersetCard] using z.2.2⟩, by
          simp only [F, Finset.mem_powersetCard] at z
          simpa using z.2.1⟩
      left_inv := by intro x; rfl
      right_inv := by intro z; rfl }
  rw [Fintype.card_congr e', Fintype.card_coe]
  simp [F, y.2]

private lemma card_off_event_zero {H m B : ℕ} (hmb : m ≤ B)
    (hB : B ≤ H) (x : FullInput H m) :
    (feasibleScheduleEvent (D := 0) (fun y : OffSchedule H B => y.1) x).card =
      Nat.choose (H - m) (B - m) := by
  have hev : feasibleScheduleEvent (D := 0) (fun y : OffSchedule H B => y.1) x =
      Finset.univ.filter (fun y : OffSchedule H B => x.1 ⊆ y.1) := by
    ext y
    simp [feasibleScheduleEvent, feasible_zero_iff_subset]
  rw [hev, ← Fintype.card_subtype]
  exact card_off_containing hmb hB x

private lemma choose_ratio_off {H m B : ℕ} (hm : m ≤ H)
    (hmb : m ≤ B) (hB : B ≤ H) :
    (Nat.choose (H - m) (B - m) : ℝ) / Nat.choose H B =
      (Nat.choose B m : ℝ) / Nat.choose H m := by
  have h₁ : 0 < Nat.choose H B := Nat.choose_pos hB
  have h₂ : 0 < Nat.choose H m := Nat.choose_pos hm
  have hmul := Nat.choose_mul (n := H) (k := B) (s := m) hmb
  have hmulR : (Nat.choose H B : ℝ) * Nat.choose B m =
      (Nat.choose H m : ℝ) * Nat.choose (H - m) (B - m) := by
    exact_mod_cast hmul
  field_simp [ne_of_gt h₁, ne_of_gt h₂]
  nlinarith

private lemma off_uniform_row {H m B : ℕ} [Nonempty (OffSchedule H B)] (hm : m ≤ H)
    (hmb : m ≤ B) (hB : B ≤ H) (x : FullInput H m) :
    coverage (offMatrix H m B 0) (Law.uniform : Law (OffSchedule H B)) x =
      (Nat.choose B m : ℝ) / Nat.choose H m := by
  change coverage (coverageMatrix (D := 0)
      (fun y : OffSchedule H B => y.1)) (Law.uniform : Law (OffSchedule H B)) x = _
  rw [coverageMatrix_eq_mass]
  rw [Law.uniform_mass, card_off_event_zero hmb hB x, card_offSchedule]
  exact choose_ratio_off hm hmb hB

private lemma law_uniform_weighted_filter {α : Type*} [Fintype α] [Nonempty α]
    (P : α → Prop) [DecidablePred P] :
    ∑ a, (Law.uniform : Law α).val a * (if P a then (1 : ℝ) else 0) =
      (Fintype.card {a : α // P a} : ℝ) / Fintype.card α := by
  classical
  let E : Finset α := Finset.univ.filter P
  have hcard : E.card = Fintype.card {a : α // P a} := by
    simpa [E] using (Fintype.card_subtype P).symm
  change (∑ a, (Law.uniform : Law α).val a * (if P a then (1 : ℝ) else 0)) = _
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  change (Law.uniform : Law α).mass E = _
  rw [Law.uniform_mass, hcard]

private def onSetEquiv {H m B : ℕ} (hm : m ≤ H) :
    OnSchedule H m B ≃
      {y : Set.powersetCard (Fin H) B // terminal H m ⊆ y.1} :=
  { toFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
    invFun := fun y => ⟨y.1.1, y.1.2, y.2⟩
    left_inv := by intro y; rfl
    right_inv := by intro y; rfl }

private lemma card_on_containing {H m B : ℕ} (hm : m ≤ H)
    (hmb : m ≤ B) (hB : B ≤ H) (x : FullInput H m) :
    Fintype.card {y : OnSchedule H m B // x.1 ⊆ y.1} =
      if (tracePrefix (H - m) x.1).card ≤ B - m then
        Nat.choose ((H - m) - (tracePrefix (H - m) x.1).card)
          ((B - m) - (tracePrefix (H - m) x.1).card)
      else 0 := by
  let e : {y : OnSchedule H m B // x.1 ⊆ y.1} ≃
      {y : {z : Set.powersetCard (Fin H) B // terminal H m ⊆ z.1} //
        x.1 ⊆ y.1.1} :=
    (onSetEquiv hm).subtypeEquiv (by intro y; rfl)
  rw [Fintype.card_congr e]
  let F : Finset (Finset (Fin H)) :=
    ((Finset.univ : Finset (Fin H)).powersetCard B).filter
      (fun z => terminal H m ⊆ z ∧ x.1 ⊆ z)
  let e' : {y : {z : Set.powersetCard (Fin H) B // terminal H m ⊆ z.1} //
        x.1 ⊆ y.1.1} ≃ {z : Finset (Fin H) // z ∈ F} :=
    { toFun := fun y => ⟨y.1.1, by
          simp only [F, Finset.mem_filter]
          exact ⟨Finset.mem_powersetCard_univ.mpr y.1.1.2,
            y.1.2, y.2⟩⟩
      invFun := fun z => by
        have hz := Finset.mem_filter.mp (show z.1 ∈ F from z.2)
        exact ⟨⟨⟨z.1, Finset.mem_powersetCard_univ.mp hz.1⟩,
              hz.2.1⟩, hz.2.2⟩
      left_inv := by intro y; rfl
      right_inv := by intro z; rfl }
  rw [Fintype.card_congr e', Fintype.card_coe]
  have hF : F = ((Finset.univ : Finset (Fin H)).powersetCard B).filter
      ((terminal H m ∪ x.1) ⊆ ·) := by
    ext z
    simp only [F, Finset.mem_filter]
    rw [Finset.union_subset_iff]
  rw [hF]
  by_cases hs : (terminal H m ∪ x.1).card ≤ B
  · rw [Finset.card_filter_powersetCard_subset (terminal H m ∪ x.1)
      (Finset.univ : Finset (Fin H)) B (Finset.subset_univ _) hs]
    have hcard_union : (terminal H m ∪ x.1).card =
        m + (tracePrefix (H - m) x.1).card := by
      rw [Finset.union_comm, union_terminal_eq_prefix_union_terminal hm x.1]
      rw [Finset.card_union_of_disjoint (prefix_disjoint_terminal hm x.1)]
      rw [terminal_card hm]
      omega
    rw [hcard_union]
    have hc : (tracePrefix (H - m) x.1).card ≤ B - m := by
      omega
    simp [if_pos hc, Fintype.card_fin, Nat.sub_sub]
  · have hzero : ((Finset.univ : Finset (Fin H)).powersetCard B).filter
        ((terminal H m ∪ x.1) ⊆ ·) = ∅ := by
      ext z
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hzmem, hsz⟩
        have hzcard := (Finset.mem_powersetCard.mp hzmem).2
        have hc := Finset.card_le_card hsz
        have : False := by omega
        exact this.elim
      · intro hz
        simp at hz
    rw [hzero]
    simp only [Finset.card_empty]
    have hlt : B - m < (tracePrefix (H - m) x.1).card := by
      have hcard_union : (terminal H m ∪ x.1).card =
          m + (tracePrefix (H - m) x.1).card := by
        rw [Finset.union_comm, union_terminal_eq_prefix_union_terminal hm x.1]
        rw [Finset.card_union_of_disjoint (prefix_disjoint_terminal hm x.1)]
        rw [terminal_card hm]
        omega
      omega
    simp [not_le.mpr hlt]

private lemma card_fixedSubset_contained {α : Type*} [Fintype α] [DecidableEq α]
    (s t : Finset α) (k : ℕ) (hts : t ⊆ s) :
    Fintype.card {u : FixedSubset s k // u.1 ⊆ t} = Nat.choose t.card k := by
  classical
  let e : {u : FixedSubset s k // u.1 ⊆ t} ≃
      {z : Finset α // z ∈ t.powersetCard k} :=
    { toFun := fun u => ⟨u.1.1, by
          exact Finset.mem_powersetCard.mpr ⟨u.2, FixedSubset.card_val u.1⟩⟩
      invFun := fun z => by
        have hz := Finset.mem_powersetCard.mp z.2
        exact ⟨⟨z.1, Finset.mem_powersetCard.mpr
              ⟨hz.1.trans hts, hz.2⟩⟩, hz.1⟩
      left_inv := by intro u; rfl
      right_inv := by intro z; rfl }
  rw [Fintype.card_congr e, Fintype.card_coe]
  simp [Finset.card_powersetCard]

private lemma extend_subset_card {α : Type*} [Fintype α] [DecidableEq α]
    (s u : Finset α) (j : ℕ) (hus : u ⊆ s) (huj : u.card ≤ j)
    (hjs : j ≤ s.card) :
    ∃ t, u ⊆ t ∧ t ⊆ s ∧ t.card = j := by
  let r := s \ u
  have hrcard : r.card = s.card - u.card := Finset.card_sdiff_of_subset hus
  have hr : j - u.card ≤ r.card := by
    rw [hrcard]
    omega
  obtain ⟨v, hvsub, hvcard⟩ := Finset.exists_subset_card_eq hr
  have huv : Disjoint u v := by
    apply Finset.disjoint_left.mpr
    intro a hau hav
    exact (Finset.mem_sdiff.mp (show a ∈ s \ u from hvsub hav)).2 hau
  refine ⟨u ∪ v, Finset.subset_union_left, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hus ha
    · exact Finset.sdiff_subset (hvsub ha)
  · rw [Finset.card_union_of_disjoint huv, hvcard]
    omega

private lemma choose_ratio_mono {α : Type*} [Fintype α] [DecidableEq α]
    (s u : Finset α) (k j : ℕ)
    (hus : u ⊆ s) (huc : u.card ≤ k) (hks : k ≤ s.card)
    (hjk : j ≤ k) (huj : u.card ≤ j) (hjs : j ≤ s.card) :
    (Nat.choose k u.card : ℝ) / Nat.choose s.card u.card ≥
      (Nat.choose k j : ℝ) / Nat.choose s.card j := by
  letI : Nonempty (FixedSubset s k) := fixedSubset_nonempty s k hks
  obtain ⟨t, hut, hts, ht⟩ := extend_subset_card s u j hus huj hjs
  have htc : t.card ≤ k := by simpa [ht] using hjk
  let E_u : Finset (FixedSubset s k) :=
    Finset.univ.filter (fun v => u ⊆ v.1)
  let E_t : Finset (FixedSubset s k) :=
    Finset.univ.filter (fun v => t ⊆ v.1)
  have hsub : E_t ⊆ E_u := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).1,
      hut.trans (Finset.mem_filter.mp hv).2⟩
  have hmass :
      (@Law.uniform (FixedSubset s k) _ (fixedSubset_nonempty s k hks)).mass E_t ≤
      (@Law.uniform (FixedSubset s k) _ (fixedSubset_nonempty s k hks)).mass E_u := by
    exact Law.mass_mono (p := (@Law.uniform (FixedSubset s k) _
      (fixedSubset_nonempty s k hks))) hsub
  have hEu := uniform_fixedSubset_containment_symmetric s u k hus huc hks
  have hEt := uniform_fixedSubset_containment_symmetric s t k hts htc hks
  rw [show E_u = Finset.univ.filter (fun v : FixedSubset s k => u ⊆ v.1) by rfl,
      show E_t = Finset.univ.filter (fun v : FixedSubset s k => t ⊆ v.1) by rfl,
      hEt, hEu] at hmass
  simpa [ht] using hmass

private lemma card_on_event_zero {H m B : ℕ} (hm : m ≤ H)
    (hmb : m ≤ B) (hB : B ≤ H) (x : FullInput H m) :
    (feasibleScheduleEvent (D := 0) (fun y : OnSchedule H m B => y.1) x).card =
      if (tracePrefix (H - m) x.1).card ≤ B - m then
        Nat.choose ((H - m) - (tracePrefix (H - m) x.1).card)
          ((B - m) - (tracePrefix (H - m) x.1).card)
      else 0 := by
  have hev : feasibleScheduleEvent (D := 0)
      (fun y : OnSchedule H m B => y.1) x =
      Finset.univ.filter (fun y : OnSchedule H m B => x.1 ⊆ y.1) := by
    ext y
    simp [feasibleScheduleEvent, feasible_zero_iff_subset]
  rw [hev, ← Fintype.card_subtype]
  exact card_on_containing hm hmb hB x

private lemma on_uniform_row {H m B : ℕ}
    [Nonempty (OnSchedule H m B)] (hm : m ≤ H)
    (hmb : m ≤ B) (hB : B ≤ H) (x : FullInput H m) :
    coverage (onMatrix H m B 0) (Law.uniform : Law (OnSchedule H m B)) x =
      (if (tracePrefix (H - m) x.1).card ≤ B - m then
        (Nat.choose ((H - m) - (tracePrefix (H - m) x.1).card)
          ((B - m) - (tracePrefix (H - m) x.1).card) : ℝ)
          / Nat.choose (H - m) (B - m)
      else 0) := by
  change coverage (coverageMatrix (D := 0)
      (fun y : OnSchedule H m B => y.1))
      (Law.uniform : Law (OnSchedule H m B)) x = _
  rw [coverageMatrix_eq_mass, Law.uniform_mass, card_on_event_zero hm hmb hB x,
    onSchedule_card hm hmb]
  by_cases hc : (tracePrefix (H - m) x.1).card ≤ B - m
  · simp [hc]
  · have hden : (Nat.choose (H - m) (B - m) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero (by omega)
    simp [hc, hden]

private lemma on_uniform_lower {H m B : ℕ}
    [Nonempty (OnSchedule H m B)] (hm : m ≤ H)
    (hmb : m ≤ B) (hB : B ≤ H) :
    ∀ x : FullInput H m,
      (Nat.choose (B - m) (min m (H - m)) : ℝ) /
          Nat.choose (H - m) (min m (H - m)) ≤
        coverage (onMatrix H m B 0)
          (Law.uniform : Law (OnSchedule H m B)) x := by
  let n := H - m
  let k := B - m
  let j := min m n
  let P : Trace H :=
    (Finset.univ : Finset (Fin n)).map (Fin.castLEEmb (by omega))
  have hPcard : P.card = n := by
    simp [P]
  have hPprefix (z : Trace H) : tracePrefix n z ⊆ P := by
    dsimp [P]
    intro a ha
    have ha' := (mem_prefix.mp ha).2
    simp only [Finset.mem_map]
    refine ⟨⟨a.val, ha'⟩, by simp, ?_⟩
    apply Fin.ext
    rfl
  have hP_eq : P = tracePrefix n (Finset.univ : Trace H) := by
    dsimp [P]
    ext a
    constructor
    · intro ha
      simp only [Finset.mem_map] at ha
      obtain ⟨i, hi, hia⟩ := ha
      subst a
      simp [tracePrefix, i.isLt]
    · intro ha
      simp only [mem_prefix] at ha
      refine Finset.mem_map.mpr ⟨⟨a.val, ha.2⟩, by simp, ?_⟩
      apply Fin.ext
      rfl
  have hkn : k ≤ n := by
    dsimp [k, n]
    omega
  have hjn : j ≤ n := by simp [j]
  have hjm : j ≤ m := by simp [j]
  intro x
  let U : Trace H := tracePrefix n x.1
  have hUsubx : U ⊆ x.1 := by
    intro a ha
    exact (mem_prefix.mp ha).1
  have hUsubP : U ⊆ P := by
    simpa [U] using hPprefix x.1
  have hUcard_m : U.card ≤ m := by
    rw [← x.2]
    exact Finset.card_le_card hUsubx
  have hUcard_n : U.card ≤ n := by
    rw [← hPcard]
    exact Finset.card_le_card hUsubP
  have hUcard_j : U.card ≤ j := by
    dsimp [j]
    exact (Nat.le_min).2 ⟨hUcard_m, hUcard_n⟩
  by_cases hjk : j ≤ k
  · have hUk : U.card ≤ k := hUcard_j.trans hjk
    have hcov := on_uniform_row (H := H) (m := m) (B := B) hm hmb hB x
    have hcov' : coverage (onMatrix H m B 0)
        (Law.uniform : Law (OnSchedule H m B)) x =
        (Nat.choose (n - U.card) (k - U.card) : ℝ) /
          Nat.choose n k := by
      rw [show tracePrefix (H - m) x.1 = U by rfl,
        show B - m = k by rfl, show H - m = n by rfl,
        if_pos hUk] at hcov
      exact hcov
    have hkp : k ≤ P.card := by simpa [hPcard] using hkn
    have hsym := containment_probability_symmetry P U k hUsubP hUk hkp
    have hratio : coverage (onMatrix H m B 0)
        (Law.uniform : Law (OnSchedule H m B)) x =
        (Nat.choose k U.card : ℝ) / Nat.choose n U.card := by
      calc
        _ = (Nat.choose (n - U.card) (k - U.card) : ℝ) /
              Nat.choose n k := hcov'
        _ = (Nat.choose k U.card : ℝ) / Nat.choose n U.card := by
          simpa [hPcard] using hsym
    have hmono := choose_ratio_mono P U k j hUsubP hUk hkp hjk
      hUcard_j (by simpa [hPcard] using hjn)
    rw [hratio]
    simpa [n, k, j, hPcard] using hmono
  · have hvzero :
        (Nat.choose (B - m) (min m (H - m)) : ℝ) /
            Nat.choose (H - m) (min m (H - m)) = 0 := by
      have hz : Nat.choose k j = 0 :=
        Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hjk)
      simp [n, k, j, hz]
    rw [hvzero]
    change 0 ≤ coverage (coverageMatrix (D := 0)
      (fun y : OnSchedule H m B => y.1))
      (Law.uniform : Law (OnSchedule H m B)) x
    rw [coverageMatrix_eq_mass]
    exact Law.mass_nonneg _ _

private lemma on_fixed_upper {H m B : ℕ}
    [Nonempty (FullInput H m)] (hm : m ≤ H)
    (hmb : m ≤ B) (hB : B ≤ H) :
    ∃ w : Law (FullInput H m),
      ∀ y : OnSchedule H m B,
        ∑ x, w.val x * onMatrix H m B 0 x y ≤
          (Nat.choose (B - m) (min m (H - m)) : ℝ) /
            Nat.choose (H - m) (min m (H - m)) := by
  let n := H - m
  let k := B - m
  let j := min m n
  let P : Trace H :=
    (Finset.univ : Finset (Fin n)).map (Fin.castLEEmb (by omega))
  have hPcard : P.card = n := by
    simp [P]
  have hP_eq : P = tracePrefix n (Finset.univ : Trace H) := by
    dsimp [P]
    ext a
    constructor
    · intro ha
      simp only [Finset.mem_map] at ha
      obtain ⟨i, hi, hia⟩ := ha
      subst a
      simp [tracePrefix, i.isLt]
    · intro ha
      simp only [mem_prefix] at ha
      refine Finset.mem_map.mpr ⟨⟨a.val, ha.2⟩, by simp, ?_⟩
      apply Fin.ext
      rfl
  have hPprefix (z : Trace H) : tracePrefix n z ⊆ P := by
    dsimp [P]
    intro a ha
    have ha' := (mem_prefix.mp ha).2
    simp only [Finset.mem_map]
    refine ⟨⟨a.val, ha'⟩, by simp, ?_⟩
    apply Fin.ext
    rfl
  have hPterminal : Disjoint P (terminal H m) := by
    rw [hP_eq]
    exact prefix_disjoint_terminal hm _
  have hkn : k ≤ n := by
    dsimp [k, n]
    omega
  have hjn : j ≤ n := by simp [j]
  have hPj : j ≤ P.card := by simpa [hPcard] using hjn
  letI : Nonempty (FixedSubset P j) := fixedSubset_nonempty P j hPj
  have hr : m - j ≤ (terminal H m).card := by
    rw [terminal_card hm]
    omega
  let t0 : FixedSubset (terminal H m) (m - j) :=
    Classical.choice (fixedSubset_nonempty (terminal H m) (m - j) hr)
  have ht0sub : t0.1 ⊆ terminal H m := FixedSubset.mem_val t0
  have ht0card : t0.1.card = m - j := FixedSubset.card_val t0
  let embed : FixedSubset P j → FullInput H m := fun u =>
    ⟨u.1 ∪ t0.1, by
      rw [Finset.card_union_of_disjoint
        (Finset.disjoint_of_subset_left (FixedSubset.mem_val u)
          (Finset.disjoint_of_subset_right ht0sub hPterminal))]
      rw [FixedSubset.card_val u, ht0card]
      omega⟩
  let uLaw : Law (FixedSubset P j) := Law.uniform
  let w : Law (FullInput H m) := uLaw.map embed
  refine ⟨w, ?_⟩
  intro y
  let Y : Trace H := y.1 ∩ P
  have hY_eq : Y = tracePrefix n y.1 := by
    dsimp [Y]
    rw [hP_eq]
    ext a
    simp [Y, mem_prefix]
  have hYcard : Y.card = k := by
    have hpart := prefix_terminal_card_of_subset hm y.2.2
    have ht := terminal_card hm
    have hy := y.2.1
    rw [hY_eq]
    dsimp [k, n]
    omega
  have ht0y : t0.1 ⊆ y.1 := ht0sub.trans y.2.2
  let E : Finset (FullInput H m) :=
    Finset.univ.filter (fun x => x.1 ⊆ y.1)
  have hsum :
      ∑ x, w.val x * onMatrix H m B 0 x y = w.mass E := by
    simp_rw [onMatrix_zero_apply]
    rw [Law.mass_eq_sum_ite]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hxy : x.1 ⊆ y.1 <;> simp [hxy]
  rw [hsum, Law.mass_map]
  have hpre :
      Finset.univ.filter (fun u : FixedSubset P j => embed u ∈ E) =
        Finset.univ.filter (fun u : FixedSubset P j => u.1 ⊆ Y) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hu
      have hu' : u.1 ∪ t0.1 ⊆ y.1 := by
        simpa [embed, E] using hu
      have huP : u.1 ⊆ P := FixedSubset.mem_val u
      change u.1 ⊆ y.1 ∩ P
      intro a ha
      exact Finset.mem_inter.mpr ⟨
        hu' (Finset.mem_union.mpr (Or.inl ha)), huP ha⟩
    · intro hu
      have huY' : u.1 ⊆ y.1 ∩ P := by
        simpa [Y] using hu
      have huY : u.1 ⊆ y.1 := fun a ha => (Finset.mem_inter.mp (huY' ha)).1
      have hu' : u.1 ∪ t0.1 ⊆ y.1 := by
        intro a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact huY ha
        · exact ht0y ha
      simpa [embed, E] using hu'
  rw [hpre]
  have hYP : Y ⊆ P := Finset.inter_subset_right
  have hfiltercard :
      (Finset.univ.filter (fun u : FixedSubset P j => u.1 ⊆ Y)).card =
        Nat.choose Y.card j := by
    rw [← Fintype.card_subtype]
    exact card_fixedSubset_contained P Y j hYP
  change (Law.uniform : Law (FixedSubset P j)).mass
      (Finset.univ.filter (fun u : FixedSubset P j => u.1 ⊆ Y)) ≤ _
  rw [Law.uniform_mass, hfiltercard, fixedSubset_card, hYcard, hPcard]

private lemma off_uniform_col {H m B : ℕ} [Nonempty (FullInput H m)]
    (hm : m ≤ H) (y : OffSchedule H B) :
    ∑ x, (Law.uniform : Law (FullInput H m)).val x *
        offMatrix H m B 0 x y =
      (Nat.choose B m : ℝ) / Nat.choose H m := by
  simp_rw [offMatrix_zero_apply]
  rw [law_uniform_weighted_filter]
  rw [card_full_contained hm y, card_fullInput]

theorem zero_delay_offGameValue {H m B : ℕ} (hm1 : 1 ≤ m)
    (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H) :
    offGameValue H m B 0 hm hB =
      (Nat.choose B m : ℝ) / Nat.choose H m := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OffSchedule H B) := exists_offSchedule H B hB
  change value (offMatrix H m B 0) = _
  let q : Law (OffSchedule H B) := Law.uniform
  let w : Law (FullInput H m) := Law.uniform
  have hrow : ∀ x : FullInput H m,
      (Nat.choose B m : ℝ) / Nat.choose H m ≤
        coverage (offMatrix H m B 0) q x := by
    intro x
    simpa [q] using (off_uniform_row hm hmb hB x).ge
  have hcol : ∀ y : OffSchedule H B,
      ∑ x, w.val x * offMatrix H m B 0 x y ≤
        (Nat.choose B m : ℝ) / Nat.choose H m := by
    intro y
    simpa [w, Law.uniform_apply, div_eq_mul_inv] using (off_uniform_col hm y).le
  exact (matching_certificate (offMatrix H m B 0) q w _ hrow hcol).1

theorem zero_delay_onGameValue {H m B : ℕ} (hm1 : 1 ≤ m)
    (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H) :
    onGameValue H m B 0 hm hmb hB =
      (Nat.choose (B - m) (min m (H - m)) : ℝ) /
        Nat.choose (H - m) (min m (H - m)) := by
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OnSchedule H m B) := exists_onSchedule hm hmb hB
  change value (onMatrix H m B 0) = _
  let q : Law (OnSchedule H m B) := Law.uniform
  have hrow : ∀ x : FullInput H m,
      (Nat.choose (B - m) (min m (H - m)) : ℝ) /
          Nat.choose (H - m) (min m (H - m)) ≤
        coverage (onMatrix H m B 0) q x := by
    intro x
    simpa [q] using (on_uniform_lower hm hmb hB x)
  obtain ⟨w, hcol⟩ := on_fixed_upper hm hmb hB
  exact (matching_certificate (onMatrix H m B 0) q w _ hrow hcol).1

theorem zero_delay_m_one_gap {H B : ℕ} (hH : 2 ≤ H)
    (hB : 1 ≤ B) (hBH : B ≤ H) :
    (1 - onGameValue H 1 B 0 (by omega) hB hBH) -
        (1 - offGameValue H 1 B 0 (by omega) hBH) =
      (H - B : ℝ) / (H * (H - 1)) := by
  have hmin : min 1 (H - 1) = 1 := by omega
  rw [zero_delay_onGameValue (by omega) (by omega) hB hBH,
    zero_delay_offGameValue (by omega) (by omega) hB hBH]
  rw [hmin]
  simp only [Nat.choose_one_right]
  have hH0 : (H : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < H))
  have hHm0 : (H : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < H := by exact_mod_cast (by omega : 1 < H)
    linarith
  rw [Nat.cast_sub hB, Nat.cast_sub (by omega : 1 ≤ H)]
  field_simp [hH0, hHm0]
  ring_nf

theorem zero_delay_onGameValue_zero_of_lt {H m B : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (hzero : B - m < min m (H - m)) :
    onGameValue H m B 0 hm hmb hB = 0 := by
  rw [zero_delay_onGameValue hm1 hm hmb hB]
  simp [Nat.choose_eq_zero_of_lt hzero]

theorem zero_delay_m_one_optimum_gap {H B : ℕ} (hH : 2 ≤ H)
    (hB : 1 ≤ B) (hBH : B ≤ H) (ε : ℝ) (hε : 0 ≤ ε) :
    causalOptimum H 1 B 0 ε - noncausalOptimum H 1 B 0 ε =
      (H - B : ℝ) / (H * (H - 1)) := by
  rw [causal_optimum_eq (by omega) (by omega) hB hBH ε hε,
    noncausal_optimum_eq (by omega) (by omega) hB hBH ε hε]
  exact zero_delay_m_one_gap hH hB hBH

theorem zero_delay_full_input_boundary {m : ℕ} (hm1 : 1 ≤ m) :
    offGameValue m m m 0 le_rfl le_rfl = 1 ∧
      onGameValue m m m 0 le_rfl le_rfl le_rfl = 1 := by
  constructor
  · rw [zero_delay_offGameValue hm1 le_rfl le_rfl le_rfl]
    norm_num
  · rw [zero_delay_onGameValue hm1 le_rfl le_rfl le_rfl]
    norm_num

end TrafficShaping
