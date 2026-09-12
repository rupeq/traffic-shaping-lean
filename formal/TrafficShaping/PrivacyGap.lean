import TrafficShaping.MainTheorem
import TrafficShaping.ThinningBound

namespace TrafficShaping

open scoped BigOperators

noncomputable def uniformLaw (α : Type*) [Fintype α] [Nonempty α] : Law α :=
  ⟨fun _ => (Fintype.card α : ℝ)⁻¹, by
    intro _
    positivity,
    by
      rw [Finset.sum_const]
      simp [Fintype.card_ne_zero]⟩

@[simp] theorem uniformLaw_apply (α : Type*) [Fintype α] [Nonempty α]
    (a : α) : (uniformLaw α).val a = (Fintype.card α : ℝ)⁻¹ := rfl

noncomputable def productLaw {α β : Type*} [Fintype α] [Fintype β]
    (p : Law α) (q : Law β) : Law (α × β) :=
  ⟨fun z => p.val z.1 * q.val z.2, by
    intro z
    exact mul_nonneg (p.nonneg z.1) (q.nonneg z.2), by
    rw [Fintype.sum_prod_type]
    calc
      (∑ x, ∑ y, p.val x * q.val y) =
          ∑ x, p.val x * ∑ y, q.val y := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.mul_sum]
      _ = 1 := by simp [q.total, p.total]⟩

@[simp] theorem productLaw_apply {α β : Type*} [Fintype α] [Fintype β]
    (p : Law α) (q : Law β) (z : α × β) :
    (productLaw p q).val z = p.val z.1 * q.val z.2 := rfl

abbrev ThinIndex (B K : ℕ) := {z : Finset (Fin B) // z.card = K}

theorem thinIndex_nonempty {B K : ℕ} (hK : K ≤ B) :
    Nonempty (ThinIndex B K) := by
  obtain ⟨z, hz, hcard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin B))) (by simpa using hK)
  exact ⟨⟨z, hcard⟩⟩

noncomputable def keptSlots {H B K : ℕ}
    (y : OffSchedule H B) (z : ThinIndex B K) : Trace H :=
  z.1.image (fun i => ((Finset.orderIsoOfFin y.1 y.2) i).1)

theorem keptSlots_card {H B K : ℕ} (y : OffSchedule H B)
    (z : ThinIndex B K) : (keptSlots y z).card = K := by
  unfold keptSlots
  rw [Finset.card_image_of_injective]
  · exact z.2
  · intro i j hij
    apply (Finset.orderIsoOfFin y.1 y.2).injective
    exact Subtype.ext hij

theorem keptSlots_subset {H B K : ℕ} (y : OffSchedule H B)
    (z : ThinIndex B K) : keptSlots y z ⊆ y.1 := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  exact ((Finset.orderIsoOfFin y.1 y.2) i).property

noncomputable def thinningBase {H m B K : ℕ}
    (y : OffSchedule H B) (z : ThinIndex B K) : Trace H :=
  keptSlots y z ∪ terminal H m

theorem thinningBase_card_le {H m B : ℕ}
    (hm : m ≤ H) (hmb : m ≤ B) (y : OffSchedule H B)
    (z : ThinIndex B (B - m)) : (thinningBase (m := m) y z).card ≤ B := by
  unfold thinningBase
  calc
    (keptSlots y z ∪ terminal H m).card ≤
        (keptSlots y z).card + (terminal H m).card :=
      Finset.card_union_le _ _
    _ = (B - m) + m := by rw [keptSlots_card, terminal_card hm]
    _ = B := Nat.sub_add_cancel hmb

noncomputable def thinningOutput {H m B : ℕ}
    (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (y : OffSchedule H B) (z : ThinIndex B (B - m)) : OnSchedule H m B := by
  let base : Trace H := thinningBase (m := m) y z
  have hbase : base.card ≤ B := by
    exact thinningBase_card_le (m := m) hm hmb y z
  let out : Trace H := extendTraceToCard base hbase hB
  exact ⟨out, extendTraceToCard_card base hbase hB, by
    intro a ha
    exact extendTraceToCard_subset base hbase hB
      (Finset.mem_union_right (keptSlots y z) ha)⟩

theorem thinningOutput_superset {H m B : ℕ}
    (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (y : OffSchedule H B) (z : ThinIndex B (B - m)) :
    thinningBase (m := m) y z ⊆ (thinningOutput hm hmb hB y z).1 := by
  let base : Trace H := thinningBase (m := m) y z
  have hbase : base.card ≤ B := thinningBase_card_le (m := m) hm hmb y z
  exact extendTraceToCard_subset base hbase hB

noncomputable def matchingIndicesOf {H m B D : ℕ}
    (x : FullInput H m) (y : OffSchedule H B)
    (hxy : Feasible D x.1 y.1) : Finset (Fin B) := by
  let f : {a : Fin H // a ∈ x.1} → Fin H := Classical.choose hxy
  let hf : ∀ a, f a ∈ y.1 ∧ a.val.val ≤ (f a).val ∧
      (f a).val ≤ a.val.val + D := (Classical.choose_spec hxy).2
  exact (Finset.univ : Finset {a : Fin H // a ∈ x.1}).image
    (fun a => (Finset.orderIsoOfFin y.1 y.2).symm ⟨f a, (hf a).1⟩)

theorem matchingIndicesOf_card {H m B D : ℕ}
    (x : FullInput H m) (y : OffSchedule H B)
    (hxy : Feasible D x.1 y.1) :
    (matchingIndicesOf x y hxy).card = m := by
  let f : {a : Fin H // a ∈ x.1} → Fin H := Classical.choose hxy
  let hf : ∀ a, f a ∈ y.1 ∧ a.val.val ≤ (f a).val ∧
      (f a).val ≤ a.val.val + D := (Classical.choose_spec hxy).2
  have hfi : Function.Injective (fun a : {a : Fin H // a ∈ x.1} =>
      (Finset.orderIsoOfFin y.1 y.2).symm ⟨f a, (hf a).1⟩) := by
    intro a b hab
    have hsub : (⟨f a, (hf a).1⟩ : {a : Fin H // a ∈ y.1}) =
        ⟨f b, (hf b).1⟩ :=
      (Finset.orderIsoOfFin y.1 y.2).symm.injective hab
    apply (Classical.choose_spec hxy).1
    exact congrArg Subtype.val hsub
  unfold matchingIndicesOf
  dsimp only
  rw [Finset.card_image_of_injective _ hfi]
  simpa [Fintype.card_coe, x.2]

theorem matchingIndicesOf_mem_keptSlots {H m B D : ℕ}
    (x : FullInput H m) (y : OffSchedule H B)
    (hxy : Feasible D x.1 y.1)
    (z : ThinIndex B (B - m))
    (hz : matchingIndicesOf x y hxy ⊆ z.1)
    {a : {b : Fin H // b ∈ x.1}} :
    (Classical.choose hxy) a ∈ keptSlots y z := by
  let f : {b : Fin H // b ∈ x.1} → Fin H := Classical.choose hxy
  let hf : ∀ b, f b ∈ y.1 ∧ b.val.val ≤ (f b).val ∧
      (f b).val ≤ b.val.val + D := (Classical.choose_spec hxy).2
  have hi : (Finset.orderIsoOfFin y.1 y.2).symm ⟨f a, (hf a).1⟩ ∈ z.1 := by
    apply hz
    unfold matchingIndicesOf
    simp only
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  unfold keptSlots
  apply Finset.mem_image.mpr
  refine ⟨(Finset.orderIsoOfFin y.1 y.2).symm ⟨f a, (hf a).1⟩, hi, ?_⟩
  change ((Finset.orderIsoOfFin y.1 y.2)
      ((Finset.orderIsoOfFin y.1 y.2).symm ⟨f a, (hf a).1⟩)).1 =
    (Classical.choose hxy) a
  rw [OrderIso.apply_symm_apply]

theorem thinningOutput_feasible {H m B D : ℕ}
    (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (x : FullInput H m) (y : OffSchedule H B)
    (hxy : Feasible D x.1 y.1)
    (z : ThinIndex B (B - m))
    (hz : matchingIndicesOf x y hxy ⊆ z.1) :
    Feasible D x.1 (thinningOutput hm hmb hB y z).1 := by
  let f : {a : Fin H // a ∈ x.1} → Fin H := Classical.choose hxy
  let hf : ∀ a, f a ∈ y.1 ∧ a.val.val ≤ (f a).val ∧
      (f a).val ≤ a.val.val + D := (Classical.choose_spec hxy).2
  refine ⟨f, (Classical.choose_spec hxy).1, ?_⟩
  intro a
  have hkeep : f a ∈ keptSlots y z := by
    exact matchingIndicesOf_mem_keptSlots x y hxy z hz (a := a)
  have hbase : f a ∈ thinningBase (m := m) y z :=
    Finset.mem_union_left _ hkeep
  have hout : f a ∈ (thinningOutput hm hmb hB y z).1 :=
    thinningOutput_superset hm hmb hB y z hbase
  exact ⟨hout, (hf a).2.1, (hf a).2.2⟩

theorem uniformLaw_mass_eq_card_div {α : Type*} [Fintype α] [Nonempty α]
    (E : Finset α) :
    (uniformLaw α).mass E = (E.card : ℝ) / Fintype.card α := by
  unfold Law.mass
  simp only [uniformLaw_apply]
  rw [Finset.sum_const]
  simp [div_eq_mul_inv]

noncomputable def thinUniformLaw {B m : ℕ} (h2m : 2 * m ≤ B) :
    Law (ThinIndex B (B - m)) := by
  letI : Nonempty (ThinIndex B (B - m)) := thinIndex_nonempty (by omega)
  exact uniformLaw _

def thinContains {B K : ℕ} (T : Finset (Fin B)) : Finset (ThinIndex B K) :=
  Finset.univ.filter (fun z => T ⊆ z.1)

theorem thinContains_card {B K : ℕ} (T : Finset (Fin B))
    (hT : T.card ≤ K) :
    (thinContains (B := B) (K := K) T).card =
      (B - T.card).choose (K - T.card) := by
  classical
  let α : Type := Finset (Fin B)
  let p : α → Prop := fun s => s.card = K ∧ T ⊆ s
  let e : {z : ThinIndex B K // T ⊆ z.1} ≃ {s : α // p s} :=
    { toFun := fun z => ⟨z.1.1, z.1.2, z.2⟩
      invFun := fun s => ⟨⟨s.1, s.2.1⟩, s.2.2⟩
      left_inv := by intro z; rfl
      right_inv := by intro s; rfl }
  have hevent : (thinContains (B := B) (K := K) T).card =
      Fintype.card {z : ThinIndex B K // T ⊆ z.1} := by
    unfold thinContains
    simpa using (Fintype.card_subtype (α := ThinIndex B K)
      (fun z => T ⊆ z.1)).symm
  have hcard : (thinContains (B := B) (K := K) T).card =
      Fintype.card {s : α // p s} := by
    calc
      _ = Fintype.card {z : ThinIndex B K // T ⊆ z.1} := hevent
      _ = Fintype.card {s : α // p s} := Fintype.card_congr e
  have hcard_p : Fintype.card {s : α // p s} =
      ((Finset.univ : Finset α).filter p).card := by
    exact Fintype.card_subtype p
  have hfilter :
      (Finset.univ : Finset α).filter p =
        (Finset.powersetCard K (Finset.univ : Finset (Fin B))).filter
          (fun s => T ⊆ s) := by
    ext s
    by_cases hs : T ⊆ s
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs]
      change p s ↔
        s ∈ Finset.powersetCard K (Finset.univ : Finset (Fin B)) ∧ True
      constructor
      · intro hcard
        exact ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard.1⟩,
          trivial⟩
      · intro hmem
        exact ⟨(Finset.mem_powersetCard.mp hmem.1).2, hs⟩
    · simp [p, hs]
  have hcount := Finset.card_filter_powersetCard_subset
    T (Finset.univ : Finset (Fin B)) K (by simp) hT
  rw [hcard, hcard_p, hfilter]
  simpa using hcount

theorem thinContainment_mass {B m : ℕ} (h2m : 2 * m ≤ B)
    (T : Finset (Fin B)) (hT : T.card = m) :
    (thinUniformLaw h2m).mass
        (thinContains (K := B - m) T) =
      ((B - m).choose ((B - m) - m) : ℝ) /
        (B.choose (B - m) : ℝ) := by
  classical
  have hK : m ≤ B - m := by omega
  letI : Nonempty (ThinIndex B (B - m)) := thinIndex_nonempty (by omega)
  change (uniformLaw (ThinIndex B (B - m))).mass _ = _
  rw [uniformLaw_mass_eq_card_div]
  rw [thinContains_card T (by simpa [hT] using hK)]
  rw [hT]
  have hchoose : 0 < B.choose (B - m) := Nat.choose_pos (by omega)
  norm_num [Fintype.card_finset_len, div_eq_mul_inv, hchoose.ne']

noncomputable def productFiberSet {α β : Type*} [Fintype α] [Fintype β]
    (E : Finset α) (F : α → Finset β) : Finset (α × β) :=
  by
    classical
    exact Finset.univ.filter
      (fun z : α × β => z.1 ∈ E ∧ z.2 ∈ F z.1)

theorem productLaw_mass_fiber {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (p : Law α) (q : Law β) (E : Finset α) (F : α → Finset β) :
    (productLaw p q).mass (productFiberSet E F) =
      ∑ a, if a ∈ E then p.val a * q.mass (F a) else 0 := by
  classical
  unfold productFiberSet
  rw [Law.mass_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hEa : a ∈ E
  · have hsum :
      (∑ b : β, if (b ∈ F a) then (p.val a * q.val b) else 0) =
          p.val a * (∑ b : β, if (b ∈ F a) then q.val b else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b hb
            split_ifs <;> ring
    have hsum2 :
        (∑ b : β, if (b ∈ F a) then (p.val a * q.val b) else 0) =
          p.val a * q.mass (F a) := by
      calc
        _ = p.val a * (∑ b : β, if (b ∈ F a) then q.val b else 0) := hsum
        _ = p.val a * q.mass (F a) := by rw [q.mass_eq_sum_ite]
    simpa [hEa, productLaw_apply] using hsum2
  · simp [hEa]

noncomputable def privacyRho (B m : ℕ) : ℝ :=
  (Nat.choose (B - m) m : ℝ) / Nat.choose B m

theorem eq19_binomial_identity {B m : ℕ} (h2m : 2 * m ≤ B) :
    (Nat.choose (B - m) (B - 2 * m) : ℝ) /
    Nat.choose B (B - m) = privacyRho B m := by
  unfold privacyRho
  have hnum : Nat.choose (B - m) (B - 2 * m) =
      Nat.choose (B - m) m := by
    have hsub : B - 2 * m = (B - m) - m := by omega
    calc
      Nat.choose (B - m) (B - 2 * m) =
          Nat.choose (B - m) ((B - m) - m) := by rw [hsub]
      _ = Nat.choose (B - m) m := Nat.choose_symm (by omega)
  have hden : Nat.choose B (B - m) = Nat.choose B m :=
    Nat.choose_symm (by omega)
  rw [hnum, hden]

theorem privacyRho_nonneg {B m : ℕ} (h2m : 2 * m ≤ B) :
    0 ≤ privacyRho B m := by
  unfold privacyRho
  have hden : 0 < (Nat.choose B m : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  positivity

noncomputable def thinningEvent {H m B D : ℕ}
    (x : FullInput H m) (y : OffSchedule H B) :
    Finset (ThinIndex B (B - m)) := by
  classical
  exact if hxy : Feasible D x.1 y.1 then
    thinContains (matchingIndicesOf x y hxy) else ∅

noncomputable def thinningMap {H m B : ℕ}
    (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H) :
    OffSchedule H B × ThinIndex B (B - m) → OnSchedule H m B :=
  fun z => thinningOutput hm hmb hB z.1 z.2

theorem thinningEvent_maps_to {H m B D : ℕ}
    (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (x : FullInput H m) (y : OffSchedule H B)
    (z : ThinIndex B (B - m))
    (hxy : Feasible D x.1 y.1)
    (hz : z ∈ thinningEvent (D := D) x y) :
    Feasible D x.1 (thinningOutput hm hmb hB y z).1 := by
  have hze : matchingIndicesOf x y hxy ⊆ z.1 := by
    unfold thinningEvent at hz
    simp only [dif_pos hxy] at hz
    exact (Finset.mem_filter.mp hz).2
  exact thinningOutput_feasible hm hmb hB x y hxy z hze

noncomputable def thinnedLaw {H m B : ℕ}
    (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H)
    (h2m : 2 * m ≤ B) (q : Law (OffSchedule H B)) :
    Law (OnSchedule H m B) :=
  (productLaw q (thinUniformLaw h2m)).map (thinningMap hm hmb hB)

theorem thinning_mass_lower {H m B D : ℕ}
    (hm1 : 1 ≤ m) (h2m : 2 * m ≤ B) (hB : B ≤ H)
    (q : Law (OffSchedule H B)) (x : FullInput H m) :
    privacyRho B m * coverage (offMatrix H m B D) q x ≤
      coverage (onMatrix H m B D) (thinnedLaw (by omega) (by omega) hB h2m q) x := by
  classical
  have hm : m ≤ H := by omega
  have hmb : m ≤ B := by omega
  let E : Finset (OffSchedule H B) :=
    feasibleScheduleEvent (D := D) (fun s : OffSchedule H B => s.1) x
  let F : OffSchedule H B → Finset (ThinIndex B (B - m)) :=
    fun y => thinningEvent (D := D) x y
  let r : Law (OffSchedule H B × ThinIndex B (B - m)) :=
    productLaw q (thinUniformLaw h2m)
  let f := thinningMap hm hmb hB
  let G := productFiberSet E F
  let N : Finset (OnSchedule H m B) :=
    feasibleScheduleEvent (D := D) (fun s : OnSchedule H m B => s.1) x
  have hmap : r.mass G ≤ (r.map f).mass N := by
    apply Law.mass_map_ge r f G N
    intro z hzpos hzG
    obtain ⟨y, w⟩ := z
    have hzG' : y ∈ E ∧ w ∈ F y := by
      simpa [G, productFiberSet] using hzG
    have hxy : Feasible D x.1 y.1 := by
      simpa [E, feasibleScheduleEvent] using hzG'.1
    have hout := thinningEvent_maps_to hm hmb hB x y w hxy hzG'.2
    simpa [f, thinningMap, N, feasibleScheduleEvent] using hout
  have hsource : r.mass G = privacyRho B m * q.mass E := by
    change (productLaw q (thinUniformLaw h2m)).mass
        (productFiberSet E F) = _
    rw [productLaw_mass_fiber]
    have hu : ∀ y : OffSchedule H B, y ∈ E →
        (thinUniformLaw h2m).mass (F y) = privacyRho B m := by
      intro y hy
      have hxy : Feasible D x.1 y.1 := by
        simpa [E, feasibleScheduleEvent] using hy
      unfold F
      unfold thinningEvent
      rw [dif_pos hxy]
      rw [thinContainment_mass h2m (matchingIndicesOf x y hxy)
        (matchingIndicesOf_card x y hxy)]
      have hsub : B - m - m = B - 2 * m := by omega
      rw [hsub]
      exact eq19_binomial_identity h2m
    calc
      (∑ y, if y ∈ E then q.val y *
          (thinUniformLaw h2m).mass (F y) else 0) =
          ∑ y, if y ∈ E then q.val y * privacyRho B m else 0 := by
            apply Finset.sum_congr rfl
            intro y hy
            by_cases hye : y ∈ E
            · simp [hye, hu y hye]
            · simp [hye]
      _ = privacyRho B m * ∑ y, if y ∈ E then q.val y else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y hy
            split_ifs <;> ring
      _ = privacyRho B m * q.mass E := by
            rw [q.mass_eq_sum_ite]
  have hmass : (r.map f).mass N ≥ privacyRho B m * q.mass E := by
    calc
      privacyRho B m * q.mass E = r.mass G := hsource.symm
      _ ≤ (r.map f).mass N := hmap
  have hon := coverageMatrix_eq_mass (D := D)
    (fun s : OnSchedule H m B => s.1) (r.map f) x
  have hoff := coverageMatrix_eq_mass (D := D)
    (fun s : OffSchedule H B => s.1) q x
  change privacyRho B m *
      coverage (coverageMatrix (D := D)
        (fun s : OffSchedule H B => s.1)) q x ≤
    coverage (coverageMatrix (D := D)
      (fun s : OnSchedule H m B => s.1)) (r.map f) x
  rw [hon, hoff]
  exact hmass

theorem onGameValue_ge_rho_mul_offGameValue {H m B D : ℕ}
    (hm1 : 1 ≤ m) (h2m : 2 * m ≤ B) (hB : B ≤ H) :
    privacyRho B m * offGameValue H m B D (by omega) hB ≤
      onGameValue H m B D (by omega) (by omega) hB := by
  classical
  let hm : m ≤ H := by omega
  let hmb : m ≤ B := by omega
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OffSchedule H B) := exists_offSchedule H B hB
  letI : Nonempty (OnSchedule H m B) := exists_onSchedule hm hmb hB
  obtain ⟨qStar, hqStar⟩ := value_attained (offMatrix H m B D)
  let pStar : Law (OnSchedule H m B) :=
    thinnedLaw hm hmb hB h2m qStar
  have hrow : ∀ x : FullInput H m,
      privacyRho B m * offGameValue H m B D hm hB ≤
        coverage (onMatrix H m B D) pStar x := by
    intro x
    have hcov := thinning_mass_lower (D := D) hm1 h2m hB qStar x
    have hoff : offGameValue H m B D hm hB ≤
        coverage (offMatrix H m B D) qStar x := by
      have hopt := optimal_coverage_ge_value (offMatrix H m B D)
        qStar hqStar x
      simpa [offGameValue] using hopt
    have hmul := mul_le_mul_of_nonneg_left hoff
      (by exact privacyRho_nonneg (B := B) (m := m) h2m)
    exact hmul.trans (by simpa [pStar] using hcov)
  have hworst : privacyRho B m * offGameValue H m B D hm hB ≤
      worst (onMatrix H m B D) pStar := by
    unfold worst
    apply Finset.le_inf' Finset.univ_nonempty
    intro x hx
    exact hrow x
  have hvalue := hworst.trans (worst_le_value (onMatrix H m B D) pStar)
  simpa [onGameValue, pStar, hm, hmb] using hvalue

def onToOff {H m B : ℕ} : OnSchedule H m B → OffSchedule H B :=
  fun s => ⟨s.1, s.2.1⟩

theorem on_coverage_eq_off_map {H m B D : ℕ}
    (q : Law (OnSchedule H m B)) (x : FullInput H m) :
    coverage (offMatrix H m B D) (q.map onToOff) x =
      coverage (onMatrix H m B D) q x := by
  classical
  have hmass := coverageMatrix_eq_mass (D := D)
    (fun s : OffSchedule H B => s.1) (q.map onToOff) x
  have hmass' := coverageMatrix_eq_mass (D := D)
    (fun s : OnSchedule H m B => s.1) q x
  have hset :
      Finset.univ.filter
          (fun s : OnSchedule H m B => onToOff s ∈
            feasibleScheduleEvent (D := D) (fun s : OffSchedule H B => s.1) x) =
        feasibleScheduleEvent (D := D)
          (fun s : OnSchedule H m B => s.1) x := by
    ext s
    simp [feasibleScheduleEvent, onToOff]
  change coverage (coverageMatrix (D := D)
      (fun s : OffSchedule H B => s.1)) (q.map onToOff) x =
    coverage (coverageMatrix (D := D)
      (fun s : OnSchedule H m B => s.1)) q x
  rw [hmass, hmass', Law.mass_map]
  rw [hset]

theorem onGameValue_le_offGameValue {H m B D : ℕ}
    (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H) :
    onGameValue H m B D hm hmb hB ≤
      offGameValue H m B D hm hB := by
  classical
  letI : Nonempty (FullInput H m) := ⟨terminalFullInput hm⟩
  letI : Nonempty (OffSchedule H B) := exists_offSchedule H B hB
  letI : Nonempty (OnSchedule H m B) := exists_onSchedule hm hmb hB
  change value (onMatrix H m B D) ≤ value (offMatrix H m B D)
  apply csSup_le (Set.range_nonempty (worst (onMatrix H m B D)))
  rintro _ ⟨q, rfl⟩
  have heq : worst (onMatrix H m B D) q =
    worst (offMatrix H m B D)
        (Law.map (onToOff (H := H) (m := m) (B := B)) q) := by
    unfold worst
    apply Finset.inf'_congr Finset.univ_nonempty rfl
    intro x hx
    exact (on_coverage_eq_off_map (D := D) q x).symm
  rw [heq]
  exact worst_le_value (offMatrix H m B D)
    (Law.map (onToOff (H := H) (m := m) (B := B)) q)

theorem privacyRho_le_one {B m : ℕ} (h2m : 2 * m ≤ B) :
    privacyRho B m ≤ 1 := by
  unfold privacyRho
  have hden : 0 < (Nat.choose B m : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hnum : (Nat.choose (B - m) m : ℝ) ≤ Nat.choose B m := by
    exact_mod_cast Nat.choose_le_choose m (by omega)
  exact (div_le_iff₀ hden).2 (by simpa using hnum)

theorem privacy_gap_bounds {H m B D : ℕ}
    (hm1 : 1 ≤ m) (h2m : 2 * m ≤ B) (hB : B ≤ H)
    (ε : ℝ) (hε : 0 ≤ ε) :
    0 ≤ causalOptimum H m B D ε - noncausalOptimum H m B D ε ∧
    causalOptimum H m B D ε - noncausalOptimum H m B D ε ≤
      (1 - privacyRho B m) *
        (1 - noncausalOptimum H m B D ε) ∧
    (1 - privacyRho B m) *
        (1 - noncausalOptimum H m B D ε) ≤ (m : ℝ) ^ 2 / B := by
  classical
  have hm : m ≤ H := by omega
  have hmb : m ≤ B := by omega
  have hoff : noncausalOptimum H m B D ε =
      1 - offGameValue H m B D hm hB :=
    noncausal_optimum_eq hm1 hm hmb hB ε hε
  have hon : causalOptimum H m B D ε =
      1 - onGameValue H m B D hm hmb hB :=
    causal_optimum_eq hm1 hm hmb hB ε hε
  have hgap : causalOptimum H m B D ε - noncausalOptimum H m B D ε =
      offGameValue H m B D hm hB - onGameValue H m B D hm hmb hB := by
    rw [hon, hoff]
    ring
  have horder : onGameValue H m B D hm hmb hB ≤
      offGameValue H m B D hm hB :=
    onGameValue_le_offGameValue hm hmb hB
  have hρ0 : 0 ≤ privacyRho B m := privacyRho_nonneg h2m
  have hρ1 : privacyRho B m ≤ 1 := privacyRho_le_one h2m
  have hgame := onGameValue_ge_rho_mul_offGameValue
    (D := D) hm1 h2m hB
  have hoffBounds := offGameValue_bounds (D := D) hm hB
  have hupper :
      offGameValue H m B D hm hB - onGameValue H m B D hm hmb hB ≤
        (1 - privacyRho B m) *
          offGameValue H m B D hm hB := by
    calc
      offGameValue H m B D hm hB - onGameValue H m B D hm hmb hB ≤
          offGameValue H m B D hm hB -
            privacyRho B m * offGameValue H m B D hm hB :=
        sub_le_sub_left hgame _
      _ = (1 - privacyRho B m) *
          offGameValue H m B D hm hB := by ring
  constructor
  · rw [hgap]
    exact sub_nonneg.mpr horder
  constructor
  · calc
      causalOptimum H m B D ε - noncausalOptimum H m B D ε =
          offGameValue H m B D hm hB - onGameValue H m B D hm hmb hB := hgap
      _ ≤ (1 - privacyRho B m) *
          offGameValue H m B D hm hB := hupper
      _ = (1 - privacyRho B m) *
          (1 - noncausalOptimum H m B D ε) := by rw [hoff]; ring
  · calc
      (1 - privacyRho B m) *
          (1 - noncausalOptimum H m B D ε) =
          (1 - privacyRho B m) *
            offGameValue H m B D hm hB := by rw [hoff]; ring
      _ ≤ 1 - privacyRho B m := by
        have hfactor : 0 ≤ 1 - privacyRho B m := sub_nonneg.mpr hρ1
        nlinarith [mul_le_mul_of_nonneg_left hoffBounds.2 hfactor]
      _ ≤ (m : ℝ) ^ 2 / B := by
        exact one_sub_rho_le_square_div hm1 h2m

end TrafficShaping
