import Mathlib

/-! Finite real-valued probability laws, without measure-theoretic assumptions. -/

namespace TrafficShaping

abbrev Law (α : Type*) [Fintype α] := ↥(stdSimplex ℝ α)

namespace Law

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

@[ext] theorem ext {p q : Law α} (h : ∀ a, p.val a = q.val a) : p = q :=
  Subtype.ext (funext h)

theorem nonneg (p : Law α) (a : α) : 0 ≤ p.val a := p.property.1 a

theorem total (p : Law α) : ∑ a, p.val a = 1 := p.property.2

def mass (p : Law α) (E : Finset α) : ℝ := ∑ a ∈ E, p.val a

@[simp] theorem mass_empty (p : Law α) : p.mass ∅ = 0 := by simp [mass]

@[simp] theorem mass_univ (p : Law α) : p.mass Finset.univ = 1 := p.total

theorem mass_nonneg (p : Law α) (E : Finset α) : 0 ≤ p.mass E :=
  Finset.sum_nonneg (fun a _ => p.nonneg a)

theorem mass_mono (p : Law α) {E F : Finset α} (h : E ⊆ F) : p.mass E ≤ p.mass F :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun a _ _ => p.nonneg a)

theorem mass_le_one (p : Law α) (E : Finset α) : p.mass E ≤ 1 := by
  simpa using p.mass_mono (Finset.subset_univ E)

variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem mass_eq_sum_ite (p : Law α) (E : Finset α) :
    p.mass E = ∑ a, if a ∈ E then p.val a else 0 := by
  simp only [mass, ← Finset.sum_filter]
  simp

@[simp] theorem mass_compl (p : Law α) (E : Finset α) :
    p.mass Eᶜ = 1 - p.mass E := by
  have h := Finset.sum_add_sum_compl E p.val
  change p.mass E + p.mass Eᶜ = ∑ a, p.val a at h
  rw [p.total] at h
  linarith

def dirac (a : α) : Law α :=
  ⟨fun b => if b = a then 1 else 0, by
    constructor
    · intro b
      change 0 ≤ (if b = a then 1 else 0 : ℝ)
      split_ifs <;> norm_num
    · simp⟩

@[simp] theorem dirac_apply (a b : α) : (dirac a).val b = if b = a then 1 else 0 := rfl

noncomputable def map (f : α → β) (p : Law α) : Law β :=
  ⟨fun b => ∑ a, if f a = b then p.val a else 0, by
    constructor
    · intro b
      apply Finset.sum_nonneg
      intro a _
      split_ifs
      · exact p.nonneg a
      · exact le_rfl
    · rw [Finset.sum_comm]
      simpa using p.total⟩

omit [DecidableEq α] in
@[simp] theorem map_apply (f : α → β) (p : Law α) (b : β) :
    (p.map f).val b = ∑ a, if f a = b then p.val a else 0 := rfl

@[simp] theorem map_id (p : Law α) : p.map id = p := by
  apply Law.ext
  intro a
  change (∑ b : α, if id b = a then p.val b else 0) = p.val a
  simp

omit [DecidableEq α] in
theorem mass_map (p : Law α) (f : α → β) (E : Finset β) :
    (p.map f).mass E = p.mass (Finset.univ.filter (fun a => f a ∈ E)) := by
  classical
  simp only [mass, map_apply]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.sum_filter]

omit [DecidableEq α] in
@[simp] theorem map_comp (p : Law α) (f : α → β) (g : β → γ) :
    (p.map f).map g = p.map (g ∘ f) := by
  classical
  apply Law.ext
  intro c
  change (∑ b : β, if g b = c then (∑ a : α, if f a = b then p.val a else 0) else 0) =
    ∑ a : α, if g (f a) = c then p.val a else 0
  calc
    _ = ∑ b : β, ∑ a : α, if f a = b ∧ g b = c then p.val a else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : g b = c <;> simp [h]
    _ = ∑ a : α, ∑ b : β, if f a = b ∧ g b = c then p.val a else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      have he (b : β) : (if f a = b ∧ g b = c then p.val a else 0) =
          (if f a = b then (if g (f a) = c then p.val a else 0) else 0) := by
        by_cases hf : f a = b
        · subst b; simp
        · simp [hf]
      simp_rw [he]
      simp


/-- Total variation of two laws on the complete finite output alphabet. -/
noncomputable def tv (p q : Law α) : ℝ := (∑ a, |p.val a - q.val a|) / 2

omit [DecidableEq α] in
theorem tv_nonneg (p q : Law α) : 0 ≤ p.tv q := by
  unfold tv
  positivity

omit [DecidableEq α] in
theorem tv_symm (p q : Law α) : p.tv q = q.tv p := by
  unfold tv
  simp_rw [abs_sub_comm]

omit [DecidableEq α] in
theorem tv_eq_sum_pos (p q : Law α) :
    p.tv q = ∑ a, if q.val a ≤ p.val a then p.val a - q.val a else 0 := by
  classical
  have ht : (∑ a, (p.val a - q.val a)) = 0 := by
    rw [Finset.sum_sub_distrib, p.total, q.total, sub_self]
  have hp (a : α) : |p.val a - q.val a| =
      2 * (if q.val a ≤ p.val a then p.val a - q.val a else 0) -
        (p.val a - q.val a) := by
    by_cases h : q.val a ≤ p.val a
    · rw [if_pos h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
    · rw [if_neg h, abs_of_neg (sub_neg.mpr (lt_of_not_ge h))]
      ring
  unfold tv
  simp_rw [hp]
  rw [Finset.sum_sub_distrib, ht, sub_zero, ← Finset.mul_sum]
  ring

noncomputable def positiveEvent (p q : Law α) : Finset α := by
  classical
  exact Finset.univ.filter (fun a => q.val a ≤ p.val a)

theorem tv_eq_event_difference (p q : Law α) :
    p.tv q = p.mass (positiveEvent p q) - q.mass (positiveEvent p q) := by
  classical
  rw [tv_eq_sum_pos, p.mass_eq_sum_ite, q.mass_eq_sum_ite, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp only [positiveEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> ring

theorem event_difference_le_tv (p q : Law α) (E : Finset α) :
    p.mass E - q.mass E ≤ p.tv q := by
  classical
  rw [p.mass_eq_sum_ite, q.mass_eq_sum_ite, ← Finset.sum_sub_distrib, tv_eq_sum_pos]
  apply Finset.sum_le_sum
  intro a _
  by_cases he : a ∈ E <;> by_cases h : q.val a ≤ p.val a <;>
    simp [he, h] <;> linarith

theorem abs_event_difference_le_tv (p q : Law α) (E : Finset α) :
    |p.mass E - q.mass E| ≤ p.tv q := by
  apply abs_le.mpr
  constructor
  · have h := q.event_difference_le_tv p E
    rw [tv_symm] at h
    linarith
  · exact p.event_difference_le_tv q E

/-- Event-wise privacy at zero multiplicative parameter is exactly TV distance. -/
theorem zero_privacy_iff_tv (p q : Law α) (δ : ℝ) :
    (∀ E : Finset α, p.mass E ≤ q.mass E + δ ∧ q.mass E ≤ p.mass E + δ) ↔
      p.tv q ≤ δ := by
  constructor
  · intro h
    rw [tv_eq_event_difference]
    have he := (h (positiveEvent p q)).1
    linarith
  · intro h E
    have h1 := p.event_difference_le_tv q E
    have h2 := q.event_difference_le_tv p E
    rw [tv_symm] at h2
    constructor <;> linarith

theorem tv_le_one (p q : Law α) : p.tv q ≤ 1 := by
  rw [tv_eq_event_difference]
  have h1 := p.mass_le_one (positiveEvent p q)
  have h0 := q.mass_nonneg (positiveEvent p q)
  linarith

omit [DecidableEq α] in
theorem mass_filter (p : Law α) (P : α → Prop) [DecidablePred P] :
    p.mass (Finset.univ.filter P) = ∑ a, if P a then p.val a else 0 := by
  simp only [mass, Finset.sum_filter]

omit [DecidableEq α] in
/-- The same-seed coupling inequality, proved with finite sums. -/
theorem coupling_tv_le (p : Law α) (f g : α → β) :
    (p.map f).tv (p.map g) ≤ p.mass (Finset.univ.filter (fun a => f a ≠ g a)) := by
  classical
  let E := positiveEvent (p.map f) (p.map g)
  rw [tv_eq_event_difference]
  change (p.map f).mass E - (p.map g).mass E ≤ _
  rw [p.mass_map, p.mass_map, p.mass_filter, p.mass_filter, p.mass_filter,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro a _
  have hn := p.nonneg a
  by_cases heq : f a = g a
  · simp [heq]
  · by_cases hf : f a ∈ E <;> by_cases hg : g a ∈ E <;>
      simp [heq, hf, hg] <;> linarith

/-- A repair that always lands in the feasible set and fixes every feasible
base output attains exactly the mass of the infeasible base schedules. -/
theorem repair_tv_identity (p : Law α) (base repair : α → β) (F : Finset β)
    (hgood : ∀ a, repair a ∈ F)
    (hfix : ∀ a, base a ∈ F → repair a = base a) :
    (p.map repair).tv (p.map base) =
      p.mass (Finset.univ.filter (fun a => base a ∉ F)) := by
  classical
  apply le_antisymm
  · apply (p.coupling_tv_le repair base).trans
    apply p.mass_mono
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    intro hf
    exact ha (hfix a hf)
  · have he := (p.map base).event_difference_le_tv (p.map repair) Fᶜ
    have hz : (p.map repair).mass Fᶜ = 0 := by
      rw [p.mass_map, p.mass_filter]
      simp [hgood]
    have hb : (p.map base).mass Fᶜ =
        p.mass (Finset.univ.filter (fun a => base a ∉ F)) := by
      rw [p.mass_map]
      simp only [Finset.mem_compl]
    rw [hz, sub_zero, hb, tv_symm] at he
    exact he


/-- Both event inequalities, with a finite real multiplicative parameter. -/
def PrivatePair (p q : Law α) (ε δ : ℝ) : Prop :=
  ∀ E : Finset α,
    p.mass E ≤ Real.exp ε * q.mass E + δ ∧
    q.mass E ≤ Real.exp ε * p.mass E + δ

theorem privatePair_zero_iff_tv (p q : Law α) (δ : ℝ) :
    PrivatePair p q 0 δ ↔ p.tv q ≤ δ := by
  simpa [PrivatePair] using p.zero_privacy_iff_tv q δ

theorem privatePair_of_tv (p q : Law α) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : p.tv q ≤ δ) : PrivatePair p q ε δ := by
  have he : 1 ≤ Real.exp ε := Real.one_le_exp_iff.mpr hε
  have hzero := (p.zero_privacy_iff_tv q δ).mpr hδ
  intro E
  have hp : p.mass E ≤ Real.exp ε * p.mass E := by
    simpa using mul_le_mul_of_nonneg_right he (p.mass_nonneg E)
  have hq : q.mass E ≤ Real.exp ε * q.mass E := by
    simpa using mul_le_mul_of_nonneg_right he (q.mass_nonneg E)
  constructor <;> have hz := hzero E <;> linarith

/-- Hard impossibility under the active law forces additive privacy loss,
independently of the value of the finite real parameter epsilon. -/
theorem forbidden_event (p q : Law α) {ε δ : ℝ} (h : PrivatePair p q ε δ)
    (E : Finset α) (hz : p.mass E = 0) : q.mass E ≤ δ := by
  have hb := (h E).2
  simpa [hz] using hb

theorem mass_zero_iff (p : Law α) (E : Finset α) :
    p.mass E = 0 ↔ ∀ a ∈ E, p.val a = 0 := by
  constructor
  · intro h a ha
    have hle : p.val a ≤ p.mass E :=
      Finset.single_le_sum (fun b _ => p.nonneg b) ha
    exact le_antisymm (by linarith) (p.nonneg a)
  · intro h
    exact Finset.sum_eq_zero h

theorem exists_of_map_pos (p : Law α) (f : α → β) (b : β)
    (hb : 0 < (p.map f).val b) : ∃ a, 0 < p.val a ∧ f a = b := by
  classical
  by_contra hn
  have hz : (p.map f).val b = 0 := by
    rw [map_apply]
    apply Finset.sum_eq_zero
    intro a _
    by_cases hf : f a = b
    · rw [if_pos hf]
      have hp : ¬ 0 < p.val a := fun h => hn ⟨a, h, hf⟩
      exact le_antisymm (le_of_not_gt hp) (p.nonneg a)
    · simp [hf]
  linarith

theorem mass_map_ge (p : Law α) (f : α → β) (E : Finset α) (F : Finset β)
    (h : ∀ a, 0 < p.val a → a ∈ E → f a ∈ F) :
    p.mass E ≤ (p.map f).mass F := by
  classical
  rw [p.mass_eq_sum_ite, p.mass_map, p.mass_filter]
  apply Finset.sum_le_sum
  intro a _
  by_cases he : a ∈ E
  · by_cases hp : 0 < p.val a
    · simp [he, h a hp he]
    · have hz : p.val a = 0 := le_antisymm (le_of_not_gt hp) (p.nonneg a)
      simp [hz]
  · simp only [if_neg he]
    split_ifs
    · exact p.nonneg a
    · exact le_rfl


theorem le_map_apply (p : Law α) (f : α → β) (a : α) :
    p.val a ≤ (p.map f).val (f a) := by
  classical
  rw [map_apply]
  calc
    p.val a = (if f a = f a then p.val a else 0) := by simp
    _ ≤ ∑ b, if f b = f a then p.val b else 0 := by
      apply Finset.single_le_sum (f := fun b : α => if f b = f a then p.val b else 0) _ (Finset.mem_univ a)
      intro b _
      split_ifs
      · exact p.nonneg b
      · exact le_rfl

theorem map_pos_of_pos (p : Law α) (f : α → β) (a : α) (ha : 0 < p.val a) :
    0 < (p.map f).val (f a) :=
  ha.trans_le (p.le_map_apply f a)

theorem mass_zero_of_support (p : Law α) (E : Finset α)
    (h : ∀ a, 0 < p.val a → a ∉ E) : p.mass E = 0 := by
  apply (p.mass_zero_iff E).mpr
  intro a ha
  have hz : ¬ 0 < p.val a := fun hp => h a hp ha
  exact le_antisymm (le_of_not_gt hz) (p.nonneg a)

end Law
end TrafficShaping
