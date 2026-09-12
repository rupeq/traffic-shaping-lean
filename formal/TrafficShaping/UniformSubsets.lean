import Mathlib
import TrafficShaping.Law

/-!
Uniform finite laws and uniform fixed-size subsets.

The definitions in this file deliberately stay at the finite-sum level used by
`TrafficShaping.Law`: this keeps the resulting API convenient for the game
files while making the counting arguments reduce to the `Finset` powerset
lemmas in Mathlib.
-/

namespace TrafficShaping

namespace Law

variable {α : Type*} [Fintype α]

/-- The uniform probability law on a nonempty finite type. -/
noncomputable def uniform [Nonempty α] : Law α :=
  ⟨fun _ => (Fintype.card α : ℝ)⁻¹, by
    constructor
    · intro _
      positivity
    · rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)⟩

@[simp] theorem uniform_apply [Nonempty α] (a : α) :
    (uniform : Law α).val a = (Fintype.card α : ℝ)⁻¹ := rfl

@[simp] theorem uniform_mass [Nonempty α] [DecidableEq α] (E : Finset α) :
    (uniform : Law α).mass E = (E.card : ℝ) / Fintype.card α := by
  change ∑ _a ∈ E, (Fintype.card α : ℝ)⁻¹ = (E.card : ℝ) / Fintype.card α
  rw [Finset.sum_const, nsmul_eq_mul]
  simp [div_eq_mul_inv]

end Law

/-- The finite type of `k`-element subsets of a finite set `s`. -/
abbrev FixedSubset (s : Finset α) (k : ℕ) := {u : Finset α // u ∈ s.powersetCard k}

@[simp] theorem fixedSubset_card (s : Finset α) (k : ℕ) :
    Fintype.card (FixedSubset s k) = Nat.choose s.card k := by
  simp [FixedSubset]

theorem fixedSubset_nonempty (s : Finset α) (k : ℕ) (h : k ≤ s.card) :
    Nonempty (FixedSubset s k) := by
  rw [← Fintype.card_pos_iff, fixedSubset_card]
  exact Nat.choose_pos h

namespace FixedSubset

variable {s : Finset α} {k : ℕ}

@[simp] theorem mem_val (u : FixedSubset s k) : u.1 ⊆ s :=
  (Finset.mem_powersetCard.mp u.2).1

@[simp] theorem card_val (u : FixedSubset s k) : u.1.card = k :=
  (Finset.mem_powersetCard.mp u.2).2

end FixedSubset

theorem card_filter_fixedSubset_containing [DecidableEq α] (s t : Finset α) (k : ℕ) :
    ((Finset.univ : Finset (FixedSubset s k)).filter (fun u => t ⊆ u.1)).card =
      ((s.powersetCard k).filter (t ⊆ ·)).card := by
  classical
  let p : Finset α → Prop := fun u => u ∈ s.powersetCard k
  let e : FixedSubset s k ↪ Finset α := Function.Embedding.subtype p
  let E : Finset (FixedSubset s k) :=
    Finset.univ.filter (fun u => t ⊆ u.1)
  have hmap : E.map e = (Finset.univ.map e).filter (t ⊆ ·) := by
    rw [Finset.filter_map]
    rfl
  have huniv : Finset.univ.map e = s.powersetCard k := by
    rw [show (Finset.univ : Finset (FixedSubset s k)) =
        (s.powersetCard k).attach by ext u; simp [FixedSubset]]
    simpa [p] using (Finset.attach_map_val (s := s.powersetCard k))
  calc
    ((Finset.univ : Finset (FixedSubset s k)).filter (fun u => t ⊆ u.1)).card = E.card := rfl
    _ = (E.map e).card := (Finset.card_map e).symm
    _ = ((Finset.univ.map e).filter (t ⊆ ·)).card := congrArg Finset.card hmap
    _ = ((s.powersetCard k).filter (t ⊆ ·)).card := by rw [huniv]

theorem uniform_fixedSubset_containment [DecidableEq α]
    (s t : Finset α) (k : ℕ) (hts : t ⊆ s) (htk : t.card ≤ k)
    (hks : k ≤ s.card) :
    (@Law.uniform (FixedSubset s k) _ (fixedSubset_nonempty s k hks)).mass
        (Finset.univ.filter (fun u : FixedSubset s k => t ⊆ u.1)) =
      (Nat.choose (s.card - t.card) (k - t.card) : ℝ) /
        Nat.choose s.card k := by
  letI : Nonempty (FixedSubset s k) := fixedSubset_nonempty s k hks
  rw [Law.uniform_mass, card_filter_fixedSubset_containing]
  rw [Finset.card_filter_powersetCard_subset t s k hts htk, fixedSubset_card]

/-- The two equivalent hypergeometric forms of the retention factor `ρ`. -/
theorem rho_binomial_identity (B m : ℕ) (h : 2 * m ≤ B) :
    (Nat.choose (B - m) m : ℝ) / Nat.choose B m =
      (Nat.choose (B - m) (B - 2 * m) : ℝ) / Nat.choose B (B - m) := by
  have hnum : Nat.choose (B - m) (B - 2 * m) = Nat.choose (B - m) m := by
    apply Nat.choose_symm_of_eq_add
    omega
  have hden : Nat.choose B (B - m) = Nat.choose B m := by
    apply Nat.choose_symm_of_eq_add
    omega
  rw [hnum, hden]

theorem containment_probability_symmetry [DecidableEq α]
    (s t : Finset α) (k : ℕ) (hts : t ⊆ s) (htk : t.card ≤ k)
    (hks : k ≤ s.card) :
    (Nat.choose (s.card - t.card) (k - t.card) : ℝ) / Nat.choose s.card k =
      (Nat.choose k t.card : ℝ) / Nat.choose s.card t.card := by
  have hchoose := Nat.choose_mul (n := s.card) (k := k) (s := t.card) htk
  have hdenk : (Nat.choose s.card k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hks
  have hdent : (Nat.choose s.card t.card : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (htk.trans hks)
  field_simp [hdenk, hdent]
  have hchoose' : Nat.choose (s.card - t.card) (k - t.card) *
      Nat.choose s.card t.card = Nat.choose s.card k * Nat.choose k t.card := by
    simpa [Nat.mul_comm] using hchoose.symm
  exact_mod_cast hchoose'

theorem uniform_fixedSubset_containment_symmetric [DecidableEq α]
    (s t : Finset α) (k : ℕ) (hts : t ⊆ s) (htk : t.card ≤ k)
    (hks : k ≤ s.card) :
    (@Law.uniform (FixedSubset s k) _ (fixedSubset_nonempty s k hks)).mass
        (Finset.univ.filter (fun u : FixedSubset s k => t ⊆ u.1)) =
      (Nat.choose k t.card : ℝ) / Nat.choose s.card t.card := by
  calc
    _ = (Nat.choose (s.card - t.card) (k - t.card) : ℝ) /
          Nat.choose s.card k :=
      uniform_fixedSubset_containment s t k hts htk hks
    _ = _ := containment_probability_symmetry s t k hts htk hks

theorem uniform_fixedSubset_containment_zero [DecidableEq α]
    (s t : Finset α) (k : ℕ) (hks : k ≤ s.card) (htk : k < t.card) :
    (@Law.uniform (FixedSubset s k) _ (fixedSubset_nonempty s k hks)).mass
        (Finset.univ.filter (fun u : FixedSubset s k => t ⊆ u.1)) = 0 := by
  letI : Nonempty (FixedSubset s k) := fixedSubset_nonempty s k hks
  have hfilter :
      (Finset.univ.filter (fun u : FixedSubset s k => t ⊆ u.1)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro u hu htu
    have hcard : t.card ≤ u.1.card := Finset.card_le_card htu
    have hle : t.card ≤ k := by simpa using hcard
    exact (Nat.not_le_of_lt htk) hle
  rw [hfilter, Law.mass_empty]

theorem uniform_fixedSubset_contains_singleton [DecidableEq α]
    (s : Finset α) (a : α) (ha : a ∈ s) (k : ℕ) (hk : 1 ≤ k)
    (hks : k ≤ s.card) :
    (@Law.uniform (FixedSubset s k) _ (fixedSubset_nonempty s k hks)).mass
        (Finset.univ.filter (fun u : FixedSubset s k => ({a} : Finset α) ⊆ u.1)) =
      (k : ℝ) / s.card := by
  letI : Nonempty (FixedSubset s k) := fixedSubset_nonempty s k hks
  have hcontain := uniform_fixedSubset_containment s ({a} : Finset α) k
    (by simpa using ha) (by simpa using hk) hks
  have hchoose := Nat.choose_mul (n := s.card) (k := k) (s := 1) hk
  have hden : (Nat.choose s.card k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hks
  have hcard : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr ⟨a, ha⟩)
  rw [show ({a} : Finset α).card = 1 by simp] at hcontain
  rw [show s.card - 1 = s.card - ({a} : Finset α).card by simp] at hcontain
  rw [show k - 1 = k - ({a} : Finset α).card by simp] at hcontain
  calc
    _ = (Nat.choose (s.card - 1) (k - 1) : ℝ) / Nat.choose s.card k := hcontain
    _ = (k : ℝ) / s.card := by
      field_simp [hden, hcard]
      have hchoose' : Nat.choose (s.card - 1) (k - 1) * s.card =
          Nat.choose s.card k * k := by
        simpa [Nat.choose_one_right, Nat.mul_comm] using hchoose.symm
      exact_mod_cast hchoose'

theorem uniform_fixedSubset_omits_singleton [DecidableEq α]
    (s : Finset α) (a : α) (ha : a ∈ s) (m : ℕ) (hm : m < s.card) :
    (@Law.uniform (FixedSubset s (s.card - m)) _
        (fixedSubset_nonempty s (s.card - m) (Nat.sub_le _ _))).mass
        (Finset.univ.filter (fun u : FixedSubset s (s.card - m) => a ∉ u.1)) =
      (m : ℝ) / s.card := by
  letI : Nonempty (FixedSubset s (s.card - m)) :=
    fixedSubset_nonempty s (s.card - m) (Nat.sub_le _ _)
  let E : Finset (FixedSubset s (s.card - m)) :=
    Finset.univ.filter (fun u => ({a} : Finset α) ⊆ u.1)
  have hkeep := uniform_fixedSubset_contains_singleton s a ha (s.card - m)
    (Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hm)) (Nat.sub_le _ _)
  have hcomp :
      (Finset.univ.filter (fun u : FixedSubset s (s.card - m) => a ∉ u.1)) = Eᶜ := by
    ext u
    simp [E, Finset.singleton_subset_iff]
  have hcard : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr ⟨a, ha⟩)
  rw [hcomp, Law.mass_compl, hkeep]
  rw [Nat.cast_sub (Nat.le_of_lt hm)]
  field_simp [hcard]
  ring

end TrafficShaping
