import TrafficShaping.UniformSubsets

/-!
The finite-union estimate for uniform thinning.  This file contains only the
counting bound used by the privacy-gap argument; the game construction stays
in its consumer module.
-/

namespace TrafficShaping

open scoped BigOperators

theorem one_sub_rho_le_square_div {B m : ℕ} (hm1 : 1 ≤ m) (h2 : 2 * m ≤ B) :
    1 - (Nat.choose (B - m) m : ℝ) / Nat.choose B m ≤ (m : ℝ) ^ 2 / B := by
  have hmb : m ≤ B := by omega
  let T : Finset (Fin B) :=
    (Finset.univ : Finset (Fin m)).map (Fin.castLEEmb hmb)
  have hTcard : T.card = m := by
    simp [T]
  let U := FixedSubset (Finset.univ : Finset (Fin B)) (B - m)
  have hSk : B - m ≤ (Finset.univ : Finset (Fin B)).card := by simp
  letI : Nonempty U := fixedSubset_nonempty (Finset.univ : Finset (Fin B)) (B - m) hSk
  let E : Finset U := Finset.univ.filter (fun u => T ⊆ u.1)
  let bad : Fin B → Finset U := fun a =>
    Finset.univ.filter (fun u => a ∉ u.1)
  have hTS : T ⊆ (Finset.univ : Finset (Fin B)) := Finset.subset_univ T
  have hTle : T.card ≤ B - m := by rw [hTcard]; omega
  have hkeep :
      (@Law.uniform U _
        (fixedSubset_nonempty (Finset.univ : Finset (Fin B)) (B - m) hSk)).mass E =
        (Nat.choose (B - m) m : ℝ) / Nat.choose B m := by
    have h := uniform_fixedSubset_containment (Finset.univ : Finset (Fin B)) T
      (B - m) hTS hTle hSk
    have h' :
        (@Law.uniform U _
          (fixedSubset_nonempty (Finset.univ : Finset (Fin B)) (B - m) hSk)).mass E =
          (Nat.choose (B - m) (B - 2 * m) : ℝ) /
            Nat.choose B (B - m) := by
      rw [hTcard] at h
      have hsub : B - m - m = B - 2 * m := by omega
      rw [hsub] at h
      simpa only [E, U, Finset.card_univ, Fintype.card_fin] using h
    calc
      _ = (Nat.choose (B - m) (B - 2 * m) : ℝ) /
            Nat.choose B (B - m) := h'
      _ = _ := (rho_binomial_identity B m h2).symm
  have hbad_subset : Eᶜ ⊆ T.biUnion bad := by
    intro u hu
    have hu' : ¬ T ⊆ u.1 := by simpa [E] using hu
    obtain ⟨a, haT, hau⟩ := Finset.not_subset.mp hu'
    apply Finset.mem_biUnion.mpr
    refine ⟨a, haT, ?_⟩
    simp [bad, hau]
  have hmass_union :
      (@Law.uniform U _
        (fixedSubset_nonempty (Finset.univ : Finset (Fin B)) (B - m) hSk)).mass
          (T.biUnion bad) ≤
        (∑ a ∈ T,
          (@Law.uniform U _
            (fixedSubset_nonempty (Finset.univ : Finset (Fin B)) (B - m) hSk)).mass
              (bad a)) := by
    have hcard : (T.biUnion bad).card ≤ ∑ a ∈ T, (bad a).card :=
      Finset.card_biUnion_le
    have hden : (0 : ℝ) < Fintype.card U := by positivity
    rw [Law.uniform_mass]
    simp_rw [Law.uniform_mass]
    rw [← Finset.sum_div]
    exact (div_le_div_iff_of_pos_right hden).mpr (by exact_mod_cast hcard)
  have hbad_mass (a : Fin B) (haT : a ∈ T) :
      (@Law.uniform U _
        (fixedSubset_nonempty (Finset.univ : Finset (Fin B)) (B - m) hSk)).mass (bad a) =
        (m : ℝ) / B := by
    have haS : a ∈ (Finset.univ : Finset (Fin B)) := Finset.mem_univ a
    have hmB : m < B := by omega
    let KeepA : Finset U :=
      Finset.univ.filter (fun u => ({a} : Finset (Fin B)) ⊆ u.1)
    have hkeepA := uniform_fixedSubset_contains_singleton
      (Finset.univ : Finset (Fin B)) a haS (B - m) (by omega) hSk
    have hkeepA' :
      (@Law.uniform U _
          (fixedSubset_nonempty (Finset.univ : Finset (Fin B)) (B - m) hSk)).mass KeepA =
          ((B - m : ℕ) : ℝ) / B := by
      simpa only [KeepA, U, Finset.card_univ, Fintype.card_fin] using hkeepA
    have hcompA : bad a = KeepAᶜ := by
      ext u
      simp [bad, KeepA, Finset.singleton_subset_iff]
    calc
      _ = (@Law.uniform U _
          (fixedSubset_nonempty (Finset.univ : Finset (Fin B)) (B - m) hSk)).mass KeepAᶜ := by
        rw [hcompA]
      _ = 1 - (@Law.uniform U _
          (fixedSubset_nonempty (Finset.univ : Finset (Fin B)) (B - m) hSk)).mass KeepA :=
        Law.mass_compl _ _
      _ = 1 - ((B - m : ℕ) : ℝ) / B := by rw [hkeepA']
      _ = (m : ℝ) / B := by
        rw [Nat.cast_sub (Nat.le_of_lt hmB)]
        have hBne : (B : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hmB))
        field_simp [hBne]
        ring
  have hsum :
      ∑ a ∈ T,
          (@Law.uniform U _
            (fixedSubset_nonempty (Finset.univ : Finset (Fin B)) (B - m) hSk)).mass
            (bad a) =
        (m : ℝ) ^ 2 / B := by
    calc
      _ = ∑ _a ∈ T, (m : ℝ) / B := by
        apply Finset.sum_congr rfl
        intro a haT
        exact hbad_mass a haT
      _ = (m : ℝ) ^ 2 / B := by
        rw [Finset.sum_const, hTcard, nsmul_eq_mul]
        ring
  calc
    1 - (Nat.choose (B - m) m : ℝ) / Nat.choose B m =
        (@Law.uniform U _
          (fixedSubset_nonempty (Finset.univ : Finset (Fin B)) (B - m) hSk)).mass Eᶜ := by
      rw [Law.mass_compl, hkeep]
    _ ≤ (@Law.uniform U _
          (fixedSubset_nonempty (Finset.univ : Finset (Fin B)) (B - m) hSk)).mass
          (T.biUnion bad) :=
      Law.mass_mono _ hbad_subset
    _ ≤ ∑ a ∈ T,
          (@Law.uniform U _
            (fixedSubset_nonempty (Finset.univ : Finset (Fin B)) (B - m) hSk)).mass
            (bad a) :=
      hmass_union
    _ = (m : ℝ) ^ 2 / B := hsum

end TrafficShaping
