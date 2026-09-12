import TrafficShaping.CorollaryDefinitions

/-!
  The fixed block schedule used for the perfect-privacy corollary.

  The auxiliary block finsets below are deliberately kept local to this file:
  they expose the elementary arithmetic behind `perfectSchedule` without
  changing the shared definitions used by the other corollaries.
-/

namespace TrafficShaping

private def blockPeriod (m D : ℕ) : ℕ := D + m

private noncomputable def fullBlockSlots {H m D : ℕ} (q : ℕ) (hq : q < H / blockPeriod m D) : Trace H := by
  classical
  let p := blockPeriod m D
  have hq1 : q + 1 ≤ H / p := Nat.succ_le_of_lt hq
  have hmul : p * (q + 1) ≤ p * (H / p) := Nat.mul_le_mul_left p hq1
  have hdiv : p * (H / p) ≤ H := by
    calc
      p * (H / p) ≤ H % p + p * (H / p) := Nat.le_add_left _ _
      _ = H := Nat.mod_add_div H p
  have hend : q * p + p ≤ H := by
    simpa [Nat.succ_mul, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hmul.trans hdiv
  exact (Finset.univ : Finset (Fin m)).image (fun j : Fin m =>
    (⟨q * p + D + (j : ℕ), by
      have hj : (j : ℕ) < m := j.2
      have hjp : D + j < p := by
        dsimp [p, blockPeriod]
        omega
      omega⟩ : Fin H))

private noncomputable def fullBlockSlotsTotal (H m D q : ℕ) : Trace H :=
  if hq : q < H / blockPeriod m D then
    fullBlockSlots q hq
  else ∅

private noncomputable def remainderSlots (H m D : ℕ) : Trace H := by
  classical
  let p := blockPeriod m D
  let a := H / p
  let b := H % p
  let c := min m b
  have hdecomp : b + a * p = H := by
    simpa [a, b, Nat.mul_comm] using Nat.mod_add_div H p
  exact (Finset.univ : Finset (Fin c)).image (fun j : Fin c =>
    (⟨a * p + (b - c) + (j : ℕ), by
      have hj : (j : ℕ) < c := j.2
      have hc : c ≤ b := min_le_right _ _
      omega⟩ : Fin H))

private lemma fullBlockSlots_card {H m D q : ℕ} (hq : q < H / blockPeriod m D) :
    (fullBlockSlots (H := H) (m := m) (D := D) q hq).card = m := by
  classical
  unfold fullBlockSlots
  dsimp only
  calc
    _ = (Finset.univ : Finset (Fin m)).card := by
      apply Finset.card_image_of_injective
      intro j₁ j₂ h
      apply Fin.ext
      simpa using congrArg Fin.val h
    _ = m := by simp

private lemma remainderSlots_card {H m D : ℕ} :
    (remainderSlots H m D).card = min m (H % blockPeriod m D) := by
  classical
  unfold remainderSlots
  dsimp only
  let c := min m (H % blockPeriod m D)
  calc
    _ = (Finset.univ : Finset (Fin c)).card := by
      apply Finset.card_image_of_injective
      intro j₁ j₂ h
      apply Fin.ext
      simpa using congrArg Fin.val h
    _ = c := by simp
    _ = min m (H % blockPeriod m D) := rfl

private lemma fullBlockSlots_mem_bounds {H m D q : ℕ}
    (hq : q < H / blockPeriod m D) {t : Fin H}
    (ht : t ∈ fullBlockSlots (H := H) (m := m) (D := D) q hq) :
    q * blockPeriod m D ≤ t.val ∧ t.val < (q + 1) * blockPeriod m D := by
  classical
  rcases Finset.mem_image.mp ht with ⟨j, hj, rfl⟩
  have hj' : (j : ℕ) < m := j.2
  let p := blockPeriod m D
  have hp : 0 < p := by
    dsimp [p, blockPeriod]
    omega
  have hq1 : q + 1 ≤ H / p := Nat.succ_le_of_lt hq
  have hmul : p * (q + 1) ≤ p * (H / p) := Nat.mul_le_mul_left p hq1
  have hdiv : p * (H / p) ≤ H := by
    calc
      p * (H / p) ≤ H % p + p * (H / p) := Nat.le_add_left _ _
      _ = H := Nat.mod_add_div H p
  have hend : q * p + p ≤ H := by
    simpa [Nat.succ_mul, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hmul.trans hdiv
  dsimp [blockPeriod]
  have hstep : q * (D + m) + (D + m) = (q + 1) * (D + m) := by
    simp [Nat.succ_mul]
  omega

private lemma remainderSlots_mem_bounds {H m D : ℕ} {t : Fin H}
    (ht : t ∈ remainderSlots H m D) :
    H / blockPeriod m D * blockPeriod m D ≤ t.val ∧ t.val < H := by
  classical
  rcases Finset.mem_image.mp ht with ⟨j, hj, rfl⟩
  let p := blockPeriod m D
  let a := H / p
  let b := H % p
  let c := min m b
  have hj' : (j : ℕ) < c := j.2
  have hc : c ≤ b := min_le_right _ _
  have hdecomp : b + a * p = H := by
    simpa [a, b, Nat.mul_comm] using Nat.mod_add_div H p
  have hdecomp' : a * p + b = H := by simpa [Nat.add_comm] using hdecomp
  dsimp [p, blockPeriod, a, b, c] at *
  omega

private lemma fullBlockSlots_mem_schedule {H m D q : ℕ}
    (hq : q < H / blockPeriod m D) {t : Fin H}
    (ht : t ∈ fullBlockSlots (H := H) (m := m) (D := D) q hq) :
    t ∈ perfectSchedule H m D := by
  classical
  have hb := fullBlockSlots_mem_bounds hq ht
  have hp : 0 < blockPeriod m D := by
    by_contra h
    have hp0 : blockPeriod m D = 0 := Nat.eq_zero_of_not_pos h
    simp [hp0] at hq
  have hq1 : q + 1 ≤ H / blockPeriod m D := Nat.succ_le_of_lt hq
  have hmul : blockPeriod m D * (q + 1) ≤
      blockPeriod m D * (H / blockPeriod m D) :=
    Nat.mul_le_mul_left _ hq1
  have hdiv : blockPeriod m D * (H / blockPeriod m D) ≤ H := by
    calc
      blockPeriod m D * (H / blockPeriod m D) ≤
          H % blockPeriod m D + blockPeriod m D * (H / blockPeriod m D) :=
        Nat.le_add_left _ _
      _ = H := Nat.mod_add_div H (blockPeriod m D)
  have hfull : (q + 1) * blockPeriod m D ≤ H := by
    simpa [Nat.mul_comm] using hmul.trans hdiv
  have hqdiv : t.val / blockPeriod m D = q := by
    apply Nat.div_eq_of_lt_le
    · exact hb.1
    · simpa [Nat.succ_mul, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hb.2
  simp only [perfectSchedule, Finset.mem_filter, Finset.mem_univ, true_and]
  change min H ((t.val / blockPeriod m D + 1) * blockPeriod m D) - m ≤ t.val
  have hmin : min H ((q + 1) * blockPeriod m D) = (q + 1) * blockPeriod m D := by
    apply min_eq_right
    exact hfull
  have hqdiv' : t.val / blockPeriod m D = q := by simpa using hqdiv
  rcases Finset.mem_image.mp ht with ⟨j, hj, rfl⟩
  have hj' : (j : ℕ) < m := j.2
  have hmul' : (q + 1) * blockPeriod m D =
      q * blockPeriod m D + D + m := by
    simp [blockPeriod, Nat.succ_mul, Nat.add_assoc, Nat.add_comm]
  have htarget : (q + 1) * blockPeriod m D - m ≤
      q * blockPeriod m D + D + (j : ℕ) := by
    omega
  simpa [hqdiv', hmin] using htarget

private lemma remainderSlots_mem_schedule {H m D : ℕ} (hm1 : 1 ≤ m) {t : Fin H}
    (ht : t ∈ remainderSlots H m D) :
    t ∈ perfectSchedule H m D := by
  classical
  let p := blockPeriod m D
  let a := H / p
  let b := H % p
  let c := min m b
  have hp : 0 < p := by
    dsimp [p, blockPeriod]
    omega
  have hdecomp : b + a * p = H := by
    simpa [a, b, Nat.mul_comm] using Nat.mod_add_div H p
  have hHle : H ≤ (a + 1) * p := by
    have hb : b < p := Nat.mod_lt _ hp
    have hdecomp' : a * p + b = H := by simpa [Nat.add_comm] using hdecomp
    have hstep : a * p + p = (a + 1) * p := by simp [Nat.succ_mul]
    omega
  have hqdiv : t.val / p = a := by
    have hb := remainderSlots_mem_bounds ht
    apply Nat.div_eq_of_lt_le
    · exact hb.1
    · exact lt_of_lt_of_le t.isLt hHle
  simp only [perfectSchedule, Finset.mem_filter, Finset.mem_univ, true_and]
  change min H ((t.val / blockPeriod m D + 1) * blockPeriod m D) - m ≤ t.val
  have hqdiv' : t.val / blockPeriod m D = a := by simpa [p] using hqdiv
  rw [hqdiv']
  have hmin : min H ((a + 1) * p) = H := by
    exact min_eq_left hHle
  rw [hmin]
  have ht' := remainderSlots_mem_bounds ht
  rcases Finset.mem_image.mp ht with ⟨j, hj, rfl⟩
  have hj' : (j : ℕ) < c := j.2
  have hstart : H - m ≤ a * p + (b - c) := by
    by_cases hb : b ≤ m
    · have hc' : c = b := by simp [c, hb]
      have hdecomp' : a * p + b = H := by simpa [Nat.add_comm] using hdecomp
      rw [hc']
      omega
    · have hb' : m ≤ b := by omega
      have hc' : c = m := by simp [c, hb']
      have hdecomp' : a * p + b = H := by simpa [Nat.add_comm] using hdecomp
      rw [hc']
      omega
  exact hstart.trans (Nat.le_add_right _ _)

private lemma fullBlockSlots_disjoint_of_lt {H m D : ℕ} {q₁ q₂ : ℕ}
    (hq₁ : q₁ < H / blockPeriod m D) (hq₂ : q₂ < H / blockPeriod m D)
    (hlt : q₁ < q₂) :
    Disjoint (fullBlockSlots (H := H) (m := m) (D := D) q₁ hq₁)
      (fullBlockSlots (H := H) (m := m) (D := D) q₂ hq₂) := by
  classical
  apply Finset.disjoint_left.mpr
  intro t ht₁ ht₂
  have hb₁ := fullBlockSlots_mem_bounds hq₁ ht₁
  have hb₂ := fullBlockSlots_mem_bounds hq₂ ht₂
  have hstep : q₁ + 1 ≤ q₂ := by omega
  have hmul : (q₁ + 1) * blockPeriod m D ≤ q₂ * blockPeriod m D := by
    exact Nat.mul_le_mul_right _ hstep
  omega

private lemma fullBlockSlots_disjoint {H m D : ℕ} {q₁ q₂ : ℕ}
    (hq₁ : q₁ < H / blockPeriod m D) (hq₂ : q₂ < H / blockPeriod m D)
    (hneq : q₁ ≠ q₂) :
    Disjoint (fullBlockSlots (H := H) (m := m) (D := D) q₁ hq₁)
      (fullBlockSlots (H := H) (m := m) (D := D) q₂ hq₂) := by
  by_cases hlt : q₁ < q₂
  · exact fullBlockSlots_disjoint_of_lt hq₁ hq₂ hlt
  · have hlt' : q₂ < q₁ := by omega
    exact (fullBlockSlots_disjoint_of_lt hq₂ hq₁ hlt').symm

private lemma fullBlockSlots_pairwiseDisjoint {H m D : ℕ} :
    (↑(Finset.range (H / blockPeriod m D)) : Set ℕ).PairwiseDisjoint
      (fun q => fullBlockSlotsTotal H m D q) := by
  intro q₁ hq₁ q₂ hq₂ hneq
  have hq₁' : q₁ < H / blockPeriod m D := Finset.mem_range.mp hq₁
  have hq₂' : q₂ < H / blockPeriod m D := Finset.mem_range.mp hq₂
  have he₁ : fullBlockSlotsTotal H m D q₁ = fullBlockSlots q₁ hq₁' := by
    simp [fullBlockSlotsTotal, hq₁']
  have he₂ : fullBlockSlotsTotal H m D q₂ = fullBlockSlots q₂ hq₂' := by
    simp [fullBlockSlotsTotal, hq₂']
  change Disjoint (fullBlockSlotsTotal H m D q₁) (fullBlockSlotsTotal H m D q₂)
  rw [he₁, he₂]
  exact fullBlockSlots_disjoint hq₁' hq₂' hneq

private lemma fullBlockUnion_card {H m D : ℕ} :
    ((Finset.range (H / blockPeriod m D)).biUnion
      (fun q => fullBlockSlotsTotal H m D q)).card =
      m * (H / blockPeriod m D) := by
  classical
  rw [Finset.card_biUnion (fullBlockSlots_pairwiseDisjoint (H := H) (m := m) (D := D))]
  have hcard (q : ℕ) (hq : q ∈ Finset.range (H / blockPeriod m D)) :
      (fullBlockSlotsTotal H m D q).card = m := by
    simp only [fullBlockSlotsTotal, dif_pos (Finset.mem_range.mp hq)]
    exact fullBlockSlots_card (Finset.mem_range.mp hq)
  calc
    _ = ∑ q ∈ Finset.range (H / blockPeriod m D), m := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [hcard q hq]
    _ = m * (H / blockPeriod m D) := by
      simp [Finset.card_range, Nat.nsmul_eq_mul, Nat.mul_comm]

private noncomputable def fullBlockUnion (H m D : ℕ) : Trace H :=
  (Finset.range (H / blockPeriod m D)).biUnion
    (fun q => fullBlockSlotsTotal H m D q)

private lemma fullBlockUnion_subset_schedule {H m D : ℕ} (hm1 : 1 ≤ m) :
    fullBlockUnion H m D ⊆ perfectSchedule H m D := by
  classical
  intro t ht
  rcases Finset.mem_biUnion.mp ht with ⟨q, hq, htq⟩
  have hq' : q < H / blockPeriod m D := Finset.mem_range.mp hq
  have htq' : t ∈ fullBlockSlots (H := H) (m := m) (D := D) q hq' := by
    simpa [fullBlockSlotsTotal, hq'] using htq
  exact fullBlockSlots_mem_schedule hq' htq'

private lemma remainder_disjoint_fullBlockUnion {H m D : ℕ} (hm1 : 1 ≤ m) :
    Disjoint (fullBlockUnion H m D) (remainderSlots H m D) := by
  classical
  apply Finset.disjoint_left.mpr
  intro t htfull htrem
  rcases Finset.mem_biUnion.mp htfull with ⟨q, hq, htq⟩
  have hq' : q < H / blockPeriod m D := Finset.mem_range.mp hq
  have htq' : t ∈ fullBlockSlots (H := H) (m := m) (D := D) q hq' := by
    simpa [fullBlockSlotsTotal, hq'] using htq
  have hfull := fullBlockSlots_mem_bounds hq' htq'
  have hrem := remainderSlots_mem_bounds htrem
  have hqa : q + 1 ≤ H / blockPeriod m D := Nat.succ_le_of_lt hq'
  have hmul : blockPeriod m D * (q + 1) ≤
      blockPeriod m D * (H / blockPeriod m D) :=
    Nat.mul_le_mul_left _ hqa
  have hdiv : blockPeriod m D * (H / blockPeriod m D) ≤ H := by
    calc
      blockPeriod m D * (H / blockPeriod m D) ≤
          H % blockPeriod m D + blockPeriod m D * (H / blockPeriod m D) :=
        Nat.le_add_left _ _
      _ = H := Nat.mod_add_div H (blockPeriod m D)
  have hlt : t.val < (H / blockPeriod m D) * blockPeriod m D := by
    have hstep : q * blockPeriod m D + blockPeriod m D =
        (q + 1) * blockPeriod m D := by simp [Nat.succ_mul]
    have hle : (q + 1) * blockPeriod m D ≤
        (H / blockPeriod m D) * blockPeriod m D := by
      simpa [Nat.mul_comm] using hmul
    omega
  omega

private lemma schedule_subset_fullBlockUnion_union_remainder {H m D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) :
    perfectSchedule H m D ⊆ fullBlockUnion H m D ∪ remainderSlots H m D := by
  classical
  intro t ht
  let p := blockPeriod m D
  let a := H / p
  let b := H % p
  have hp : 0 < p := by
    dsimp [p, blockPeriod]
    omega
  have hdecomp : b + a * p = H := by
    simpa [a, b, Nat.mul_comm] using Nat.mod_add_div H p
  have hbase : a * p ≤ H := by
    exact Nat.div_mul_le_self H p
  have hHle : H ≤ (a + 1) * p := by
    have hb : b < p := Nat.mod_lt _ hp
    have hdecomp' : a * p + b = H := by simpa [Nat.add_comm] using hdecomp
    have hstep : a * p + p = (a + 1) * p := by simp [Nat.succ_mul]
    omega
  have hq_lt : t.val / p < a + 1 := by
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    exact lt_of_lt_of_le t.isLt hHle
  let q := t.val / p
  have hqle : q ≤ a := by
    dsimp [q]
    omega
  by_cases hqfull : q < a
  · have hq1 : q + 1 ≤ a := by omega
    have hmul : (q + 1) * p ≤ a * p := Nat.mul_le_mul_right _ hq1
    have hfull : (q + 1) * p ≤ H := hmul.trans hbase
    have hqdiv : t.val / p = q := by rfl
    have hlow : q * p + D ≤ t.val := by
      simp only [perfectSchedule, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      have hmin : min H ((q + 1) * p) = (q + 1) * p := min_eq_right hfull
      have hmul' : (q + 1) * p = q * p + D + m := by
        dsimp [p, blockPeriod]
        ring
      change min H ((t.val / p + 1) * p) - m ≤ t.val at ht
      rw [hqdiv, hmin] at ht
      omega
    have hupp : t.val < q * p + D + m := by
      have hqbound : t.val < (q + 1) * p := by
        have hmod := Nat.mod_lt t.val hp
        have hdecomp_t := Nat.mod_add_div t.val p
        have hstep : (t.val / p + 1) * p = p * (t.val / p) + p := by
          ring
        dsimp [q] at hdecomp_t ⊢
        omega
      have hmul' : (q + 1) * p = q * p + D + m := by
        dsimp [p, blockPeriod]
        ring
      omega
    let j : ℕ := t.val - (q * p + D)
    have hj : j < m := by
      dsimp [j]
      omega
    have hjadd : q * p + D + j = t.val := by
      dsimp [j]
      exact Nat.add_sub_of_le hlow
    have htq : t ∈ fullBlockSlots (H := H) (m := m) (D := D) q hqfull := by
      apply Finset.mem_image.mpr
      refine ⟨⟨j, hj⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      simpa [hjadd]
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨q, Finset.mem_range.mpr hqfull, ?_⟩
    have he : fullBlockSlotsTotal H m D q = fullBlockSlots q hqfull := by
      unfold fullBlockSlotsTotal
      rw [dif_pos hqfull]
    rw [he]
    exact htq
  · have hqeq : q = a := by omega
    have hrem : t ∈ remainderSlots H m D := by
      have hqdiv : t.val / p = a := by simpa [q, hqeq]
      have hlow : H - m ≤ t.val := by
        simp only [perfectSchedule, Finset.mem_filter, Finset.mem_univ, true_and] at ht
        have hmin : min H ((a + 1) * p) = H := min_eq_left hHle
        change min H ((t.val / p + 1) * p) - m ≤ t.val at ht
        rw [hqdiv, hmin] at ht
        exact ht
      let c := min m b
      have hstart : H - m ≤ a * p + (b - c) := by
        by_cases hb : b ≤ m
        · have hc : c = b := by simp [c, hb]
          have hdecomp' : a * p + b = H := by simpa [Nat.add_comm] using hdecomp
          rw [hc]
          omega
        · have hb' : m ≤ b := by omega
          have hc : c = m := by simp [c, hb']
          have hdecomp' : a * p + b = H := by simpa [Nat.add_comm] using hdecomp
          rw [hc]
          omega
      have hbase_t : a * p ≤ t.val := by
        have hdiv_t := Nat.div_mul_le_self t.val p
        simpa [hqdiv, Nat.mul_comm] using hdiv_t
      have hlow' : a * p + (b - c) ≤ t.val := by
        by_cases hb : b ≤ m
        · have hc : c = b := by simp [c, hb]
          simpa [hc] using hbase_t
        · have hb' : m ≤ b := by omega
          have hc : c = m := by simp [c, hb']
          have hdecomp' : a * p + b = H := by simpa [Nat.add_comm] using hdecomp
          have hstart_eq : a * p + (b - m) = H - m := by
            omega
          rw [hc, hstart_eq]
          exact hlow
      have hupp : t.val < a * p + (b - c) + c := by
        have hc : c ≤ b := min_le_right _ _
        have hdecomp' : a * p + b = H := by simpa [Nat.add_comm] using hdecomp
        have hsum : a * p + (b - c) + c = H := by
          omega
        calc
          t.val < H := t.isLt
          _ = a * p + (b - c) + c := hsum.symm
      let j : ℕ := t.val - (a * p + (b - c))
      have hj : j < c := by
        dsimp [j]
        omega
      have hjadd : a * p + (b - c) + j = t.val := by
        dsimp [j]
        exact Nat.add_sub_of_le hlow'
      apply Finset.mem_image.mpr
      refine ⟨⟨j, hj⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      simpa [hjadd, c]
    exact Finset.mem_union_right _ hrem

private lemma perfectSchedule_eq_block_union {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H) :
    perfectSchedule H m D = fullBlockUnion H m D ∪ remainderSlots H m D := by
  apply Finset.Subset.antisymm
  · exact schedule_subset_fullBlockUnion_union_remainder hm1 hm
  · intro t ht
    rcases Finset.mem_union.mp ht with htfull | htrem
    · exact fullBlockUnion_subset_schedule hm1 htfull
    · exact remainderSlots_mem_schedule hm1 htrem

/- The following local matching lemma is the small finite combinatorial fact
   used for the constructive half.  A set of arrivals in an interval of
   length `len` is matched, in increasing order, to the interval beginning at
   `start`; the `max` in the assignment accounts for arrivals that occur
   after the beginning of the service interval. -/
private lemma interval_assignment {H : ℕ} {A : Finset (Fin H)} {base len start D m : ℕ}
    (hbase : ∀ a ∈ A, base ≤ a)
    (hend : ∀ a ∈ A, a < base + len)
    (hstart : start ≤ D)
    (hsc : start + min m len = len)
    (hcard : A.card ≤ min m len) :
    ∃ f : {a // a ∈ A} → ℕ,
      Function.Injective f ∧
      ∀ a, base + start ≤ f a ∧ f a < base + len ∧
        a.val.val ≤ f a ∧ f a ≤ a.val.val + D := by
  classical
  let k := A.card
  let e : Fin k ≃o {a // a ∈ A} := A.orderIsoOfFin (by rfl)
  have h_rank_le (a : {a // a ∈ A}) :
      (e.symm a).val ≤ a.val.val - base := by
    let i := e.symm a
    let g : Fin i.val → Fin (a.val.val - base) := fun j =>
      ⟨(e ⟨j.val, by omega⟩).val.val - base, by
        have hlt : (e ⟨j.val, by omega⟩) < a := by
          have hji : (⟨j.val, by omega⟩ : Fin k) < i :=
            Fin.mk_lt_mk.mpr j.isLt
          calc
            e ⟨j.val, by omega⟩ < e i := e.lt_iff_lt.mpr hji
            _ = a := e.apply_symm_apply a
        have he := (e ⟨j.val, by omega⟩).property
        have hb := hbase _ he
        have ha := hbase a.val a.property
        apply (Nat.sub_lt_iff_lt_add' hb).2
        have hrel : base + (a.val.val - base) = a.val.val := Nat.add_sub_of_le ha
        have hlt' : (e ⟨j.val, by omega⟩).val.val < a.val.val := hlt
        omega⟩
    have hg : Function.Injective g := by
      intro j₁ j₂ h
      apply Fin.ext
      have hval := congrArg Fin.val h
      change (e ⟨j₁.val, by omega⟩).val.val - base =
        (e ⟨j₂.val, by omega⟩).val.val - base at hval
      have h1 := hbase _ (e ⟨j₁.val, by omega⟩).property
      have h2 := hbase _ (e ⟨j₂.val, by omega⟩).property
      have hv : (e ⟨j₁.val, by omega⟩).val.val =
          (e ⟨j₂.val, by omega⟩).val.val := by
        calc
          (e ⟨j₁.val, by omega⟩).val.val =
              ((e ⟨j₁.val, by omega⟩).val.val - base) + base :=
            (Nat.sub_add_cancel h1).symm
          _ = ((e ⟨j₂.val, by omega⟩).val.val - base) + base := by rw [hval]
          _ = (e ⟨j₂.val, by omega⟩).val.val := Nat.sub_add_cancel h2
      have heq : e ⟨j₁.val, by omega⟩ = e ⟨j₂.val, by omega⟩ := by
        apply Subtype.ext
        exact Fin.ext hv
      have hidx := e.injective heq
      exact congrArg (fun z : Fin k => z.val) hidx
    have hc := Fintype.card_le_of_injective g hg
    change (e.symm a).val ≤ a.val.val - base
    simpa using hc
  let f : {a // a ∈ A} → ℕ := fun a =>
    max (base + start + (e.symm a).val) a.val.val
  have hstrict : ∀ (a₁ a₂ : {a // a ∈ A}),
      a₁.val.val < a₂.val.val → (e.symm a₁).val < (e.symm a₂).val →
      f a₁ < f a₂ := by
    intro a₁ a₂ ha12 hi12
    dsimp [f]
    have hfirst : base + start + (e.symm a₁).val <
        base + start + (e.symm a₂).val := by omega
    by_cases h2 : base + start + (e.symm a₂).val ≤ a₂.val.val
    · have hmax1 : max (base + start + (e.symm a₁).val) a₁.val.val < a₂.val.val :=
        Nat.max_lt.mpr ⟨by omega, ha12⟩
      exact hmax1.trans_le (Nat.le_max_right _ _)
    · have hmax1 : max (base + start + (e.symm a₁).val) a₁.val.val <
          base + start + (e.symm a₂).val :=
        Nat.max_lt.mpr ⟨hfirst, by omega⟩
      exact hmax1.trans_le (Nat.le_max_left _ _)
  refine ⟨f, ?_, ?_⟩
  · intro a₁ a₂ h12
    by_cases heqv : a₁.val.val = a₂.val.val
    · exact Subtype.ext (Fin.ext heqv)
    · by_cases hlt : a₁.val.val < a₂.val.val
      · have hi : (e.symm a₁).val < (e.symm a₂).val := by
          exact Fin.mk_lt_mk.mp (e.symm.lt_iff_lt.mpr (by
            change a₁.val.val < a₂.val.val
            exact hlt))
        exact False.elim ((Nat.ne_of_lt (hstrict a₁ a₂ hlt hi)) h12)
      · have hlt' : a₂.val.val < a₁.val.val := by omega
        have hi' : (e.symm a₂).val < (e.symm a₁).val := by
          exact Fin.mk_lt_mk.mp (e.symm.lt_iff_lt.mpr (by
            change a₂.val.val < a₁.val.val
            exact hlt'))
        exact False.elim ((Nat.ne_of_lt (hstrict a₂ a₁ hlt' hi')) h12.symm)
  · intro a
    have ha := hbase a.val a.property
    have hae := hend a.val a.property
    have hi := (e.symm a).isLt
    have hr := h_rank_le a
    have hlow : base + start ≤ f a := by
      dsimp [f]
      exact (Nat.le_add_right _ _).trans (Nat.le_max_left _ _)
    have hupper : f a < base + len := by
      dsimp [f]
      exact Nat.max_lt.mpr (by
        constructor
        · have hsmall : (e.symm a).val < min m len := lt_of_lt_of_le hi hcard
          omega
        · exact hae)
    have hge : a.val.val ≤ f a := by
      dsimp [f]
      exact Nat.le_max_right _ _
    have hdeadline : f a ≤ a.val.val + D := by
      dsimp [f]
      exact Nat.max_le.mpr ⟨by omega, by omega⟩
    exact ⟨hlow, hupper, hge, hdeadline⟩

private def ppBlockEnd (H m D q : ℕ) : ℕ :=
  min H ((q + 1) * blockPeriod m D)

private def ppBlockArrivals {H m D : ℕ} (x : Trace H) (q : ℕ) : Trace H :=
  x.filter (fun t =>
    q * blockPeriod m D ≤ t.val ∧ t.val < ppBlockEnd H m D q)

private lemma pp_block_assignment {H m D q : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (hq : q ≤ H / blockPeriod m D) (x : Trace H) (hx : x.card ≤ m) :
    ∃ f : {a // a ∈ (ppBlockArrivals (H := H) (m := m) (D := D) x q)} → ℕ,
      Function.Injective f ∧
      ∀ a,
        q * blockPeriod m D +
            (ppBlockEnd H m D q - q * blockPeriod m D -
              min m (ppBlockEnd H m D q - q * blockPeriod m D)) ≤ f a ∧
        f a < ppBlockEnd H m D q ∧
        a.val.val ≤ f a ∧ f a ≤ a.val.val + D := by
  let p := blockPeriod m D
  let base := q * p
  let finish := ppBlockEnd H m D q
  let len := finish - base
  let c := min m len
  let start := len - c
  have hp : 0 < p := by
    dsimp [p, blockPeriod]
    omega
  have hbaseH : base ≤ H := by
    have hq' : q ≤ H / p := by simpa [p] using hq
    have hmul : q * p ≤ (H / p) * p := Nat.mul_le_mul_right p hq'
    have hdiv : (H / p) * p ≤ H := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self H p
    simpa [base, p] using hmul.trans hdiv
  have hbaseFinish : base ≤ finish := by
    dsimp [finish, base, ppBlockEnd]
    have hnext : base ≤ (q + 1) * p := by
      simpa [base, p] using (Nat.mul_le_mul_right p (Nat.le_succ q))
    exact le_min hbaseH hnext
  have hfinish_le : finish ≤ base + p := by
    change min H ((q + 1) * p) ≤ base + p
    exact (min_le_right _ _).trans (by simp [base, Nat.succ_mul])
  have hlen_le : len ≤ p := by
    dsimp [len]
    omega
  have hstartD : start ≤ D := by
    by_cases hlenm : len ≤ m
    · have hc : c = len := by
        dsimp [c]
        exact min_eq_right hlenm
      simp [start, hc]
    · have hmlen : m ≤ len := Nat.le_of_not_ge hlenm
      have hc : c = m := by
        dsimp [c]
        exact min_eq_left hmlen
      dsimp [start]
      rw [hc]
      have hpm : p = D + m := by rfl
      omega
  have hsc : start + c = len := by
    dsimp [start]
    exact Nat.sub_add_cancel (min_le_right _ _)
  let A := ppBlockArrivals (H := H) (m := m) (D := D) x q
  have hbaseA : ∀ a ∈ A, base ≤ a := by
    intro a ha
    simp only [A, ppBlockArrivals, Finset.mem_filter] at ha
    exact ha.2.1
  have hendA : ∀ a ∈ A, a < base + len := by
    intro a ha
    simp only [A, ppBlockArrivals, Finset.mem_filter] at ha
    have hfinish : base + len = finish := by
      exact Nat.add_sub_of_le hbaseFinish
    rw [hfinish]
    exact ha.2.2
  have hcard_m : A.card ≤ m := by
    have hfilter : A.card ≤ x.card := by
      exact Finset.card_filter_le _ _
    exact hfilter.trans hx
  have hcard_len : A.card ≤ len := by
    let g : {a // a ∈ A} → Fin len := fun a =>
      ⟨a.val.val - base, by
        have ha := hbaseA a.val a.property
        have hae := hendA a.val a.property
        have hfinish : base + len = finish := Nat.add_sub_of_le hbaseFinish
        omega⟩
    have hg : Function.Injective g := by
      intro a₁ a₂ h
      apply Subtype.ext
      apply Fin.ext
      have hv := congrArg Fin.val h
      have h1 := hbaseA a₁.val a₁.property
      have h2 := hbaseA a₂.val a₂.property
      change a₁.val.val - base = a₂.val.val - base at hv
      have h1' := Nat.sub_add_cancel h1
      have h2' := Nat.sub_add_cancel h2
      omega
    have hc := Fintype.card_le_of_injective g hg
    simpa using hc
  have hcard : A.card ≤ c := by
    dsimp [c]
    exact (Nat.le_min).2 ⟨hcard_m, hcard_len⟩
  obtain ⟨f, hf, hprops⟩ := interval_assignment
    (A := A) (base := base) (len := len) (start := start) (D := D) (m := m)
    hbaseA hendA hstartD hsc hcard
  refine ⟨f, hf, ?_⟩
  intro a
  have hp1 := hprops a
  have hfinish : base + len = finish := Nat.add_sub_of_le hbaseFinish
  have hp1' : base + start ≤ f a ∧ f a < finish ∧
      a.val.val ≤ f a ∧ f a ≤ a.val.val + D := by
    rw [← hfinish]
    exact hp1
  simpa only [base, start, len, c, finish, p, ppBlockEnd, blockPeriod] using hp1'

private lemma fullBlockSlots_of_interval {H m D q : ℕ}
    (hq : q < H / blockPeriod m D) {t : Fin H}
    (hlo : q * blockPeriod m D + D ≤ t.val)
    (hupp : t.val < (q + 1) * blockPeriod m D) :
    t ∈ fullBlockSlots (H := H) (m := m) (D := D) q hq := by
  classical
  let j := t.val - (q * blockPeriod m D + D)
  have hj : j < m := by
    dsimp [j]
    have hstep : q * blockPeriod m D + D + m =
        (q + 1) * blockPeriod m D := by
      simp [blockPeriod, Nat.succ_mul, Nat.add_assoc, Nat.add_comm]
    omega
  have hjadd : q * blockPeriod m D + D + j = t.val := by
    dsimp [j]
    exact Nat.add_sub_of_le hlo
  unfold fullBlockSlots
  refine Finset.mem_image.mpr ⟨⟨j, hj⟩, Finset.mem_univ _, ?_⟩
  apply Fin.ext
  simpa [hjadd]

private lemma remainderSlots_of_interval {H m D : ℕ} (hm1 : 1 ≤ m) {t : Fin H}
    (hlo : H / blockPeriod m D * blockPeriod m D +
        (H % blockPeriod m D - min m (H % blockPeriod m D)) ≤ t.val)
    (hupp : t.val < H) :
    t ∈ remainderSlots H m D := by
  classical
  let p := blockPeriod m D
  let a := H / p
  let b := H % p
  let c := min m b
  have hp : 0 < p := by
    dsimp [p, blockPeriod]
    omega
  have hdecomp : a * p + b = H := by
    simpa [a, b, Nat.add_comm, Nat.mul_comm] using (Nat.mod_add_div H p)
  have hc : c ≤ b := min_le_right _ _
  have hsum : a * p + (b - c) + c = H := by omega
  let j := t.val - (a * p + (b - c))
  have hj : j < c := by
    dsimp [j]
    have hlo' : a * p + (b - c) ≤ t.val := by
      simpa [a, b, c, p] using hlo
    omega
  have hjadd : a * p + (b - c) + j = t.val := by
    dsimp [j]
    have hlo' : a * p + (b - c) ≤ t.val := by
      simpa [a, b, c, p] using hlo
    exact Nat.add_sub_of_le hlo'
  unfold remainderSlots
  dsimp only
  refine Finset.mem_image.mpr ⟨⟨j, hj⟩, Finset.mem_univ _, ?_⟩
  apply Fin.ext
  simpa [a, b, c, p, hjadd]

theorem perfectSchedule_card {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H) :
    (perfectSchedule H m D).card = perfectBudget H m D := by
  rw [perfectSchedule_eq_block_union hm1 hm]
  rw [Finset.card_union_of_disjoint (remainder_disjoint_fullBlockUnion hm1)]
  unfold fullBlockUnion
  rw [fullBlockUnion_card, remainderSlots_card]
  simp [perfectBudget, blockPeriod, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem perfectSchedule_terminal_subset {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H) :
    terminal H m ⊆ perfectSchedule H m D := by
  intro t ht
  simp only [perfectSchedule, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [mem_terminal] at ht
  have hmin : min H ((t.val / (D + m) + 1) * (D + m)) ≤ H :=
    min_le_left _ _
  omega

private lemma pp_block_arrival_mem {H m D : ℕ} (hm1 : 1 ≤ m)
    {x : Trace H} {a : Fin H} (ha : a ∈ x) :
    a ∈ ppBlockArrivals (H := H) (m := m) (D := D) x
      (a.val / blockPeriod m D) := by
  have hp : 0 < blockPeriod m D := by
    dsimp [blockPeriod]
    omega
  simp only [ppBlockArrivals, Finset.mem_filter]
  refine ⟨ha, Nat.div_mul_le_self _ _, ?_⟩
  unfold ppBlockEnd
  apply lt_min
  · exact a.isLt
  · have hmod := Nat.mod_lt a.val hp
    have hdec := Nat.mod_add_div a.val (blockPeriod m D)
    have hstep : (a.val / blockPeriod m D + 1) * blockPeriod m D =
        blockPeriod m D * (a.val / blockPeriod m D) + blockPeriod m D := by
      simp [Nat.succ_mul, Nat.mul_comm]
    omega

theorem perfectSchedule_feasible {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    {x : Trace H} (hx : x.card ≤ m) :
    Feasible D x (perfectSchedule H m D) := by
  classical
  let p := blockPeriod m D
  have hp : 0 < p := by
    dsimp [p, blockPeriod]
    omega
  let g (q : ℕ) :
      {a // a ∈ ppBlockArrivals (H := H) (m := m) (D := D) x q} → ℕ :=
    if hq : q ≤ H / blockPeriod m D then
      Classical.choose (pp_block_assignment hm1 hm hq x hx)
    else fun _ => 0
  have g_spec (q : ℕ) (hq : q ≤ H / blockPeriod m D) :
      Function.Injective (g q) ∧
      ∀ a,
        q * blockPeriod m D +
            (ppBlockEnd H m D q - q * blockPeriod m D -
              min m (ppBlockEnd H m D q - q * blockPeriod m D)) ≤ g q a ∧
        g q a < ppBlockEnd H m D q ∧
        a.val.val ≤ g q a ∧ g q a ≤ a.val.val + D := by
    dsimp [g]
    rw [dif_pos hq]
    exact Classical.choose_spec (pp_block_assignment hm1 hm hq x hx)
  let F : {a // a ∈ x} → Fin H := fun a =>
    let q := a.val.val / blockPeriod m D
    let aq : {z // z ∈ ppBlockArrivals (H := H) (m := m) (D := D) x q} :=
      ⟨a.val, pp_block_arrival_mem hm1 a.property⟩
    ⟨g q aq, by
      have hq : q ≤ H / blockPeriod m D := by
        dsimp [q]
        exact Nat.div_le_div_right (Nat.le_of_lt a.val.isLt)
      have hs := (g_spec q hq).2 aq
      have hfinish : ppBlockEnd H m D q ≤ H := min_le_left _ _
      omega⟩
  refine ⟨F, ?_, ?_⟩
  · intro a₁ a₂ hF
    set q₁ : ℕ := a₁.val.val / blockPeriod m D with q₁def
    set q₂ : ℕ := a₂.val.val / blockPeriod m D with q₂def
    have hq₁ : q₁ ≤ H / blockPeriod m D := by
      rw [q₁def]
      exact Nat.div_le_div_right (Nat.le_of_lt a₁.val.isLt)
    have hq₂ : q₂ ≤ H / blockPeriod m D := by
      rw [q₂def]
      exact Nat.div_le_div_right (Nat.le_of_lt a₂.val.isLt)
    let aq₁ : {z // z ∈ ppBlockArrivals (H := H) (m := m) (D := D) x q₁} :=
      ⟨a₁.val, by simpa only [q₁def] using pp_block_arrival_mem hm1 a₁.property⟩
    let aq₂ : {z // z ∈ ppBlockArrivals (H := H) (m := m) (D := D) x q₂} :=
      ⟨a₂.val, by simpa only [q₂def] using pp_block_arrival_mem hm1 a₂.property⟩
    have hG : g q₁ aq₁ = g q₂ aq₂ := by
      have hval := congrArg Fin.val hF
      simpa [F, q₁def, q₂def, aq₁, aq₂] using hval
    have hqeq : q₁ = q₂ := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hs₁ := (g_spec q₁ hq₁).2 aq₁
        have hs₂ := (g_spec q₂ hq₂).2 aq₂
        have hfinish₁ : ppBlockEnd H m D q₁ ≤ (q₁ + 1) * p := by
          unfold ppBlockEnd
          exact min_le_right _ _
        have hstep : (q₁ + 1) * p ≤ q₂ * p := by
          exact Nat.mul_le_mul_right p (by omega)
        have hupper₁ : g q₁ aq₁ < ppBlockEnd H m D q₁ := hs₁.2.1
        have hlower₂ : q₂ * p ≤ g q₂ aq₂ := by
          have h₂ := hs₂.1
          dsimp [p] at hstep ⊢
          omega
        have hltG : g q₁ aq₁ < g q₂ aq₂ := by
          dsimp [p] at hstep hfinish₁ hlower₂ ⊢
          omega
        exact (Nat.ne_of_lt hltG) hG
      · have hs₁ := (g_spec q₁ hq₁).2 aq₁
        have hs₂ := (g_spec q₂ hq₂).2 aq₂
        have hfinish₂ : ppBlockEnd H m D q₂ ≤ (q₂ + 1) * p := by
          unfold ppBlockEnd
          exact min_le_right _ _
        have hstep : (q₂ + 1) * p ≤ q₁ * p := by
          exact Nat.mul_le_mul_right p (by omega)
        have hupper₂ : g q₂ aq₂ < ppBlockEnd H m D q₂ := hs₂.2.1
        have hlower₁ : q₁ * p ≤ g q₁ aq₁ := by
          have h₁ := hs₁.1
          dsimp [p] at hstep ⊢
          omega
        have hltG : g q₂ aq₂ < g q₁ aq₁ := by
          dsimp [p] at hstep hfinish₂ hlower₁ ⊢
          omega
        exact (Nat.ne_of_lt hltG) hG.symm
    let aq₂' : {z // z ∈ ppBlockArrivals (H := H) (m := m) (D := D) x q₁} := by
      rw [hqeq]
      exact aq₂
    have hcast : ∀ (r s : ℕ) (h : r = s)
        (u : {z // z ∈ ppBlockArrivals (H := H) (m := m) (D := D) x s}),
        g r (by rw [h]; exact u) = g s u := by
      intro r s h u
      cases h
      rfl
    have hcastval : ∀ (r s : ℕ) (h : r = s)
        (u : {z // z ∈ ppBlockArrivals (H := H) (m := m) (D := D) x s}),
        (by rw [h]; exact u : {z // z ∈ ppBlockArrivals (H := H) (m := m) (D := D) x r}).val =
          u.val := by
      intro r s h u
      cases h
      rfl
    have hG' : g q₁ aq₁ = g q₁ aq₂' := by
      have hc := hcast q₁ q₂ hqeq aq₂
      exact hG.trans hc.symm
    have haa := (g_spec q₁ hq₁).1 hG'
    have haa1 : aq₁.val = aq₂'.val := congrArg (fun z => z.val) haa
    have haacast : aq₂'.val = aq₂.val := by
      exact hcastval q₁ q₂ hqeq aq₂
    have haa' : aq₁.val = aq₂.val := haa1.trans haacast
    apply Subtype.ext
    exact haa'
  · intro a
    let q := a.val.val / blockPeriod m D
    let aq : {z // z ∈ ppBlockArrivals (H := H) (m := m) (D := D) x q} :=
      ⟨a.val, by simpa [q] using pp_block_arrival_mem hm1 a.property⟩
    have hq : q ≤ H / blockPeriod m D := by
      dsimp [q]
      exact Nat.div_le_div_right (Nat.le_of_lt a.val.isLt)
    have hs := (g_spec q hq).2 aq
    have hmem : (F a) ∈ perfectSchedule H m D := by
      rcases lt_or_eq_of_le hq with hqfull | hqeq
      · have hfinish : ppBlockEnd H m D q = (q + 1) * blockPeriod m D := by
          unfold ppBlockEnd
          apply min_eq_right
          have hq1 : q + 1 ≤ H / blockPeriod m D := Nat.succ_le_of_lt hqfull
          have hmul := Nat.mul_le_mul_right (blockPeriod m D) hq1
          exact (by simpa [Nat.mul_comm] using
            hmul.trans (Nat.div_mul_le_self H (blockPeriod m D)))
        have hlen : ppBlockEnd H m D q - q * blockPeriod m D =
            blockPeriod m D := by
          rw [hfinish]
          have hstep : (q + 1) * blockPeriod m D =
              q * blockPeriod m D + blockPeriod m D := by
            simp [Nat.succ_mul]
          omega
        have hc : min m (ppBlockEnd H m D q - q * blockPeriod m D) = m := by
          rw [hlen]
          apply min_eq_left
          dsimp [blockPeriod]
          omega
        have hlo : q * blockPeriod m D + D ≤ (F a).val := by
          have h := hs.1
          rw [hlen] at h
          have hmp : m ≤ blockPeriod m D := by
            dsimp [blockPeriod]
            omega
          have hcp : min m (blockPeriod m D) = m := min_eq_left hmp
          rw [hcp] at h
          have hFval : (F a).val = g q aq := by
            rfl
          rw [hFval]
          simpa [blockPeriod, Nat.add_assoc, Nat.add_comm] using h
        have hupp : (F a).val < (q + 1) * blockPeriod m D := by
          have h := hs.2.1
          have hFval : (F a).val = g q aq := by
            rfl
          rw [hFval]
          simpa [hfinish] using h
        exact fullBlockSlots_mem_schedule hqfull
          (fullBlockSlots_of_interval hqfull hlo hupp)
      · have hqeq' : q = H / blockPeriod m D := hqeq
        have hlo := hs.1
        have hupp := hs.2.1
        have hFval : (F a).val = g q aq := by
          rfl
        rw [← hFval] at hlo hupp
        have hfinish : ppBlockEnd H m D q = H := by
          unfold ppBlockEnd
          rw [hqeq']
          apply min_eq_left
          have hp' : 0 < blockPeriod m D := by
            dsimp [blockPeriod]
            omega
          have hmod := Nat.mod_lt H hp'
          have hdec := Nat.mod_add_div H (blockPeriod m D)
          have hdec' : H % blockPeriod m D +
              (H / blockPeriod m D) * blockPeriod m D = H := by
            simpa [Nat.mul_comm] using hdec
          have hstep : (H / blockPeriod m D + 1) * blockPeriod m D =
              H / blockPeriod m D * blockPeriod m D + blockPeriod m D := by
            simp [Nat.succ_mul]
          omega
        have hlo' : q * blockPeriod m D +
              (H - q * blockPeriod m D - min m (H - q * blockPeriod m D)) ≤
              (F a).val := by
          simpa [hfinish] using hlo
        have hdecomp : H % blockPeriod m D +
              blockPeriod m D * (H / blockPeriod m D) = H :=
          Nat.mod_add_div H (blockPeriod m D)
        have hqmul : q * blockPeriod m D =
              (H / blockPeriod m D) * blockPeriod m D := by rw [hqeq']
        have hnormF :
              H / blockPeriod m D * blockPeriod m D +
                (H % blockPeriod m D - min m (H % blockPeriod m D)) ≤
              (F a).val := by
          have hdecomp' : H % blockPeriod m D +
                (H / blockPeriod m D) * blockPeriod m D = H := by
            simpa [Nat.mul_comm] using hdecomp
          have hEq : H - q * blockPeriod m D = H % blockPeriod m D := by
            omega
          rw [← hqmul, ← hEq]
          exact hlo'
        have hupp' : (F a).val < H := by simpa [hfinish] using hupp
        have hrem := remainderSlots_of_interval hm1 hnormF hupp'
        rw [perfectSchedule_eq_block_union hm1 hm]
        exact Finset.mem_union_right _ hrem
    have hrel := hs.2.2
    have hFval : (F a).val = g q aq := by
      rfl
    rw [← hFval] at hrel
    exact ⟨hmem, hrel.1, hrel.2⟩

end TrafficShaping
