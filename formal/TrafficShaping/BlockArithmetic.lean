import TrafficShaping.BlockTests

/-!
  Arithmetic bridges for the finite block construction.  The names in this
  file are deliberately suffixed so that they can coexist with the
  corollary-specific budget lemmas.
-/

namespace TrafficShaping

theorem testBlockCount_eq_ceil_div {H m D : ℕ} (hm1 : 1 ≤ m) :
    testBlockCount H m D = (H + (D + m) - 1) / (D + m) := by
  have hL : 0 < D + m := by omega
  let q := H / (D + m)
  let r := H % (D + m)
  have hdecomp : r + q * (D + m) = H := by
    dsimp [q, r]
    simpa [Nat.mul_comm] using Nat.mod_add_div H (D + m)
  by_cases hr : r = 0
  · have hq : (H + (D + m) - 1) / (D + m) = q := by
      have hH0 : H = q * (D + m) := by
        rw [← hdecomp, hr]
        simp
      have hlo : q * (D + m) ≤ H + (D + m) - 1 := by
        rw [hH0]
        apply (Nat.le_sub_iff_add_le (by omega : 1 ≤ q * (D + m) + (D + m))).2
        omega
      have hhi : H + (D + m) - 1 < (q + 1) * (D + m) := by
        rw [hH0, Nat.succ_mul]
        exact Nat.sub_lt (by omega) (by omega)
      apply Nat.div_eq_of_lt_le
      · exact hlo
      · exact hhi
    simp [testBlockCount, q, r, hr, hq]

  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    have hrlt : r < D + m := by
      dsimp [r]
      exact Nat.mod_lt _ hL
    have hq : (H + (D + m) - 1) / (D + m) = q + 1 := by
      have hH' : H = r + q * (D + m) := hdecomp.symm
      have hlo : (q + 1) * (D + m) ≤ H + (D + m) - 1 := by
        rw [hH', Nat.succ_mul]
        apply (Nat.le_sub_iff_add_le (by omega : 1 ≤ r + q * (D + m) + (D + m))).2
        omega
      have hhi : H + (D + m) - 1 < (q + 1 + 1) * (D + m) := by
        rw [hH', Nat.succ_mul]
        rw [Nat.succ_mul]
        have hsub : r + q * (D + m) + (D + m) - 1 <
            r + q * (D + m) + (D + m) := Nat.sub_lt (by omega) (by omega)
        have hbound : r + q * (D + m) + (D + m) <
            q * (D + m) + (D + m) + (D + m) := by omega
        exact hsub.trans hbound
      apply Nat.div_eq_of_lt_le
      · exact hlo
      · exact hhi
    simp [testBlockCount, q, r, hr, hq]

theorem testBlockCount_eq_real_ceil {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H) :
    testBlockCount H m D = Nat.ceil ((H : ℝ) / (D + m)) := by
  have hL : 0 < D + m := by omega
  have hLr : (0 : ℝ) < (D + m : ℝ) := by exact_mod_cast hL
  have hK : 0 < testBlockCount H m D := testBlockCount_pos hm1 hm
  symm
  apply (Nat.ceil_eq_iff (Nat.ne_of_gt hK)).2
  let q := H / (D + m)
  let r := H % (D + m)
  have hdecomp : r + q * (D + m) = H := by
    dsimp [q, r]
    simpa [Nat.mul_comm] using Nat.mod_add_div H (D + m)
  by_cases hr : r = 0
  · have hKq : testBlockCount H m D = q := by
      simp [testBlockCount, q, r, hr]
    have hH0 : H = q * (D + m) := by
      rw [← hdecomp, hr]
      simp
    have hqpos : 0 < q := by
      have hH : 0 < H := lt_of_lt_of_le hm1 hm
      by_contra hq0
      have hqz : q = 0 := Nat.eq_zero_of_not_pos hq0
      rw [hH0, hqz] at hH
      simp at hH
    rw [hKq]
    constructor
    · apply (lt_div_iff₀ hLr).2
      have hnat : (q - 1) * (D + m) < H := by
        rw [hH0]
        exact Nat.mul_lt_mul_of_pos_right (Nat.sub_lt (by omega) (by omega)) hL
      exact_mod_cast hnat
    · apply (div_le_iff₀ hLr).2
      have hnat : H ≤ q * (D + m) := hH0.le
      exact_mod_cast hnat
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    have hrlt : r < D + m := by
      dsimp [r]
      exact Nat.mod_lt _ hL
    have hKq : testBlockCount H m D = q + 1 := by
      simp [testBlockCount, q, r, hr]
    rw [hKq]
    simp only [Nat.add_sub_cancel]
    constructor
    · apply (lt_div_iff₀ hLr).2
      have hnat : q * (D + m) < H := by omega
      exact_mod_cast hnat
    · apply (div_le_iff₀ hLr).2
      have hnat : H ≤ (q + 1) * (D + m) := by
        rw [← hdecomp]
        rw [Nat.succ_mul]
        omega
      exact_mod_cast hnat

theorem perfectBudget_lower_arithmetic {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H) :
    m ≤ perfectBudget H m D := by
  let q := H / (D + m)
  let r := H % (D + m)
  by_cases hq : q = 0
  · have hlt : H < D + m := by
      have hL : 0 < D + m := by omega
      dsimp [q] at hq
      exact (Nat.div_eq_zero_iff_lt hL).mp hq
    have hrem : r = H := by
      dsimp [r]
      exact Nat.mod_eq_of_lt hlt
    have hmin : min m r = m := by
      rw [hrem, min_eq_left hm]
    change m ≤ m * q + min m r
    rw [hmin]
    simp [hq]
  · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq
    have hmul : m ≤ m * q := by
      simpa [Nat.mul_comm] using (Nat.le_mul_of_pos_left m hq1)
    exact hmul.trans (Nat.le_add_right _ _)

theorem perfectBudget_upper_arithmetic {H m D : ℕ} (hm : m ≤ H) :
    perfectBudget H m D ≤ H := by
  let L := D + m
  let q := H / L
  let r := H % L
  have hdecomp : q * L + r = H := by
    dsimp [q, r]
    simpa [Nat.mul_comm] using Nat.div_add_mod H L
  have hmL : m ≤ L := by
    dsimp [L]
    omega
  have hq : m * q ≤ q * L := by
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left q hmL
  have hr : min m r ≤ r := min_le_right _ _
  have hsum : m * q + min m r ≤ q * L + r := Nat.add_le_add hq hr
  calc
    perfectBudget H m D = m * q + min m r := by rfl
    _ ≤ q * L + r := hsum
    _ = H := hdecomp

theorem perfectBudget_eq_quotient_remainder
    {H m D a b : ℕ} (hH : H = a * (D + m) + b) (hb : b < D + m) :
    perfectBudget H m D = m * a + min m b := by
  have hL : 0 < D + m := by omega
  have hdiv : H / (D + m) = a := by
    apply Nat.div_eq_of_lt_le
    · rw [hH]
      omega
    · rw [hH]
      rw [Nat.succ_mul]
      omega
  have hmod : H % (D + m) = b := by
    rw [hH, Nat.add_mod]
    simp [Nat.mul_mod_left, Nat.mod_eq_of_lt hb]
  simp [perfectBudget, hdiv, hmod]

end TrafficShaping
