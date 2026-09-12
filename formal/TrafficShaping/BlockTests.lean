import TrafficShaping.CorollaryDefinitions

/-!
  The finite family of block tests used for the lower bounds in Corollaries 3
  and 5.  The tests are separate inputs.  In particular, no union of their
  arrival sets is used as an admissible input.
-/

namespace TrafficShaping

private theorem block_length_pos {m D : ℕ} (hm1 : 1 ≤ m) :
    0 < D + m := by
  omega

theorem testBlockCount_pos {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H) :
    0 < testBlockCount H m D := by
  have hH : 0 < H := lt_of_lt_of_le hm1 hm
  have hL : 0 < D + m := block_length_pos hm1
  unfold testBlockCount
  by_cases hr : H % (D + m) = 0
  · have hq : 0 < H / (D + m) := by
      apply (Nat.div_pos_iff).2
      refine ⟨hL, ?_⟩
      by_contra hLH
      have hlt : H < D + m := Nat.lt_of_not_ge hLH
      have hmod : H % (D + m) = H := Nat.mod_eq_of_lt hlt
      omega
    simp [hr, hq]
  · simp [hr]

private theorem block_start_lt {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (i : Fin (testBlockCount H m D)) :
    i.val * (D + m) < H := by
  have hL : 0 < D + m := block_length_pos hm1
  have hqL : (H / (D + m)) * (D + m) ≤ H := Nat.div_mul_le_self H (D + m)
  by_cases hr : H % (D + m) = 0
  · have hiq : i.val < H / (D + m) := by
      simpa [testBlockCount, hr] using i.isLt
    exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hiq hL) hqL
  · have hiq : i.val ≤ H / (D + m) := by
      have hi := i.isLt
      simp [testBlockCount, hr] at hi
      omega
    have hrem : 0 < H % (D + m) := Nat.pos_of_ne_zero hr
    have hdecomp : H % (D + m) + (H / (D + m)) * (D + m) = H := by
      simpa [Nat.mul_comm] using Nat.mod_add_div H (D + m)
    have hqLt : (H / (D + m)) * (D + m) < H := by
      omega
    exact lt_of_le_of_lt (Nat.mul_le_mul_right (D + m) hiq) hqLt

private theorem block_start_lt_next {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (i : Fin (testBlockCount H m D)) :
    i.val * (D + m) < (i.val + 1) * (D + m) := by
  exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self i.val) (block_length_pos hm1)

private theorem block_start_lt_stop {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (i : Fin (testBlockCount H m D)) :
    i.val * (D + m) < min H ((i.val + 1) * (D + m)) := by
  exact lt_min (block_start_lt hm1 hm i) (block_start_lt_next hm1 hm i)

private theorem block_stop_le_horizon {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (i : Fin (testBlockCount H m D)) :
    min H ((i.val + 1) * (D + m)) ≤ H :=
  Nat.min_le_left _ _

private theorem block_stop_pos {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (i : Fin (testBlockCount H m D)) :
    0 < min H ((i.val + 1) * (D + m)) := by
  have h := block_start_lt_stop hm1 hm i
  omega

private def blockStartFin {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (i : Fin (testBlockCount H m D)) : Fin H :=
  ⟨i.val * (D + m), block_start_lt hm1 hm i⟩

private def blockStopLastFin {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (i : Fin (testBlockCount H m D)) : Fin H :=
  ⟨min H ((i.val + 1) * (D + m)) - 1, by
    have hpos := block_stop_pos hm1 hm i
    have hle := block_stop_le_horizon hm1 hm i
    omega⟩

def blockArrivalCount (H m D i : ℕ) : ℕ :=
  min m (H - i * (D + m))

theorem blockArrivalCount_pos {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (i : Fin (testBlockCount H m D)) :
    0 < blockArrivalCount H m D i.val := by
  have hs := block_start_lt hm1 hm i
  have hr : 0 < H - i.val * (D + m) := (Nat.sub_pos_iff_lt).2 hs
  unfold blockArrivalCount
  rw [Nat.pos_iff_ne_zero]
  intro h
  rw [Nat.min_eq_zero_iff] at h
  omega

def blockArrivals {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (i : Fin (testBlockCount H m D)) : Trace H :=
  Finset.Icc (blockStartFin hm1 hm i)
    ⟨i.val * (D + m) + blockArrivalCount H m D i.val - 1, by
      have hqpos := blockArrivalCount_pos hm1 hm i
      have hqle : blockArrivalCount H m D i.val ≤ H - i.val * (D + m) :=
        Nat.min_le_right _ _
      omega⟩

def blockService {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (i : Fin (testBlockCount H m D)) : Trace H :=
  Finset.Icc (blockStartFin hm1 hm i) (blockStopLastFin hm1 hm i)

theorem blockArrivals_card {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (i : Fin (testBlockCount H m D)) :
    (blockArrivals hm1 hm i).card = blockArrivalCount H m D i.val := by
  have hqpos := blockArrivalCount_pos hm1 hm i
  have hqle : blockArrivalCount H m D i.val ≤ H - i.val * (D + m) :=
    Nat.min_le_right _ _
  simp [blockArrivals, blockStartFin, blockArrivalCount]
  omega

def blockTest {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (i : Fin (testBlockCount H m D)) : Input H m :=
  ⟨blockArrivals hm1 hm i, by
    rw [blockArrivals_card hm1 hm i]
    exact Nat.min_le_left _ _⟩

def blockTests {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H) :
    Fin (testBlockCount H m D) → Input H m :=
  fun i => blockTest hm1 hm i

theorem blockTest_card {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (i : Fin (testBlockCount H m D)) :
    (blockTest hm1 hm i).1.card = blockArrivalCount H m D i.val := by
  exact blockArrivals_card hm1 hm i

theorem blockArrivalCount_sum {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H) :
    (∑ i : Fin (testBlockCount H m D), blockArrivalCount H m D i.val) =
      perfectBudget H m D := by
  let q := H / (D + m)
  let r := H % (D + m)
  have hqL : q * (D + m) ≤ H := by
    exact Nat.div_mul_le_self H (D + m)
  have hfull : ∀ i : Fin q,
      blockArrivalCount H m D i.val = m := by
    intro i
    have hiq : i.val + 1 ≤ q := by omega
    have hstep : (i.val + 1) * (D + m) ≤ q * (D + m) :=
      Nat.mul_le_mul_right (D + m) hiq
    have hstart : i.val * (D + m) + m ≤ (i.val + 1) * (D + m) := by
      rw [Nat.succ_mul]
      omega
    have hadd : i.val * (D + m) + m ≤ H :=
      le_trans hstart (le_trans hstep hqL)
    have hmrem : m ≤ H - i.val * (D + m) := by
      apply Nat.le_sub_of_add_le
      simpa [Nat.add_comm] using hadd
    unfold blockArrivalCount
    rw [Nat.min_eq_left hmrem]
  have hdecomp : r + q * (D + m) = H := by
    dsimp [q, r]
    simpa [Nat.mul_comm] using Nat.mod_add_div H (D + m)
  by_cases hr : r = 0
  · have hK : testBlockCount H m D = q := by
      simp [testBlockCount, q, r, hr]
    rw [hK]
    have hsum : (∑ i : Fin q, blockArrivalCount H m D i) = ∑ _i : Fin q, m := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hfull i
    rw [hsum]
    simp [perfectBudget, q, r, hr, Nat.mul_comm]
  · have hK : testBlockCount H m D = q + 1 := by
      simp [testBlockCount, q, r, hr]
    have hlast :
        blockArrivalCount H m D q = min m r := by
      have hrem : H - q * (D + m) = r := by
        omega
      simp [blockArrivalCount, hrem]
    rw [hK, Fin.sum_univ_castSucc]
    have hsum : (∑ i : Fin q, blockArrivalCount H m D i.castSucc.val) =
        ∑ _i : Fin q, m := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa using hfull i
    have hlast' : blockArrivalCount H m D (Fin.last q).val = min m r := by
      simpa using hlast
    rw [hsum, hlast']
    simp [perfectBudget, q, r, hr, Nat.mul_comm]

theorem blockService_nonempty {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (i : Fin (testBlockCount H m D)) :
    (blockService hm1 hm i).Nonempty := by
  apply (Finset.nonempty_Icc).2
  change i.val * (D + m) ≤ min H ((i.val + 1) * (D + m)) - 1
  have h := block_start_lt_stop hm1 hm i
  omega

theorem blockArrivals_subset_service {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (i : Fin (testBlockCount H m D)) :
    blockArrivals hm1 hm i ⊆ blockService hm1 hm i := by
  intro a ha
  have ha' := Finset.mem_Icc.mp ha
  change i.val * (D + m) ≤ a.val ∧
      a.val ≤ i.val * (D + m) + blockArrivalCount H m D i.val - 1 at ha'
  have hqle : blockArrivalCount H m D i.val ≤ m := Nat.min_le_left _ _
  have hnext : i.val * (D + m) + (D + m) = (i.val + 1) * (D + m) := by
    rw [Nat.succ_mul]
  have ha_next : a.val < (i.val + 1) * (D + m) := by
    rw [← hnext]
    omega
  have ha_horizon : a.val < H := a.isLt
  have ha_stop : a.val < min H ((i.val + 1) * (D + m)) :=
    lt_min ha_horizon ha_next
  have ha_last : a.val ≤ min H ((i.val + 1) * (D + m)) - 1 := by
    omega
  apply Finset.mem_Icc.mpr
  change i.val * (D + m) ≤ a.val ∧
      a.val ≤ min H ((i.val + 1) * (D + m)) - 1
  exact ⟨ha'.1, ha_last⟩

theorem blockService_pairwise_disjoint {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    {i j : Fin (testBlockCount H m D)} (hij : i ≠ j) :
    Disjoint (blockService hm1 hm i) (blockService hm1 hm j) := by
  refine Finset.disjoint_left.2 ?_
  intro a hai haj
  have hai' := Finset.mem_Icc.mp hai
  have haj' := Finset.mem_Icc.mp haj
  change i.val * (D + m) ≤ a.val ∧
      a.val ≤ min H ((i.val + 1) * (D + m)) - 1 at hai'
  change j.val * (D + m) ≤ a.val ∧
      a.val ≤ min H ((j.val + 1) * (D + m)) - 1 at haj'
  have hval : i.val ≠ j.val := by
    intro h
    apply hij
    exact Fin.ext h
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · have hnext : (i.val + 1) * (D + m) ≤ j.val * (D + m) := by
      exact Nat.mul_le_mul_right (D + m) (by omega)
    have hstop : min H ((i.val + 1) * (D + m)) ≤
        (i.val + 1) * (D + m) := Nat.min_le_right _ _
    have hpos : 0 < min H ((i.val + 1) * (D + m)) :=
      block_stop_pos hm1 hm i
    have hainext : a.val < (i.val + 1) * (D + m) := by
      have hai_stop : a.val < min H ((i.val + 1) * (D + m)) := by
        exact lt_of_le_of_lt hai'.2 (Nat.sub_lt hpos (by omega))
      exact lt_of_lt_of_le hai_stop hstop
    exact (Nat.not_lt_of_ge haj'.1) (lt_of_lt_of_le hainext hnext)
  · have hnext : (j.val + 1) * (D + m) ≤ i.val * (D + m) := by
      exact Nat.mul_le_mul_right (D + m) (by omega)
    have hstop : min H ((j.val + 1) * (D + m)) ≤
        (j.val + 1) * (D + m) := Nat.min_le_right _ _
    have hpos : 0 < min H ((j.val + 1) * (D + m)) :=
      block_stop_pos hm1 hm j
    have hajnext : a.val < (j.val + 1) * (D + m) := by
      have haj_stop : a.val < min H ((j.val + 1) * (D + m)) := by
        exact lt_of_le_of_lt haj'.2 (Nat.sub_lt hpos (by omega))
      exact lt_of_lt_of_le haj_stop hstop
    exact (Nat.not_lt_of_ge hai'.1) (lt_of_lt_of_le hajnext hnext)

private theorem feasible_block_assignment {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (i : Fin (testBlockCount H m D)) (y : Trace H)
    (h : Feasible D (blockArrivals hm1 hm i) y) :
    ∃ f : {a : Fin H // a ∈ blockArrivals hm1 hm i} → Fin H,
      Function.Injective f ∧
        ∀ a, f a ∈ y ∧ f a ∈ blockService hm1 hm i := by
  obtain ⟨f, hfi, hf⟩ := h
  refine ⟨f, hfi, ?_⟩
  intro a
  have ha := Finset.mem_Icc.mp a.property
  change i.val * (D + m) ≤ a.val ∧
      a.val ≤ i.val * (D + m) + blockArrivalCount H m D i.val - 1 at ha
  have hqle : blockArrivalCount H m D i.val ≤ m := Nat.min_le_left _ _
  have hstart : i.val * (D + m) ≤ (f a).val :=
    le_trans ha.1 (hf a).2.1
  have ha_m : a.val < i.val * (D + m) + m := by
    omega
  have haD_next : a.val + D < (i.val + 1) * (D + m) := by
    calc
      a.val + D < i.val * (D + m) + m + D := Nat.add_lt_add_right ha_m D
      _ = i.val * (D + m) + (D + m) := by omega
      _ = (i.val + 1) * (D + m) := by rw [Nat.succ_mul]
  have hf_next : (f a).val < (i.val + 1) * (D + m) :=
    lt_of_le_of_lt (Nat.le_trans (hf a).2.2 (by omega)) haD_next
  have hf_horizon : (f a).val < H := (f a).isLt
  have hf_stop : (f a).val < min H ((i.val + 1) * (D + m)) :=
    lt_min hf_horizon hf_next
  have hf_last : (f a).val ≤ min H ((i.val + 1) * (D + m)) - 1 := by
    omega
  have hf_service : f a ∈ blockService hm1 hm i := by
    apply Finset.mem_Icc.mpr
    change i.val * (D + m) ≤ (f a).val ∧
        (f a).val ≤ min H ((i.val + 1) * (D + m)) - 1
    exact ⟨hstart, hf_last⟩
  exact ⟨(hf a).1, hf_service⟩

theorem block_tests_lower_bound {H m D : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ H)
    (y : Trace H)
    (hfeas : ∀ i : Fin (testBlockCount H m D),
      Feasible D (blockTests hm1 hm i).1 y) :
    perfectBudget H m D ≤ y.card := by
  have hassign : ∀ i : Fin (testBlockCount H m D),
      ∃ f : {a : Fin H // a ∈ blockArrivals hm1 hm i} → Fin H,
        Function.Injective f ∧
          ∀ a, f a ∈ y ∧ f a ∈ blockService hm1 hm i := by
    intro i
    apply feasible_block_assignment hm1 hm i y
    simpa [blockTests, blockTest] using hfeas i
  choose f hf_inj hf_mem using hassign
  let G : (Σ i : Fin (testBlockCount H m D),
      {a : Fin H // a ∈ blockArrivals hm1 hm i}) →
      {a : Fin H // a ∈ y} := fun z =>
    ⟨f z.1 z.2, (hf_mem z.1 z.2).1⟩
  have hG : Function.Injective G := by
    intro p q hpq
    have hval : f p.1 p.2 = f q.1 q.2 := congrArg Subtype.val hpq
    by_cases hidx : p.1 = q.1
    · rcases p with ⟨pi, pa⟩
      rcases q with ⟨qi, qa⟩
      dsimp at hidx hval ⊢
      subst qi
      have hsnd : pa = qa := by
        apply Subtype.ext
        exact congrArg Subtype.val (hf_inj pi hval)
      cases hsnd
      rfl
    · have hdisj := blockService_pairwise_disjoint hm1 hm hidx
      have hqserv : f p.1 p.2 ∈ blockService hm1 hm q.1 := by
        rw [hval]
        exact (hf_mem q.1 q.2).2
      exact (Finset.disjoint_left.mp hdisj (hf_mem p.1 p.2).2 hqserv).elim
  have hcard := Fintype.card_le_of_injective G hG
  have hdomain : Fintype.card (Σ i : Fin (testBlockCount H m D),
      {a : Fin H // a ∈ blockArrivals hm1 hm i}) =
      ∑ i : Fin (testBlockCount H m D), (blockArrivals hm1 hm i).card := by
    simp [Fintype.card_sigma, Fintype.card_coe]
  calc
    perfectBudget H m D =
        ∑ i : Fin (testBlockCount H m D), blockArrivalCount H m D i.val :=
      (blockArrivalCount_sum hm1 hm).symm
    _ = ∑ i : Fin (testBlockCount H m D), (blockArrivals hm1 hm i).card := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (blockArrivals_card hm1 hm i).symm
    _ = Fintype.card (Σ i : Fin (testBlockCount H m D),
        {a : Fin H // a ∈ blockArrivals hm1 hm i}) := hdomain.symm
    _ ≤ Fintype.card {a : Fin H // a ∈ y} := hcard
    _ = y.card := by simp [Fintype.card_coe]

end TrafficShaping
