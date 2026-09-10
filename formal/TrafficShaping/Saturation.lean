import TrafficShaping.Model

/-!
Finite saturation and terminal-reserve lemmas used by the converse.

The functions in this file are intentionally noncomputable choice functions:
the converse only needs existence and the corresponding specifications.
-/

namespace TrafficShaping

theorem terminal_card {H m : ℕ} (hm : m ≤ H) : (terminal H m).card = m := by
  let e : Fin m ≃ {a : Fin H // a ∈ terminal H m} :=
    { toFun := fun i =>
        ⟨⟨H - m + i.1, by omega⟩, by
          simp only [mem_terminal]
          omega⟩
      invFun := fun a =>
        ⟨a.1.1 - (H - m), by
          have ha : H - m ≤ a.1.1 := (mem_terminal.mp a.2)
          omega⟩
      left_inv := by
        intro i
        apply Fin.ext
        simp
      right_inv := by
        intro a
        apply Subtype.ext
        apply Fin.ext
        dsimp
        have ha : H - m ≤ a.1.1 := mem_terminal.mp a.2
        omega }
  have hcard := Fintype.card_congr e
  simpa only [Fintype.card_fin, Fintype.card_coe] using hcard.symm

theorem prefix_disjoint_terminal {H m : ℕ} (hm : m ≤ H) (y : Trace H) :
    Disjoint (tracePrefix (H - m) y) (terminal H m) := by
  refine Finset.disjoint_left.2 ?_
  intro a ha hta
  have hprefix : a.val < H - m := (mem_prefix.mp ha).2
  have hterminal : H - m ≤ a.val := mem_terminal.mp hta
  omega

theorem prefix_terminal_partition {H m : ℕ} (hm : m ≤ H) (y : Trace H) :
    tracePrefix (H - m) y ∪ (y ∩ terminal H m) = y := by
  ext a
  by_cases hterminal : H - m ≤ a.val
  · have hprefix : ¬ a.val < H - m := by omega
    simp [mem_prefix, mem_terminal, hterminal, hprefix]
  · have hprefix : a.val < H - m := by omega
    simp [mem_prefix, mem_terminal, hterminal, hprefix]

theorem prefix_terminal_card_partition {H m : ℕ} (hm : m ≤ H) (y : Trace H) :
    (tracePrefix (H - m) y).card + (y ∩ terminal H m).card = y.card := by
  have hdisj : Disjoint (tracePrefix (H - m) y) (y ∩ terminal H m) := by
    refine Finset.disjoint_left.2 ?_
    intro a ha hya
    have hya' : a ∈ y ∧ a ∈ terminal H m := by simpa using hya
    exact (Finset.disjoint_left.mp (prefix_disjoint_terminal hm y) ha) hya'.2
  calc
    _ = (tracePrefix (H - m) y ∪ (y ∩ terminal H m)).card :=
      (Finset.card_union_of_disjoint hdisj).symm
    _ = y.card := by rw [prefix_terminal_partition hm y]

theorem prefix_terminal_card_of_subset {H m : ℕ} (hm : m ≤ H) {y : Trace H}
    (hterminal : terminal H m ⊆ y) :
    (tracePrefix (H - m) y).card + (terminal H m).card = y.card := by
  have hinter : y ∩ terminal H m = terminal H m := by
    ext a
    constructor
    · intro ha
      exact (show a ∈ y ∧ a ∈ terminal H m by simpa using ha).2
    · intro ha
      exact (by simpa using (show a ∈ y ∧ a ∈ terminal H m from ⟨hterminal ha, ha⟩))
  simpa [hinter] using prefix_terminal_card_partition hm y

theorem union_terminal_eq_prefix_union_terminal {H m : ℕ} (hm : m ≤ H) (y : Trace H) :
    y ∪ terminal H m = tracePrefix (H - m) y ∪ terminal H m := by
  ext a
  by_cases hterminal : H - m ≤ a.val
  · simp [mem_prefix, mem_terminal, hterminal]
  · have hprefix : a.val < H - m := by omega
    simp [mem_prefix, mem_terminal, hterminal, hprefix]

theorem exists_trace_superset_card_eq {H B : ℕ} {y : Trace H}
    (hy : y.card ≤ B) (hB : B ≤ H) :
    ∃ z : Trace H, y ⊆ z ∧ z.card = B := by
  obtain ⟨z, hyz, hz⟩ := Finset.exists_superset_card_eq hy (by simpa using hB)
  exact ⟨z, hyz, hz⟩

noncomputable def extendTraceToCard {H B : ℕ} (y : Trace H)
    (hy : y.card ≤ B) (hB : B ≤ H) : Trace H :=
  Classical.choose (exists_trace_superset_card_eq hy hB)

theorem extendTraceToCard_subset {H B : ℕ} (y : Trace H)
    (hy : y.card ≤ B) (hB : B ≤ H) :
    y ⊆ extendTraceToCard y hy hB := by
  exact (Classical.choose_spec (exists_trace_superset_card_eq hy hB)).1

theorem extendTraceToCard_card {H B : ℕ} (y : Trace H)
    (hy : y.card ≤ B) (hB : B ≤ H) :
    (extendTraceToCard y hy hB).card = B := by
  exact (Classical.choose_spec (exists_trace_superset_card_eq hy hB)).2

noncomputable def saturateOff {H B : ℕ} (y : Trace H)
    (hy : y.card ≤ B) (hB : B ≤ H) : OffSchedule H B :=
  ⟨extendTraceToCard y hy hB, extendTraceToCard_card y hy hB⟩

theorem saturateOff_subset {H B : ℕ} (y : Trace H)
    (hy : y.card ≤ B) (hB : B ≤ H) :
    y ⊆ (saturateOff y hy hB).1 :=
  extendTraceToCard_subset y hy hB

theorem saturateOff_card {H B : ℕ} (y : Trace H)
    (hy : y.card ≤ B) (hB : B ≤ H) :
    (saturateOff y hy hB).1.card = B :=
  (saturateOff y hy hB).2

theorem exists_offSchedule (H B : ℕ) (hB : B ≤ H) :
    Nonempty (OffSchedule H B) := by
  obtain ⟨z, hz, hcard⟩ := exists_trace_superset_card_eq (y := (∅ : Trace H)) (by simp) hB
  exact ⟨⟨z, hcard⟩⟩

theorem exists_onSchedule {H m B : ℕ} (hm : m ≤ H) (hmb : m ≤ B) (hB : B ≤ H) :
    Nonempty (OnSchedule H m B) := by
  obtain ⟨z, hzt, hcard⟩ := exists_trace_superset_card_eq
    (y := terminal H m) (by simpa [terminal_card hm] using hmb) hB
  exact ⟨⟨z, hcard, hzt⟩⟩

theorem exists_onSchedule_superset {H m B : ℕ} (hm : m ≤ H)
    (hmb : m ≤ B) (hB : B ≤ H) {y : Trace H}
    (hy : (tracePrefix (H - m) y).card ≤ B - m) :
    ∃ z : Trace H, y ⊆ z ∧ z.card = B ∧ terminal H m ⊆ z := by
  have hbase_card : (y ∪ terminal H m).card ≤ B := by
    rw [union_terminal_eq_prefix_union_terminal hm y]
    rw [Finset.card_union_of_disjoint (prefix_disjoint_terminal hm y)]
    rw [terminal_card hm]
    omega
  obtain ⟨z, hbasez, hcard⟩ := exists_trace_superset_card_eq hbase_card hB
  refine ⟨z, ?_, hcard, ?_⟩
  · exact fun a ha => hbasez (Finset.mem_union_left _ ha)
  · exact fun a ha => hbasez (Finset.mem_union_right _ ha)

noncomputable def saturateOn {H m B : ℕ} (hm : m ≤ H)
    (hmb : m ≤ B) (hB : B ≤ H) (y : Trace H)
    (hy : (tracePrefix (H - m) y).card ≤ B - m) : OnSchedule H m B := by
  let z := Classical.choose (exists_onSchedule_superset hm hmb hB hy)
  have hz := Classical.choose_spec (exists_onSchedule_superset hm hmb hB hy)
  exact ⟨z, hz.2.1, hz.2.2⟩

theorem saturateOn_subset {H m B : ℕ} (hm : m ≤ H)
    (hmb : m ≤ B) (hB : B ≤ H) (y : Trace H)
    (hy : (tracePrefix (H - m) y).card ≤ B - m) :
    y ⊆ (saturateOn hm hmb hB y hy).1 := by
  exact (Classical.choose_spec (exists_onSchedule_superset hm hmb hB hy)).1

theorem saturateOn_terminal_subset {H m B : ℕ} (hm : m ≤ H)
    (hmb : m ≤ B) (hB : B ≤ H) (y : Trace H)
    (hy : (tracePrefix (H - m) y).card ≤ B - m) :
    terminal H m ⊆ (saturateOn hm hmb hB y hy).1 := by
  exact (Classical.choose_spec (exists_onSchedule_superset hm hmb hB hy)).2.2

theorem saturateOn_card {H m B : ℕ} (hm : m ≤ H)
    (hmb : m ≤ B) (hB : B ≤ H) (y : Trace H)
    (hy : (tracePrefix (H - m) y).card ≤ B - m) :
    (saturateOn hm hmb hB y hy).1.card = B := by
  exact (saturateOn hm hmb hB y hy).2.1

theorem exists_fullInput_superset {H m : ℕ} (hm : m ≤ H) (x : Input H m) :
    ∃ z : FullInput H m, x.1 ⊆ z.1 := by
  obtain ⟨z, hxz, hcard⟩ := exists_trace_superset_card_eq x.2 hm
  exact ⟨⟨z, hcard⟩, hxz⟩

noncomputable def extendInputToFull {H m : ℕ} (hm : m ≤ H) (x : Input H m) :
    FullInput H m :=
  Classical.choose (exists_fullInput_superset hm x)

theorem extendInputToFull_subset {H m : ℕ} (hm : m ≤ H) (x : Input H m) :
    x.1 ⊆ (extendInputToFull hm x).1 :=
  Classical.choose_spec (exists_fullInput_superset hm x)

def terminalFullInput {H m : ℕ} (hm : m ≤ H) : FullInput H m :=
  ⟨terminal H m, terminal_card hm⟩

theorem terminal_subset_of_feasible {H m D : ℕ} (hm : m ≤ H) {y : Trace H}
    (h : Feasible D (terminal H m) y) : terminal H m ⊆ y := by
  obtain ⟨f, hf, hservice⟩ := h
  let g : {a : Fin H // a ∈ terminal H m} → {a : Fin H // a ∈ terminal H m} :=
    fun a =>
      ⟨f a, by
        have ha : H - m ≤ a.1.1 := mem_terminal.mp a.2
        have hs := (hservice a).2.1
        simp only [mem_terminal]
        omega⟩
  have hg : Function.Injective g := by
    intro a b hab
    apply hf
    exact congrArg Subtype.val hab
  have hsurj : Function.Surjective g := Finite.surjective_of_injective hg
  intro a ha
  let target : {a : Fin H // a ∈ terminal H m} := ⟨a, ha⟩
  obtain ⟨b, hb⟩ := hsurj target
  have hfb : f b = a := by
    exact congrArg Subtype.val hb
  simpa [hfb] using (hservice b).1

theorem prefix_card_le_sub_of_terminal_feasible {H m B D : ℕ}
    (hm : m ≤ H) (hmb : m ≤ B) {y : Trace H}
    (hcap : y.card ≤ B) (h : Feasible D (terminal H m) y) :
    (tracePrefix (H - m) y).card ≤ B - m := by
  have hterminal : terminal H m ⊆ y := terminal_subset_of_feasible hm h
  have hinter : y ∩ terminal H m = terminal H m := by
    ext a
    constructor
    · intro ha
      exact (show a ∈ y ∧ a ∈ terminal H m by simpa using ha).2
    · intro ha
      exact (by simpa using (show a ∈ y ∧ a ∈ terminal H m from ⟨hterminal ha, ha⟩))
  have hpartition := prefix_terminal_card_partition hm y
  rw [hinter, terminal_card hm] at hpartition
  omega

end TrafficShaping
