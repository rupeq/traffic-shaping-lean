import TrafficShaping.Model

/-!
FIFO earliest-slot matching for the finite traffic-shaping model.

The implementation below deliberately works with finite sets rather than a
particular list representation.  The head packet is the least arrival and
the selected service slot is the least available slot not before it.  The
proofs in this file establish that this recursive greedy test is equivalent
to the injective assignment predicate in `Model.Feasible`.
-/

namespace TrafficShaping

def candidates {H : ℕ} (a : Fin H) (y : Trace H) : Trace H :=
  y.filter (fun s => a.val ≤ s.val)

def greedyStep {H D : ℕ} (a : Fin H) (y : Trace H) : Option (Fin H) :=
  let c := candidates a y
  if hc : c.Nonempty then
    let s := c.min' hc
    if s.val ≤ a.val + D then some s else none
  else none

/-- The FIFO earliest-slot greedy decision.

At each recursive step the least arrival is paired with the least available
transmission slot not before it.  A pair is accepted only if its deadline is
respected; the chosen arrival and slot are then removed. -/
def greedy {H D : ℕ} (x y : Trace H) : Bool :=
  if hx : x.Nonempty then
    let a := x.min' hx
    match greedyStep (D := D) a y with
    | some s => greedy (D := D) (x.erase a) (y.erase s)
    | none => false
  else true
termination_by x.card
decreasing_by
  exact Finset.card_erase_lt_of_mem (Finset.min'_mem x hx)

@[simp] theorem mem_candidates {H : ℕ} {a s : Fin H} {y : Trace H} :
    s ∈ candidates a y ↔ s ∈ y ∧ a.val ≤ s.val := by
  simp [candidates]

theorem earliest_available_mem {H : ℕ} {a : Fin H} {y : Trace H}
    (hc : (candidates a y).Nonempty) :
    (candidates a y).min' hc ∈ y ∧
      a.val ≤ ((candidates a y).min' hc).val := by
  exact mem_candidates.mp (Finset.min'_mem _ hc)

theorem earliest_available_le {H : ℕ} {a s : Fin H} {y : Trace H}
    (hc : (candidates a y).Nonempty) (hs : s ∈ y) (has : a.val ≤ s.val) :
    (candidates a y).min' hc ≤ s := by
  exact Finset.min'_le _ s (mem_candidates.mpr ⟨hs, has⟩)

@[simp] theorem greedy_empty {H D : ℕ} (y : Trace H) :
    greedy (D := D) (∅ : Trace H) y = true := by
  simp [greedy]

theorem greedy_nonempty {H D : ℕ} {x y : Trace H} (hx : x.Nonempty) :
    greedy (D := D) x y =
      match greedyStep (D := D) (x.min' hx) y with
      | some s => greedy (D := D) (x.erase (x.min' hx)) (y.erase s)
      | none => false := by
  rw [greedy.eq_1, dif_pos hx]

theorem greedyStep_eq_some {H D : ℕ} {a : Fin H} {y : Trace H}
    (hc : (candidates a y).Nonempty)
    (hs : ((candidates a y).min' hc).val ≤ a.val + D) :
    greedyStep (D := D) a y = some ((candidates a y).min' hc) := by
  simp [greedyStep, hc, hs]

theorem greedyStep_eq_none_of_not_nonempty {H D : ℕ} {a : Fin H} {y : Trace H}
    (hc : ¬(candidates a y).Nonempty) :
    greedyStep (D := D) a y = none := by
  simp [greedyStep, hc]

theorem greedyStep_eq_none_of_deadline {H D : ℕ} {a : Fin H} {y : Trace H}
    (hc : (candidates a y).Nonempty)
    (hs : ¬((candidates a y).min' hc).val ≤ a.val + D) :
    greedyStep (D := D) a y = none := by
  simp [greedyStep, hc, hs]

theorem greedyStep_some_spec {H D : ℕ} {a s : Fin H} {y : Trace H}
    (h : greedyStep (D := D) a y = some s) :
    s ∈ y ∧ a.val ≤ s.val ∧ s.val ≤ a.val + D ∧
      ∀ t ∈ y, a.val ≤ t.val → s ≤ t := by
  classical
  unfold greedyStep at h
  dsimp only at h
  split at h <;> rename_i hc
  · split at h <;> rename_i hs
    · have heq : (candidates a y).min' hc = s := Option.some.inj h
      subst s
      have hmem := earliest_available_mem hc
      refine ⟨hmem.1, hmem.2, hs, ?_⟩
      intro t ht hat
      exact earliest_available_le hc ht hat
    · simp_all
  · simp_all

theorem greedy_head_some {H D : ℕ} {x y : Trace H}
    (hx : x.Nonempty) (h : greedy (D := D) x y = true) :
    ∃ s, greedyStep (D := D) (x.min' hx) y = some s ∧
      greedy (D := D) (x.erase (x.min' hx)) (y.erase s) = true := by
  rw [greedy.eq_1, dif_pos hx] at h
  dsimp only at h
  split at h <;> rename_i s hs
  · exact ⟨s, hs, h⟩
  · exact Bool.noConfusion h

theorem candidates_nonempty_of_feasible {H D : ℕ} {x y : Trace H}
    (hx : x.Nonempty) (hxy : Feasible D x y) :
    (candidates (x.min' hx) y).Nonempty := by
  obtain ⟨f, hi, hf⟩ := hxy
  let a : Fin H := x.min' hx
  have ha : a ∈ x := Finset.min'_mem x hx
  let aa : {b : Fin H // b ∈ x} := ⟨a, ha⟩
  let s : Fin H := f aa
  refine ⟨s, ?_⟩
  exact Finset.mem_filter.mpr ⟨(hf aa).1, (hf aa).2.1⟩

theorem not_feasible_of_greedy_deadline {H D : ℕ} {x y : Trace H}
    (hx : x.Nonempty)
    (hc : (candidates (x.min' hx) y).Nonempty)
    (hs : ¬((candidates (x.min' hx) y).min' hc).val ≤ (x.min' hx).val + D) :
    ¬Feasible D x y := by
  intro hxy
  obtain ⟨f, hi, hf⟩ := hxy
  let a : Fin H := x.min' hx
  have ha : a ∈ x := Finset.min'_mem x hx
  let aa : {b : Fin H // b ∈ x} := ⟨a, ha⟩
  let s : Fin H := f aa
  have hsy : s ∈ y := (hf aa).1
  have hsa : a.val ≤ s.val := (hf aa).2.1
  have hsc : s ∈ candidates a y := by
    exact Finset.mem_filter.mpr ⟨hsy, hsa⟩
  have hmins : (candidates a y).min' hc ≤ s :=
    Finset.min'_le (candidates a y) s hsc
  have hsd : s.val ≤ a.val + D := (hf aa).2.2
  exact hs (le_trans (Fin.le_iff_val_le_val.mp hmins) hsd)

theorem feasible_erase_min_iff {H D : ℕ} {x y : Trace H}
    (hx : x.Nonempty)
    (hc : (candidates (x.min' hx) y).Nonempty)
    (hs : ((candidates (x.min' hx) y).min' hc).val ≤ (x.min' hx).val + D) :
    Feasible D x y ↔
      Feasible D (x.erase (x.min' hx))
        (y.erase ((candidates (x.min' hx) y).min' hc)) := by
  classical
  let a : Fin H := x.min' hx
  let ha : a ∈ x := Finset.min'_mem x hx
  let aa : {b : Fin H // b ∈ x} := ⟨a, ha⟩
  let c : Trace H := candidates a y
  let hc' : c.Nonempty := by simpa [c] using hc
  let s : Fin H := c.min' hc'
  have hca : s ∈ c := Finset.min'_mem c hc'
  have hsy : s ∈ y := (Finset.mem_filter.mp hca).1
  have hsa : a.val ≤ s.val := (Finset.mem_filter.mp hca).2
  have hsd : s.val ≤ a.val + D := by simpa [a, c, s] using hs
  have ha_min (b : Fin H) (hb : b ∈ x) : a ≤ b :=
    Finset.min'_le x b hb
  have hs_min (b : Fin H) (hb : b ∈ c) : s ≤ b :=
    Finset.min'_le c b hb
  constructor
  · intro hxy
    obtain ⟨f, hfi, hf⟩ := hxy
    let s0 : Fin H := f aa
    have hs0y : s0 ∈ y := (hf aa).1
    have hsa0 : a.val ≤ s0.val := (hf aa).2.1
    have hs0d : s0.val ≤ a.val + D := (hf aa).2.2
    have hs0c : s0 ∈ c := Finset.mem_filter.mpr ⟨hs0y, hsa0⟩
    have hss0 : s ≤ s0 := hs_min s0 hs0c
    have hss0val : s.val ≤ s0.val := Fin.le_iff_val_le_val.mp hss0
    let emb : {b : Fin H // b ∈ x.erase a} → {b : Fin H // b ∈ x} :=
      fun b => ⟨b.val, Finset.erase_subset a x b.property⟩
    by_cases hse : s = s0
    · let g : {b : Fin H // b ∈ x.erase a} → Fin H := fun b => f (emb b)
      refine ⟨g, ?_, ?_⟩
      · intro b1 b2 h12
        have he : emb b1 = emb b2 := by
          apply hfi
          simpa [g] using h12
        exact Subtype.ext (by
          simpa [emb] using congrArg (fun z : {b : Fin H // b ∈ x} => z.val) he)
      · intro b
        have hbmem : b.val ∈ x := Finset.erase_subset a x b.property
        have hbneq : f (emb b) ≠ s := by
          intro heq
          have heq' : f (emb b) = f aa := by simpa [s0, hse] using heq
          have hab : emb b = aa := hfi heq'
          have hv : b.val = a := by
            simpa [emb, aa] using congrArg (fun z : {b : Fin H // b ∈ x} => z.val) hab
          exact (Finset.mem_erase.mp b.property).1 hv
        have hfb := hf (emb b)
        simpa [g, emb] using
          (⟨Finset.mem_erase.mpr ⟨hbneq, hfb.1⟩, hfb.2⟩ :
            f (emb b) ∈ y.erase s ∧
              (emb b).val.val ≤ (f (emb b)).val ∧
              (f (emb b)).val ≤ (emb b).val.val + D)
    · let g : {b : Fin H // b ∈ x.erase a} → Fin H := fun b =>
        if f (emb b) = s then s0 else f (emb b)
      refine ⟨g, ?_, ?_⟩
      · intro b1 b2 h12
        by_cases h1 : f (emb b1) = s <;>
          by_cases h2 : f (emb b2) = s
        · have he : emb b1 = emb b2 := hfi (h1.trans h2.symm)
          exact Subtype.ext (by
            simpa [emb] using congrArg (fun z : {b : Fin H // b ∈ x} => z.val) he)
        · exfalso
          have heq : f (emb b2) = f aa := by
            simpa [g, h1, h2, s0] using h12.symm
          have hab : emb b2 = aa := hfi heq
          have hv : b2.val = a := by
            simpa [emb, aa] using congrArg (fun z : {b : Fin H // b ∈ x} => z.val) hab
          exact (Finset.mem_erase.mp b2.property).1 hv
        · exfalso
          have heq : f (emb b1) = f aa := by
            simpa [g, h1, h2, s0] using h12
          have hab : emb b1 = aa := hfi heq
          have hv : b1.val = a := by
            simpa [emb, aa] using congrArg (fun z : {b : Fin H // b ∈ x} => z.val) hab
          exact (Finset.mem_erase.mp b1.property).1 hv
        · have he : emb b1 = emb b2 := by
            apply hfi
            simpa [g, h1, h2] using h12
          exact Subtype.ext (by
            simpa [emb] using congrArg (fun z : {b : Fin H // b ∈ x} => z.val) he)
      · intro b
        have hbmem : b.val ∈ x := Finset.erase_subset a x b.property
        have hfb := hf (emb b)
        by_cases hbs : f (emb b) = s
        · have hab : a ≤ b.val := ha_min b.val hbmem
          have habval : a.val ≤ b.val.val := Fin.le_iff_val_le_val.mp hab
          have hbd : s0.val ≤ b.val.val + D :=
            le_trans hs0d (Nat.add_le_add_right habval D)
          have hbs0 : s0 ≠ s := by
            intro h0
            exact hse h0.symm
          have hgb_eq : g b = s0 := by simp [g, hbs]
          have hgb_y : g b ∈ y.erase s := by
            rw [hgb_eq]
            exact Finset.mem_erase.mpr ⟨hbs0, hs0y⟩
          have hfb_rel0 : (emb b).val.val ≤ s.val := by simpa [hbs] using hfb.2.1
          have hfb_rel : b.val.val ≤ s.val := by simpa [emb] using hfb_rel0
          have hgb_rel : b.val.val ≤ (g b).val := by
            rw [hgb_eq]
            exact le_trans hfb_rel hss0val
          have hgb_dead : (g b).val ≤ b.val.val + D := by
            rw [hgb_eq]
            exact hbd
          exact ⟨hgb_y, hgb_rel, hgb_dead⟩
        · have hbs' : ¬f (emb b) =
              (candidates (x.min' hx) y).min' hc := by
            simpa [s, c] using hbs
          have hmem : f (emb b) ∈
              y.erase ((candidates (x.min' hx) y).min' hc) :=
            Finset.mem_erase.mpr ⟨hbs', hfb.1⟩
          have hgb_eq : g b = f (emb b) := by simp [g, hbs]
          rw [hgb_eq]
          exact ⟨hmem, by simpa [emb] using hfb.2.1,
            by simpa [emb] using hfb.2.2⟩
  · intro hrest
    obtain ⟨g, hgi, hg⟩ := hrest
    let emb : {b : Fin H // b ∈ x.erase a} → {b : Fin H // b ∈ x} :=
      fun b => ⟨b.val, Finset.erase_subset a x b.property⟩
    let f : {b : Fin H // b ∈ x} → Fin H := fun b =>
      if hba : b.val = a then s
      else g ⟨b.val, Finset.mem_erase.mpr ⟨hba, b.property⟩⟩
    refine ⟨f, ?_, ?_⟩
    · intro b1 b2 h12
      by_cases h1 : b1.val = a <;> by_cases h2 : b2.val = a
      · apply Subtype.ext
        exact h1.trans h2.symm
      · exfalso
        have hmem := hg ⟨b2.val, Finset.mem_erase.mpr ⟨h2, b2.property⟩⟩
        have hn : g ⟨b2.val, Finset.mem_erase.mpr ⟨h2, b2.property⟩⟩ ≠ s := by
          intro heq
          exact (Finset.mem_erase.mp hmem.1).1 heq
        exact hn (by simpa [f, h1, h2] using h12.symm)
      · exfalso
        have hmem := hg ⟨b1.val, Finset.mem_erase.mpr ⟨h1, b1.property⟩⟩
        have hn : g ⟨b1.val, Finset.mem_erase.mpr ⟨h1, b1.property⟩⟩ ≠ s := by
          intro heq
          exact (Finset.mem_erase.mp hmem.1).1 heq
        exact hn (by simpa [f, h1, h2] using h12)
      · have he :
            g ⟨b1.val, Finset.mem_erase.mpr ⟨h1, b1.property⟩⟩ =
              g ⟨b2.val, Finset.mem_erase.mpr ⟨h2, b2.property⟩⟩ := by
          simpa [f, h1, h2] using h12
        have he' := hgi he
        exact Subtype.ext (congrArg
          (fun z : {q : Fin H // q ∈ x.erase a} => z.val) he')
    · intro b
      by_cases hba : b.val = a
      · have hbs : s ∈ y := hsy
        simpa [f, hba] using (⟨hbs, hsa, hsd⟩ :
          s ∈ y ∧ a.val ≤ s.val ∧ s.val ≤ a.val + D)
      · let rb : {q : Fin H // q ∈ x.erase a} :=
          ⟨b.val, Finset.mem_erase.mpr ⟨hba, b.property⟩⟩
        have hgb := hg rb
        have hgbmem : g rb ∈ y.erase s := by simpa [s, c] using hgb.1
        have hgbrel : b.val.val ≤ (g rb).val := by
          simpa [rb] using hgb.2.1
        have hgbdead : (g rb).val ≤ b.val.val + D := by
          simpa [rb] using hgb.2.2
        have hfb_eq : f b = g rb := by simp [f, hba, rb]
        rw [hfb_eq]
        exact ⟨Finset.erase_subset s y hgbmem, hgbrel, hgbdead⟩

theorem greedy_true_iff_feasible {H D : ℕ} (x y : Trace H) :
    greedy (D := D) x y = true ↔ Feasible D x y := by
  revert y
  refine Finset.strongInductionOn x ?_
  intro x ih y
  by_cases hx : x.Nonempty
  · let a : Fin H := x.min' hx
    let c : Trace H := candidates a y
    by_cases hc : c.Nonempty
    · let s : Fin H := c.min' hc
      by_cases hs : s.val ≤ a.val + D
      · dsimp [a, c] at hc s hs
        rw [greedy.eq_1, dif_pos hx]
        change (match greedyStep (D := D) a y with
          | some s' => greedy (D := D) (x.erase a) (y.erase s')
          | none => false) = true ↔ Feasible D x y
        rw [greedyStep_eq_some hc hs]
        change greedy (D := D) (x.erase a) (y.erase s) = true ↔ Feasible D x y
        rw [ih (x.erase a) (Finset.erase_ssubset (Finset.min'_mem x hx))]
        exact (feasible_erase_min_iff hx hc hs).symm
      · dsimp [a, c] at hc s hs
        rw [greedy.eq_1, dif_pos hx]
        change (match greedyStep (D := D) a y with
          | some s' => greedy (D := D) (x.erase a) (y.erase s')
          | none => false) = true ↔ Feasible D x y
        rw [greedyStep_eq_none_of_deadline hc hs]
        constructor
        · intro h
          exact Bool.noConfusion h
        · intro h
          exact (not_feasible_of_greedy_deadline hx hc hs h).elim
    · dsimp [a, c] at hc
      rw [greedy.eq_1, dif_pos hx]
      change (match greedyStep (D := D) a y with
        | some s' => greedy (D := D) (x.erase a) (y.erase s')
        | none => false) = true ↔ Feasible D x y
      rw [greedyStep_eq_none_of_not_nonempty hc]
      constructor
      · intro h
        exact Bool.noConfusion h
      · intro h
        exact (hc (candidates_nonempty_of_feasible (D := D) (x := x)
          (y := y) hx h)).elim
  · have hxe : x = ∅ := Finset.not_nonempty_iff_eq_empty.mp hx
    subst x
    simp [feasible_empty]

end TrafficShaping
