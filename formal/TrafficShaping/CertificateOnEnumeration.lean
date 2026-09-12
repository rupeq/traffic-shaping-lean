import TrafficShaping.CertificateHelpers

/-!
An explicit enumeration of causal schedules.

`onScheduleEnum` starts with all `B`-subsets of the horizon and then filters
for the terminal reserve. This file enumerates the `B - m` free slots first
and adjoins the terminal reserve, so the executable enumeration has exactly
`(H - m).choose (B - m)` candidates.
-/

namespace TrafficShaping

def onPrefixSlots (H m : ℕ) : Finset (Fin H) :=
  (Finset.univ : Finset (Fin (H - m))).map (Fin.castLEEmb (Nat.sub_le _ _))

lemma onPrefixSlots_mem_lt {H m : ℕ} {a : Fin H}
    (ha : a ∈ onPrefixSlots H m) : a.val < H - m := by
  rcases Finset.mem_map.mp ha with ⟨i, hi, rfl⟩
  exact i.isLt

lemma cardEnum_mem_subset {α : Type*} [DecidableEq α]
    (k : ℕ) (u : Finset α) {s : {s : Finset α // s.card = k}}
    (hs : s ∈ cardEnum k u) : s.1 ⊆ u := by
  unfold cardEnum at hs
  rcases Finset.mem_map.mp hs with ⟨t, ht, hts⟩
  have hval := congrArg
    (fun z : {s : Finset α // s.card = k} => z.1) hts
  change t.1 = s.1 at hval
  rw [← hval]
  exact (Finset.mem_powersetCard.mp t.2).1

private def optimizedOnScheduleEnumCore (H m B : ℕ)
    (hm : m ≤ H) (hmb : m ≤ B) : Finset (OnSchedule H m B) :=
  (cardEnum (B - m) (onPrefixSlots H m)).attach.map
    { toFun := fun t =>
        ⟨t.1.1 ∪ terminal H m, by
          have hdisj : Disjoint t.1.1 (terminal H m) := by
            apply Finset.disjoint_left.mpr
            intro a ha hta
            have hsubset : t.1.1 ⊆ onPrefixSlots H m :=
              cardEnum_mem_subset (B - m) (onPrefixSlots H m) t.2
            have ha' : a.val < H - m := onPrefixSlots_mem_lt (hsubset ha)
            have hta' : H - m ≤ a.val := mem_terminal.mp hta
            omega
          rw [Finset.card_union_of_disjoint hdisj]
          rw [t.1.2, terminal_card hm]
          omega,
          Finset.subset_union_right⟩
      inj' := by
        intro a b hab
        have hdisj_a : Disjoint a.1.1 (terminal H m) := by
          apply Finset.disjoint_left.mpr
          intro z hz hzt
          have hz' : z.val < H - m := onPrefixSlots_mem_lt
            ((cardEnum_mem_subset (B - m) (onPrefixSlots H m) a.2) hz)
          have hzt' : H - m ≤ z.val := mem_terminal.mp hzt
          omega
        have hdisj_b : Disjoint b.1.1 (terminal H m) := by
          apply Finset.disjoint_left.mpr
          intro z hz hzt
          have hz' : z.val < H - m := onPrefixSlots_mem_lt
            ((cardEnum_mem_subset (B - m) (onPrefixSlots H m) b.2) hz)
          have hzt' : H - m ≤ z.val := mem_terminal.mp hzt
          omega
        have hab' := congrArg (fun z : OnSchedule H m B => z.1) hab
        dsimp at hab'
        change a.1.1 ∪ terminal H m = b.1.1 ∪ terminal H m at hab'
        have hfree : a.1.1 = b.1.1 := by
          apply Finset.ext
          intro z
          constructor
          · intro hz
            have hzu : z ∈ a.1.1 ∪ terminal H m :=
              Finset.mem_union_left _ hz
            rw [hab'] at hzu
            rcases Finset.mem_union.mp hzu with hzb | hzt
            · exact hzb
            · exact ((Finset.disjoint_left.mp hdisj_a hz) hzt).elim
          · intro hz
            have hzu : z ∈ b.1.1 ∪ terminal H m :=
              Finset.mem_union_left _ hz
            rw [← hab'] at hzu
            rcases Finset.mem_union.mp hzu with hza | hzt
            · exact hza
            · exact ((Finset.disjoint_left.mp hdisj_b hz) hzt).elim
        apply Subtype.ext
        exact Subtype.ext hfree }

/-- Enumerate causal schedules by choosing the nonterminal slots first. -/
def optimizedOnScheduleEnum (H m B : ℕ)
    (hm : m ≤ H) (hmb : m ≤ B) : Finset (OnSchedule H m B) :=
  optimizedOnScheduleEnumCore H m B hm hmb

theorem optimizedOnScheduleEnum_eq_univ {H m B : ℕ}
    (hm : m ≤ H) (hmb : m ≤ B) :
    optimizedOnScheduleEnum H m B hm hmb =
      (Finset.univ : Finset (OnSchedule H m B)) := by
  apply Finset.eq_univ_of_card
  unfold optimizedOnScheduleEnum
  unfold optimizedOnScheduleEnumCore
  simp only [Finset.card_map, Finset.card_attach]
  rw [card_cardEnum]
  simp [onPrefixSlots, onSchedule_card hm hmb]

end TrafficShaping
