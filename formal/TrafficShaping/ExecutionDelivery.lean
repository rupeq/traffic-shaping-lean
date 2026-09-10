import TrafficShaping.ExecutionCore

/-!
  Final delivery for the concrete queue execution.

  The tail argument tracks the number of queued arrivals together with the
  arrivals that have not reached the processed prefix.  Once the terminal
  reserve begins, every processed slot is a service slot, so this pending
  count fits in the remaining horizon and is zero at the end.
-/

namespace TrafficShaping

private def future {H : ℕ} (n : ℕ) (x : Trace H) : Trace H :=
  x \ tracePrefix n x

private lemma mem_future_iff {H n : ℕ} {x : Trace H} {a : Fin H} :
    a ∈ future n x ↔ a ∈ x ∧ n ≤ a.val := by
  unfold future
  constructor
  · intro h
    have h' := Finset.mem_sdiff.mp h
    refine ⟨h'.1, ?_⟩
    by_contra hlt
    exact h'.2 (mem_prefix.mpr ⟨h'.1, by omega⟩)
  · rintro ⟨hax, han⟩
    refine Finset.mem_sdiff.mpr ⟨hax, ?_⟩
    intro hp
    exact (not_lt_of_ge han) (mem_prefix.mp hp).2

private lemma future_succ {H n : ℕ} (hn : n < H) (x : Trace H) :
    future (n + 1) x =
      if (⟨n, hn⟩ : Fin H) ∈ x then
        (future n x).erase ⟨n, hn⟩
      else future n x := by
  classical
  ext a
  by_cases htx : (⟨n, hn⟩ : Fin H) ∈ x
  · simp only [htx, ↓reduceIte, Finset.mem_erase]
    rw [mem_future_iff, mem_future_iff]
    constructor
    · rintro ⟨hay, hn1⟩
      have hne : a ≠ (⟨n, hn⟩ : Fin H) := by
        intro heq
        subst a
        simp at hn1
      refine ⟨hne, hay, by omega⟩
    · rintro ⟨hne, hay, hnle⟩
      have hneval : a.val ≠ n := by
        intro heq
        apply hne
        exact Fin.ext (by simpa using heq)
      exact ⟨hay, by omega⟩
  · simp only [htx, ↓reduceIte]
    rw [mem_future_iff, mem_future_iff]
    constructor
    · rintro ⟨hay, hn1⟩
      exact ⟨hay, by omega⟩
    · rintro ⟨hay, hnle⟩
      have hneval : a.val ≠ n := by
        intro heq
        apply htx
        have hae : a = (⟨n, hn⟩ : Fin H) := Fin.ext (by simpa using heq)
        exact hae ▸ hay
      exact ⟨hay, by omega⟩

private lemma future_card_le {H n : ℕ} (hn : n ≤ H) (x : Trace H) :
    (future n x).card ≤ H - n := by
  classical
  let f : {a : Fin H // a ∈ future n x} → Fin (H - n) := fun a =>
    ⟨a.1.1 - n, by
      have ha := (mem_future_iff.mp a.2)
      have hge : n ≤ a.1.1 := ha.2
      omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Fin.ext
    have hab' := congrArg Fin.val hab
    dsimp [f] at hab'
    have hga : n ≤ a.1.1 := (mem_future_iff.mp a.2).2
    have hgb : n ≤ b.1.1 := (mem_future_iff.mp b.2).2
    omega
  have hcard := Fintype.card_le_of_injective f hf
  have hcard' : (future n x).card ≤ Fintype.card (Fin (H - n)) := by
    simpa only [Fintype.card_coe] using hcard
  simpa only [Fintype.card_fin] using hcard'

private lemma queue_subset_prefix {H n : ℕ} {x : Trace H} {s : ExecState H}
    (hs : QueueInvariant x n s) : s.queue.toFinset ⊆ tracePrefix n x := by
  rcases hs with ⟨_, _, hpart, _, _⟩
  rw [← hpart]
  exact Finset.subset_union_left

private lemma pending_at_prefix {H m : ℕ}
    (hm : m ≤ H) {x : Trace H} (hx : x.card ≤ m) (n : ℕ)
    (s : ExecState H) (hs : QueueInvariant x n s)
    (hn : H - m = n) :
    s.queue.length + (future n x).card ≤ H - n := by
  classical
  have hqnodup := hs.1
  have hqcard : s.queue.length = s.queue.toFinset.card :=
    (List.toFinset_card_of_nodup hqnodup).symm
  have hqsub : s.queue.toFinset ⊆ tracePrefix n x := queue_subset_prefix hs
  have hdisj : Disjoint s.queue.toFinset (future n x) := by
    refine Finset.disjoint_left.2 ?_
    intro a haq haf
    exact (not_lt_of_ge (mem_future_iff.mp haf).2) (mem_prefix.mp (hqsub haq)).2
  have hunion : s.queue.toFinset ∪ (future n x) ⊆ x := by
    intro a ha
    rcases Finset.mem_union.mp ha with haq | haf
    · exact (mem_prefix.mp (hqsub haq)).1
    · exact (mem_future_iff.mp haf).1
  have hcard_union :
      s.queue.toFinset.card + (future n x).card ≤ x.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hunion
  rw [hqcard]
  omega

private lemma terminal_mem_of_ge {H m n : ℕ} (hm : m ≤ H)
    (hn : H - m ≤ n) (hnlt : n < H) :
    (⟨n, hnlt⟩ : Fin H) ∈ terminal H m := by
  simp only [mem_terminal]
  omega

private lemma step_queue_tail {H m D : ℕ} (hm : m ≤ H)
    {x y : Trace H} (hterminal : terminal H m ⊆ y)
    {n : ℕ} (hn : H - m ≤ n) (hnlt : n < H) (s : ExecState H) :
    (step D x y ⟨n, hnlt⟩ s).queue =
      (if (⟨n, hnlt⟩ : Fin H) ∈ x then
        enqueue s.queue ⟨n, hnlt⟩ else s.queue).tail := by
  classical
  let t : Fin H := ⟨n, hnlt⟩
  have ht : t ∈ y := hterminal (terminal_mem_of_ge hm hn hnlt)
  let q : List (Fin H) := if t ∈ x then enqueue s.queue t else s.queue
  have hqdef : (if t ∈ x then enqueue s.queue t else s.queue) = q := rfl
  cases hmde : s.mode with
  | schedule =>
      by_cases hq : q = []
      · simp [step, t, hmde, hqdef, hq, ht]
      · obtain ⟨a, qtail, hq'⟩ := List.exists_cons_of_ne_nil hq
        simp [step, t, hmde, hqdef, hq, hq', ht]
  | service serviceAt =>
      by_cases hq : q = []
      · simp [step, t, hmde, hqdef, hq, ht]
      · obtain ⟨a, qtail, hq'⟩ := List.exists_cons_of_ne_nil hq
        simp [step, t, hmde, hqdef, hq, hq', ht]

private theorem pending_tail {H m D : ℕ} (hm : m ≤ H)
    {x y : Trace H} (hx : x.card ≤ m) (hterminal : terminal H m ⊆ y)
    {n : ℕ} (hnlo : H - m ≤ n) (hnhi : n ≤ H) :
    (executeState D x y n).queue.length + (future n x).card ≤ H - n := by
  have htail : ∀ k, H - m ≤ k → k ≤ H →
      (executeState D x y k).queue.length + (future k x).card ≤ H - k := by
    intro k hklo hkhi
    induction k, hklo using Nat.le_induction with
    | base =>
        exact pending_at_prefix hm hx (H - m) (executeState D x y (H - m))
          (executeState_queueInvariant (by omega) D x y) rfl
    | succ k hklo ih =>
        have hklt : k < H := by omega
        let t : Fin H := ⟨k, hklt⟩
        let s : ExecState H := executeState D x y k
        have hprev : s.queue.length + (future k x).card ≤ H - k := by
          simpa [s] using ih (by omega)
        have hqstep := step_queue_tail (D := D) hm (x := x) (y := y)
          hterminal hklo hklt s
        have hstate :
            (executeState D x y (k + 1)).queue =
              (step D x y ⟨k, hklt⟩ s).queue := by
          simp [executeState, runN, hklt, s]
        rw [hstate, hqstep]
        change (if t ∈ x then enqueue s.queue t else s.queue).tail.length +
          (future (k + 1) x).card ≤ H - (k + 1)
        by_cases htx : t ∈ x
        · have hq_len :
              (enqueue s.queue t).tail.length = s.queue.length := by
            simp [enqueue, List.length_tail]
          have htfut : t ∈ future k x :=
            mem_future_iff.mpr ⟨htx, le_rfl⟩
          have hfuture : future (k + 1) x = (future k x).erase t := by
            simpa [t, htx] using future_succ hklt x
          have hcardpos : 0 < (future k x).card :=
            Finset.card_pos.mpr ⟨t, htfut⟩
          have hsub : H - k = H - (k + 1) + 1 := by omega
          simp only [htx, if_true] at ⊢
          rw [hfuture, Finset.card_erase_of_mem htfut]
          rw [hq_len]
          omega
        · by_cases hqempty : s.queue = []
          · have hfuture_le : (future (k + 1) x).card ≤ H - (k + 1) := by
              exact future_card_le (by omega) x
            simpa [htx, hqempty] using hfuture_le
          have hfuture : future (k + 1) x = future k x := by
            simpa [t, htx] using future_succ hklt x
          have hqlenpos : 0 < s.queue.length :=
            List.length_pos_of_ne_nil hqempty
          have hsub : H - k = H - (k + 1) + 1 := by omega
          simp only [htx, if_false] at ⊢
          rw [hfuture, List.length_tail]
          omega
  exact htail n hnlo hnhi

theorem executeState_queue_empty {H m D : ℕ} (hm : m ≤ H)
    {x y : Trace H} (hx : x.card ≤ m) (hterminal : terminal H m ⊆ y) :
    (executeState D x y H).queue = [] := by
  have hp := pending_tail (D := D) hm hx hterminal (n := H) (by omega) le_rfl
  have hlen : (executeState D x y H).queue.length = 0 := by
    omega
  exact List.eq_nil_of_length_eq_zero hlen

theorem executeState_served_eq {H m D : ℕ} (hm : m ≤ H)
    {x y : Trace H} (hx : x.card ≤ m) (hterminal : terminal H m ⊆ y) :
    (executeState D x y H).served = x := by
  have hqueue := executeState_queue_empty (D := D) hm hx hterminal
  have hq := executeState_queueInvariant (H := H) (n := H) le_rfl D x y
  have hpartition :
      (executeState D x y H).queue.toFinset ∪ (executeState D x y H).served =
        tracePrefix H x := hq.2.2.1
  rw [hqueue] at hpartition
  simpa using hpartition

end TrafficShaping
