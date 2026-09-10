import TrafficShaping.ExecutionCore
import TrafficShaping.Matching

/-!
  Preservation of a feasible base schedule by the operational execution.

  The proof uses a residual matching invariant: after the first `n` slots,
  the arrivals that have not been served (including future arrivals) still
  have an injective deadline-respecting assignment to the one-slots of `y`
  that have not yet been processed.  This is the invariant that rules out a
  deadline switch when the base schedule is feasible.
-/

namespace TrafficShaping

private def residual {H : ℕ} (n : ℕ) (y : Trace H) : Trace H :=
  y \ tracePrefix n y

private def unserved {H : ℕ} (x : Trace H) (served : Trace H) : Trace H :=
  x \ served

private def enqueued {H : ℕ} (x : Trace H) (t : Fin H)
    (queue : List (Fin H)) : List (Fin H) :=
  if t ∈ x then enqueue queue t else queue

private lemma mem_residual_iff {H n : ℕ} {y : Trace H} {a : Fin H} :
    a ∈ residual n y ↔ a ∈ y ∧ n ≤ a.val := by
  unfold residual
  constructor
  · intro h
    have h' := Finset.mem_sdiff.mp h
    refine ⟨h'.1, ?_⟩
    by_contra hlt
    exact h'.2 (mem_prefix.mpr ⟨h'.1, by omega⟩)
  · rintro ⟨hay, han⟩
    refine Finset.mem_sdiff.mpr ⟨hay, ?_⟩
    intro hp
    exact (not_lt_of_ge han) (mem_prefix.mp hp).2

private lemma residual_succ {H n : ℕ} (hn : n < H) (y : Trace H) :
    residual (n + 1) y =
      if (⟨n, hn⟩ : Fin H) ∈ y then
        (residual n y).erase ⟨n, hn⟩
      else residual n y := by
  classical
  ext a
  by_cases hty : (⟨n, hn⟩ : Fin H) ∈ y
  · simp only [hty, ↓reduceIte]
    have hL := mem_residual_iff (n := n + 1) (y := y) (a := a)
    have hR := mem_residual_iff (n := n) (y := y) (a := a)
    rw [hL, Finset.mem_erase, hR]
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
        exact Fin.ext (by simpa [heq] using heq)
      exact ⟨hay, by omega⟩
  · simp only [hty, ↓reduceIte]
    have hL := mem_residual_iff (n := n + 1) (y := y) (a := a)
    have hR := mem_residual_iff (n := n) (y := y) (a := a)
    rw [hL, hR]
    constructor
    · rintro ⟨hay, hn1⟩
      exact ⟨hay, by omega⟩
    · rintro ⟨hay, hnle⟩
      have hneval : a.val ≠ n := by
        intro heq
        apply hty
        have hae : a = (⟨n, hn⟩ : Fin H) := Fin.ext (by simpa [heq])
        exact hae ▸ hay
      exact ⟨hay, by omega⟩

private lemma queue_mem_unserved {H n : ℕ} {x : Trace H} {s : ExecState H}
    (hs : QueueInvariant x n s) {a : Fin H} (ha : a ∈ s.queue) :
    a ∈ unserved x s.served := by
  rcases hs with ⟨_, _, hpart, hdisj, _⟩
  have hap : a ∈ tracePrefix n x := by
    rw [← hpart]
    exact Finset.mem_union_left _ (by simpa using ha)
  have hax : a ∈ x := (mem_prefix.mp hap).1
  have has : a ∉ s.served := by
    intro has
    exact (Finset.disjoint_left.mp hdisj) (by simpa using ha) has
  exact Finset.mem_sdiff.mpr ⟨hax, has⟩

private lemma served_subset_prefix {H n : ℕ} {x : Trace H} {s : ExecState H}
    (hs : QueueInvariant x n s) : s.served ⊆ tracePrefix n x := by
  rcases hs with ⟨_, _, hpart, _, _⟩
  intro a ha
  rw [← hpart]
  exact Finset.mem_union_right _ ha

private lemma enqueued_pairwise {H n : ℕ} (hn : n < H) {x : Trace H}
    {t : Fin H} (ht : t.val = n) {s : ExecState H}
    (hs : QueueInvariant x n s) :
    (enqueued x t s.queue).Pairwise (fun a b => a.val < b.val) := by
  classical
  rcases hs with ⟨_, hpair, _, _, hpast⟩
  by_cases htx : t ∈ x
  · simp only [enqueued, htx, ↓reduceIte]
    rw [show enqueue s.queue t = s.queue ++ [t] by rfl,
      List.pairwise_append]
    refine ⟨hpair, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    have hpa := hpast a ha
    omega
  · simpa [enqueued, htx] using hpair

private lemma enqueued_all_le {H n : ℕ} (hn : n < H) {x : Trace H}
    {t : Fin H} (ht : t.val = n) {s : ExecState H}
    (hs : QueueInvariant x n s) :
    ∀ a ∈ enqueued x t s.queue, a.val ≤ n := by
  classical
  rcases hs with ⟨_, _, _, _, hpast⟩
  by_cases htx : t ∈ x
  · intro a ha
    simp only [enqueued, htx, ↓reduceIte, enqueue, List.mem_append,
      List.mem_singleton] at ha
    rcases ha with ha | rfl
    · have hpa := hpast a ha
      omega
    · exact le_of_eq ht
  · intro a ha
    have ha' : a ∈ s.queue := by simpa [enqueued, htx] using ha
    exact Nat.le_of_lt (hpast a ha')

private lemma unserved_le_mem_enqueued {H n : ℕ} (hn : n < H) {x : Trace H}
    {t : Fin H} (ht : t.val = n) {s : ExecState H}
    (hs : QueueInvariant x n s) {a : Fin H}
    (ha : a ∈ unserved x s.served) (hale : a.val ≤ n) :
    a ∈ enqueued x t s.queue := by
  classical
  rcases hs with ⟨_, _, hpart, _, _⟩
  have hax : a ∈ x := (Finset.mem_sdiff.mp ha).1
  have has : a ∉ s.served := (Finset.mem_sdiff.mp ha).2
  by_cases hal : a.val < n
  · have hap : a ∈ tracePrefix n x := mem_prefix.mpr ⟨hax, hal⟩
    have hor : a ∈ s.queue.toFinset ∨ a ∈ s.served := by
      rw [← hpart] at hap
      exact Finset.mem_union.mp hap
    have haq : a ∈ s.queue.toFinset := by
      rcases hor with hq | hsrv
      · exact hq
      · exact False.elim (has hsrv)
    have haq' : a ∈ s.queue := by simpa using haq
    by_cases htx : t ∈ x
    · simp only [enqueued, htx, ↓reduceIte, enqueue, List.mem_append]
      exact Or.inl haq'
    · simpa [enqueued, htx] using haq'
  · have haeq : a = t := by
      have hav : a.val = n := by omega
      exact Fin.ext (by simpa [ht] using hav)
    subst a
    have htx : t ∈ x := hax
    simp [enqueued, enqueue, htx]

private lemma unserved_future_of_enqueued_empty {H n : ℕ} (hn : n < H)
    {x : Trace H} {t : Fin H} (ht : t.val = n) {s : ExecState H}
    (hs : QueueInvariant x n s)
    (hq : enqueued x t s.queue = []) {a : Fin H}
    (ha : a ∈ unserved x s.served) : n < a.val := by
  by_contra hnot
  have hale : a.val ≤ n := by omega
  have hamem := unserved_le_mem_enqueued hn ht hs ha hale
  rw [hq] at hamem
  simpa using hamem

private lemma head_le_unserved {H n : ℕ} (hn : n < H) {x : Trace H}
    {t a : Fin H} (ht : t.val = n) {s : ExecState H} {q : List (Fin H)}
    (hs : QueueInvariant x n s)
    (hq : enqueued x t s.queue = a :: q)
    (hpair : (enqueued x t s.queue).Pairwise
      (fun u v => u.val < v.val))
    (hle : ∀ u ∈ enqueued x t s.queue, u.val ≤ n) :
    ∀ b ∈ unserved x s.served, a ≤ b := by
  intro b hb
  by_cases hbn : b.val ≤ n
  · have hbq := unserved_le_mem_enqueued hn ht hs hb hbn
    rw [hq] at hbq
    simp only [List.mem_cons] at hbq
    rcases hbq with rfl | hbq
    · exact le_rfl
    · have hpair' : (a :: q).Pairwise (fun u v => u.val < v.val) := by
        simpa [hq] using hpair
      exact Nat.le_of_lt ((List.pairwise_cons.mp hpair').1 b hbq)
  · have han := hle a (by simp [hq])
    have hbn' : n < b.val := by omega
    exact Fin.le_iff_val_le_val.mpr (by omega)

private lemma enqueued_head_mem_unserved {H n : ℕ} (hn : n < H)
    {x : Trace H} {t a : Fin H} (ht : t.val = n) {s : ExecState H}
    (hs : QueueInvariant x n s) {q : List (Fin H)}
    (hq : enqueued x t s.queue = a :: q) :
    a ∈ unserved x s.served := by
  have haq : a ∈ enqueued x t s.queue := by simp [hq]
  by_cases htx : t ∈ x
  · have haq' : a ∈ s.queue ∨ a = t := by
      simpa [enqueued, htx, enqueue] using haq
    rcases haq' with haq | hta
    · exact queue_mem_unserved hs haq
    · subst a
      exact Finset.mem_sdiff.mpr ⟨htx, by
        intro has
        have hpre : t ∈ tracePrefix n x := (served_subset_prefix hs) has
        have hlt := (mem_prefix.mp hpre).2
        omega⟩
  · have haq' : a ∈ s.queue := by simpa [enqueued, htx] using haq
    exact queue_mem_unserved hs haq'

private lemma enqueued_head_is_min {H n : ℕ} (hn : n < H)
    {x : Trace H} {t a : Fin H} (ht : t.val = n) {s : ExecState H}
    (hs : QueueInvariant x n s) {q : List (Fin H)}
    (hq : enqueued x t s.queue = a :: q)
    (hpair : (enqueued x t s.queue).Pairwise
      (fun u v => u.val < v.val))
    (hle : ∀ u ∈ enqueued x t s.queue, u.val ≤ n) :
    ∀ (hu : (unserved x s.served).Nonempty),
      (unserved x s.served).min' hu = a := by
  intro hu
  let u := unserved x s.served
  have ha : a ∈ u := enqueued_head_mem_unserved hn ht hs hq
  apply Fin.le_antisymm
  · exact Finset.min'_le u a ha
  · apply head_le_unserved hn ht hs hq hpair hle
    exact Finset.min'_mem u hu

private lemma residual_zero {H : ℕ} (y : Trace H) : residual 0 y = y := by
  ext a
  simp [residual, tracePrefix]

private lemma unserved_insert_eq {H : ℕ} {x served : Trace H} {a : Fin H}
    (hax : a ∈ x) (has : a ∉ served) :
    unserved x (insert a served) = (unserved x served).erase a := by
  ext b
  constructor
  · intro hb
    have hbx : b ∈ x := (Finset.mem_sdiff.mp hb).1
    have hbn : b ∉ insert a served := (Finset.mem_sdiff.mp hb).2
    have hba : b ≠ a := by
      intro h
      apply hbn
      simp [h]
    have hbs : b ∉ served := by
      intro h
      apply hbn
      simp [h]
    exact Finset.mem_erase.mpr ⟨hba, Finset.mem_sdiff.mpr ⟨hbx, hbs⟩⟩
  · intro hb
    have hbe : b ≠ a := (Finset.mem_erase.mp hb).1
    have hbu : b ∈ unserved x served := (Finset.mem_erase.mp hb).2
    have hbx : b ∈ x := (Finset.mem_sdiff.mp hbu).1
    have hbs : b ∉ served := (Finset.mem_sdiff.mp hbu).2
    exact Finset.mem_sdiff.mpr ⟨hbx, by
      intro hba
      rcases Finset.mem_insert.mp hba with rfl | hserv
      · exact hbe rfl
      · exact hbs hserv⟩

private lemma residual_mem_at {H n : ℕ} (hn : n < H) {y : Trace H}
    {t : Fin H} (ht : t.val = n) (hty : t ∈ y) : t ∈ residual n y := by
  rw [mem_residual_iff]
  exact ⟨hty, by omega⟩

private lemma residual_candidate_min {H D n : ℕ} (hn : n < H)
    {y : Trace H} {a t : Fin H} (ht : t.val = n) (hty : t ∈ y)
    (hale : a.val ≤ n) :
    let c := candidates a (residual n y)
    c.Nonempty ∧ c.min' (by
      dsimp [c]
      exact ⟨t, Finset.mem_filter.mpr
        ⟨residual_mem_at hn ht hty, by omega⟩⟩) = t := by
  let c : Trace H := candidates a (residual n y)
  have hct : t ∈ c := by
    exact Finset.mem_filter.mpr
      ⟨residual_mem_at hn ht hty, by omega⟩
  have hc : c.Nonempty := ⟨t, hct⟩
  have hminle : c.min' hc ≤ t := Finset.min'_le c t hct
  have hlemin : t ≤ c.min' hc := by
    have hmem := Finset.min'_mem c hc
    have hmem' := mem_candidates.mp hmem
    have hres : n ≤ (c.min' hc).val := (mem_residual_iff.mp hmem'.1).2
    exact Fin.le_iff_val_le_val.mpr (by omega)
  dsimp [c]
  refine ⟨hc, ?_⟩
  exact Fin.le_antisymm hminle hlemin

private lemma feasible_erase_output_of_future {H D : ℕ}
    {x y : Trace H} {t : Fin H}
    (hxy : Feasible D x y)
    (hfuture : ∀ a : {b : Fin H // b ∈ x}, t.val < a.val) :
    Feasible D x (y.erase t) := by
  classical
  obtain ⟨f, hfi, hf⟩ := hxy
  refine ⟨f, hfi, ?_⟩
  intro a
  have hne : f a ≠ t := by
    intro heq
    have hlow : a.val ≤ t.val := by simpa [heq] using (hf a).2.1
    have hfuturea := hfuture a
    omega
  exact ⟨Finset.mem_erase.mpr ⟨hne, (hf a).1⟩, (hf a).2.1, (hf a).2.2⟩

private lemma feasible_deadline_at_candidate {H D n : ℕ} {x y : Trace H}
    {a t : Fin H} (ht : t.val = n)
    (hxy : Feasible D x y) (hax : a ∈ x)
    (hc : (candidates a y).Nonempty)
    (hmin : (candidates a y).min' hc = t) :
    t.val ≤ a.val + D := by
  obtain ⟨f, _, hf⟩ := hxy
  let aa : {b : Fin H // b ∈ x} := ⟨a, hax⟩
  have hfa := hf aa
  have hminle : (candidates a y).min' hc ≤ f aa :=
    earliest_available_le hc hfa.1 hfa.2.1
  have hminle' : t.val ≤ (f aa).val := by
    rw [hmin] at hminle
    exact Fin.le_iff_val_le_val.mp hminle
  exact le_trans hminle' hfa.2.2

private lemma feasible_erase_min_output {H D n : ℕ}
    {x y : Trace H} {a t : Fin H}
    (hn : n < H) (ht : t.val = n) (hxy : Feasible D x y)
    (hx : x.Nonempty) (hminx : x.min' hx = a)
    (hax : a ∈ x) (hale : a.val ≤ n) (hty : t ∈ y)
    (hyge : ∀ b ∈ y, n ≤ b.val) :
    Feasible D (x.erase (x.min' hx)) (y.erase t) := by
  have hc : (candidates a y).Nonempty := by
    exact ⟨t, Finset.mem_filter.mpr ⟨hty, by omega⟩⟩
  have hmin : (candidates a y).min' hc = t := by
    apply Fin.le_antisymm
    · exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hty, by omega⟩)
    · have hm := Finset.min'_mem (candidates a y) hc
      have hm' := mem_candidates.mp hm
      have hge := hyge _ hm'.1
      exact Fin.le_iff_val_le_val.mpr (by omega)
  have hdead : t.val ≤ a.val + D :=
    feasible_deadline_at_candidate ht hxy hax hc hmin
  have hc' : (candidates (x.min' hx) y).Nonempty := by
    simpa [hminx] using hc
  have hmin' : (candidates (x.min' hx) y).min' hc' = t := by
    simpa [hminx] using hmin
  have hdead' : (candidates (x.min' hx) y).min' hc' ≤ (x.min' hx).val + D := by
    rw [hmin']
    simpa [hminx] using hdead
  simpa [hmin'] using (feasible_erase_min_iff
    (D := D) (x := x) (y := y) hx hc' hdead').mp hxy

private def Preserved {H : ℕ} (D : ℕ) (x y : Trace H) (n : ℕ)
    (s : ExecState H) : Prop :=
  s.mode = .schedule ∧
    s.output = tracePrefix n y ∧
    Feasible D (unserved x s.served) (residual n y)

private theorem executeState_preserved {H D : ℕ} {x y : Trace H}
    (hxy : Feasible D x y) {n : ℕ} (hn : n ≤ H) :
    Preserved D x y n (executeState D x y n) := by
  induction n with
  | zero =>
      refine ⟨rfl, ?_, ?_⟩
      · simp [executeState, runN, initialState, tracePrefix]
      · simpa [executeState, runN, initialState, unserved, residual] using hxy
  | succ n ih =>
      have hnlt : n < H := by omega
      let s : ExecState H := executeState D x y n
      let t : Fin H := ⟨n, hnlt⟩
      have hnext : executeState D x y (n + 1) = step D x y t s := by
        simp [executeState, runN, hnlt, s, t]
      rw [hnext]
      have hs0 := ih (by omega)
      have hs : Preserved D x y n s := by simpa [s] using hs0
      rcases hs with ⟨hmode, hout, hfeas⟩
      have hqInv : QueueInvariant x n s := by
        simpa [s] using (executeState_queueInvariant (by omega) D x y)
      have ht : t.val = n := rfl
      let q : List (Fin H) := if t ∈ x then enqueue s.queue t else s.queue
      have hqdef : (if t ∈ x then enqueue s.queue t else s.queue) = q := rfl
      by_cases hqempty : q = []
      · have hqempty' : enqueued x t s.queue = [] := by
          simpa [enqueued, q] using hqempty
        by_cases hty : t ∈ y
        · have hresmem : t ∈ residual n y := residual_mem_at hnlt ht hty
          have hfuture : ∀ a : {b : Fin H // b ∈ unserved x s.served},
              t.val < a.val := by
            intro a
            exact unserved_future_of_enqueued_empty hnlt ht hqInv hqempty'
              a.property
          have hnew : Feasible D (unserved x s.served)
              ((residual n y).erase t) :=
            feasible_erase_output_of_future hfeas hfuture
          have hresnext : residual (n + 1) y = (residual n y).erase t := by
            rw [residual_succ hnlt y]
            simp [hty, t]
          have htarget : Preserved D x y (n + 1)
              ({ queue := [], served := s.served, output := insert t s.output,
                  mode := (.schedule : ExecMode H) } : ExecState H) := by
            refine ⟨rfl, ?_, ?_⟩
            · rw [hout, tracePrefix_succ hnlt y]
              simp [t, hty]
            · rw [hresnext]
              exact hnew
          simpa [Preserved, step, t,
            hmode, hqdef, hqempty, hty] using htarget
        · have htarget : Preserved D x y (n + 1)
              ({ queue := [], served := s.served, output := s.output,
                  mode := (.schedule : ExecMode H) } : ExecState H) := by
            refine ⟨rfl, ?_, ?_⟩
            · rw [hout, tracePrefix_succ hnlt y]
              simp [t, hty]
            · have hresnext : residual (n + 1) y = residual n y := by
                rw [residual_succ hnlt y]
                simp [hty, t]
              rw [hresnext]
              exact hfeas
          simpa [Preserved, step, t,
            hmode, hqdef, hqempty, hty] using htarget
      · obtain ⟨a, qtail, hqeq⟩ := List.exists_cons_of_ne_nil hqempty
        have hqdef' : (if t ∈ x then enqueue s.queue t else s.queue) = a :: qtail := by
          simpa [q] using hqeq
        have hpair : (enqueued x t s.queue).Pairwise
            (fun u v => u.val < v.val) := enqueued_pairwise hnlt ht hqInv
        have hle : ∀ u ∈ enqueued x t s.queue, u.val ≤ n :=
          enqueued_all_le hnlt ht hqInv
        have ha : a ∈ unserved x s.served :=
          enqueued_head_mem_unserved hnlt ht hqInv hqdef'
        have hu : (unserved x s.served).Nonempty := ⟨a, ha⟩
        have hamin : (unserved x s.served).min' hu = a :=
          enqueued_head_is_min hnlt ht hqInv hqdef' hpair hle hu
        have hax : a ∈ x := (Finset.mem_sdiff.mp ha).1
        have hasa : a ∉ s.served := (Finset.mem_sdiff.mp ha).2
        have hale : a.val ≤ n := by
          have haq : a ∈ enqueued x t s.queue := by
            unfold enqueued
            rw [hqdef']
            simp
          exact hle a haq
        by_cases hty : t ∈ y
        · have hresmem : t ∈ residual n y := residual_mem_at hnlt ht hty
          have hresge : ∀ b ∈ residual n y, n ≤ b.val := by
            intro b hb
            exact (mem_residual_iff.mp hb).2
          have hnew : Feasible D
              ((unserved x s.served).erase a) ((residual n y).erase t) := by
            simpa [hamin] using
              (feasible_erase_min_output (x := unserved x s.served)
                (y := residual n y) (a := a) (t := t)
                hnlt ht hfeas hu hamin ha hale hresmem hresge)
          have hunserved : unserved x (insert a s.served) =
              (unserved x s.served).erase a :=
            unserved_insert_eq hax hasa
          have hresnext : residual (n + 1) y = (residual n y).erase t := by
            rw [residual_succ hnlt y]
            simp [hty, t]
          have hnew' : Feasible D (unserved x (insert a s.served))
              (residual (n + 1) y) := by
            simpa [hunserved, hresnext] using hnew
          have htarget : Preserved D x y (n + 1)
              ({ queue := qtail, served := insert a s.served,
                  output := insert t s.output,
                  mode := (.schedule : ExecMode H) } : ExecState H) := by
            refine ⟨rfl, ?_, hnew'⟩
            rw [hout, tracePrefix_succ hnlt y]
            simp [t, hty]
          simpa [Preserved, step, t,
            hmode, hqdef', hqeq, hty] using htarget
        · by_cases hdeadline : deadline H D a = t.val
          · have hfalse : False := by
              obtain ⟨f, _, hf⟩ := hfeas
              let aa : {b : Fin H // b ∈ unserved x s.served} := ⟨a, ha⟩
              have hfa := hf aa
              have hres := mem_residual_iff.mp hfa.1
              have hfa_dead : (f aa).val ≤ a.val + D := by
                simpa [aa] using hfa.2.2
              have hbt' : (f aa).val ≤ deadline H D a := by
                have hd := hdeadline
                unfold deadline at hd
                unfold deadline
                by_cases hclip : a.val + D ≤ H - 1
                · rw [Nat.min_eq_left hclip] at hd ⊢
                  omega
                · rw [Nat.min_eq_right (by omega)] at hd ⊢
                  omega
              have hbt : (f aa).val ≤ t.val := by
                calc
                  (f aa).val ≤ deadline H D a := hbt'
                  _ = t.val := hdeadline
              have hbn : n ≤ (f aa).val := hres.2
              have hbeq : (f aa).val = n := by omega
              have hfeq : f aa = t := Fin.ext (by simpa [ht] using hbeq)
              have hty' : t ∈ y := by simpa [hfeq] using hres.1
              exact hty hty'
            exact hfalse.elim
          · have htarget : Preserved D x y (n + 1)
                ({ queue := a :: qtail, served := s.served, output := s.output,
                    mode := (.schedule : ExecMode H) } : ExecState H) := by
              have hresnext : residual (n + 1) y = residual n y := by
                rw [residual_succ hnlt y]
                simp [hty, t]
              refine ⟨rfl, ?_, ?_⟩
              · rw [hout, tracePrefix_succ hnlt y]
                simp [t, hty]
              · rw [hresnext]
                exact hfeas
            simpa [Preserved, step, t,
              hmode, hqdef', hqeq, hty, hdeadline] using htarget

theorem execute_eq_of_feasible {H D : ℕ} {x y : Trace H}
    (hxy : Feasible D x y) : execute D x y = y := by
  have hpres := executeState_preserved (D := D) (x := x) (y := y) hxy
    (n := H) (by rfl)
  rcases hpres with ⟨hmode, hout, _⟩
  simpa [execute, executeState, prefix_horizon] using hout

end TrafficShaping
