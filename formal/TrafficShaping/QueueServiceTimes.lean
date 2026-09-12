import TrafficShaping.QueueCorollaries

/-!
  The bridge from the arithmetic FIFO recurrence to the operational queue.

  `QueueCorollaries` proves the recurrence and its bounds.  This file exposes
  the exact per-slot work-conserving transition used by `executeState`, and a
  suffix API whose remaining-arrival list is an actual partition of the
  unserved input.  The API is deliberately stated in terms of `ExecState`, so
  a service-time claim cannot be discharged by defining a second, unrelated
  queue machine.
-/

namespace TrafficShaping

def WorkConservingAt {H : ℕ} (x y : Trace H) (t : Fin H)
    (s : ExecState H) : Prop :=
  (∃ serviceAt, s.mode = .service serviceAt) ∨
    (s.mode = .schedule ∧ t ∈ y)

def WorkConservingSuffix {H : ℕ} (D : ℕ) (x y : Trace H) (start : ℕ) : Prop :=
  ∀ {n : ℕ} (hnlo : start ≤ n) (hnhi : n < H),
    WorkConservingAt x y ⟨n, hnhi⟩ (executeState D x y n)

theorem workConserving_step_shape {H D : ℕ} {x y : Trace H}
    {t : Fin H} {s : ExecState H}
    (hwork : WorkConservingAt x y t s) :
    let q := if t ∈ x then enqueue s.queue t else s.queue
    (step D x y t s).queue = q.tail ∧
      (step D x y t s).served =
        match q with
        | [] => s.served
        | a :: q' => insert a s.served := by
  classical
  let q := if t ∈ x then enqueue s.queue t else s.queue
  rcases hwork with hservice | hsched
  · rcases hservice with ⟨serviceAt, hmode⟩
    cases hq : q with
    | nil => simp [step, q, hq, hmode]
    | cons a q' => simp [step, q, hq, hmode]
  · rcases hsched with ⟨hmode, hty⟩
    cases hq : q with
    | nil => simp [step, q, hq, hmode, hty]
    | cons a q' => simp [step, q, hq, hmode, hty]

theorem executeState_workConserving_step {H D : ℕ} {x y : Trace H}
    {n : ℕ} (hn : n < H)
    (hwork : WorkConservingAt x y ⟨n, hn⟩ (executeState D x y n)) :
    let s := executeState D x y n
    let q := if (⟨n, hn⟩ : Fin H) ∈ x then enqueue s.queue ⟨n, hn⟩ else s.queue
    (executeState D x y (n + 1)).queue = q.tail ∧
      (executeState D x y (n + 1)).served =
        match q with
        | [] => s.served
        | a :: q' => insert a s.served := by
  let s := executeState D x y n
  let q := if (⟨n, hn⟩ : Fin H) ∈ x then enqueue s.queue ⟨n, hn⟩ else s.queue
  have hshape := workConserving_step_shape (D := D) (x := x) (y := y)
    (t := ⟨n, hn⟩) (s := s) hwork
  simpa [executeState_succ_step hn, s, q] using hshape

/- The operational suffix condition used by later service-event lemmas.  It
  permits either explicit service mode, or schedule mode at a slot that is
  known to be a one-slot.  Both branches execute the same enqueue-then-dequeue
  transition above. -/
theorem workConservingSuffix_step {H D : ℕ} {x y : Trace H} {start n : ℕ}
    (hwork : WorkConservingSuffix D x y start)
    (hnlo : start ≤ n) (hnhi : n < H) :
    WorkConservingAt x y ⟨n, hnhi⟩ (executeState D x y n) :=
  hwork hnlo hnhi

/- The queue seen by the transition at slot `n`.  This is the queue after
   the current input has been appended and before the work-conserving
   dequeue.  Keeping this definition separate makes the head hypotheses
   below refer to the actual operational queue rather than to a second FIFO
   machine. -/
def suffixQueueAt {H D : ℕ} (x y : Trace H) (t : Fin H) :
    List (Fin H) :=
  if t ∈ x then enqueue (executeState D x y t.val).queue t
  else (executeState D x y t.val).queue

/- `FifoHeadSchedule` is the operational part of the FIFO suffix API.  The
   list `arrivals` is the ordered list of packets that remain at `start`; for
   its `i`-th packet, the corresponding arithmetic service slot is the
   `i`-th element of `fifoServices`.  The predicate says that the actual
   enqueued queue has this packet at its head at that slot, and that it is not
   at the head earlier.  The event theorem below turns these head facts into
   first inclusion in the actual `served` trace.  A terminal all-ones suffix
   supplies the same head facts through `WorkConservingAt`; a service-mode
   suffix supplies them directly. -/
def FifoHeadSchedule {H D : ℕ} (x y : Trace H) (start : ℕ)
    (arrivals : List (Fin H)) : Prop :=
  ∀ {i : ℕ} (hi : i < arrivals.length),
    let services := fifoServices start (arrivals.map Fin.val)
    let si := services[i]'(by simpa [services, fifoServices_length] using hi)
    let a := arrivals[i]'hi
    ∃ hsi : si < H,
      (suffixQueueAt (D := D) x y ⟨si, hsi⟩).head? = some a ∧
      ∀ {n : ℕ} (hnlo : start ≤ n) (hnlt : n < si) (hnhi : n < H),
        (suffixQueueAt (D := D) x y ⟨n, hnhi⟩).head? ≠ some a

/- A suffix witness records the concrete remaining set as well as the
   ordered head schedule.  The set equality is what identifies `arrivals`
   with the unserved input of `executeState`; in particular it provides the
   initial non-membership needed for a first-service claim. -/
structure FifoSuffixWitness {H D : ℕ} (x y : Trace H) (start : ℕ)
    (arrivals : List (Fin H)) : Prop where
  sorted : arrivals.Pairwise (fun a b : Fin H => a.val < b.val)
  remaining : arrivals.toFinset = x \ (executeState D x y start).served
  queue_at_start :
    (executeState D x y start).queue =
      arrivals.filter (fun a => a.val < start)
  heads : FifoHeadSchedule (D := D) x y start arrivals

/- This is the non-circular input for the constructive suffix theorem below.
   It contains only the actual unserved set, its sorted list representation,
   the queue at the beginning of the suffix, and a horizon bound for the
   arithmetic recurrence.  It does not mention service events or head
   positions at `fifoServices` slots. -/
structure FifoSuffixBase {H D : ℕ} (x y : Trace H) (start : ℕ)
    (arrivals : List (Fin H)) : Prop where
  sorted : arrivals.Pairwise (fun a b : Fin H => a.val < b.val)
  remaining : arrivals.toFinset = x \ (executeState D x y start).served
  queue_at_start :
    (executeState D x y start).queue =
      arrivals.filter (fun a => a.val < start)
  horizon : ∀ {i : ℕ} (hi : i < arrivals.length),
    (fifoServices start (arrivals.map Fin.val))[i]'
      (by simpa [fifoServices_length] using hi) < H

private theorem sorted_list_eq_of_toFinset_eq {H : ℕ}
    {p q : List (Fin H)}
    (hp : p.Pairwise (fun a b : Fin H => a.val < b.val))
    (hq : q.Pairwise (fun a b : Fin H => a.val < b.val))
    (hset : p.toFinset = q.toFinset) : p = q := by
  induction p generalizing q with
  | nil =>
      cases q with
      | nil => rfl
      | cons b qs =>
          have hb : b ∈ ([] : List (Fin H)).toFinset := by
            rw [hset]
            simp
          simp at hb
  | cons a ps ih =>
      cases q with
      | nil =>
          have ha : a ∈ (a :: ps).toFinset := by simp
          rw [hset] at ha
          simp at ha
      | cons b qs =>
          have habmem : a ∈ b :: qs := by
            have ha : a ∈ (a :: ps).toFinset := by simp
            rw [hset] at ha
            simpa using ha
          have hba_mem : b ∈ a :: ps := by
            have hb : b ∈ (b :: qs).toFinset := by simp
            rw [← hset] at hb
            simpa using hb
          have hab_le : a.val ≤ b.val := by
            have hba_cases : b = a ∨ b ∈ ps := by simpa using hba_mem
            rcases hba_cases with hba | hmem
            · exact Nat.le_of_eq (congrArg Fin.val hba.symm)
            · exact Nat.le_of_lt ((List.pairwise_cons.mp hp).1 _ hmem)
          have hba_le : b.val ≤ a.val := by
            have hab_cases : a = b ∨ a ∈ qs := by simpa using habmem
            rcases hab_cases with hab | hmem
            · exact Nat.le_of_eq (congrArg Fin.val hab.symm)
            · exact Nat.le_of_lt ((List.pairwise_cons.mp hq).1 _ hmem)
          have hab : a = b := Fin.ext (by omega)
          cases hab
          have htailset : ps.toFinset = qs.toFinset := by
            ext c
            have hcons : c ∈ (a :: ps).toFinset ↔ c ∈ (a :: qs).toFinset := by
              rw [hset]
            simp only [List.mem_toFinset, List.mem_cons] at hcons ⊢
            by_cases hca : c = a
            · have haps : a ∉ ps := by
                intro h
                exact (Nat.lt_irrefl a.val)
                  ((List.pairwise_cons.mp hp).1 a h)
              have haq : a ∉ qs := by
                intro h
                exact (Nat.lt_irrefl a.val)
                  ((List.pairwise_cons.mp hq).1 a h)
              simp [hca, haps, haq]
            · simpa [hca] using hcons
          have hpt : ps.Pairwise (fun u v : Fin H => u.val < v.val) :=
            (List.pairwise_cons.mp hp).2
          have hqt : qs.Pairwise (fun u v : Fin H => u.val < v.val) :=
            (List.pairwise_cons.mp hq).2
          exact congrArg (List.cons a) (ih hpt hqt htailset)

private theorem served_subset_prefix_of_queueInvariant {H n : ℕ}
    {x : Trace H} {s : ExecState H}
    (hs : QueueInvariant x n s) : s.served ⊆ tracePrefix n x := by
  intro a ha
  rw [← hs.2.2.1]
  exact Finset.mem_union_right _ ha

private theorem step_empty_queue {H D : ℕ} {x y : Trace H}
    {t : Fin H} {s : ExecState H}
    (hq : (if t ∈ x then enqueue s.queue t else s.queue) = []) :
    (step D x y t s).queue = [] ∧
      (step D x y t s).served = s.served := by
  classical
  cases hm : s.mode with
  | service serviceAt =>
      simp [step, hm, hq]
  | schedule =>
      by_cases hty : t ∈ y <;> simp [step, hm, hq, hty]

private theorem fifo_empty_gap {H D : ℕ} {x y : Trace H} {start : ℕ}
    {a : Fin H} {as : List (Fin H)}
    (hbase : FifoSuffixBase (D := D) x y start (a :: as))
    (hfirst : start ≤ a.val) :
    ∀ {n : ℕ}, start ≤ n → n ≤ a.val →
      (executeState D x y n).queue = [] ∧
        (executeState D x y n).served =
          (executeState D x y start).served := by
  have hfilter : (a :: as).filter (fun b => b.val < start) = [] := by
    rw [List.filter_eq_nil_iff]
    intro b hb
    simp only [Bool.not_eq_true, decide_eq_true_eq]
    by_cases hba : b = a
    · subst b
      omega
    · have hb_tail : b ∈ as := by
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact False.elim (hba rfl)
        · exact hb
      have hab := (List.pairwise_cons.mp hbase.sorted).1 b hb_tail
      omega
  have hqstart : (executeState D x y start).queue = [] := by
    rw [hbase.queue_at_start]
    exact hfilter
  intro n hnlo hnhi
  have hno : ∀ k : ℕ, start + k ≤ n →
      (executeState D x y (start + k)).queue = [] ∧
        (executeState D x y (start + k)).served =
          (executeState D x y start).served := by
    intro k
    induction k with
    | zero =>
        intro hk
        constructor
        · simpa using hqstart
        · simp
    | succ k ih =>
        intro hk
        have hprev := ih (by omega)
        have hprevH : start + k < H := by omega
        let t : Fin H := ⟨start + k, hprevH⟩
        have htx : t ∉ x := by
          intro htx
          have hqInv := executeState_queueInvariant
            (H := H) (n := start + k) (by omega) D x y
          have hservedStart : t ∉
              (executeState D x y start).served := by
            intro hts
            have hprefix := served_subset_prefix_of_queueInvariant
              (executeState_queueInvariant (H := H) (n := start) (by omega) D x y)
              hts
            have hpast := (mem_prefix.mp hprefix).2
            have hpast' : start + k < start := by simpa [t] using hpast
            omega
          have htA : t ∈ (a :: as).toFinset := by
            rw [hbase.remaining]
            apply Finset.mem_sdiff.mpr
            refine ⟨htx, ?_⟩
            simpa [hprev.2] using hservedStart
          have htA' : t ∈ a :: as := by simpa using htA
          simp only [List.mem_cons] at htA'
          rcases htA' with hta | htas
          · have hval : t.val = a.val := by simpa [← hta]
            dsimp [t] at hval
            omega
          · have hab := (List.pairwise_cons.mp hbase.sorted).1 t htas
            dsimp [t] at hab
            omega
        have hqempty :
            (if t ∈ x then enqueue (executeState D x y (start + k)).queue t
             else (executeState D x y (start + k)).queue) = [] := by
          simp [htx, hprev.1]
        have hstep := step_empty_queue (D := D) (x := x) (y := y)
          (t := t) (s := executeState D x y (start + k)) hqempty
        have hstate : executeState D x y (start + k + 1) =
            step D x y t (executeState D x y (start + k)) := by
          simpa [t] using executeState_succ_step hprevH
        have hrewrite : start + (k + 1) = start + k + 1 := by omega
        rw [hrewrite, hstate]
        refine ⟨hstep.1, ?_⟩
        rw [hstep.2]
        exact hprev.2
  obtain ⟨k, hk⟩ : ∃ k, n = start + k := by
    exact ⟨n - start, by omega⟩
  simpa [hk] using hno k (by omega)

private theorem fifo_tail_base {H D : ℕ} {x y : Trace H} {start s : ℕ}
    {a : Fin H} {as : List (Fin H)}
    (hbase : FifoSuffixBase (D := D) x y start (a :: as))
    (hsdef : s = max a.val start)
    (hslt : s < H)
    (hserved_s : (executeState D x y s).served =
      (executeState D x y start).served)
    (hserved_next : (executeState D x y (s + 1)).served =
      insert a (executeState D x y s).served) :
    FifoSuffixBase (D := D) x y (s + 1) as := by
  classical
  have haa : a ∉ as := by
    intro haa
    exact (Nat.lt_irrefl a.val)
      ((List.pairwise_cons.mp hbase.sorted).1 a haa)
  have htail_remaining : as.toFinset =
      x \ (executeState D x y (s + 1)).served := by
    rw [hserved_next, hserved_s]
    ext b
    by_cases hba : b = a
    · subst b
      have ha_start : a ∉ (executeState D x y start).served := by
        intro has
        have haRem : a ∈ x \ (executeState D x y start).served := by
          rw [← hbase.remaining]
          simp
        exact (Finset.mem_sdiff.mp haRem).2 has
      simp [haa, ha_start]
    · have hmem : b ∈ (a :: as).toFinset ↔
          b ∈ x ∧ b ∉ (executeState D x y start).served := by
        rw [hbase.remaining]
        simp only [Finset.mem_sdiff]
      simpa [hba] using hmem
  have hqset : (executeState D x y (s + 1)).queue.toFinset =
      (as.filter (fun b => b.val < s + 1)).toFinset := by
    have hqInv := executeState_queueInvariant (H := H) (n := s + 1)
      (by omega) D x y
    ext b
    constructor
    · intro hbq
      have hbpref : b ∈ tracePrefix (s + 1) x := by
        rw [← hqInv.2.2.1]
        exact Finset.mem_union_left _ hbq
      have hbx := (mem_prefix.mp hbpref).1
      have hbval := (mem_prefix.mp hbpref).2
      have hbnotserved : b ∉ (executeState D x y (s + 1)).served := by
        exact (Finset.disjoint_left.mp hqInv.2.2.2.1) hbq
      have hbrem : b ∈ as.toFinset := by
        rw [htail_remaining]
        exact Finset.mem_sdiff.mpr ⟨hbx, hbnotserved⟩
      have hbArr : b ∈ as := by simpa using hbrem
      have hbval' : b.val ≤ s := by omega
      simp [hbArr, hbval']
    · intro hbq
      have hbqList : b ∈ as.filter (fun b => b.val < s + 1) := by
        simpa using hbq
      have hbqParts := List.mem_filter.mp hbqList
      have hbArr : b ∈ as := hbqParts.1
      have hbval : b.val < s + 1 := by simpa using hbqParts.2
      have hbrem : b ∈ as.toFinset := by simpa using hbArr
      have hbnotserved : b ∉ (executeState D x y (s + 1)).served := by
        intro hbs
        have : b ∈ x \ (executeState D x y (s + 1)).served := by
          rw [← htail_remaining]
          exact hbrem
        exact (Finset.mem_sdiff.mp this).2 hbs
      have hbx : b ∈ x := by
        have hrem : b ∈ x \ (executeState D x y (s + 1)).served := by
          rw [← htail_remaining]
          exact hbrem
        exact (Finset.mem_sdiff.mp hrem).1
      have hbpref : b ∈ tracePrefix (s + 1) x :=
        mem_prefix.mpr ⟨hbx, hbval⟩
      have hunion : b ∈ (executeState D x y (s + 1)).queue.toFinset ∪
          (executeState D x y (s + 1)).served := by
        rw [hqInv.2.2.1]
        exact hbpref
      rcases Finset.mem_union.mp hunion with hbq' | hbs
      · exact hbq'
      · exact False.elim (hbnotserved hbs)
  have hqsorted := (executeState_queueInvariant (H := H) (n := s + 1)
      (by omega) D x y).2.1
  have htail_sorted : (as.filter (fun b => b.val < s + 1)).Pairwise
      (fun u v : Fin H => u.val < v.val) :=
    List.Pairwise.filter _ (List.pairwise_cons.mp hbase.sorted).2
  have hqueue : (executeState D x y (s + 1)).queue =
      as.filter (fun b => b.val < s + 1) :=
    sorted_list_eq_of_toFinset_eq hqsorted htail_sorted hqset
  refine
    { sorted := (List.pairwise_cons.mp hbase.sorted).2
      remaining := htail_remaining
      queue_at_start := hqueue
      horizon := ?_ }
  intro i hi
  have hi' : i + 1 < (a :: as).length := by simpa using hi
  have hfull := hbase.horizon hi'
  simpa [fifoServices, hsdef, fifoServices_length] using hfull

private theorem workConservingSuffix_mono {H D : ℕ} {x y : Trace H}
    {start start' : ℕ}
    (hstart : start ≤ start')
    (hwork : WorkConservingSuffix D x y start) :
    WorkConservingSuffix D x y start' := by
  intro n hnlo hnhi
  exact hwork (le_trans hstart hnlo) hnhi

private theorem executeState_served_eq_insert_of_head
    {H D : ℕ} {x y : Trace H} {n : ℕ} (hn : n < H)
    (hwork : WorkConservingAt x y ⟨n, hn⟩ (executeState D x y n))
    {a : Fin H}
    (hhead : (suffixQueueAt (D := D) x y ⟨n, hn⟩).head? = some a) :
    (executeState D x y (n + 1)).served =
      insert a (executeState D x y n).served := by
  have hshape := executeState_workConserving_step (D := D) (x := x) (y := y)
    (n := n) hn hwork
  let q := suffixQueueAt (D := D) x y ⟨n, hn⟩
  have hshape' : (executeState D x y (n + 1)).served =
      match q with
      | [] => (executeState D x y n).served
      | b :: _ => insert b (executeState D x y n).served := by
    simpa [q, suffixQueueAt] using hshape.2
  have hheadq : q.head? = some a := by simpa [q] using hhead
  cases hq : q with
  | nil => simp [hq] at hheadq
  | cons b bs =>
      have hba : b = a := by simpa [hq] using hheadq
      simpa [hq, hba] using hshape'

theorem fifoSuffix_service_events_of_base
    {H D : ℕ} {x y : Trace H} :
    ∀ (start : ℕ) (arrivals : List (Fin H)),
      WorkConservingSuffix D x y start →
      FifoSuffixBase (D := D) x y start arrivals →
      ∀ {i : ℕ} (hi : i < arrivals.length),
        let services := fifoServices start (arrivals.map Fin.val)
        let si := services[i]'(by simpa [services, fifoServices_length] using hi)
        let a := arrivals[i]'hi
        a ∉ (executeState D x y si).served ∧
          a ∈ (executeState D x y (si + 1)).served := by
  intro start arrivals
  induction arrivals generalizing start with
  | nil =>
      intro hwork hbase i hi
      simp at hi
  | cons a as ih =>
      intro hwork hbase i hi
      have hzero := hbase.horizon (i := 0) (by simp)
      have hslt : max a.val start < H := by
        simpa [fifoServices] using hzero
      let s := max a.val start
      have hslt' : s < H := by simpa [s] using hslt
      have haRem : a ∈ x \ (executeState D x y start).served := by
        rw [← hbase.remaining]
        simp
      have haStart : a ∉ (executeState D x y start).served :=
        (Finset.mem_sdiff.mp haRem).2
      have haX : a ∈ x := (Finset.mem_sdiff.mp haRem).1
      have hs_data :
          (executeState D x y s).served =
              (executeState D x y start).served ∧
            (suffixQueueAt (D := D) x y ⟨s, hslt'⟩).head? = some a := by
        by_cases hlt : a.val < start
        · have hs_eq : s = start := by
            dsimp [s]
            exact Nat.max_eq_right (Nat.le_of_lt hlt)
          have hqhead :
              (executeState D x y start).queue.head? = some a := by
            rw [hbase.queue_at_start]
            simp [hlt]
          refine ⟨?_, ?_⟩
          · simpa [hs_eq]
          · have hstate_s : executeState D x y s =
                executeState D x y start := by rw [hs_eq]
            cases hq : (executeState D x y start).queue with
            | nil => simp [hq] at hqhead
            | cons b bs =>
                have hba : b = a := by simpa [hq] using hqhead
                unfold suffixQueueAt
                by_cases htx : (⟨s, hslt'⟩ : Fin H) ∈ x
                · rw [if_pos htx, hstate_s, hq]
                  simp [hba, enqueue]
                · rw [if_neg htx, hstate_s, hq]
                  simp [hba]
        · have hle : start ≤ a.val := by omega
          have hgap := fifo_empty_gap (D := D) hbase hle
            (n := s) (by dsimp [s]; omega) (by dsimp [s]; omega)
          have hs_eq : s = a.val := by
            dsimp [s]
            exact Nat.max_eq_left hle
          have hteq : (⟨s, hslt'⟩ : Fin H) = a := by
            apply Fin.ext
            simpa [hs_eq]
          have htX : (⟨s, hslt'⟩ : Fin H) ∈ x := by
            simpa [hteq] using haX
          refine ⟨?_, ?_⟩
          · exact hgap.2
          · unfold suffixQueueAt
            rw [if_pos htX, hgap.1]
            simp [hteq, enqueue]
      have hserved_s := hs_data.1
      have hhead_s := hs_data.2
      have hwork_s : WorkConservingAt x y ⟨s, hslt'⟩
          (executeState D x y s) := hwork (by dsimp [s]; omega) hslt'
      have hserved_next := executeState_served_eq_insert_of_head
        (D := D) (x := x) (y := y) hslt' hwork_s hhead_s
      have ha_s : a ∉ (executeState D x y s).served := by
        rw [hserved_s]
        exact haStart
      have htail_base := fifo_tail_base (D := D) hbase (s := s) rfl
        hslt' hserved_s hserved_next
      have hstart_mono : start ≤ s + 1 := by dsimp [s]; omega
      have htail_work : WorkConservingSuffix D x y (s + 1) :=
        workConservingSuffix_mono (D := D) (x := x) (y := y)
          (start := start) (start' := s + 1) hstart_mono hwork
      have hfirst :
          a ∉ (executeState D x y s).served ∧
            a ∈ (executeState D x y (s + 1)).served := by
        exact ⟨ha_s, by
          rw [hserved_next]
          simp [ha_s]⟩
      cases i with
      | zero =>
          simpa [fifoServices, s] using hfirst
      | succ i =>
          have hi_tail : i < as.length := by simpa using hi
          have htail_event := ih (start := s + 1) htail_work htail_base hi_tail
          simpa [fifoServices, s] using htail_event

theorem executeState_switch_step_served_eq_insert
    {H D : ℕ} {x y : Trace H} {n : ℕ} (hn : n < H)
    (hmode : (executeState D x y n).mode = .schedule)
    {a : Fin H}
    (hhead : (suffixQueueAt (D := D) x y ⟨n, hn⟩).head? = some a)
    (hswitch : (⟨n, hn⟩ : Fin H) ∉ y ∧ deadline H D a = n) :
    (executeState D x y (n + 1)).served =
      insert a (executeState D x y n).served := by
  let t : Fin H := ⟨n, hn⟩
  let q := if t ∈ x then enqueue (executeState D x y n).queue t
    else (executeState D x y n).queue
  have hqhead : q.head? = some a := by
    simpa [q, suffixQueueAt, t] using hhead
  have hstate : executeState D x y (n + 1) =
      step D x y t (executeState D x y n) := by
    simpa [t] using executeState_succ_step hn
  cases hq : q with
  | nil => simp [hq] at hqhead
  | cons b bs =>
      have hba : b = a := by simpa [hq] using hqhead
      have hswitch : t ∉ y ∧ deadline H D b = t.val := by
        subst b
        simpa [t] using hswitch
      have hswitch_decide :
          decide (t ∉ y ∧ deadline H D b = t.val) = true := by
        simp [hswitch]
      have hswitch_a : t ∉ y ∧ deadline H D a = t.val := by
        simpa [hba] using hswitch
      rw [hstate]
      simp [step, q, hq, hmode, hswitch_a.1, hswitch_a.2, hba, t]

theorem executeState_switch_step_mode_service
    {H D : ℕ} {x y : Trace H} {n : ℕ} (hn : n < H)
    (hmode : (executeState D x y n).mode = .schedule)
    {a : Fin H}
    (hhead : (suffixQueueAt (D := D) x y ⟨n, hn⟩).head? = some a)
    (hswitch : (⟨n, hn⟩ : Fin H) ∉ y ∧ deadline H D a = n) :
    (executeState D x y (n + 1)).mode = .service ⟨n, hn⟩ := by
  let t : Fin H := ⟨n, hn⟩
  let q := if t ∈ x then enqueue (executeState D x y n).queue t
    else (executeState D x y n).queue
  have hqhead : q.head? = some a := by
    simpa [q, suffixQueueAt, t] using hhead
  have hstate : executeState D x y (n + 1) =
      step D x y t (executeState D x y n) := by
    simpa [t] using executeState_succ_step hn
  cases hq : q with
  | nil => simp [hq] at hqhead
  | cons b bs =>
      have hba : b = a := by simpa [hq] using hqhead
      have hswitch_a : t ∉ y ∧ deadline H D a = t.val := by
        change (⟨n, hn⟩ : Fin H) ∉ y ∧ deadline H D a = n
        exact hswitch
      rw [hstate]
      simp [step, q, hq, hmode, hswitch_a.1, hswitch_a.2, hba, t]

theorem fifoSuffix_service_events_of_switch
    {H D : ℕ} {x y : Trace H} {tau : ℕ}
    {a : Fin H} {as : List (Fin H)}
    (hbase : FifoSuffixBase (D := D) x y tau (a :: as))
    (htau : tau < H)
    (hmode : (executeState D x y tau).mode = .schedule)
    (hhead : (suffixQueueAt (D := D) x y ⟨tau, htau⟩).head? = some a)
    (hswitch : (⟨tau, htau⟩ : Fin H) ∉ y ∧ deadline H D a = tau)
    (hwork : WorkConservingSuffix D x y (tau + 1)) :
    ∀ {i : ℕ} (hi : i < (a :: as).length),
      let services := fifoServices tau ((a :: as).map Fin.val)
      let si := services[i]'(by simpa [services, fifoServices_length] using hi)
      let ai := (a :: as)[i]'hi
      ai ∉ (executeState D x y si).served ∧
        ai ∈ (executeState D x y (si + 1)).served := by
  have hle : a.val ≤ tau := by
    simp [deadline] at hswitch
    omega
  have hbase_horizon := hbase.horizon (i := 0) (by simp)
  have hfirst_lt : tau < H := by
    have hmax : max a.val tau = tau := Nat.max_eq_right hle
    simpa [fifoServices, hmax] using hbase_horizon
  have hnext := executeState_switch_step_served_eq_insert
    (D := D) (x := x) (y := y) htau hmode hhead hswitch
  have htail_base := fifo_tail_base (D := D) hbase (s := tau)
    (by simp [Nat.max_eq_right hle]) htau rfl hnext
  intro i hi
  cases i with
  | zero =>
      have hzero : a ∉ (executeState D x y tau).served ∧
          a ∈ (executeState D x y (tau + 1)).served := by
        have ha_start : a ∉ (executeState D x y tau).served := by
          have haRem : a ∈ x \ (executeState D x y tau).served := by
            rw [← hbase.remaining]
            simp
          exact (Finset.mem_sdiff.mp haRem).2
        exact ⟨ha_start, by rw [hnext]; simp [ha_start]⟩
      have hmax : max a.val tau = tau := Nat.max_eq_right hle
      simpa [fifoServices, hmax] using hzero
  | succ i =>
      have hi_tail : i < as.length := by simpa using hi
      have htail_event := fifoSuffix_service_events_of_base
        (D := D) (x := x) (y := y) (tau + 1) as hwork htail_base
        (i := i) hi_tail
      have hmax : max a.val tau = tau := Nat.max_eq_right hle
      simpa [fifoServices, hmax] using htail_event

private theorem step_service_mode_persists
    {H D : ℕ} {x y : Trace H} {t : Fin H} {s : ExecState H}
    {serviceAt : Fin H} (hmode : s.mode = .service serviceAt) :
    (step D x y t s).mode = .service serviceAt := by
  let q := if t ∈ x then enqueue s.queue t else s.queue
  cases hq : q with
  | nil => simp [step, hmode, q, hq]
  | cons a q' => simp [step, hmode, q, hq]

theorem executeState_service_mode_persists
    {H D : ℕ} {x y : Trace H} {start : ℕ}
    (hstart : start ≤ H) {serviceAt : Fin H}
    (hmode : (executeState D x y start).mode = .service serviceAt) :
    ∀ {n : ℕ}, start ≤ n → n ≤ H →
      (executeState D x y n).mode = .service serviceAt := by
  have hno : ∀ k : ℕ, start + k ≤ H →
      (executeState D x y (start + k)).mode = .service serviceAt := by
    intro k
    induction k with
    | zero =>
        intro hk
        simpa using hmode
    | succ k ih =>
        intro hk
        have hprev : (executeState D x y (start + k)).mode =
            .service serviceAt := ih (by omega)
        have hprevH : start + k < H := by omega
        have hstate : executeState D x y (start + k + 1) =
            step D x y ⟨start + k, hprevH⟩
              (executeState D x y (start + k)) :=
          executeState_succ_step hprevH
        have hrewrite : start + (k + 1) = start + k + 1 := by omega
        rw [hrewrite, hstate]
        exact step_service_mode_persists hprev
  intro n hnlo hnhi
  obtain ⟨k, hk⟩ : ∃ k, n = start + k := by
    exact ⟨n - start, by omega⟩
  rw [hk]
  exact hno k (by omega)

theorem executeState_service_workConservingSuffix
    {H D : ℕ} {x y : Trace H} {start : ℕ}
    (hstart : start ≤ H)
    (hmode : ∃ serviceAt, (executeState D x y start).mode =
      .service serviceAt) :
    WorkConservingSuffix D x y start := by
  obtain ⟨serviceAt, hmode⟩ := hmode
  intro n hnlo hnhi
  exact Or.inl ⟨serviceAt,
    executeState_service_mode_persists hstart hmode hnlo (by omega)⟩

theorem executeState_switch_workConservingSuffix
    {H D : ℕ} {x y : Trace H} {tau : ℕ}
    (htau : tau < H)
    (hmode : (executeState D x y tau).mode = .schedule)
    {a : Fin H}
    (hhead : (suffixQueueAt (D := D) x y ⟨tau, htau⟩).head? = some a)
    (hswitch : (⟨tau, htau⟩ : Fin H) ∉ y ∧ deadline H D a = tau) :
    WorkConservingSuffix D x y (tau + 1) := by
  have hnextmode := executeState_switch_step_mode_service
    (D := D) (x := x) (y := y) htau hmode hhead hswitch
  intro n hnlo hnhi
  have hmode_n := executeState_service_mode_persists
    (D := D) (x := x) (y := y) (start := tau + 1) (by omega)
    hnextmode hnlo (by omega)
  exact Or.inl ⟨⟨tau, htau⟩, hmode_n⟩

private theorem step_served_avoids_head {H D : ℕ} {x y : Trace H}
    {t : Fin H} {s : ExecState H} {a : Fin H}
    (ha : a ∉ s.served)
    (hhead : (if t ∈ x then enqueue s.queue t else s.queue).head? ≠ some a) :
    a ∉ (step D x y t s).served := by
  classical
  let q := if t ∈ x then enqueue s.queue t else s.queue
  cases hq : q with
  | nil =>
      cases hm : s.mode with
      | schedule =>
          by_cases hty : t ∈ y <;> simp [step, q, hq, hm, hty, ha]
      | service serviceAt =>
          simp [step, q, hq, hm, ha]
  | cons b bs =>
      have hba : b ≠ a := by
        intro h
        apply hhead
        simp [q, hq, h]
      have hab : a ≠ b := Ne.symm hba
      cases hm : s.mode with
      | schedule =>
          by_cases hty : t ∈ y
          · simp [step, q, hq, hm, hty, ha, hab]
          · by_cases hswitch : t ∉ y ∧ deadline H D b = t.val
            · simp [step, q, hq, hm, hty, hswitch, ha, hab]
            · have hdead : deadline H D b ≠ t.val := by
                intro h
                exact hswitch ⟨hty, h⟩
              simp [step, q, hq, hm, hty, hswitch, hdead, ha, hab]
      | service serviceAt =>
          simp [step, q, hq, hm, ha, hab]

private theorem executeState_served_avoids_head_gap
    {H D : ℕ} {x y : Trace H} {start stop : ℕ} {a : Fin H}
    (hstart : start ≤ stop) (hstop : stop < H)
    (ha : a ∉ (executeState D x y start).served)
    (hhead : ∀ {n : ℕ} (hnlo : start ≤ n) (hnlt : n < stop)
      (hnhi : n < H),
      (suffixQueueAt (D := D) x y ⟨n, hnhi⟩).head? ≠ some a) :
    a ∉ (executeState D x y stop).served := by
  have hno : ∀ k : ℕ, start + k ≤ stop →
      a ∉ (executeState D x y (start + k)).served := by
    intro k
    induction k with
    | zero =>
        intro hk
        simpa using ha
    | succ k ih =>
        intro hk
        have hprev : a ∉ (executeState D x y (start + k)).served :=
          ih (by omega)
        have hprevH : start + k < H := by omega
        have hstep := step_served_avoids_head (D := D) (x := x) (y := y)
          (t := (⟨start + k, hprevH⟩ : Fin H))
          (s := executeState D x y (start + k)) hprev
          (hhead (by omega) (by omega) (by omega))
        have hstate : executeState D x y (start + k + 1) =
            step D x y ⟨start + k, hprevH⟩
              (executeState D x y (start + k)) :=
          executeState_succ_step hprevH
        have hrewrite : start + (k + 1) = start + k + 1 := by omega
        rw [hrewrite, hstate]
        exact hstep
  obtain ⟨k, hk⟩ : ∃ k, stop = start + k := by
    exact ⟨stop - start, by omega⟩
  rw [hk]
  exact hno k (by omega)

theorem executeState_first_service_event
    {H D : ℕ} {x y : Trace H} {start : ℕ}
    (hwork : WorkConservingSuffix D x y start)
    (arrivals : List (Fin H))
    (hwitness : FifoSuffixWitness (D := D) x y start arrivals)
    {i : ℕ} (hi : i < arrivals.length) :
    let services := fifoServices start (arrivals.map Fin.val)
    let si := services[i]'(by simpa [services, fifoServices_length] using hi)
    let a := arrivals[i]'hi
    a ∉ (executeState D x y si).served ∧
      a ∈ (executeState D x y (si + 1)).served := by
  let services := fifoServices start (arrivals.map Fin.val)
  let si := services[i]'(by simpa [services, fifoServices_length] using hi)
  let a := arrivals[i]'hi
  obtain ⟨hsi, hheadsi, hheadbefore⟩ := hwitness.heads hi
  have hpairNat : (arrivals.map Fin.val).Pairwise (fun u v : ℕ => u < v) := by
    rw [List.pairwise_map]
    simpa using hwitness.sorted
  have hiNat : i < (arrivals.map Fin.val).length := by simpa using hi
  have hformula : si = max a.val (start + i) := by
    have hf := fifoServices_get_eq_max (start := start)
      (arrivals := arrivals.map Fin.val) hpairNat hiNat
    simpa [si, services] using hf
  have hstartsi : start ≤ si := by
    rw [hformula]
    omega
  have hsi' : si < H := by
    simpa [si, services] using hsi
  have hheadsi' : (suffixQueueAt (D := D) x y ⟨si, hsi'⟩).head? = some a := by
    simpa [si, services] using hheadsi
  have hheadbefore' : ∀ {n : ℕ} (hnlo : start ≤ n) (hnlt : n < si)
      (hnhi : n < H),
      (suffixQueueAt (D := D) x y ⟨n, hnhi⟩).head? ≠ some a := by
    intro n hnlo hnlt hnhi
    exact hheadbefore hnlo (by simpa [si, services] using hnlt) hnhi
  have hinitial : a ∉ (executeState D x y start).served := by
    have haA : a ∈ arrivals.toFinset := by simp [a]
    have haRem : a ∈ x \ (executeState D x y start).served := by
      rw [← hwitness.remaining]
      exact haA
    exact (Finset.mem_sdiff.mp haRem).2
  have hbefore : a ∉ (executeState D x y si).served :=
    executeState_served_avoids_head_gap (D := D) (x := x) (y := y)
      (start := start) (stop := si) (a := a)
      hstartsi hsi' hinitial hheadbefore'
  have hworksi : WorkConservingAt x y ⟨si, hsi'⟩
      (executeState D x y si) := hwork (by omega) hsi'
  have hshape := executeState_workConserving_step (D := D) (x := x) (y := y)
    (n := si) hsi' hworksi
  have hqcons : suffixQueueAt (D := D) x y ⟨si, hsi'⟩ =
      a :: (suffixQueueAt (D := D) x y ⟨si, hsi'⟩).tail := by
    cases hq : suffixQueueAt (D := D) x y ⟨si, hsi'⟩ with
    | nil => simp [hq] at hheadsi'
    | cons b bs =>
        have hba : b = a := by simpa [hq] using hheadsi'
        simp [hq, hba]
  have ha_next : a ∈ (executeState D x y (si + 1)).served := by
    rw [show (executeState D x y (si + 1)).served =
      (match suffixQueueAt (D := D) x y ⟨si, hsi'⟩ with
      | [] => (executeState D x y si).served
      | b :: _ => insert b (executeState D x y si).served) by
      simpa [suffixQueueAt] using hshape.2]
    rw [hqcons]
    simp [hbefore]
  exact ⟨hbefore, ha_next⟩

theorem fifoSuffix_service_events
    {H D : ℕ} {x y : Trace H} {start : ℕ}
    (hwork : WorkConservingSuffix D x y start)
    (arrivals : List (Fin H))
    (hwitness : FifoSuffixWitness (D := D) x y start arrivals) :
    ∀ {i : ℕ} (hi : i < arrivals.length),
      let services := fifoServices start (arrivals.map Fin.val)
      let si := services[i]'(by simpa [services, fifoServices_length] using hi)
      let a := arrivals[i]'hi
      a ∉ (executeState D x y si).served ∧
        a ∈ (executeState D x y (si + 1)).served := by
  intro i hi
  exact executeState_first_service_event hwork arrivals hwitness hi

end TrafficShaping
