import TrafficShaping.OnAchievability

/-!
  Arithmetic and operational corollaries for the queue execution.

  The paper numbers arrivals from one.  The definitions below use zero-based
  list positions: the first service is `max a₀ start`, and position `i` has
  the closed form `max aᵢ (start + i)`.  The `fifoServices` definition is the
  actual FIFO recurrence; `closedFifoServices` is its closed form under
  strictly increasing arrivals.
-/

namespace TrafficShaping

def fifoServices : ℕ → List ℕ → List ℕ
  | _, [] => []
  | ready, a :: as =>
      let s := max a ready
      s :: fifoServices (s + 1) as

@[simp] theorem fifoServices_cons (ready a : ℕ) (as : List ℕ) :
    fifoServices ready (a :: as) =
      max a ready :: fifoServices (max a ready + 1) as := by
  rfl

def closedFifoServices (start : ℕ) (arrivals : List ℕ) : List ℕ :=
  arrivals.zipWith max (List.range' start arrivals.length)

theorem closedFifoServices_get_eq_max {start : ℕ} {arrivals : List ℕ}
    {i : ℕ} (hi : i < arrivals.length) :
    (closedFifoServices start arrivals)[i]'(by
      simp [closedFifoServices, hi]) = max (arrivals[i]'hi) (start + i) := by
  simp [closedFifoServices]

theorem fifoServices_length (start : ℕ) (arrivals : List ℕ) :
    (fifoServices start arrivals).length = arrivals.length := by
  induction arrivals generalizing start with
  | nil => rfl
  | cons a as ih =>
      simp only [fifoServices, List.length_cons]
      rw [ih]

private theorem pairwise_cons_get_ge (a : ℕ) :
    (as : List ℕ) → (a :: as).Pairwise (fun u v : ℕ => u < v) →
      ∀ {i : ℕ}, (hi : i < as.length) → a + (i + 1) ≤ as[i]'hi
  | [], hpair, i, hi => by simp at hi
  | b :: bs, hpair, 0, hi => by
      have hab : a < b := (List.pairwise_cons.mp hpair).1 b (by simp)
      simpa using (show a + 1 ≤ b by omega)
  | b :: bs, hpair, i + 1, hi => by
      have hi' : i < bs.length := by simpa using hi
      have htail : (b :: bs).Pairwise (fun u v : ℕ => u < v) :=
        (List.pairwise_cons.mp hpair).2
      have hbi : b + (i + 1) ≤ bs[i]'hi' :=
        pairwise_cons_get_ge b bs htail hi'
      have hab : a < b := (List.pairwise_cons.mp hpair).1 b (by simp)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (show a + (i + 1 + 1) ≤ bs[i]'hi' by omega)

theorem fifoServices_get_eq_max {start : ℕ} {arrivals : List ℕ}
    (hpair : arrivals.Pairwise (fun a b : ℕ => a < b))
    {i : ℕ} (hi : i < arrivals.length) :
    (fifoServices start arrivals)[i]'(by simpa [fifoServices_length] using hi) =
      max (arrivals[i]'hi) (start + i) := by
  induction arrivals generalizing start i with
  | nil => simp at hi
  | cons a as ih =>
      cases i with
      | zero => simp [fifoServices]
      | succ i =>
          have hi' : i < as.length := by simpa using hi
          have hpair' : as.Pairwise (fun u v : ℕ => u < v) :=
            (List.pairwise_cons.mp hpair).2
          have ha_i : a < as[i]'hi' :=
            (List.pairwise_cons.mp hpair).1 _ (by simp)
          have ha_i_strong : a + (i + 1) ≤ as[i]'hi' :=
            pairwise_cons_get_ge a as hpair hi'
          have htail := ih (start := max a start + 1) hpair' hi'
          have hmax : max (as[i]'hi') (i + (max a start + 1)) =
              max (as[i]'hi') (start + (i + 1)) := by
            by_cases hstart : a ≤ start
            · have hmaxa : max a start = start := Nat.max_eq_right hstart
              rw [hmaxa]
              have hadd : i + (start + 1) = start + (i + 1) := by omega
              rw [hadd]
            · have hstarta : start < a := by omega
              have hmaxa : max a start = a := Nat.max_eq_left (by omega)
              rw [hmaxa]
              have hleft : i + (a + 1) ≤ as[i]'hi' := by omega
              have hright : start + (i + 1) ≤ as[i]'hi' := by omega
              rw [Nat.max_eq_left hleft, Nat.max_eq_left hright]
          have hleft_order : i + (max a start + 1) = max a start + 1 + i := by omega
          rw [hleft_order] at hmax
          rw [hmax] at htail
          simpa [fifoServices] using htail

theorem fifoServices_eq_closedFifoServices {start : ℕ} {arrivals : List ℕ}
    (hpair : arrivals.Pairwise (fun a b : ℕ => a < b)) :
    fifoServices start arrivals = closedFifoServices start arrivals := by
  apply List.ext_getElem
  · rw [fifoServices_length]
    simp [closedFifoServices]
  · intro i hleft hright
    have hi : i < arrivals.length := by
      simpa [fifoServices_length] using hleft
    rw [fifoServices_get_eq_max hpair hi]
    rw [closedFifoServices_get_eq_max hi]

private theorem fifoServices_delay_bound_aux (D start a : ℕ) :
    (as : List ℕ) →
      (a :: as).Pairwise (fun u v : ℕ => u < v) →
      start ≤ a + D →
      List.Forall₂ (fun arrival service : ℕ => service ≤ arrival + D)
        (a :: as) (fifoServices start (a :: as))
  | [], hpair, hstart => by
      have hs : max a start ≤ a + D := by
        exact max_le (Nat.le_add_right a D) hstart
      simpa [fifoServices] using
        (List.Forall₂.cons (R := fun arrival service : ℕ => service ≤ arrival + D)
          hs (List.Forall₂.nil :
          List.Forall₂ (fun arrival service : ℕ => service ≤ arrival + D) [] []))
  | b :: bs, hpair, hstart => by
      have hab : a < b := (List.pairwise_cons.mp hpair).1 b (by simp)
      have hpair_tail : (b :: bs).Pairwise (fun u v : ℕ => u < v) :=
        (List.pairwise_cons.mp hpair).2
      let s := max a start
      have hs : s + 1 ≤ b + D := by
        dsimp [s]
        by_cases h : a ≤ start
        · rw [Nat.max_eq_right h]
          omega
        · rw [Nat.max_eq_left (by omega)]
          omega
      have htail := fifoServices_delay_bound_aux D (s + 1) b bs
        hpair_tail hs
      have hhead : s ≤ a + D := by
        dsimp [s]
        exact max_le (Nat.le_add_right a D) hstart
      simpa [fifoServices, s] using
        (List.Forall₂.cons (R := fun arrival service : ℕ => service ≤ arrival + D)
          hhead htail)

theorem fifoServices_delay_bound_of_first {D start a : ℕ} {as : List ℕ}
    (hpair : (a :: as).Pairwise (fun u v : ℕ => u < v))
    (hstart : start ≤ a + D) :
    List.Forall₂ (fun arrival service : ℕ => service ≤ arrival + D)
      (a :: as) (fifoServices start (a :: as)) :=
  fifoServices_delay_bound_aux D start a as hpair hstart

theorem fifoServices_get_le_arrival_add_of_first {D start a : ℕ} {as : List ℕ}
    (hpair : (a :: as).Pairwise (fun u v : ℕ => u < v))
    (hstart : start ≤ a + D) {i : ℕ}
    (hi : i < (a :: as).length) :
    (fifoServices start (a :: as))[i]'(by simpa [fifoServices_length] using hi) ≤
      (a :: as)[i]'hi + D := by
  have hdelay := fifoServices_delay_bound_of_first hpair hstart
  have hserv : i < (fifoServices start (a :: as)).length := by
    simpa [fifoServices_length] using hi
  have hget := hdelay.get hi hserv
  simpa using hget

theorem fifoServices_get_lt_horizon {H start : ℕ} {arrivals : List ℕ}
    (hpair : arrivals.Pairwise (fun a b : ℕ => a < b))
    (hcount : arrivals.length ≤ H - start)
    (harrival : ∀ a ∈ arrivals, a < H) {i : ℕ}
    (hi : i < arrivals.length) :
    (fifoServices start arrivals)[i]'(by simpa [fifoServices_length] using hi) < H := by
  have hi_succ : i + 1 ≤ arrivals.length := by omega
  have hcount' : i + 1 ≤ H - start := hi_succ.trans hcount
  have ha : arrivals[i]'hi < H := harrival _ (by simp)
  rw [fifoServices_get_eq_max hpair hi]
  omega

theorem fifoServices_get_le_horizon_minus_one {H start : ℕ} {arrivals : List ℕ}
    (hpair : arrivals.Pairwise (fun a b : ℕ => a < b))
    (hcount : arrivals.length ≤ H - start)
    (harrival : ∀ a ∈ arrivals, a < H) {i : ℕ}
    (hi : i < arrivals.length) :
    (fifoServices start arrivals)[i]'(by simpa [fifoServices_length] using hi) ≤ H - 1 := by
  have hlt := fifoServices_get_lt_horizon hpair hcount harrival hi
  omega

theorem fifoServices_get_le_deadline_of_first
    {H D start a : ℕ} {as : List ℕ}
    (hpair : (a :: as).Pairwise (fun u v : ℕ => u < v))
    (hcount : (a :: as).length ≤ H - start)
    (harrivals : ∀ z ∈ a :: as, z < H)
    (hstart : start ≤ a + D) {i : ℕ}
    (hi : i < (a :: as).length) :
    (fifoServices start (a :: as))[i]'(by simpa [fifoServices_length] using hi) ≤
      min ((a :: as)[i]'hi + D) (H - 1) := by
  have hdelay := fifoServices_get_le_arrival_add_of_first hpair hstart hi
  have hhorizon := fifoServices_get_le_horizon_minus_one hpair hcount harrivals hi
  exact (Nat.le_min).2 ⟨hdelay, hhorizon⟩

/- The terminal block in the paper is Eq. (12).  Its `i` is one-based;
  `i` below is zero-based, so `r + i` is the paper's `r + i - 1`. -/
theorem terminal_fifo_service_formula {H m D r : ℕ} {a : ℕ} {as : List ℕ}
    (hm : m ≤ H) (hr : r = H - m)
    (hpair : (a :: as).Pairwise (fun u v : ℕ => u < v))
    (hcount : (a :: as).length ≤ m)
    (harrivals : ∀ z ∈ a :: as, z < H)
    (hstart : r ≤ a + D) :
    (∀ {i : ℕ} (hi : i < (a :: as).length),
      (fifoServices r (a :: as))[i]'(by simpa [fifoServices_length] using hi) =
        max ((a :: as)[i]'hi) (r + i)) ∧
    List.Forall₂ (fun arrival service : ℕ => service ≤ arrival + D)
      (a :: as) (fifoServices r (a :: as)) ∧
    (∀ {i : ℕ} (hi : i < (a :: as).length),
      (fifoServices r (a :: as))[i]'(by simpa [fifoServices_length] using hi) ≤
        min ((a :: as)[i]'hi + D) (H - 1)) := by
  have hcount' : (a :: as).length ≤ H - r := by omega
  refine ⟨?_, fifoServices_delay_bound_of_first hpair hstart, ?_⟩
  · intro i hi
    exact fifoServices_get_eq_max hpair hi
  · intro i hi
    exact fifoServices_get_le_deadline_of_first hpair hcount' harrivals hstart hi

/- The post-switch block in the paper is Eq. (13).  The same zero-based
  recurrence is used with `tau` as the first service-ready slot. -/
theorem switch_fifo_service_formula {H m D tau : ℕ} {a : ℕ} {as : List ℕ}
    (hm : m ≤ H) (htau : tau < H - m)
    (hpair : (a :: as).Pairwise (fun u v : ℕ => u < v))
    (hcount : (a :: as).length ≤ m)
    (harrivals : ∀ z ∈ a :: as, z < H)
    (hstart : tau ≤ a + D) :
    (∀ {i : ℕ} (hi : i < (a :: as).length),
      (fifoServices tau (a :: as))[i]'(by simpa [fifoServices_length] using hi) =
        max ((a :: as)[i]'hi) (tau + i)) ∧
    List.Forall₂ (fun arrival service : ℕ => service ≤ arrival + D)
      (a :: as) (fifoServices tau (a :: as)) ∧
    (∀ {i : ℕ} (hi : i < (a :: as).length),
      (fifoServices tau (a :: as))[i]'(by simpa [fifoServices_length] using hi) ≤
        min ((a :: as)[i]'hi + D) (H - 1)) := by
  have hcount' : (a :: as).length ≤ H - tau := by omega
  refine ⟨?_, fifoServices_delay_bound_of_first hpair hstart, ?_⟩
  · intro i hi
    exact fifoServices_get_eq_max hpair hi
  · intro i hi
    exact fifoServices_get_le_deadline_of_first hpair hcount' harrivals hstart hi

/- This is the concrete FIFO link: after a service-mode transition, the
  current arrival is appended before the head is removed.  The arithmetic
  recurrence above therefore describes the service slots generated by this
  operational queue, rather than an independently postulated schedule. -/
theorem service_step_queue_eq {H D : ℕ} {x y : Trace H} {t : Fin H}
    {s : ExecState H} {serviceAt : Fin H}
    (hmode : s.mode = .service serviceAt) :
    (step D x y t s).queue =
      (if t ∈ x then enqueue s.queue t else s.queue).tail := by
  classical
  let q := if t ∈ x then enqueue s.queue t else s.queue
  cases hq : q with
  | nil => simp [step, hmode, q, hq]
  | cons b bs => simp [step, hmode, q, hq]

theorem queue_head_is_fifo {H : ℕ} {x : Trace H} {n : ℕ}
    {s : ExecState H} (hs : QueueInvariant x n s)
    {a : Fin H} {q : List (Fin H)} (hqueue : s.queue = a :: q) :
    ∀ b ∈ s.queue, a.val ≤ b.val := by
  intro b hb
  rw [hqueue] at hb
  simp only [List.mem_cons] at hb
  rcases hb with rfl | hb
  · exact le_rfl
  · have hp := hs.2.1
    rw [hqueue] at hp
    exact Nat.le_of_lt ((List.pairwise_cons.mp hp).1 b hb)

theorem executeState_queue_fifo_order {H D n : ℕ}
    (hn : n ≤ H) (x y : Trace H) :
    (executeState D x y n).queue.Pairwise (fun a b : Fin H => a.val < b.val) :=
  (executeState_queueInvariant hn D x y).2.1

theorem executeState_queue_length_le {H m D n : ℕ}
    (x : Input H m) (hn : n ≤ H) (y : Trace H) :
    (executeState D x.1 y n).queue.length ≤ m := by
  have hq := executeState_queueInvariant hn D x.1 y
  let q := (executeState D x.1 y n).queue
  have hqsub : q.toFinset ⊆ x.1 := by
    intro a ha
    have hap : a ∈ tracePrefix n x.1 := by
      rw [← hq.2.2.1]
      exact Finset.mem_union_left _ ha
    exact (mem_prefix.mp hap).1
  have hcard : q.toFinset.card ≤ x.1.card := Finset.card_le_card hqsub
  have hlen : q.length = q.toFinset.card :=
    (List.toFinset_card_of_nodup hq.1).symm
  change q.length ≤ m
  rw [hlen]
  exact hcard.trans x.2

/- `runN` is a structural traversal of slots `0, ..., n - 1`.  This relation
  records each actual call to `step`, so the horizon theorem below exposes the
  exact transition count without assigning an unprovided machine-cost model
  to membership tests or finite-set operations. -/
inductive ExecStepRun {H : ℕ} (D : ℕ) (x y : Trace H) :
    ℕ → ExecState H → ExecState H → Prop where
  | zero (s : ExecState H) : ExecStepRun D x y 0 s s
  | succ {n : ℕ} {s u : ExecState H} (hn : n < H) :
      ExecStepRun D x y n s u →
      ExecStepRun D x y (n + 1) s (step D x y ⟨n, hn⟩ u)

theorem runN_execStepRun {H D : ℕ} {x y : Trace H} {n : ℕ}
    (hn : n ≤ H) (s : ExecState H) :
    ExecStepRun D x y n s (runN D x y n s) := by
  induction n generalizing s with
  | zero => exact ExecStepRun.zero s
  | succ n ih =>
      have hnlt : n < H := by omega
      simpa [runN, hnlt] using
        (ExecStepRun.succ hnlt (ih (by omega) s))

theorem executeState_succ_step {H D : ℕ} {x y : Trace H} {n : ℕ}
    (hn : n < H) :
    executeState D x y (n + 1) =
      step D x y ⟨n, hn⟩ (executeState D x y n) := by
  simp [executeState, runN, hn]

theorem execute_exactly_H_steps {H D : ℕ} (x y : Trace H) :
    ExecStepRun D x y H (initialState H) (executeState D x y H) := by
  simpa [executeState] using
    (runN_execStepRun (D := D) (x := x) (y := y) (n := H) le_rfl
      (initialState H))

end TrafficShaping
