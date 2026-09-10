import TrafficShaping.Model

/-!
  The causal switch-to-service execution rule.

  The state below is deliberately operational.  It contains the FIFO queue,
  the set of packets already served, the public output prefix, and (when the
  rule has switched) the slot at which service mode started.  In particular,
  `execute` never searches for a feasible future trace.
-/

namespace TrafficShaping

inductive ExecMode (H : ℕ) where
  | schedule
  | service (serviceAt : Fin H)
deriving DecidableEq

structure ExecState (H : ℕ) where
  queue : List (Fin H)
  served : Trace H
  output : Trace H
  mode : ExecMode H

def deadline (H D : ℕ) (a : Fin H) : ℕ := min (a.val + D) (H - 1)

def initialState (H : ℕ) : ExecState H :=
  { queue := []
    served := ∅
    output := ∅
    mode := .schedule }

def enqueue (q : List (Fin H)) (a : Fin H) : List (Fin H) := q ++ [a]

def step (D : ℕ) (x y : Trace H) (t : Fin H) (s : ExecState H) : ExecState H := by
  let q := if t ∈ x then enqueue s.queue t else s.queue
  let switchNow : Bool :=
    match s.mode, q.head? with
    | .schedule, some a => decide (t ∉ y ∧ deadline H D a = t.val)
    | _, _ => false
  let mode' := if switchNow then .service t else s.mode
  exact match mode' with
  | .service serviceAt =>
      match q with
      | [] =>
          { queue := []
            served := s.served
            output := s.output
            mode := .service serviceAt }
      | a :: q' =>
          { queue := q'
            served := insert a s.served
            output := insert t s.output
            mode := .service serviceAt }
  | .schedule =>
      if t ∈ y then
        match q with
        | [] =>
            { queue := []
              served := s.served
              output := insert t s.output
              mode := .schedule }
        | a :: q' =>
            { queue := q'
              served := insert a s.served
              output := insert t s.output
              mode := .schedule }
      else
        { queue := q
          served := s.served
          output := s.output
          mode := .schedule }

def runN (D : ℕ) (x y : Trace H) : ℕ → ExecState H → ExecState H
  | 0, s => s
  | n + 1, s =>
      let s' := runN D x y n s
      if h : n < H then step D x y ⟨n, h⟩ s' else s'

def execute (D : ℕ) (x y : Trace H) : Trace H :=
  (runN D x y H (initialState H)).output

def executeState (D : ℕ) (x y : Trace H) (n : ℕ) : ExecState H :=
  runN D x y n (initialState H)

@[simp] theorem tracePrefix_zero (x : Trace H) : tracePrefix 0 x = ∅ := by
  ext a
  simp [tracePrefix]

theorem tracePrefix_succ {n : ℕ} (hn : n < H) (x : Trace H) :
    tracePrefix (n + 1) x =
      if (⟨n, hn⟩ : Fin H) ∈ x then insert ⟨n, hn⟩ (tracePrefix n x)
      else tracePrefix n x := by
  ext a
  simp only [tracePrefix, Finset.mem_filter, Finset.mem_insert]
  by_cases hax : (⟨n, hn⟩ : Fin H) ∈ x
  · simp only [hax, ↓reduceIte]
    simp only [Finset.mem_insert, Finset.mem_filter]
    constructor
    · rintro ⟨ha, hlt⟩
      by_cases heq : a = (⟨n, hn⟩ : Fin H)
      · exact Or.inl heq
      · right
        refine ⟨ha, ?_⟩
        by_contra hnot
        have heqVal : a.val = n := by omega
        exact heq (Fin.ext heqVal)
    · rintro (rfl | ⟨ha, hlt⟩)
      · exact ⟨hax, by simp⟩
      · exact ⟨ha, by omega⟩
  · simp only [hax, Bool.false_eq_true, ↓reduceIte]
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ha, hlt⟩
      refine ⟨ha, ?_⟩
      by_contra hnot
      have heqVal : a.val = n := by omega
      have heq : a = (⟨n, hn⟩ : Fin H) := Fin.ext heqVal
      exact hax (heq ▸ ha)
    · rintro ⟨ha, hlt⟩
      exact ⟨ha, by omega⟩

def QueueInvariant (x : Trace H) (n : ℕ) (s : ExecState H) : Prop :=
  s.queue.Nodup ∧
    s.queue.Pairwise (fun a b => a.val < b.val) ∧
    s.queue.toFinset ∪ s.served = tracePrefix n x ∧
    Disjoint s.queue.toFinset s.served ∧
    ∀ a ∈ s.queue, a.val < n

private theorem queueInvariant_initial (x : Trace H) :
    QueueInvariant x 0 (initialState H) := by
  classical
  simp [QueueInvariant, initialState, tracePrefix]

theorem enqueue_invariant {n : ℕ} (hn : n < H) (D : ℕ)
    (x y : Trace H) (t : Fin H) (ht : t.val = n) (s : ExecState H)
    (hs : QueueInvariant x n s) :
    let q := if t ∈ x then enqueue s.queue t else s.queue
    q.Nodup ∧
      q.Pairwise (fun a b => a.val < b.val) ∧
      q.toFinset ∪ s.served = tracePrefix (n + 1) x ∧
      Disjoint q.toFinset s.served ∧
      ∀ a ∈ q, a.val < n + 1 := by
  classical
  rcases hs with ⟨hsnodup, hspair, hspart, hsdisj, hspast⟩
  dsimp
  by_cases htx : t ∈ x
  · simp only [htx, if_true]
    have htqueue : t ∉ s.queue := by
      intro htm
      have := hspast t htm
      omega
    have hnodup : (enqueue s.queue t).Nodup := by
      apply List.Nodup.append hsnodup (by simp)
      intro a ha hb
      have heq : a = t := by simpa [enqueue] using hb
      exact htqueue (heq ▸ ha)
    have hpair : (enqueue s.queue t).Pairwise (fun a b => a.val < b.val) := by
      rw [show enqueue s.queue t = s.queue ++ [t] by rfl, List.pairwise_append]
      refine ⟨hspair, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      have := hspast a ha
      omega
    have hto : (enqueue s.queue t).toFinset = insert t s.queue.toFinset := by
      simp [enqueue, htqueue]
    have hprefix : tracePrefix (n + 1) x = insert t (tracePrefix n x) := by
      have hteq : t = (⟨n, hn⟩ : Fin H) := Fin.ext ht
      have hax : (⟨n, hn⟩ : Fin H) ∈ x := by simpa [← hteq] using htx
      simpa [hax, hteq] using tracePrefix_succ hn x
    refine ⟨hnodup, hpair, ?_, ?_, ?_⟩
    · rw [hto]
      calc
        insert t s.queue.toFinset ∪ s.served =
            insert t (s.queue.toFinset ∪ s.served) := Finset.insert_union t _ _
        _ = insert t (tracePrefix n x) := by rw [hspart]
        _ = tracePrefix (n + 1) x := hprefix.symm
    · rw [hto]
      rw [Finset.disjoint_insert_left]
      refine ⟨?_, hsdisj⟩
      intro hts
      have : t ∈ tracePrefix n x := by
        rw [← hspart]
        exact Finset.mem_union_right _ hts
      have := (mem_prefix.mp this).2
      omega
    · intro a ha
      simp only [enqueue, List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact Nat.lt_succ_of_lt (hspast a ha)
      · omega
  · simp only [htx, if_false]
    refine ⟨hsnodup, hspair, ?_, hsdisj, ?_⟩
    · calc
        s.queue.toFinset ∪ s.served = tracePrefix n x := hspart
        _ = tracePrefix (n + 1) x := by
          have hax : (⟨n, hn⟩ : Fin H) ∉ x := by
            intro h
            apply htx
            have hteq : t = (⟨n, hn⟩ : Fin H) := Fin.ext ht
            simpa [hteq] using h
          symm
          rw [tracePrefix_succ hn x]
          simp [hax]
    · intro a ha
      exact Nat.lt_succ_of_lt (hspast a ha)

private theorem dequeue_invariant {n : ℕ} (x : Trace H) (a : Fin H) (q : List (Fin H))
    (served : Trace H) (hout : Trace H) (mode : ExecMode H)
    (hnodup : (a :: q).Nodup)
    (hpair : (a :: q).Pairwise (fun u v => u.val < v.val))
    (hpart : (a :: q).toFinset ∪ served = tracePrefix n x)
    (hdisj : Disjoint (a :: q).toFinset served)
    (hpast : ∀ u ∈ a :: q, u.val < n) :
    QueueInvariant x n
      ({ queue := q, served := insert a served, output := hout, mode := mode } : ExecState H) := by
  classical
  change q.Nodup ∧
    q.Pairwise (fun u v => u.val < v.val) ∧
    q.toFinset ∪ insert a served = tracePrefix n x ∧
    Disjoint q.toFinset (insert a served) ∧
    ∀ u ∈ q, u.val < n
  simp only [List.nodup_cons, List.pairwise_cons] at hnodup hpair
  rcases hnodup with ⟨haq, hqnodup⟩
  rcases hpair with ⟨harel, hqpair⟩
  have hto : (a :: q).toFinset = insert a q.toFinset := by simp
  refine ⟨hqnodup, hqpair, ?_, ?_, ?_⟩
  · have hto : (a :: q).toFinset = insert a q.toFinset := by simp
    rw [hto] at hpart
    rw [Finset.union_insert]
    rw [Finset.insert_union] at hpart
    exact hpart
  · have hanotin : a ∉ q.toFinset := by
      intro haqfin
      have : a ∈ q := by simpa using haqfin
      exact haq (by simp [this])
    have hanoserved : a ∉ served := by
      intro has
      have hdisj' : Disjoint (insert a q.toFinset) served := by simpa [hto] using hdisj
      exact (Finset.disjoint_left.mp hdisj') (by simp) has
    rw [Finset.disjoint_insert_right]
    refine ⟨?_, ?_⟩
    · exact hanotin
    · exact hdisj.mono_left (by simp)
  · intro b hb
    exact hpast b (by simp [hb])

private theorem step_queueInvariant {n : ℕ} (hn : n < H) (D : ℕ)
    (x y : Trace H) (s : ExecState H) (hs : QueueInvariant x n s) :
    QueueInvariant x (n + 1) (step D x y ⟨n, hn⟩ s) := by
  classical
  let t : Fin H := ⟨n, hn⟩
  have ht : t.val = n := rfl
  have hq := enqueue_invariant hn D x y t ht s hs
  dsimp at hq
  let q : List (Fin H) := if t ∈ x then enqueue s.queue t else s.queue
  have hq' : QueueInvariant x (n + 1)
      { queue := q, served := s.served, output := s.output, mode := s.mode } := by
    change q.Nodup ∧
      q.Pairwise (fun u v => u.val < v.val) ∧
      q.toFinset ∪ s.served = tracePrefix (n + 1) x ∧
      Disjoint q.toFinset s.served ∧
      ∀ u ∈ q, u.val < n + 1
    simpa [q] using hq
  by_cases hsched : s.mode = .schedule
  · by_cases hhead : q = []
    · by_cases hty : t ∈ y
      · have hqdef : (if t ∈ x then enqueue s.queue t else s.queue) = [] := by
          simpa [q] using hhead
        have htarget : QueueInvariant x (n + 1)
            (ExecState.mk ([] : List (Fin H)) s.served (insert t s.output)
              (ExecMode.schedule : ExecMode H)) := by
          change ([] : List (Fin H)).Nodup ∧
            ([] : List (Fin H)).Pairwise (fun u v : Fin H => u.val < v.val) ∧
            (∅ : Trace H) ∪ s.served = tracePrefix (n + 1) x ∧
            Disjoint (∅ : Trace H) s.served ∧ ∀ u ∈ (∅ : List (Fin H)), u.val < n + 1
          have hq'' := hq'
          rw [hhead] at hq''
          simpa [QueueInvariant] using hq''
        simpa [QueueInvariant, step, t, hsched, hqdef, hty] using htarget
      · have hqdef : (if t ∈ x then enqueue s.queue t else s.queue) = [] := by
          simpa [q] using hhead
        have htarget : QueueInvariant x (n + 1)
            (ExecState.mk ([] : List (Fin H)) s.served s.output
              (ExecMode.schedule : ExecMode H)) := by
          change ([] : List (Fin H)).Nodup ∧
            ([] : List (Fin H)).Pairwise (fun u v : Fin H => u.val < v.val) ∧
            (∅ : Trace H) ∪ s.served = tracePrefix (n + 1) x ∧
            Disjoint (∅ : Trace H) s.served ∧ ∀ u ∈ (∅ : List (Fin H)), u.val < n + 1
          have hq'' := hq'
          rw [hhead] at hq''
          simpa [QueueInvariant] using hq''
        simpa [QueueInvariant, step, t, hsched, hqdef, hty] using htarget
    · obtain ⟨a, qtail, hqeq⟩ := List.exists_cons_of_ne_nil hhead
      have hqdef : (if t ∈ x then enqueue s.queue t else s.queue) = a :: qtail := by
        simpa [q] using hqeq
      have hqcomp := hq'
      rw [hqeq] at hqcomp
      change (a :: qtail).Nodup ∧
        (a :: qtail).Pairwise (fun u v => u.val < v.val) ∧
        (a :: qtail).toFinset ∪ s.served = tracePrefix (n + 1) x ∧
        Disjoint (a :: qtail).toFinset s.served ∧
        (∀ u ∈ a :: qtail, u.val < n + 1) at hqcomp
      by_cases hswitch : t ∉ y ∧ deadline H D a = t.val
      · have hdec : decide (t ∉ y ∧ deadline H D a = t.val) = true := by
          simp [hswitch]
        rcases hqcomp with ⟨hnodup, hpair, hpart, hdisj, hpast⟩
        simpa [QueueInvariant, step, t, hqdef, hsched, hswitch, hdec] using
          (dequeue_invariant x a qtail s.served (insert t s.output) (.service t)
            hnodup hpair hpart hdisj hpast)
      · by_cases hty : t ∈ y
        · rcases hqcomp with ⟨hnodup, hpair, hpart, hdisj, hpast⟩
          simpa [QueueInvariant, step, t, hqdef, hsched, hswitch, hty] using
            (dequeue_invariant x a qtail s.served (insert t s.output) (.schedule)
              hnodup hpair hpart hdisj hpast)
        · have hdec : decide (t ∉ y ∧ deadline H D a = t.val) = false := by
            simp [hswitch]
          have hdeadline : deadline H D a ≠ t.val := by
            intro h
            exact hswitch ⟨hty, h⟩
          simpa [QueueInvariant, step, t, hqdef, hsched, hswitch, hty, hdec,
            hdeadline] using hqcomp
  · have hservice : ∃ serviceAt, s.mode = .service serviceAt := by
      cases hm : s.mode with
      | schedule => exact False.elim (hsched hm)
      | service serviceAt => exact ⟨serviceAt, rfl⟩
    obtain ⟨serviceAt, hserviceAt⟩ := hservice
    by_cases hqempty : q = ([] : List (Fin H))
    · have hqdef : (if t ∈ x then enqueue s.queue t else s.queue) = [] := by
        simpa [q] using hqempty
      have htarget : QueueInvariant x (n + 1)
          (ExecState.mk ([] : List (Fin H)) s.served s.output
            (ExecMode.service serviceAt)) := by
        change ([] : List (Fin H)).Nodup ∧
          ([] : List (Fin H)).Pairwise (fun u v : Fin H => u.val < v.val) ∧
          (∅ : Trace H) ∪ s.served = tracePrefix (n + 1) x ∧
          Disjoint (∅ : Trace H) s.served ∧ ∀ u ∈ (∅ : List (Fin H)), u.val < n + 1
        have hq'' := hq'
        rw [hqempty] at hq''
        simpa [QueueInvariant] using hq''
      simpa [QueueInvariant, step, t, hserviceAt, hqdef] using htarget
    · obtain ⟨a, qtail, hqeq⟩ := List.exists_cons_of_ne_nil hqempty
      have hqdef : (if t ∈ x then enqueue s.queue t else s.queue) = a :: qtail := by
        simpa [q] using hqeq
      have hqcomp := hq'
      rw [hqeq] at hqcomp
      change (a :: qtail).Nodup ∧
        (a :: qtail).Pairwise (fun u v => u.val < v.val) ∧
        (a :: qtail).toFinset ∪ s.served = tracePrefix (n + 1) x ∧
        Disjoint (a :: qtail).toFinset s.served ∧
        (∀ u ∈ a :: qtail, u.val < n + 1) at hqcomp
      rcases hqcomp with ⟨hnodup, hpair, hpart, hdisj, hpast⟩
      simpa [QueueInvariant, step, t, hqdef, hserviceAt] using
        (dequeue_invariant x a qtail s.served (insert t s.output) (.service serviceAt)
          hnodup hpair hpart hdisj hpast)

theorem executeState_queueInvariant {n : ℕ} (hn : n ≤ H) (D : ℕ)
    (x y : Trace H) : QueueInvariant x n (executeState D x y n) := by
  induction n with
  | zero =>
      change QueueInvariant x 0 (initialState H)
      exact queueInvariant_initial x
  | succ n ih =>
      have hnlt : n < H := by omega
      simpa [executeState, runN, hnlt] using
        (step_queueInvariant hnlt D x y (executeState D x y n) (ih (by omega)))

theorem deadline_lt {hH D : ℕ} (hHpos : 0 < hH) (a : Fin hH) :
    deadline hH D a < hH := by
  simp [deadline]
  omega

theorem deadline_ge_arrival {hH D : ℕ} (hHpos : 0 < hH) (a : Fin hH) :
    a.val ≤ deadline hH D a := by
  simp [deadline]
  omega

theorem deadline_strict_mono {hH D n : ℕ} (hn : n + 1 < hH)
    {a b : Fin hH} (hab : a.val < b.val)
    (ha : n ≤ deadline hH D a) :
    n + 1 ≤ deadline hH D b := by
  unfold deadline at ha ⊢
  by_cases hclip : a.val + D ≤ hH - 1
  · rw [Nat.min_eq_left hclip] at ha
    by_cases hclipb : b.val + D ≤ hH - 1
    · rw [Nat.min_eq_left hclipb]
      omega
    · rw [Nat.min_eq_right (by omega)]
      omega
  · rw [Nat.min_eq_right (by omega)] at ha
    by_cases hclipb : b.val + D ≤ hH - 1
    · rw [Nat.min_eq_left hclipb]
      omega
    · rw [Nat.min_eq_right (by omega)]
      omega

def HeadSafe (hH D n : ℕ) (s : ExecState hH) : Prop :=
  ∀ a, s.queue.head? = some a → n ≤ deadline hH D a

theorem enqueue_head_safe {hH D n : ℕ} (hHpos : 0 < hH)
    (q : List (Fin hH))
    (hsafe : ∀ a, q.head? = some a → n ≤ deadline hH D a)
    (t : Fin hH) (ht : t.val = n) :
    ∀ a, (enqueue q t).head? = some a → n ≤ deadline hH D a := by
  cases q with
  | nil =>
      intro a ha
      simp [enqueue] at ha
      cases ha
      simpa [ht] using (deadline_ge_arrival hHpos t)
  | cons b q =>
      intro a ha
      simp [enqueue] at ha
      exact hsafe a (by simpa using ha)

private theorem tail_head_safe {hH D n : ℕ} (hn : n + 1 < hH)
    {a : Fin hH} {q : List (Fin hH)}
    (hpair : (a :: q).Pairwise (fun u v => u.val < v.val))
    (hsafe : ∀ u, (a :: q).head? = some u → n ≤ deadline hH D u) :
    ∀ b, q.head? = some b → n + 1 ≤ deadline hH D b := by
  cases q with
  | nil =>
      intro b hb
      simp at hb
  | cons c q =>
      intro b hb
      simp at hb
      subst b
      have hrel : a.val < c.val := (List.pairwise_cons.mp hpair).1 c (by simp)
      have ha : n ≤ deadline hH D a := hsafe a rfl
      exact deadline_strict_mono hn hrel ha

private theorem step_headSafe {hH D n : ℕ} (hHpos : 0 < hH)
    (hn : n + 1 < hH) (x y : Trace hH) (s : ExecState hH)
    (hq : QueueInvariant x n s)
    (hsafe : HeadSafe hH D n s) :
    HeadSafe hH D (n + 1) (step D x y ⟨n, by omega⟩ s) := by
  classical
  let t : Fin hH := ⟨n, by omega⟩
  have ht : t.val = n := rfl
  let q : List (Fin hH) := if t ∈ x then enqueue s.queue t else s.queue
  have hq' := enqueue_invariant (by omega : n < hH) D x y t ht s hq
  dsimp at hq'
  have hqInv : QueueInvariant x (n + 1)
      { queue := q, served := s.served, output := s.output, mode := s.mode } := by
    change q.Nodup ∧ q.Pairwise (fun u v => u.val < v.val) ∧
      q.toFinset ∪ s.served = tracePrefix (n + 1) x ∧
      Disjoint q.toFinset s.served ∧ ∀ u ∈ q, u.val < n + 1
    simpa [q] using hq'
  have hqPair : q.Pairwise (fun u v => u.val < v.val) := hqInv.2.1
  have hqSafe : ∀ a, q.head? = some a → n ≤ deadline hH D a := by
    by_cases htx : t ∈ x
    · simpa [q, htx] using
        (enqueue_head_safe hHpos s.queue (by simpa [HeadSafe] using hsafe) t ht)
    · simpa [q, htx] using (by simpa [HeadSafe] using hsafe)
  by_cases hsched : s.mode = .schedule
  · by_cases hqempty : q = []
    · have hqdef : (if t ∈ x then enqueue s.queue t else s.queue) = [] := by
        simpa [q] using hqempty
      intro a ha
      have hnone : (step D x y ⟨n, by omega⟩ s).queue = [] := by
        by_cases hty : t ∈ y <;> simp [step, t, hsched, hqdef, hty]
      have : False := by simpa [hnone] using ha
      exact this.elim
    · obtain ⟨a, qtail, hqeq⟩ := List.exists_cons_of_ne_nil hqempty
      have hqdef : (if t ∈ x then enqueue s.queue t else s.queue) = a :: qtail := by
        simpa [q] using hqeq
      have hqPair' : (a :: qtail).Pairwise (fun u v => u.val < v.val) := by
        simpa [hqeq] using hqPair
      have hqSafe' : ∀ u, (a :: qtail).head? = some u → n ≤ deadline hH D u := by
        intro u hu
        apply hqSafe u
        simpa [hqeq] using hu
      have haSafe : n ≤ deadline hH D a := hqSafe a (by simp [hqeq])
      by_cases hty : t ∈ y
      · have htail := tail_head_safe (D := D) hn hqPair' hqSafe'
        intro b hb
        have hb' : qtail.head? = some b := by
          simpa [step, t, hsched, hqdef, hty] using hb
        exact htail b hb'
      · by_cases hdeadline : deadline hH D a = t.val
        · have htail := tail_head_safe (D := D) hn hqPair' hqSafe'
          intro b hb
          have hb' : qtail.head? = some b := by
            simpa [step, t, hsched, hqdef, hty, hdeadline] using hb
          exact htail b hb'
        · intro b hb
          have hbhead : b = a := by
            have hab : a = b := by
              simpa [step, t, hqdef, hsched, hty, hdeadline] using hb
            exact hab.symm
          subst b
          omega
  · obtain ⟨serviceAt, hserviceAt⟩ : ∃ serviceAt, s.mode = .service serviceAt := by
      cases hm : s.mode with
      | schedule => exact False.elim (hsched hm)
      | service serviceAt => exact ⟨serviceAt, rfl⟩
    by_cases hqempty : q = []
    · have hqdef : (if t ∈ x then enqueue s.queue t else s.queue) = [] := by
        simpa [q] using hqempty
      intro a ha
      have hnone : (step D x y ⟨n, by omega⟩ s).queue = [] := by
        simp [step, t, hserviceAt, hqdef]
      have : False := by simpa [hnone] using ha
      exact this.elim
    · obtain ⟨a, qtail, hqeq⟩ := List.exists_cons_of_ne_nil hqempty
      have hqdef : (if t ∈ x then enqueue s.queue t else s.queue) = a :: qtail := by
        simpa [q] using hqeq
      have hqPair' : (a :: qtail).Pairwise (fun u v => u.val < v.val) := by
        simpa [hqeq] using hqPair
      have hqSafe' : ∀ u, (a :: qtail).head? = some u → n ≤ deadline hH D u := by
        intro u hu
        apply hqSafe u
        simpa [hqeq] using hu
      have htail := tail_head_safe (D := D) hn hqPair' hqSafe'
      intro b hb
      have hb' : qtail.head? = some b := by
        simpa [step, t, hserviceAt, hqdef] using hb
      exact htail b hb'

@[simp] theorem executeState_zero (D : ℕ) (x y : Trace H) :
    executeState D x y 0 = initialState H := rfl

@[simp] theorem executeState_horizon (D : ℕ) (x y : Trace H) :
    executeState D x y H = runN D x y H (initialState H) := rfl

/-! The remaining lemmas expose the operational facts needed by the
    mechanism layer.  They are stated for the actual queue transition above;
    no search over future schedules is used in any of these arguments. -/

def OutputPast (n : ℕ) (s : ExecState H) : Prop :=
  ∀ a, a ∈ s.output → a.val < n

def OutputModeInvariant (m : ℕ) (y : Trace H) (n : ℕ) (s : ExecState H) : Prop :=
  match s.mode with
  | .schedule => s.output = tracePrefix n y
  | .service serviceAt =>
      serviceAt.val < H - m ∧
        s.output.card ≤ (tracePrefix serviceAt.val y).card + s.served.card

private theorem step_output_shape {n : ℕ} (hn : n < H) (D : ℕ)
    (x y : Trace H) (s : ExecState H) :
    (step D x y ⟨n, hn⟩ s).output = s.output ∨
      (step D x y ⟨n, hn⟩ s).output = insert ⟨n, hn⟩ s.output := by
  classical
  let t : Fin H := ⟨n, hn⟩
  unfold step
  dsimp only
  generalize hq : (if t ∈ x then enqueue s.queue t else s.queue) = q
  cases hm : s.mode with
  | schedule =>
      cases hq' : q with
      | nil =>
          by_cases hty : t ∈ y
          · simp [t, hm, hq', hq, hty]
          · simp [t, hm, hq', hq, hty]
      | cons a qtail =>
          by_cases hswitch : decide (t ∉ y ∧ deadline H D a = t.val) = true
          · simp [t, hm, hq', hq, hswitch]
          · by_cases hty : t ∈ y
            · simp [t, hm, hq', hq, hswitch, hty]
            · by_cases hd : deadline H D a = t.val
              · exact False.elim (hswitch (by simp [hty, hd]))
              · simp [t, hm, hq', hq, hswitch, hty, hd]
  | service serviceAt =>
      cases hq' : q with
      | nil =>
          simp [t, hm, hq', hq]
      | cons a qtail =>
          simp [t, hm, hq', hq]

private theorem step_outputPast {n : ℕ} (hn : n < H) (D : ℕ)
    (x y : Trace H) (s : ExecState H) (hs : OutputPast n s) :
    OutputPast (n + 1) (step D x y ⟨n, hn⟩ s) := by
  change ∀ a, a ∈ (step D x y ⟨n, hn⟩ s).output → a.val < n + 1
  rcases step_output_shape hn D x y s with hsame | hinsert
  · rw [hsame]
    intro a ha
    exact Nat.lt_succ_of_lt (hs a ha)
  · rw [hinsert]
    intro a ha
    simp only [Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · simp
    · exact Nat.lt_succ_of_lt (hs a ha)

theorem executeState_outputPast {n : ℕ} (hn : n ≤ H) (D : ℕ)
    (x y : Trace H) : OutputPast n (executeState D x y n) := by
  induction n with
  | zero =>
      change OutputPast 0 (initialState H)
      simp [OutputPast, initialState]
  | succ n ih =>
      have hnlt : n < H := by omega
      simpa [executeState, runN, hnlt] using
        (step_outputPast hnlt D x y (executeState D x y n) (ih (by omega)))

theorem executeState_headSafe {n : ℕ} (hHpos : 0 < H) (hn : n < H)
    (D : ℕ) (x y : Trace H) :
    HeadSafe H D n (executeState D x y n) := by
  induction n with
  | zero =>
      intro a ha
      simpa [executeState, initialState] using ha
  | succ n ih =>
      have hnlt : n < H := by omega
      simpa [executeState, runN, hnlt] using
        (step_headSafe hHpos hn x y (executeState D x y n)
          (executeState_queueInvariant (by omega) D x y)
          (ih (by omega)))

private theorem step_outputModeInvariant {n : ℕ} (hm : m ≤ H)
    (hn : n < H) (D : ℕ) (x : Trace H) (y : Trace H)
    (hterminal : terminal H m ⊆ y) (s : ExecState H)
    (hq : QueueInvariant x n s) (hp : OutputPast n s)
    (ho : OutputModeInvariant m y n s) :
    OutputModeInvariant m y (n + 1) (step D x y ⟨n, hn⟩ s) := by
  classical
  let t : Fin H := ⟨n, hn⟩
  have ht : t.val = n := rfl
  let q : List (Fin H) := if t ∈ x then enqueue s.queue t else s.queue
  have hqdef : (if t ∈ x then enqueue s.queue t else s.queue) = q := rfl
  have hqenq := enqueue_invariant hn D x y t ht s hq
  dsimp at hqenq
  have hqdisj : Disjoint q.toFinset s.served := by
    simpa [q] using hqenq.2.2.2.1
  have hhead_not_served : ∀ a, q.head? = some a → a ∉ s.served := by
    intro a ha hsa
    have hamem : a ∈ q := by
      cases hqv : q with
      | nil => simp [hqv] at ha
      | cons b qtail =>
          have hab : b = a := by simpa [hqv] using ha
          exact by simpa [hqv] using (show a = b ∨ a ∈ qtail from Or.inl hab.symm)
    have hafin : a ∈ q.toFinset := by simpa using hamem
    exact (Finset.disjoint_left.mp hqdisj hafin) hsa
  cases hmde : s.mode with
  | schedule =>
      have hos : s.output = tracePrefix n y := by
        simpa [OutputModeInvariant, hmde] using ho
      cases hqv : q with
      | nil =>
          by_cases hty : t ∈ y
          · have htarget : OutputModeInvariant m y (n + 1)
                (ExecState.mk ([] : List (Fin H)) s.served (insert t s.output)
                  (ExecMode.schedule : ExecMode H)) := by
              change insert t s.output = tracePrefix (n + 1) y
              rw [hos]
              have hpref := tracePrefix_succ hn y
              simpa [t, hty] using hpref.symm
            simpa [OutputModeInvariant, step, t, hqdef, hmde, hqv, hty] using htarget
          · have htarget : OutputModeInvariant m y (n + 1)
                (ExecState.mk ([] : List (Fin H)) s.served s.output
                  (ExecMode.schedule : ExecMode H)) := by
              change s.output = tracePrefix (n + 1) y
              rw [hos]
              have hpref := tracePrefix_succ hn y
              simpa [t, hty] using hpref.symm
            simpa [OutputModeInvariant, step, t, hqdef, hmde, hqv, hty] using htarget
      | cons a qtail =>
          have ha_not_served : a ∉ s.served := hhead_not_served a (by simp [hqv])
          by_cases hswitch : decide (t ∉ y ∧ deadline H D a = t.val) = true
          · have hsw : t ∉ y ∧ deadline H D a = t.val := of_decide_eq_true hswitch
            have htreserve : t.val < H - m := by
              by_contra hnot
              have hterm : t ∈ terminal H m := by
                simp only [mem_terminal]
                omega
              exact hsw.1 (hterminal hterm)
            have htarget : OutputModeInvariant m y (n + 1)
                (ExecState.mk qtail (insert a s.served) (insert t s.output)
                  (ExecMode.service t)) := by
              change t.val < H - m ∧
                (insert t s.output).card ≤ (tracePrefix t.val y).card +
                  (insert a s.served).card
              have htout : t ∉ s.output := by
                intro h
                have := hp t h
                omega
              have hprefix : tracePrefix t.val y = tracePrefix n y := by
                simp [t]
              have hcardout : (insert t s.output).card = s.output.card + 1 := by
                simp [htout]
              have hcardserved : (insert a s.served).card = s.served.card + 1 := by
                simp [ha_not_served]
              refine ⟨htreserve, ?_⟩
              rw [hcardout, hcardserved, hprefix, hos]
              omega
            simpa [OutputModeInvariant, step, t, hqdef, hmde, hqv, hswitch] using htarget
          · by_cases hty : t ∈ y
            · have htarget : OutputModeInvariant m y (n + 1)
                  (ExecState.mk qtail (insert a s.served) (insert t s.output)
                    (ExecMode.schedule : ExecMode H)) := by
                change insert t s.output = tracePrefix (n + 1) y
                rw [hos]
                have hpref := tracePrefix_succ hn y
                simpa [t, hty] using hpref.symm
              simpa [OutputModeInvariant, step, t, hqdef, hmde, hqv, hswitch, hty] using htarget
            · by_cases hd : deadline H D a = t.val
              · exact False.elim (hswitch (by simp [hty, hd]))
              · have htarget : OutputModeInvariant m y (n + 1)
                    (ExecState.mk (a :: qtail) s.served s.output
                      (ExecMode.schedule : ExecMode H)) := by
                  change s.output = tracePrefix (n + 1) y
                  rw [hos]
                  have hpref := tracePrefix_succ hn y
                  simpa [t, hty] using hpref.symm
                simpa [OutputModeInvariant, step, t, hqdef, hmde, hqv, hswitch, hty, hd] using htarget
  | service serviceAt =>
      have hos : serviceAt.val < H - m ∧
          s.output.card ≤ (tracePrefix serviceAt.val y).card + s.served.card := by
        simpa [OutputModeInvariant, hmde] using ho
      cases hqv : q with
      | nil =>
          have htarget : OutputModeInvariant m y (n + 1)
                (ExecState.mk ([] : List (Fin H)) s.served s.output
                  (ExecMode.service serviceAt)) := by
            exact hos
          simpa [OutputModeInvariant, step, t, hqdef, hmde, hqv] using htarget
      | cons a qtail =>
          have ha_not_served : a ∉ s.served := hhead_not_served a (by simp [hqv])
          have htout : t ∉ s.output := by
            intro h
            have := hp t h
            omega
          have htarget : OutputModeInvariant m y (n + 1)
                (ExecState.mk qtail (insert a s.served) (insert t s.output)
                  (ExecMode.service serviceAt)) := by
            change serviceAt.val < H - m ∧
              (insert t s.output).card ≤
                (tracePrefix serviceAt.val y).card + (insert a s.served).card
            have hcardout : (insert t s.output).card = s.output.card + 1 := by
              simp [htout]
            have hcardserved : (insert a s.served).card = s.served.card + 1 := by
              simp [ha_not_served]
            refine ⟨hos.1, ?_⟩
            rw [hcardout, hcardserved]
            omega
          simpa [OutputModeInvariant, step, t, hqdef, hmde, hqv] using htarget

theorem executeState_outputModeInvariant {n : ℕ} (hm : m ≤ H)
    (hn : n ≤ H) (D : ℕ) (x : Trace H) (y : Trace H)
    (hterminal : terminal H m ⊆ y) :
    OutputModeInvariant m y n (executeState D x y n) := by
  induction n with
  | zero =>
      change OutputModeInvariant m y 0 (initialState H)
      simp [OutputModeInvariant, initialState, tracePrefix_zero]
  | succ n ih =>
      have hnlt : n < H := by omega
      simpa [executeState, runN, hnlt] using
        (step_outputModeInvariant hm hnlt D x y hterminal
          (executeState D x y n)
          (executeState_queueInvariant (by omega) D x y)
          (executeState_outputPast (by omega) D x y)
          (ih (by omega)))


end TrafficShaping
