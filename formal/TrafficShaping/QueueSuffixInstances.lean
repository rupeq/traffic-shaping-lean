import TrafficShaping.QueueServiceTimes

/-!
  Canonical instances of the FIFO suffix API.

  The remaining packets at a suffix start are represented by the increasing
  sort of the actual unserved input.  The queue invariant then identifies the
  operational queue with exactly those remaining packets that have already
  arrived.  This gives a concrete `FifoSuffixBase` witness without assuming
  service events or a head schedule.
-/

namespace TrafficShaping

/-- The increasing list of input packets not served by the given suffix start. -/
noncomputable def canonicalRemainingArrivals {H m D : ℕ}
    (x : Input H m) (y : Trace H) (start : ℕ) : List (Fin H) :=
  (x.1 \ (executeState D x.1 y start).served).sort (fun a b => a ≤ b)

private theorem canonicalRemainingArrivals_sorted {H m D : ℕ}
    (x : Input H m) (y : Trace H) (start : ℕ) :
    (canonicalRemainingArrivals (D := D) x y start).Pairwise
      (fun a b : Fin H => a.val < b.val) := by
  classical
  let rem := x.1 \ (executeState D x.1 y start).served
  have hle : (rem.sort (fun a b => a ≤ b)).Pairwise (fun a b => a ≤ b) :=
    Finset.pairwise_sort rem (fun a b => a ≤ b)
  have hne : (rem.sort (fun a b => a ≤ b)).Pairwise (fun a b => a ≠ b) := by
    exact (Finset.sort_nodup rem (fun a b => a ≤ b)).pairwise_of_forall_ne
      (by intro a _ b _ hab; exact hab)
  simpa [canonicalRemainingArrivals, rem] using
    (hle.and hne).imp (fun h => lt_of_le_of_ne h.1 h.2)

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

/-- The canonical list is exactly the unserved input set. -/
theorem canonicalRemainingArrivals_remaining {H m D : ℕ}
    (x : Input H m) (y : Trace H) (start : ℕ) :
    (canonicalRemainingArrivals (D := D) x y start).toFinset =
      x.1 \ (executeState D x.1 y start).served := by
  classical
  simp [canonicalRemainingArrivals]

private theorem canonical_queue_toFinset_eq_filter_toFinset
    {H m D : ℕ} (x : Input H m) (y : Trace H)
    {start : ℕ} (hstart : start ≤ H - m) :
    (executeState D x.1 y start).queue.toFinset =
      ((canonicalRemainingArrivals (D := D) x y start).filter
        (fun a : Fin H => a.val < start)).toFinset := by
  classical
  let s := executeState D x.1 y start
  have hstartH : start ≤ H := by omega
  have hinv := executeState_queueInvariant (H := H) (n := start) hstartH D x.1 y
  have hrem := canonicalRemainingArrivals_remaining (D := D) x y start
  ext b
  constructor
  · intro hbq
    have hbpref : b ∈ tracePrefix start x.1 := by
      rw [← hinv.2.2.1]
      exact Finset.mem_union_left _ hbq
    have hbx : b ∈ x.1 := (mem_prefix.mp hbpref).1
    have hbval : b.val < start := hinv.2.2.2.2 b (by simpa [s] using hbq)
    have hbserved : b ∉ (executeState D x.1 y start).served := by
      exact (Finset.disjoint_left.mp hinv.2.2.2.1) hbq
    have hbrem : b ∈ x.1 \ (executeState D x.1 y start).served :=
      Finset.mem_sdiff.mpr ⟨hbx, hbserved⟩
    have hbc' : b ∈ (canonicalRemainingArrivals (D := D) x y start).toFinset := by
      rw [hrem]
      exact hbrem
    have hbc : b ∈ canonicalRemainingArrivals (D := D) x y start := by
      simpa using hbc' 
    simp [hbc, hbval]
  · intro hbf
    have hbf' : b ∈ canonicalRemainingArrivals (D := D) x y start ∧ b.val < start := by
      simpa using hbf
    have hbc : b ∈ canonicalRemainingArrivals (D := D) x y start := hbf'.1
    have hbval : b.val < start := hbf'.2
    have hbc' : b ∈ (canonicalRemainingArrivals (D := D) x y start).toFinset := by
      simpa using hbc
    have hbrem : b ∈ x.1 \ (executeState D x.1 y start).served := by
      rw [hrem] at hbc'
      exact hbc' 
    have hbx : b ∈ x.1 := (Finset.mem_sdiff.mp hbrem).1
    have hbserved : b ∉ (executeState D x.1 y start).served :=
      (Finset.mem_sdiff.mp hbrem).2
    have hbpref : b ∈ tracePrefix start x.1 := mem_prefix.mpr ⟨hbx, hbval⟩
    have hpart : b ∈ (executeState D x.1 y start).queue.toFinset ∪
        (executeState D x.1 y start).served := by
      rw [hinv.2.2.1]
      exact hbpref
    rcases Finset.mem_union.mp hpart with hbq | hbs
    · exact hbq
    · exact False.elim (hbserved hbs)

/-- The sorted unserved input list gives a base suffix witness at any feasible
suffix start. -/
theorem canonicalRemainingArrivals_fifoSuffixBase {H m D : ℕ}
    (x : Input H m) (y : Trace H) {start : ℕ}
    (hstart : start ≤ H - m) :
    FifoSuffixBase (D := D) x.1 y start
      (canonicalRemainingArrivals (D := D) x y start) := by
  classical
  let arrivals := canonicalRemainingArrivals (D := D) x y start
  have hsorted : arrivals.Pairwise (fun a b : Fin H => a.val < b.val) := by
    exact canonicalRemainingArrivals_sorted x y start
  have hremaining : arrivals.toFinset = x.1 \ (executeState D x.1 y start).served := by
    exact canonicalRemainingArrivals_remaining x y start
  have hqset := canonical_queue_toFinset_eq_filter_toFinset (D := D) x y hstart
  have hqsorted : (executeState D x.1 y start).queue.Pairwise
      (fun a b : Fin H => a.val < b.val) :=
    (executeState_queueInvariant (H := H) (n := start) (by omega) D x.1 y).2.1
  have hfilter_sorted : (arrivals.filter (fun a => a.val < start)).Pairwise
      (fun a b : Fin H => a.val < b.val) :=
    List.Pairwise.filter _ hsorted
  have hqueue : (executeState D x.1 y start).queue =
      arrivals.filter (fun a => a.val < start) := by
    apply sorted_list_eq_of_toFinset_eq hqsorted hfilter_sorted
    exact hqset
  have harrival : ∀ a ∈ arrivals, a.val < H := by
    intro a ha
    exact a.isLt
  have harrivalNat : ∀ a ∈ arrivals.map Fin.val, a < H := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    exact z.isLt
  have hpairNat : (arrivals.map Fin.val).Pairwise (fun a b : ℕ => a < b) := by
    rw [List.pairwise_map]
    simpa using hsorted
  have hcount : arrivals.length ≤ H - start := by
    have hlen : arrivals.length =
        (x.1 \ (executeState D x.1 y start).served).card := by
      simp [arrivals, canonicalRemainingArrivals]
    have hcard : (x.1 \ (executeState D x.1 y start).served).card ≤ x.1.card :=
      Finset.card_le_card (Finset.sdiff_subset)
    have hxH : x.1.card ≤ H := by
      simpa using (Finset.card_le_univ x.1)
    have hxm : x.1.card ≤ m := x.2
    rw [hlen]
    by_cases hmH : m ≤ H
    · omega
    · have hzero : start = 0 := by omega
      omega
  refine { sorted := hsorted, remaining := hremaining, queue_at_start := hqueue, horizon := ?_ }
  intro i hi
  have hi' : i < (arrivals.map Fin.val).length := by simpa using hi
  simpa [fifoServices_length] using
    (fifoServices_get_lt_horizon (H := H) (start := start)
      (arrivals := arrivals.map Fin.val) hpairNat (by simpa using hcount) harrivalNat hi')

/-- On a terminal all-one suffix, every actual execution slot is work-conserving.
If the state is in service mode this is immediate; schedule mode is covered by
membership of every slot in the terminal block. -/
theorem terminal_workConservingSuffix {H m D : ℕ}
    (hm : m ≤ H) {x y : Trace H}
    (hterminal : terminal H m ⊆ y) :
    WorkConservingSuffix D x y (H - m) := by
  intro n hnlo hnhi
  cases hmode : (executeState D x y n).mode with
  | service serviceAt =>
      exact Or.inl ⟨serviceAt, hmode⟩
  | schedule =>
      exact Or.inr ⟨hmode, hterminal (mem_terminal.mpr (by omega))⟩

end TrafficShaping

namespace TrafficShaping

/-- If the actual queue at a suffix start has head `a`, then `a` is the
first element of the canonical unserved-arrival list at that start. -/
theorem canonicalRemainingArrivals_eq_cons_of_head
    {H m D : ℕ} (x : Input H m) (y : Trace H) {tau : ℕ}
    (htau : tau < H) (hstart : tau ≤ H - m) {a : Fin H}
    (hhead : (suffixQueueAt (D := D) x.1 y ⟨tau, htau⟩).head? = some a) :
    ∃ as, canonicalRemainingArrivals (D := D) x y tau = a :: as := by
  classical
  let t : Fin H := ⟨tau, htau⟩
  let q := executeState D x.1 y tau
  have hbase : FifoSuffixBase (D := D) x.1 y tau
      (canonicalRemainingArrivals (D := D) x y tau) :=
    canonicalRemainingArrivals_fifoSuffixBase x y hstart
  have hqeq : q.queue =
      (canonicalRemainingArrivals (D := D) x y tau).filter
        (fun b : Fin H => b.val < tau) := by
    simpa [q] using hbase.queue_at_start
  have hqpair : q.queue.Pairwise (fun u v : Fin H => u.val < v.val) := by
    simpa [q] using
      (executeState_queueInvariant (H := H) (n := tau) (by omega) D x.1 y).2.1
  have hqpast : ∀ b ∈ q.queue, b.val < tau := by
    intro b hb
    simpa [q] using
      (executeState_queueInvariant (H := H) (n := tau) (by omega) D x.1 y).2.2.2.2 b hb
  have hhead' : (if t ∈ x.1 then enqueue q.queue t else q.queue).head? =
      some a := by
    simpa [suffixQueueAt, q, t] using hhead
  have hcanon : a ∈ canonicalRemainingArrivals (D := D) x y tau := by
    by_cases htx : t ∈ x.1
    · rw [if_pos htx] at hhead'
      cases hq : q.queue with
      | nil =>
          have hat : a = t := by simpa [hq, enqueue] using hhead'.symm
          subst a
          have hnotserved : t ∉ q.served := by
            intro hserv
            have hpref : t ∈ tracePrefix tau x.1 := by
              rw [← (executeState_queueInvariant (H := H) (n := tau)
                (by omega) D x.1 y).2.2.1]
              exact Finset.mem_union_right _ hserv
            have := (mem_prefix.mp hpref).2
            dsimp [t] at this
            omega
          have hrem : t ∈ x.1 \ q.served := Finset.mem_sdiff.mpr ⟨htx, hnotserved⟩
          have hset : t ∈
              (canonicalRemainingArrivals (D := D) x y tau).toFinset := by
            rw [hbase.remaining]
            exact hrem
          simpa using hset
      | cons b bs =>
          have hba : b = a := by simpa [hq, enqueue] using hhead'
          have hbq : b ∈ q.queue := by simp [hq]
          have hfilter : b ∈
              (canonicalRemainingArrivals (D := D) x y tau).filter
                (fun c : Fin H => c.val < tau) := by
            rw [← hqeq]
            exact hbq
          have hfilter' : b ∈ canonicalRemainingArrivals (D := D) x y tau ∧ b.val < tau := by
            simpa using hfilter
          have hbcanon : b ∈ canonicalRemainingArrivals (D := D) x y tau := hfilter'.1
          simpa [hba] using hbcanon
    · rw [if_neg htx] at hhead'
      cases hq : q.queue with
      | nil => simp [hq] at hhead'
      | cons b bs =>
          have hba : b = a := by simpa [hq] using hhead'
          have hbq : b ∈ q.queue := by simp [hq]
          have hfilter : b ∈
              (canonicalRemainingArrivals (D := D) x y tau).filter
                (fun c : Fin H => c.val < tau) := by
            rw [← hqeq]
            exact hbq
          have hfilter' : b ∈ canonicalRemainingArrivals (D := D) x y tau ∧ b.val < tau := by
            simpa using hfilter
          have hbcanon : b ∈ canonicalRemainingArrivals (D := D) x y tau := hfilter'.1
          simpa [hba] using hbcanon
  have hmin : ∀ b ∈ canonicalRemainingArrivals (D := D) x y tau, a.val ≤ b.val := by
    intro b hb
    by_cases hbtau : b.val < tau
    · have hbf : b ∈
          (canonicalRemainingArrivals (D := D) x y tau).filter
            (fun c : Fin H => c.val < tau) := by
        simp [hb, hbtau]
      have hbq : b ∈ q.queue := by
        rw [hqeq]
        simpa using hbf
      by_cases htx : t ∈ x.1
      · rw [if_pos htx] at hhead'
        cases hq : q.queue with
        | nil => simp [hq] at hbq
        | cons c cs =>
            have hca : c = a := by simpa [hq, enqueue] using hhead'
            have hbmem : b = c ∨ b ∈ cs := by simpa [hq] using hbq
            have hcb : c.val ≤ b.val := by
              rcases hbmem with rfl | hbmem
              · exact le_rfl
              · exact Nat.le_of_lt ((List.pairwise_cons.mp
                    (by simpa [hq] using hqpair)).1 b hbmem)
            simpa [hca] using hcb
      · rw [if_neg htx] at hhead'
        cases hq : q.queue with
        | nil => simp [hq] at hbq
        | cons c cs =>
            have hca : c = a := by simpa [hq] using hhead'
            have hbmem : b = c ∨ b ∈ cs := by simpa [hq] using hbq
            have hcb : c.val ≤ b.val := by
              rcases hbmem with rfl | hbmem
              · exact le_rfl
              · exact Nat.le_of_lt ((List.pairwise_cons.mp
                    (by simpa [hq] using hqpair)).1 b hbmem)
            simpa [hca] using hcb
    · have hatau : a.val ≤ tau := by
        by_cases htx : t ∈ x.1
        · rw [if_pos htx] at hhead'
          cases hq : q.queue with
          | nil =>
              have hat : a = t := by simpa [hq, enqueue] using hhead'.symm
              simpa [hat, t]
          | cons c cs =>
              have hca : c = a := by simpa [hq, enqueue] using hhead'
              have hclt := hqpast c (by simp [hq])
              simpa [hca] using (Nat.le_of_lt hclt)
        · rw [if_neg htx] at hhead'
          cases hq : q.queue with
          | nil => simp [hq] at hhead'
          | cons c cs =>
              have hca : c = a := by simpa [hq] using hhead'
              have hclt := hqpast c (by simp [hq])
              simpa [hca] using (Nat.le_of_lt hclt)
      omega
  cases hc : canonicalRemainingArrivals (D := D) x y tau with
  | nil =>
      simp [hc] at hcanon
  | cons c cs =>
      by_cases hac : a = c
      · subst a
        exact ⟨cs, rfl⟩
      · have hacmem : a ∈ cs := by
          have : a = c ∨ a ∈ cs := by simpa [hc] using hcanon
          exact this.resolve_left hac
        have hca : c.val < a.val :=
          (List.pairwise_cons.mp (by simpa [hc] using hbase.sorted)).1 a hacmem
        have hacle := hmin c (by simp [hc])
        omega

end TrafficShaping
