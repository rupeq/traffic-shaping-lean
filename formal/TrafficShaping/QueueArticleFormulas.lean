import TrafficShaping.QueueSuffixInstances

/-!
Equations (12) and (13) for the actual queue execution. The remaining-arrival
list is determined by the input and the served set at the suffix start.
The service times are explicit maxima, and both membership changes and the
clipped deadline bound concern `executeState` itself.
-/

namespace TrafficShaping

theorem fifoSuffixBase_first_deadline {H D start : ℕ} {x y : Trace H}
    {a : Fin H} {as : List (Fin H)}
    (hstart : start < H)
    (hbase : FifoSuffixBase (D := D) x y start (a :: as)) :
    start ≤ a.val + D := by
  by_cases ha : a.val < start
  · have hhead : (executeState D x y start).queue.head? = some a := by
      rw [hbase.queue_at_start]
      simp [ha]
    have hsafe := executeState_headSafe (by omega : 0 < H) hstart D x y
    have hbound : start ≤ deadline H D a := hsafe a hhead
    exact hbound.trans (min_le_left _ _)
  · omega

theorem fifoSuffixBase_service_le_deadline {H D start : ℕ} {x y : Trace H}
    (hstart : start < H) (arrivals : List (Fin H))
    (hbase : FifoSuffixBase (D := D) x y start arrivals)
    {i : ℕ} (hi : i < arrivals.length) :
    (fifoServices start (arrivals.map Fin.val))[i]'
      (by simpa [fifoServices_length] using hi) ≤
        deadline H D (arrivals[i]'hi) := by
  cases arrivals with
  | nil => simp at hi
  | cons a as =>
      have hfirst := fifoSuffixBase_first_deadline hstart hbase
      have hpair : ((a :: as).map Fin.val).Pairwise (fun u v : ℕ => u < v) := by
        rw [List.pairwise_map]
        exact hbase.sorted
      have hdelay := fifoServices_get_le_arrival_add_of_first
        (D := D) (start := start) (a := a.val) (as := as.map Fin.val)
        (by simpa using hpair) hfirst (i := i) (by simpa using hi)
      have hhorizon := hbase.horizon hi
      unfold deadline
      apply le_min
      · change (fifoServices start ((a :: as).map Fin.val))[i]'
            (by simpa [fifoServices_length] using hi) ≤
          ((a :: as).map Fin.val)[i]'(by simpa using hi) + D at hdelay
        simpa only [List.getElem_map] using hdelay
      · omega

/-- Equation (12), with zero-based arrival positions. There is no assumed
service schedule: the canonical list and actual queue determine every event. -/
theorem terminal_actual_fifo_eq12 {H m D : ℕ}
    (hm1 : 1 ≤ m) (hm : m ≤ H) (x : Input H m) (y : Trace H)
    (hterminal : terminal H m ⊆ y)
    {i : ℕ}
    (hi : i < (canonicalRemainingArrivals (D := D) x y (H - m)).length) :
    let a := (canonicalRemainingArrivals (D := D) x y (H - m))[i]'hi
    let si := max a.val (H - m + i)
    si ≤ deadline H D a ∧
      a ∉ (executeState D x.1 y si).served ∧
      a ∈ (executeState D x.1 y (si + 1)).served := by
  let arrivals := canonicalRemainingArrivals (D := D) x y (H - m)
  have hbase : FifoSuffixBase (D := D) x.1 y (H - m) arrivals :=
    canonicalRemainingArrivals_fifoSuffixBase x y le_rfl
  have hwork : WorkConservingSuffix D x.1 y (H - m) :=
    terminal_workConservingSuffix (D := D) (x := x.1) hm hterminal
  have hevent := fifoSuffix_service_events_of_base
    (D := D) (x := x.1) (y := y) (H - m) arrivals hwork hbase hi
  have hdeadline := fifoSuffixBase_service_le_deadline
    (D := D) (x := x.1) (y := y) (by omega : H - m < H) arrivals hbase hi
  have hpair : (arrivals.map Fin.val).Pairwise (fun u v : ℕ => u < v) := by
    rw [List.pairwise_map]
    exact hbase.sorted
  have hformula := fifoServices_get_eq_max (start := H - m)
    hpair (i := i) (by simpa using hi)
  dsimp only at hevent
  simp only [hformula, List.getElem_map] at hevent hdeadline
  exact ⟨hdeadline, hevent⟩

/-- Equation (13) at an actual switching slot. The hypotheses describe the
observed trigger; persistence of service mode and the entire later head
schedule are derived from the queue transition. -/
theorem switch_actual_fifo_eq13 {H m D : ℕ}
    (x : Input H m) (y : Trace H) (tau : Fin H)
    (htau : tau.val < H - m)
    (hmode : (executeState D x.1 y tau.val).mode = .schedule)
    {a : Fin H}
    (hhead : (suffixQueueAt (D := D) x.1 y tau).head? = some a)
    (hswitch : tau ∉ y ∧ deadline H D a = tau.val)
    {i : ℕ}
    (hi : i < (canonicalRemainingArrivals (D := D) x y tau.val).length) :
    let ai := (canonicalRemainingArrivals (D := D) x y tau.val)[i]'hi
    let si := max ai.val (tau.val + i)
    si ≤ deadline H D ai ∧
      ai ∉ (executeState D x.1 y si).served ∧
      ai ∈ (executeState D x.1 y (si + 1)).served := by
  let arrivals := canonicalRemainingArrivals (D := D) x y tau.val
  have hbase : FifoSuffixBase (D := D) x.1 y tau.val arrivals :=
    canonicalRemainingArrivals_fifoSuffixBase x y htau.le
  obtain ⟨as, harr⟩ := canonicalRemainingArrivals_eq_cons_of_head
    (D := D) x y tau.isLt htau.le hhead
  have hbase' : FifoSuffixBase (D := D) x.1 y tau.val (a :: as) := by
    simpa only [arrivals, harr] using hbase
  have hwork : WorkConservingSuffix D x.1 y (tau.val + 1) :=
    executeState_switch_workConservingSuffix tau.isLt hmode hhead hswitch
  have hevent := fifoSuffix_service_events_of_switch hbase'
    tau.isLt hmode hhead hswitch hwork (i := i) (by simpa [harr] using hi)
  have hevent' :
      let si := (fifoServices tau.val (arrivals.map Fin.val))[i]'
        (by simpa [fifoServices_length] using hi)
      let ai := arrivals[i]'hi
      ai ∉ (executeState D x.1 y si).served ∧
        ai ∈ (executeState D x.1 y (si + 1)).served := by
    simpa only [arrivals, harr] using hevent
  have hdeadline := fifoSuffixBase_service_le_deadline
    (D := D) (x := x.1) (y := y) tau.isLt arrivals hbase hi
  have hpair : (arrivals.map Fin.val).Pairwise (fun u v : ℕ => u < v) := by
    rw [List.pairwise_map]
    exact hbase.sorted
  have hformula := fifoServices_get_eq_max (start := tau.val)
    hpair (i := i) (by simpa using hi)
  dsimp only at hevent'
  simp only [hformula, List.getElem_map] at hevent' hdeadline
  exact ⟨hdeadline, hevent'⟩

end TrafficShaping
