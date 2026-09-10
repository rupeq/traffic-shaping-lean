import TrafficShaping.ExecutionCore

/-!
  Feasibility and hard-cap consequences of the operational switch-to-service
  rule.  The state machine and its local invariants live in
  `TrafficShaping.ExecutionCore`; this file keeps the public execution
  interface small for the mechanism layer.
-/

namespace TrafficShaping

private theorem feasible_insert_of_feasible {H D : ℕ}
    {served output : Trace H} {a t : Fin H}
    (h : Feasible D served output) (ha : a ∉ served) (ht : t ∉ output)
    (hrel : a.val ≤ t.val) (hdead : t.val ≤ a.val + D) :
    Feasible D (insert a served) (insert t output) := by
  classical
  obtain ⟨f, hfi, hf⟩ := h
  have member_served : ∀ b : {q : Fin H // q ∈ insert a served},
      b.val ≠ a → b.val ∈ served := by
    intro b hba
    exact (Finset.mem_insert.mp b.property).resolve_left hba
  let f' : {b : Fin H // b ∈ insert a served} → Fin H := fun b =>
    if hba : b.val = a then t
    else f ⟨b.val, member_served b hba⟩
  refine ⟨f', ?_, ?_⟩
  · intro b1 b2 h12
    by_cases h1 : b1.val = a <;> by_cases h2 : b2.val = a
    · apply Subtype.ext
      exact h1.trans h2.symm
    · exfalso
      have hb2 : b2.val ∈ served := member_served b2 h2
      let rb2 : {q : Fin H // q ∈ served} := ⟨b2.val, hb2⟩
      have hfb2 := hf rb2
      have hne : f rb2 ≠ t := by
        intro heq
        exact ht (heq ▸ hfb2.1)
      exact hne (by simpa [f', h1, h2, rb2] using h12.symm)
    · exfalso
      have hb1 : b1.val ∈ served := member_served b1 h1
      let rb1 : {q : Fin H // q ∈ served} := ⟨b1.val, hb1⟩
      have hfb1 := hf rb1
      have hne : f rb1 ≠ t := by
        intro heq
        exact ht (heq ▸ hfb1.1)
      exact hne (by simpa [f', h1, h2, rb1] using h12)
    · have hb1 : b1.val ∈ served := member_served b1 h1
      have hb2 : b2.val ∈ served := member_served b2 h2
      let rb1 : {q : Fin H // q ∈ served} := ⟨b1.val, hb1⟩
      let rb2 : {q : Fin H // q ∈ served} := ⟨b2.val, hb2⟩
      have heq : f rb1 = f rb2 := by
        simpa [f', h1, h2, rb1, rb2] using h12
      have hr : rb1 = rb2 := hfi heq
      exact Subtype.ext (congrArg (fun z : {q : Fin H // q ∈ served} => z.val) hr)
  · intro b
    by_cases hba : b.val = a
    · have hbmem : t ∈ insert t output := by simp
      simpa [f', hba] using (⟨hbmem, hrel, hdead⟩ :
        t ∈ insert t output ∧ a.val ≤ t.val ∧ t.val ≤ a.val + D)
    · have hbserv : b.val ∈ served := member_served b hba
      let rb : {q : Fin H // q ∈ served} := ⟨b.val, hbserv⟩
      have hfb := hf rb
      have hfb_eq : f' b = f rb := by simp [f', hba, rb]
      rw [hfb_eq]
      exact ⟨Finset.mem_insert_of_mem hfb.1, hfb.2.1, hfb.2.2⟩

private theorem step_servedFeasible {n : ℕ} (hHpos : 0 < H) (hn : n < H)
    (D : ℕ) (x y : Trace H) (s : ExecState H)
    (hq : QueueInvariant x n s) (hp : OutputPast n s)
    (hsafe : HeadSafe H D n s)
    (hserv : Feasible D s.served s.output) :
    Feasible D (step D x y ⟨n, hn⟩ s).served
      (step D x y ⟨n, hn⟩ s).output := by
  classical
  let t : Fin H := ⟨n, hn⟩
  have ht : t.val = n := rfl
  let q : List (Fin H) := if t ∈ x then enqueue s.queue t else s.queue
  have hqdef : (if t ∈ x then enqueue s.queue t else s.queue) = q := rfl
  have hqenq := enqueue_invariant hn D x y t ht s hq
  dsimp at hqenq
  have hqPast : ∀ a ∈ q, a.val < n + 1 := by
    simpa [q] using hqenq.2.2.2.2
  have hqdisj : Disjoint q.toFinset s.served := by
    simpa [q] using hqenq.2.2.2.1
  have hqSafe : ∀ a, q.head? = some a → n ≤ deadline H D a := by
    by_cases htx : t ∈ x
    · simpa [q, htx] using
        (enqueue_head_safe hHpos s.queue (by simpa [HeadSafe] using hsafe) t ht)
    · simpa [q, htx] using (by simpa [HeadSafe] using hsafe)
  have htout : t ∉ s.output := by
    intro h
    have := hp t h
    omega
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
      cases hqv : q with
      | nil =>
          by_cases hty : t ∈ y
          · have htarget : Feasible D s.served (insert t s.output) := by
              apply Feasible.mono_output hserv
              intro a ha
              exact Finset.mem_insert_of_mem ha
            simpa [step, t, hqdef, hmde, hqv, hty] using htarget
          · simpa [step, t, hqdef, hmde, hqv, hty] using hserv
      | cons a qtail =>
          have ha_not_served : a ∉ s.served := hhead_not_served a (by simp [hqv])
          have ha_safe : n ≤ deadline H D a := hqSafe a (by simp [hqv])
          have ha_past : a.val < n + 1 := by
            exact hqPast a (by simp [hqv])
          have hrel : a.val ≤ t.val := by omega
          have hdead' : deadline H D a ≤ a.val + D := by simp [deadline]
          have hdead : t.val ≤ a.val + D := le_trans ha_safe hdead'
          by_cases hswitch : decide (t ∉ y ∧ deadline H D a = t.val) = true
          · have htarget := feasible_insert_of_feasible hserv ha_not_served htout hrel hdead
            simpa [step, t, hqdef, hmde, hqv, hswitch] using htarget
          · by_cases hty : t ∈ y
            · have htarget := feasible_insert_of_feasible hserv ha_not_served htout hrel hdead
              simpa [step, t, hqdef, hmde, hqv, hswitch, hty] using htarget
            · by_cases hd : deadline H D a = t.val
              · exact False.elim (hswitch (by simp [hty, hd]))
              · simpa [step, t, hqdef, hmde, hqv, hswitch, hty, hd] using hserv
  | service serviceAt =>
      cases hqv : q with
      | nil =>
          simpa [step, t, hqdef, hmde, hqv] using hserv
      | cons a qtail =>
          have ha_not_served : a ∉ s.served := hhead_not_served a (by simp [hqv])
          have ha_safe : n ≤ deadline H D a := hqSafe a (by simp [hqv])
          have ha_past : a.val < n + 1 := by
            exact hqPast a (by simp [hqv])
          have hrel : a.val ≤ t.val := by omega
          have hdead' : deadline H D a ≤ a.val + D := by simp [deadline]
          have hdead : t.val ≤ a.val + D := le_trans ha_safe hdead'
          have htarget := feasible_insert_of_feasible hserv ha_not_served htout hrel hdead
          simpa [step, t, hqdef, hmde, hqv] using htarget

theorem executeState_servedFeasible {n : ℕ} (hHpos : 0 < H) (hn : n ≤ H)
    (D : ℕ) (x y : Trace H) :
    Feasible D (executeState D x y n).served (executeState D x y n).output := by
  induction n with
  | zero =>
      change Feasible D (∅ : Trace H) (∅ : Trace H)
      exact feasible_empty D ∅
  | succ n ih =>
      have hnlt : n < H := by omega
      have hq := executeState_queueInvariant (by omega) D x y
      have hp := executeState_outputPast (by omega) D x y
      have hs := executeState_headSafe hHpos (by omega) D x y
      simpa [executeState, runN, hnlt] using
        (step_servedFeasible hHpos hnlt D x y (executeState D x y n)
          (executeState_queueInvariant (by omega) D x y)
          (executeState_outputPast (by omega) D x y)
          (executeState_headSafe hHpos (by omega) D x y) (ih (by omega)))

end TrafficShaping
