import TrafficShaping.Matching

/-!
# A costed two-pointer implementation of FIFO matching

`TrafficShaping.greedy` is a useful finite-set specification, but its
`filter`/`min'` implementation does not expose the linear scan used by the
algorithm in the paper.  This file gives that implementation on sorted
lists.  The lists contain the one-slots of binary traces; a list cell is
inspected at most once by `advance`, and an arrival cell is inspected once by
`scan`.

The counter in `ScanResult.ops` is an explicit cost model: one unit pays for
one list/pointer inspection.  Comparisons and the constant amount of state
update in an inspection are deliberately charged to that same unit.  Thus the
cost theorem is a statement about this executable contract, rather than about
recursion fuel.
-/

namespace TrafficShaping

/-- A binary trace represented by its strictly increasing one-slots. -/
structure SortedTrace (H : ℕ) where
  slots : List (Fin H)
  sorted : slots.Pairwise (fun a b => a < b)

namespace SortedTrace

instance : Coe (SortedTrace H) (List (Fin H)) := ⟨SortedTrace.slots⟩

def toTrace (q : SortedTrace H) : Trace H := q.slots.toFinset

@[simp] theorem toTrace_nil (H : ℕ) :
    toTrace (⟨[], by simp⟩ : SortedTrace H) = ∅ := by
  simp [toTrace]

theorem nodup (q : SortedTrace H) : q.slots.Nodup := by
  exact q.sorted.nodup

theorem card_toTrace (q : SortedTrace H) : q.toTrace.card = q.slots.length := by
  exact List.toFinset_card_of_nodup q.nodup

theorem head_lt_of_mem {a : Fin H} {xs : List (Fin H)}
    (hs : (a :: xs).Pairwise (fun u v => u < v)) {b : Fin H}
    (hb : b ∈ xs) : a < b := by
  exact (List.pairwise_cons.mp hs).1 b hb

theorem head_le_of_mem {a : Fin H} {xs : List (Fin H)}
    (hs : (a :: xs).Pairwise (fun u v => u < v)) {b : Fin H}
    (hb : b ∈ xs) : a ≤ b :=
  (head_lt_of_mem hs hb).le

theorem tail_sorted {a : Fin H} {xs : List (Fin H)}
    (hs : (a :: xs).Pairwise (fun u v => u < v)) :
    xs.Pairwise (fun u v => u < v) :=
  (List.pairwise_cons.mp hs).2

theorem head_min' {a : Fin H} {xs : List (Fin H)}
    (hs : (a :: xs).Pairwise (fun u v => u < v)) :
    (a :: xs).toFinset.min' (by simp) = a := by
  apply (Finset.min'_eq_iff _ (by simp) a).mpr
  constructor
  · simp
  · intro b hb
    have hb' : b = a ∨ b ∈ xs := by simpa using hb
    rcases hb' with rfl | hb'
    · exact le_rfl
    · exact head_le_of_mem hs hb'

theorem erase_head_toFinset {a : Fin H} {xs : List (Fin H)}
    (hs : (a :: xs).Pairwise (fun u v => u < v)) :
    (a :: xs).toFinset.erase a = xs.toFinset := by
  rw [List.toFinset_cons]
  have hnot : a ∉ xs := by
    intro ha
    exact (head_lt_of_mem hs ha).ne rfl
  simp [hnot]

theorem tail_toTrace (a : Fin H) (xs : List (Fin H))
    (hs : (a :: xs).Pairwise (fun u v => u < v)) :
    toTrace ⟨xs, tail_sorted hs⟩ = (toTrace ⟨a :: xs, hs⟩).erase a := by
  symm
  exact erase_head_toFinset hs

end SortedTrace

/-- Result of the executable scan.  `remaining` is the unconsumed suffix of
the service-slot list; `ops` is the explicit list/pointer cost. -/
structure ScanResult (H : ℕ) where
  accepted : Bool
  remaining : List (Fin H)
  ops : ℕ

namespace ScanResult

instance : Inhabited (ScanResult H) :=
  ⟨⟨false, [], 0⟩⟩

end ScanResult

/-- Move the service pointer to the first slot not earlier than `a`.

Every invocation inspects exactly one list cell (including the terminal empty
cell).  On a deadline failure the original candidate is retained, since no
successful matching state is returned. -/
def advance (D : ℕ) (a : Fin H) : List (Fin H) → ScanResult H
  | [] => ⟨false, [], 1⟩
  | s :: ys =>
      if h₁ : a.val ≤ s.val then
        if h₂ : s.val ≤ a.val + D then
          ⟨true, ys, 1⟩
        else
          ⟨false, s :: ys, 1⟩
      else
        let r := advance D a ys
        ⟨r.accepted, r.remaining, r.ops + 1⟩

/-- Scan arrivals in increasing order while carrying the service pointer. -/
def scan (D : ℕ) : List (Fin H) → List (Fin H) → ScanResult H
  | [], ys => ⟨true, ys, 0⟩
  | a :: xs, ys =>
      let r := advance D a ys
      if r.accepted then
        let q := scan D xs r.remaining
        ⟨q.accepted, q.remaining, r.ops + q.ops + 1⟩
      else
        ⟨false, r.remaining, r.ops + 1⟩

def scanBool (D : ℕ) (xs ys : List (Fin H)) : Bool :=
  (scan D xs ys).accepted

/-! A successful or failed advance always returns a suffix of its input. -/

theorem advance_remaining_subset {D : ℕ} {a : Fin H} {ys : List (Fin H)} :
    (advance D a ys).remaining <:+ ys := by
  induction ys with
  | nil => simp [advance]
  | cons s ys ih =>
      by_cases h₁ : a.val ≤ s.val
      · by_cases h₂ : s.val ≤ a.val + D
        · simp [advance, h₁, h₂]
        · simp [advance, h₁, h₂]
      · simp only [advance, h₁]
        exact List.IsSuffix.trans ih (by simp)

theorem advance_remaining_length_le {D : ℕ} {a : Fin H} {ys : List (Fin H)} :
    (advance D a ys).remaining.length ≤ ys.length := by
  exact (advance_remaining_subset (D := D) (a := a) (ys := ys)).length_le

/-! ## Cost accounting -/

theorem advance_ops_eq_one_of_nonempty_success {D : ℕ} {a s : Fin H}
    {ys : List (Fin H)} (h₁ : a.val ≤ s.val) (h₂ : s.val ≤ a.val + D) :
    (advance D a (s :: ys)).ops = 1 := by
  simp [advance, h₁, h₂]

theorem advance_ops_le_remaining {D : ℕ} {a : Fin H} {ys : List (Fin H)} :
    (advance D a ys).ops ≤ 2 * (ys.length - (advance D a ys).remaining.length) + 2 := by
  induction ys with
  | nil => simp [advance]
  | cons s ys ih =>
      by_cases h₁ : a.val ≤ s.val
      · by_cases h₂ : s.val ≤ a.val + D
        · simp [advance, h₁, h₂]
        · simp [advance, h₁, h₂]
      · simp only [advance, h₁, ↓reduceIte]
        let r := advance D a ys
        have hi := ih
        have hlen : r.remaining.length ≤ ys.length := by
          dsimp [r]
          exact advance_remaining_length_le (D := D) (a := a) (ys := ys)
        dsimp [r] at hi ⊢
        dsimp [r] at hlen
        omega

theorem advance_ops_le_two_mul_length_add_two {D : ℕ} {a : Fin H}
    {ys : List (Fin H)} :
    (advance D a ys).ops ≤ 2 * ys.length + 2 := by
  have h := advance_ops_le_remaining (D := D) (a := a) (ys := ys)
  omega

theorem scan_ops_le (D : ℕ) (xs ys : List (Fin H)) :
    (scan D xs ys).ops ≤ 3 * xs.length + 2 * ys.length := by
  induction xs generalizing ys with
  | nil => simp [scan]
  | cons a xs ih =>
      let r := advance D a ys
      by_cases hr : r.accepted
      · simp only [scan, r, hr, ↓reduceIte]
        let q := scan D xs r.remaining
        have hi := ih r.remaining
        have ha := advance_ops_le_remaining (D := D) (a := a) (ys := ys)
        have hlen : r.remaining.length ≤ ys.length := by
          dsimp [r]
          exact advance_remaining_length_le (D := D) (a := a) (ys := ys)
        dsimp [q, r] at hi ha ⊢
        dsimp [r] at hlen
        omega
      · simp only [scan, r, hr, ↓reduceIte]
        have ha := advance_ops_le_remaining (D := D) (a := a) (ys := ys)
        dsimp [r] at ha ⊢
        omega

theorem scan_ops_le_five_mul_H {H D : ℕ} (xs ys : List (Fin H))
    (hx : xs.length ≤ H) (hy : ys.length ≤ H) :
    (scan D xs ys).ops ≤ 5 * H := by
  have h := scan_ops_le D xs ys
  omega

/-! ## List facts used by the semantic proof -/

theorem pairwise_of_suffix {α : Type} {R : α → α → Prop}
    {xs ys : List α} (hxs : xs.Pairwise R) (hys : ys <:+ xs) :
    ys.Pairwise R := by
  obtain ⟨pre, hprefix⟩ := hys
  rw [← hprefix] at hxs
  exact (List.pairwise_append.mp hxs).2.1

theorem advance_accepts_iff_exists {D : ℕ} {a : Fin H} {ys : List (Fin H)}
    (hys : ys.Pairwise (fun u v => u < v)) :
    (advance D a ys).accepted = true ↔
      ∃ s ∈ ys, a.val ≤ s.val ∧ s.val ≤ a.val + D := by
  induction ys with
  | nil => simp [advance]
  | cons s ys ih =>
      have htail : ys.Pairwise (fun u v => u < v) :=
        (List.pairwise_cons.mp hys).2
      by_cases h₁ : a.val ≤ s.val
      · by_cases h₂ : s.val ≤ a.val + D
        · constructor
          · intro _
            exact ⟨s, by simp, h₁, h₂⟩
          · intro _
            simp [advance, h₁, h₂]
        · constructor
          · intro h
            simp [advance, h₁, h₂] at h
          · rintro ⟨t, ht, hat, htd⟩
            have ht' : t = s ∨ t ∈ ys := by simpa using ht
            rcases ht' with rfl | ht'
            · exact (h₂ htd).elim
            · have hst : s < t := (List.pairwise_cons.mp hys).1 t ht'
              exfalso
              omega
      · constructor
        · intro h
          have h' : (advance D a ys).accepted = true := by
            simpa [advance, h₁] using h
          obtain ⟨t, ht, hat, htd⟩ := (ih htail).mp h'
          exact ⟨t, by simp [ht], hat, htd⟩
        · rintro ⟨t, ht, hat, htd⟩
          have ht' : t ∈ ys := by
            have hc : t = s ∨ t ∈ ys := by simpa using ht
            rcases hc with rfl | hc
            · exact (h₁ hat).elim
            · exact hc
          have h' : (advance D a ys).accepted = true :=
            (ih htail).mpr ⟨t, ht', hat, htd⟩
          simpa [advance, h₁] using h'

theorem advance_success_spec {D : ℕ} {a : Fin H} {ys : List (Fin H)}
    (hys : ys.Pairwise (fun u v => u < v))
    (hacc : (advance D a ys).accepted = true) :
    ∃ pre s post,
      ys = pre ++ s :: post ∧
      (∀ t ∈ pre, t.val < a.val) ∧
      a.val ≤ s.val ∧ s.val ≤ a.val + D ∧
      (advance D a ys).remaining = post := by
  induction ys with
  | nil => simp [advance] at hacc
  | cons s ys ih =>
      have htail : ys.Pairwise (fun u v => u < v) :=
        (List.pairwise_cons.mp hys).2
      by_cases h₁ : a.val ≤ s.val
      · by_cases h₂ : s.val ≤ a.val + D
        · refine ⟨[], s, ys, by simp, ?_, h₁, h₂, ?_⟩
          · intro t ht
            simp at ht
          · simp [advance, h₁, h₂]
        · simp [advance, h₁, h₂] at hacc
      · have hacc' : (advance D a ys).accepted = true := by
          simpa [advance, h₁] using hacc
        obtain ⟨pre, s', post, hdecomp, hpre, has', hs'd, hrem⟩ :=
          ih htail hacc'
        have hslt : s.val < a.val := by omega
        refine ⟨s :: pre, s', post, ?_, ?_, has', hs'd, ?_⟩
        · simpa [hdecomp, List.cons_append]
        · intro t ht
          have ht' : t = s ∨ t ∈ pre := by simpa using ht
          rcases ht' with rfl | ht'
          · exact hslt
          · exact hpre t ht'
        · simpa [advance, h₁] using hrem

theorem feasible_drop_early {H D : ℕ} {x pre post : Trace H}
    (hpre : ∀ a ∈ x, ∀ p ∈ pre, p.val < a.val) :
    Feasible D x (pre ∪ post) ↔ Feasible D x post := by
  constructor
  · rintro ⟨f, hfi, hf⟩
    refine ⟨f, hfi, ?_⟩
    intro a
    have hpost : f a ∈ post := by
      rcases Finset.mem_union.mp (hf a).1 with hp | hp
      · have hlt := hpre a a.property (f a) hp
        exact False.elim ((Nat.not_lt_of_ge (hf a).2.1) hlt)
      · exact hp
    exact ⟨hpost, (hf a).2.1, (hf a).2.2⟩
  · rintro ⟨f, hfi, hf⟩
    refine ⟨f, hfi, ?_⟩
    intro a
    exact ⟨Finset.mem_union_right pre (hf a).1, (hf a).2.1, (hf a).2.2⟩

theorem toFinset_erase_cons_append_eq_union {H : ℕ} {pre post : List (Fin H)}
    {s : Fin H} (hpre : s ∉ pre) (hpost : s ∉ post) :
    (pre ++ s :: post).toFinset.erase s = pre.toFinset ∪ post.toFinset := by
  ext t
  simp [hpre, hpost]

theorem scan_empty_true_iff_feasible {H D : ℕ} (ys : List (Fin H)) :
    scanBool D [] ys = true ↔ Feasible D [].toFinset ys.toFinset := by
  constructor
  · intro _
    exact feasible_empty D ys.toFinset
  · intro _
    change (scan D [] ys).accepted = true
    rw [scan.eq_1]

theorem scan_cons_true_iff_feasible {H D : ℕ} {a : Fin H} {xs ys : List (Fin H)}
    (ih : ∀ ys : List (Fin H),
      xs.Pairwise (fun u v => u < v) →
      ys.Pairwise (fun u v => u < v) →
      (scanBool D xs ys = true ↔ Feasible D xs.toFinset ys.toFinset))
    (hxs : (a :: xs).Pairwise (fun u v => u < v))
    (hys : ys.Pairwise (fun u v => u < v)) :
    scanBool D (a :: xs) ys = true ↔
      Feasible D (a :: xs).toFinset ys.toFinset := by
      have hxtail : xs.Pairwise (fun u v => u < v) :=
        (List.pairwise_cons.mp hxs).2
      let r := advance D a ys
      by_cases hacc : r.accepted = true
      · obtain ⟨pre, s, post, hdecomp, hpre, has, hsd, hrem⟩ :=
          advance_success_spec hys (by simpa [r] using hacc)
        have hpost_suffix : post <:+ ys := by
          have hr_suf : r.remaining <:+ ys :=
            advance_remaining_subset (D := D) (a := a) (ys := ys)
          have hrem' : r.remaining = post := by simpa [r] using hrem
          rw [← hrem']
          exact hr_suf
        have hpost : post.Pairwise (fun u v => u < v) :=
          pairwise_of_suffix hys hpost_suffix
        have hpair : (pre ++ s :: post).Pairwise (fun u v => u < v) := by
          simpa [hdecomp] using hys
        have hs_post : ∀ t ∈ post, s < t := by
          intro t ht
          exact (List.pairwise_cons.mp
            (List.pairwise_append.mp hpair).2.1).1 t ht
        have hs_y : s ∈ ys.toFinset := by
          simp [hdecomp]
        let c : Trace H := candidates a ys.toFinset
        have hc : c.Nonempty := by
          refine ⟨s, ?_⟩
          exact Finset.mem_filter.mpr ⟨hs_y, has⟩
        have hs_c : s ∈ c := by
          exact Finset.mem_filter.mpr ⟨hs_y, has⟩
        have hs_min : c.min' hc = s := by
          apply (Finset.min'_eq_iff c hc s).mpr
          refine ⟨hs_c, ?_⟩
          intro t ht
          have ht_y : t ∈ ys.toFinset := (mem_candidates.mp ht).1
          have ht_cases : t = s ∨ t ∈ pre ∨ t ∈ post := by
            simpa [hdecomp] using ht_y
          rcases ht_cases with rfl | ht_pre | ht_post
          · exact le_rfl
          · have hta := (mem_candidates.mp ht).2
            have htp := hpre t ht_pre
            exact False.elim (by omega)
          · exact (hs_post t ht_post).le
        have hpre_not_s : s ∉ pre := by
          intro hsp
          have hlt := hpre s hsp
          exact (by omega)
        have hpost_not_s : s ∉ post := by
          intro hsp
          exact (hs_post s hsp).ne rfl
        have hyerase : ys.toFinset.erase s = pre.toFinset ∪ post.toFinset := by
          rw [hdecomp]
          exact toFinset_erase_cons_append_eq_union hpre_not_s hpost_not_s
        have hpre_tail : ∀ b ∈ xs.toFinset, ∀ p ∈ pre.toFinset, p.val < b.val := by
          intro b hb p hp
          have hb' : b ∈ xs := by simpa using hb
          have hp' : p ∈ pre := by simpa using hp
          have hab : a.val < b.val := Fin.lt_iff_val_lt_val.mp
            (SortedTrace.head_lt_of_mem hxs hb')
          have hpa := hpre p hp'
          omega
        have hdrop :
            Feasible D xs.toFinset (pre.toFinset ∪ post.toFinset) ↔
              Feasible D xs.toFinset post.toFinset :=
          feasible_drop_early hpre_tail
        let xfin : Trace H := (a :: xs).toFinset
        let yfin : Trace H := ys.toFinset
        have hx : xfin.Nonempty := by simp [xfin]
        have hamin : xfin.min' hx = a := by
          exact SortedTrace.head_min' hxs
        have hc0 : (candidates (xfin.min' hx) yfin).Nonempty := by
          rw [hamin]
          simpa [xfin, yfin, c] using hc
        have hs_min0 :
            (candidates (xfin.min' hx) yfin).min' hc0 = s := by
          apply (Finset.min'_eq_iff _ hc0 s).mpr
          constructor
          · rw [hamin]
            exact hs_c
          · intro t ht
            have ht_c : t ∈ c := by
              rw [hamin] at ht
              exact ht
            have hle : c.min' hc ≤ t := Finset.min'_le c t ht_c
            simpa [hs_min] using hle
        have hdeadline :
            ((candidates (xfin.min' hx) yfin).min' hc0).val ≤ a.val + D := by
          simpa [hs_min0] using hsd
        have hdeadline0 :
            ((candidates (xfin.min' hx) yfin).min' hc0).val ≤
              (xfin.min' hx).val + D := by
          simpa [hamin] using hdeadline
        have hfeas0 := feasible_erase_min_iff (D := D) (x := xfin) (y := yfin)
          hx hc0 hdeadline0
        have hscan :
            scanBool D (a :: xs) ys = scanBool D xs post := by
          simp [scanBool, scan, r, hacc, hrem]
        have hih :
            scanBool D xs post = true ↔
              Feasible D xs.toFinset post.toFinset := by
          have ihpost :
              xs.Pairwise (fun u v => u < v) →
                post.Pairwise (fun u v => u < v) →
                (scanBool D xs post = true ↔
                  Feasible D xs.toFinset post.toFinset) := ih post
          exact ihpost hxtail hpost
        have hxerase : xfin.erase (xfin.min' hx) = xs.toFinset := by
          rw [hamin]
          exact SortedTrace.erase_head_toFinset hxs
        have hymin :
            yfin.erase ((candidates (xfin.min' hx) yfin).min' hc0) =
              pre.toFinset ∪ post.toFinset := by
          rw [hs_min0]
          exact hyerase
        have hrest :
            Feasible D (xfin.erase (xfin.min' hx))
                (yfin.erase ((candidates (xfin.min' hx) yfin).min' hc0)) ↔
              Feasible D xs.toFinset (pre.toFinset ∪ post.toFinset) := by
          rw [hxerase, hymin]
        have hfeas :
            Feasible D xfin yfin ↔
              Feasible D xs.toFinset (pre.toFinset ∪ post.toFinset) :=
          hfeas0.trans hrest
        change scanBool D (a :: xs) ys = true ↔ Feasible D xfin yfin
        rw [hscan, hih]
        exact hdrop.symm.trans hfeas.symm
      · have hrfalse : r.accepted = false := Bool.eq_false_of_not_eq_true hacc
        have hscan_false : scanBool D (a :: xs) ys ≠ true := by
          simp [scanBool, scan, r, hacc, hrfalse]
        let xfin : Trace H := (a :: xs).toFinset
        let yfin : Trace H := ys.toFinset
        have hx : xfin.Nonempty := by simp [xfin]
        have hamin : xfin.min' hx = a := by
          exact SortedTrace.head_min' hxs
        let c : Trace H := candidates a yfin
        by_cases hc : c.Nonempty
        · have hc0 : (candidates (xfin.min' hx) yfin).Nonempty := by
            rw [hamin]
            simpa [c] using hc
          have hs_min0 :
              (candidates (xfin.min' hx) yfin).min' hc0 = c.min' hc := by
            apply (Finset.min'_eq_iff _ hc0 (c.min' hc)).mpr
            constructor
            · simpa [hamin, c] using (Finset.min'_mem c hc)
            · intro t ht
              have ht_c : t ∈ c := by simpa [hamin, c] using ht
              have hle : c.min' hc ≤ t := Finset.min'_le c t ht_c
              exact hle
          have hnot : ¬((candidates (xfin.min' hx) yfin).min' hc0).val ≤
              (xfin.min' hx).val + D := by
            intro hgood
            let s := c.min' hc
            have hs_mem_fin : s ∈ yfin :=
              (mem_candidates.mp (Finset.min'_mem c hc)).1
            have hs_mem : s ∈ ys := by simpa [yfin] using hs_mem_fin
            have hs_arr : a.val ≤ s.val :=
              (mem_candidates.mp (Finset.min'_mem c hc)).2
            have hgood_a :
                ((candidates (xfin.min' hx) yfin).min' hc0).val ≤ a.val + D := by
              simpa [hamin] using hgood
            have hs_dead : s.val ≤ a.val + D := by
              simpa [s, hs_min0] using hgood_a
            have hex : ∃ t ∈ ys, a.val ≤ t.val ∧ t.val ≤ a.val + D :=
              ⟨s, hs_mem, hs_arr, hs_dead⟩
            exact hacc ((advance_accepts_iff_exists hys).mpr hex)
          have hnf : ¬Feasible D xfin yfin := by
            intro hfeas
            have hnf' := not_feasible_of_greedy_deadline
              (D := D) (x := xfin) (y := yfin) hx
              hc0
              hnot
            exact hnf' hfeas
          change scanBool D (a :: xs) ys = true ↔ Feasible D xfin yfin
          exact iff_of_false hscan_false hnf
        · have hnf : ¬Feasible D xfin yfin := by
            intro hfeas
            have hc0 := candidates_nonempty_of_feasible
              (D := D) (x := xfin) (y := yfin) hx hfeas
            rw [hamin] at hc0
            exact hc (by simpa [c] using hc0)
          change scanBool D (a :: xs) ys = true ↔ Feasible D xfin yfin
          exact iff_of_false hscan_false hnf
    

theorem scan_true_iff_feasible_aux {H D : ℕ} :
    ∀ (xs ys : List (Fin H)),
      xs.Pairwise (fun u v => u < v) →
      ys.Pairwise (fun u v => u < v) →
      (scanBool D xs ys = true ↔ Feasible D xs.toFinset ys.toFinset) := by
  intro xs
  exact List.rec (motive := fun xs =>
      ∀ ys : List (Fin H),
        xs.Pairwise (fun u v => u < v) →
        ys.Pairwise (fun u v => u < v) →
        (scanBool D xs ys = true ↔ Feasible D xs.toFinset ys.toFinset))
    (fun (ys : List (Fin H))
        (_ : ([] : List (Fin H)).Pairwise (fun u v => u < v))
        (_ : ys.Pairwise (fun u v => u < v)) => by
      exact @scan_empty_true_iff_feasible H D ys)
    (fun (a : Fin H) (xs : List (Fin H))
        (ih : ∀ ys : List (Fin H),
          xs.Pairwise (fun u v => u < v) →
          ys.Pairwise (fun u v => u < v) →
          (scanBool D xs ys = true ↔ Feasible D xs.toFinset ys.toFinset))
        (ys : List (Fin H))
        (hxs : (a :: xs).Pairwise (fun u v => u < v))
        (hys : ys.Pairwise (fun u v => u < v)) =>
      scan_cons_true_iff_feasible ih hxs hys)
    xs

theorem scan_true_iff_feasible {H D : ℕ} (x y : SortedTrace H) :
    scanBool D x.slots y.slots = true ↔ Feasible D x.toTrace y.toTrace := by
  change scanBool D x.slots y.slots = true ↔
    Feasible D x.slots.toFinset y.slots.toFinset
  exact @scan_true_iff_feasible_aux H D x.slots y.slots x.sorted y.sorted

/-- Enumerate the horizon in increasing order and retain the slots in `x`.

This bounded enumeration is deliberately structural: unlike `Finset.sort`, it
reduces in the kernel on concrete finite traces. -/
def fastSortedSlots {H : ℕ} (x : Trace H) : List (Fin H) :=
  (List.finRange H).filter (fun a => a ∈ x)

theorem fastSortedSlots_pairwise {H : ℕ} (x : Trace H) :
    (fastSortedSlots x).Pairwise (fun a b => a < b) := by
  unfold fastSortedSlots
  apply List.pairwise_filter.mpr
  have hbase : (List.finRange H).Pairwise (fun a b => a < b) := by
    change (List.ofFn (fun i : Fin H => i)).Pairwise (fun a b => a < b)
    rw [List.pairwise_ofFn]
    intro i j hij
    exact hij
  exact hbase.imp (fun hab _ _ => hab)

@[simp] theorem fastSortedSlots_toTrace {H : ℕ} (x : Trace H) :
    (fastSortedSlots x).toFinset = x := by
  unfold fastSortedSlots
  simp only [List.toFinset_filter, List.toFinset_finRange]
  ext a
  simp

/-- The executable matcher for arbitrary finite traces.  The bounded horizon
enumeration is sorted once, then `scan` advances the two list pointers
monotonically. -/
def fastSortedTrace {H : ℕ} (x : Trace H) : SortedTrace H :=
  ⟨fastSortedSlots x, fastSortedSlots_pairwise x⟩

def fastMatchRun {H D : ℕ} (x y : Trace H) : ScanResult H :=
  scan D (fastSortedTrace x).slots (fastSortedTrace y).slots

def fastMatch {H D : ℕ} (x y : Trace H) : Bool :=
  (fastMatchRun (D := D) x y).accepted

theorem fastMatch_iff_feasible {H D : ℕ} (x y : Trace H) :
    fastMatch (D := D) x y = true ↔ Feasible D x y := by
  have h := scan_true_iff_feasible (D := D) (fastSortedTrace x) (fastSortedTrace y)
  simpa [fastMatch, fastMatchRun, scanBool, fastSortedTrace, SortedTrace.toTrace,
    Finset.sort_toFinset] using h

theorem fastMatch_ops_le_five_mul_H {H D : ℕ} (x y : Trace H)
    (hx : x.card ≤ H) (hy : y.card ≤ H) :
    (fastMatchRun (D := D) x y).ops ≤ 5 * H := by
  have hxl : (fastSortedSlots x).length ≤ H := by
    simpa [fastSortedSlots] using
      (List.length_filter_le (fun a : Fin H => a ∈ x) (List.finRange H))
  have hyl : (fastSortedSlots y).length ≤ H := by
    simpa [fastSortedSlots] using
      (List.length_filter_le (fun a : Fin H => a ∈ y) (List.finRange H))
  exact scan_ops_le_five_mul_H _ _ hxl hyl

end TrafficShaping
