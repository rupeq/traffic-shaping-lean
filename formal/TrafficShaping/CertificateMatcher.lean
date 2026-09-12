import TrafficShaping.MatchingComplexity

/-!
# Kernel-reducible matcher for rational certificate checks

`greedy` is the finite-set specification and `scan` is the costed matcher.
The certificate check below uses a fuelled wrapper with the same scan
behaviour and structural recursion on horizon fuel, so closed `decide` proofs
reduce without `native_decide`.
-/

namespace TrafficShaping

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

def certificateTraceList {H : ℕ} (x : Trace H) : List (Fin H) :=
  (List.finRange H).filter (fun a => decide (a ∈ x))

def certificateSortedTrace {H : ℕ} (x : Trace H) : SortedTrace H :=
  ⟨certificateTraceList x,
    (List.sortedLT_finRange H).pairwise.filter
      (fun a => decide (a ∈ x))⟩

def certificateAdvanceFuel {H D : ℕ} (a : Fin H) :
    List (Fin H) → Option (List (Fin H))
  | [] => none
  | s :: ys =>
      if h₁ : a.val ≤ s.val then
        if h₂ : s.val ≤ a.val + D then some ys else none
      else certificateAdvanceFuel (D := D) a ys

def certificateScanFuel {H D : ℕ} :
    ℕ → List (Fin H) → List (Fin H) → Bool
  | 0, [], _ => true
  | 0, _ :: _, _ => false
  | fuel + 1, [], _ => true
  | fuel + 1, a :: xs, ys =>
      match certificateAdvanceFuel (D := D) a ys with
      | some rem => certificateScanFuel (D := D) fuel xs rem
      | none => false

lemma certificateAdvanceFuel_spec {H D : ℕ} (a : Fin H)
    (ys : List (Fin H)) :
    (certificateAdvanceFuel (D := D) a ys).isSome =
        (advance D a ys).accepted := by
  induction ys with
  | nil => simp [certificateAdvanceFuel, advance]
  | cons s ys ih =>
      by_cases h₁ : a.val ≤ s.val
      · by_cases h₂ : s.val ≤ a.val + D
        · simp [certificateAdvanceFuel, advance, h₁, h₂]
        · simp [certificateAdvanceFuel, advance, h₁, h₂]
      · simp [certificateAdvanceFuel, advance, h₁, ih]

lemma certificateAdvanceFuel_spec_full {H D : ℕ} (a : Fin H)
    (ys : List (Fin H)) (rem : List (Fin H)) :
    certificateAdvanceFuel (D := D) a ys = some rem ↔
      (advance D a ys).accepted = true ∧
        (advance D a ys).remaining = rem := by
  induction ys with
  | nil => simp [certificateAdvanceFuel, advance]
  | cons s ys ih =>
      by_cases h₁ : a.val ≤ s.val
      · by_cases h₂ : s.val ≤ a.val + D
        · simp [certificateAdvanceFuel, advance, h₁, h₂]
        · simp [certificateAdvanceFuel, advance, h₁, h₂]
      · simp [certificateAdvanceFuel, advance, h₁, ih]

lemma certificateScanFuel_eq_scanBool {H D : ℕ} :
    ∀ (fuel : ℕ) (xs ys : List (Fin H)), xs.length ≤ fuel →
      certificateScanFuel (D := D) fuel xs ys = scanBool D xs ys := by
  intro fuel
  induction fuel with
  | zero =>
      intro xs ys hlen
      have hnil : xs = [] := by simpa using hlen
      subst hnil
      simp [certificateScanFuel, scanBool, scan]
  | succ fuel ih =>
      intro xs
      cases xs with
      | nil =>
          intro ys _
          simp [certificateScanFuel, scanBool, scan]
      | cons a xs =>
          intro ys hlen
          have hxs : xs.length ≤ fuel := by simp at hlen; omega
          let r := advance D a ys
          cases ha : certificateAdvanceFuel (D := D) a ys with
          | none =>
              have hr : r.accepted = false := by
                have hs := certificateAdvanceFuel_spec (D := D) a ys
                simpa [ha, r] using hs
              simp [certificateScanFuel, scanBool, scan, r, ha, hr]
          | some rem =>
              have hfull :=
                (certificateAdvanceFuel_spec_full (D := D) a ys rem).mp ha
              have hr : r.accepted = true := by simpa [r] using hfull.1
              have hrem : r.remaining = rem := by simpa [r] using hfull.2
              simp [certificateScanFuel, scanBool, scan, r, ha, hr, hrem,
                ih xs rem hxs]

@[simp] theorem certificateSortedTrace_toTrace {H : ℕ} (x : Trace H) :
    (certificateSortedTrace x).toTrace = x := by
  simp [certificateSortedTrace, certificateTraceList, SortedTrace.toTrace]

lemma certificateSortedTrace_length_le {H : ℕ} (x : Trace H) :
    (certificateSortedTrace x).slots.length ≤ H := by
  simpa [certificateSortedTrace, certificateTraceList] using
    (List.length_filter_le (fun a : Fin H => decide (a ∈ x))
      (List.finRange H))

def certificateScanFeasible (D : ℕ) (x y : Trace H) : Bool :=
  certificateScanFuel (D := D) H
    (certificateSortedTrace x).slots (certificateSortedTrace y).slots

theorem certificateScanFeasible_true_iff {H D : ℕ} (x y : Trace H) :
    certificateScanFeasible D x y = true ↔ Feasible D x y := by
  unfold certificateScanFeasible
  rw [certificateScanFuel_eq_scanBool (D := D) H _ _
    (certificateSortedTrace_length_le x)]
  rw [scan_true_iff_feasible]
  simp [certificateSortedTrace_toTrace]

end TrafficShaping
