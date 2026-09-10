import Mathlib

/-! The finite public-session model. Traces are the sets of their one-slots. -/

namespace TrafficShaping

abbrev Trace (H : ℕ) := Finset (Fin H)

abbrev Input (H m : ℕ) := {x : Trace H // x.card ≤ m}

abbrev FullInput (H m : ℕ) := {x : Trace H // x.card = m}

/-- A trace prefix, represented in the original slot type with no later ones. -/
def tracePrefix {H : ℕ} (t : ℕ) (x : Trace H) : Trace H :=
  x.filter (fun a => a.val < t)

/-- Terminal service slots. -/
def terminal (H m : ℕ) : Trace H :=
  Finset.univ.filter (fun a => H - m ≤ a.val)

/-- Injective assignment of every real packet to an available service slot.
The codomain `Fin H` enforces service before the public session ends. -/
def Feasible {H : ℕ} (D : ℕ) (x y : Trace H) : Prop :=
  ∃ f : {a : Fin H // a ∈ x} → Fin H,
    Function.Injective f ∧
    ∀ a, f a ∈ y ∧ a.val.val ≤ (f a).val ∧ (f a).val ≤ a.val.val + D

abbrev OffSchedule (H B : ℕ) := {y : Trace H // y.card = B}

abbrev OnSchedule (H m B : ℕ) :=
  {y : Trace H // y.card = B ∧ terminal H m ⊆ y}

/-- Empty input is admissible for every nonnegative workload bound. -/
def emptyInput (H m : ℕ) : Input H m := ⟨∅, by simp⟩

@[simp] theorem prefix_empty (H t : ℕ) : tracePrefix t (∅ : Trace H) = ∅ := by
  simp [tracePrefix]

@[simp] theorem mem_prefix {H t : ℕ} {x : Trace H} {a : Fin H} :
    a ∈ tracePrefix t x ↔ a ∈ x ∧ a.val < t := by
  simp [tracePrefix]

@[simp] theorem mem_terminal {H m : ℕ} {a : Fin H} :
    a ∈ terminal H m ↔ H - m ≤ a.val := by
  simp [terminal]

@[simp] theorem prefix_horizon {H : ℕ} (x : Trace H) : tracePrefix H x = x := by
  ext a
  simp [a.isLt]

theorem feasible_self {H : ℕ} (D : ℕ) (x : Trace H) : Feasible D x x := by
  refine ⟨Subtype.val, Subtype.val_injective, ?_⟩
  intro a
  exact ⟨a.property, le_rfl, Nat.le_add_right _ _⟩

theorem Feasible.mono_output {H D : ℕ} {x y z : Trace H}
    (h : Feasible D x y) (hyz : y ⊆ z) : Feasible D x z := by
  obtain ⟨f, hi, hf⟩ := h
  exact ⟨f, hi, fun a => ⟨hyz (hf a).1, (hf a).2⟩⟩

theorem Feasible.mono_input {H D : ℕ} {x z y : Trace H}
    (h : Feasible D x y) (hzx : z ⊆ x) : Feasible D z y := by
  obtain ⟨f, hi, hf⟩ := h
  let emb : {a : Fin H // a ∈ z} → {a : Fin H // a ∈ x} :=
    fun a => ⟨a.val, hzx a.property⟩
  refine ⟨f ∘ emb, ?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    exact congrArg (fun c : {a : Fin H // a ∈ x} => c.val) (hi hab)
  · intro a
    exact hf (emb a)

theorem feasible_empty {H : ℕ} (D : ℕ) (y : Trace H) : Feasible D ∅ y :=
  (feasible_self D ∅).mono_output (Finset.empty_subset y)

theorem Feasible.card_le {H D : ℕ} {x y : Trace H}
    (h : Feasible D x y) : x.card ≤ y.card := by
  obtain ⟨f, hi, hf⟩ := h
  let g : {a : Fin H // a ∈ x} → {a : Fin H // a ∈ y} :=
    fun a => ⟨f a, (hf a).1⟩
  have hg : Function.Injective g := by
    intro a b hab
    apply hi
    exact congrArg Subtype.val hab
  simpa using Fintype.card_le_of_injective g hg

end TrafficShaping
