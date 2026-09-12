import TrafficShaping.CertificatePartitions
import TrafficShaping.CertificateOnEnumeration

-- Elaborate these expensive closed certificates sequentially.
set_option Elab.async false

namespace TrafficShaping

open scoped BigOperators

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

/- Each theorem replays one independently checked rational primal/dual
   certificate over the complete finite input and schedule types. -/

theorem certificate_value_off_H8_m2_B2_D1 :
    offGameValue 8 2 2 1 (by decide +kernel) (by decide +kernel) = (1/10 : ℝ) := by
  let schedules : Finset (OffSchedule 8 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : OffSchedule 8 2), 1),
      ((⟨{1, 3}, by decide +kernel⟩ : OffSchedule 8 2), 1),
      ((⟨{1, 5}, by decide +kernel⟩ : OffSchedule 8 2), 1),
      ((⟨{1, 7}, by decide +kernel⟩ : OffSchedule 8 2), 1),
      ((⟨{2, 4}, by decide +kernel⟩ : OffSchedule 8 2), 1),
      ((⟨{3, 6}, by decide +kernel⟩ : OffSchedule 8 2), 1),
      ((⟨{3, 7}, by decide +kernel⟩ : OffSchedule 8 2), 1),
      ((⟨{4, 5}, by decide +kernel⟩ : OffSchedule 8 2), 1),
      ((⟨{5, 7}, by decide +kernel⟩ : OffSchedule 8 2), 1),
      ((⟨{6, 7}, by decide +kernel⟩ : OffSchedule 8 2), 1) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{0, 3}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{0, 5}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{0, 7}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{2, 3}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{2, 5}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{2, 7}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{4, 5}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{4, 7}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 8 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 10 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 10 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := offScheduleEnum 8 2
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 8 2
  have h := off_certificate_value (H := 8) (m := 2) (B := 2) (D := 1)
    (by decide +kernel) (by decide +kernel) schedules 10 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H8_m2_B3_D1 :
    offGameValue 8 2 3 1 (by decide +kernel) (by decide +kernel) = (3/10 : ℝ) := by
  let schedules : Finset (OffSchedule 8 3 × ℕ) :=
    { ((⟨{0, 2, 7}, by decide +kernel⟩ : OffSchedule 8 3), 5),
      ((⟨{0, 3, 5}, by decide +kernel⟩ : OffSchedule 8 3), 1),
      ((⟨{0, 4, 5}, by decide +kernel⟩ : OffSchedule 8 3), 1),
      ((⟨{0, 6, 7}, by decide +kernel⟩ : OffSchedule 8 3), 2),
      ((⟨{1, 2, 4}, by decide +kernel⟩ : OffSchedule 8 3), 5),
      ((⟨{1, 2, 6}, by decide +kernel⟩ : OffSchedule 8 3), 2),
      ((⟨{1, 3, 5}, by decide +kernel⟩ : OffSchedule 8 3), 3),
      ((⟨{1, 3, 7}, by decide +kernel⟩ : OffSchedule 8 3), 2),
      ((⟨{1, 5, 7}, by decide +kernel⟩ : OffSchedule 8 3), 2),
      ((⟨{1, 6, 7}, by decide +kernel⟩ : OffSchedule 8 3), 1),
      ((⟨{2, 4, 5}, by decide +kernel⟩ : OffSchedule 8 3), 4),
      ((⟨{2, 6, 7}, by decide +kernel⟩ : OffSchedule 8 3), 2),
      ((⟨{3, 4, 7}, by decide +kernel⟩ : OffSchedule 8 3), 3),
      ((⟨{4, 6, 7}, by decide +kernel⟩ : OffSchedule 8 3), 7) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 8 2), 4),
      ((⟨{0, 3}, by decide +kernel⟩ : FullInput 8 2), 4),
      ((⟨{0, 5}, by decide +kernel⟩ : FullInput 8 2), 4),
      ((⟨{0, 7}, by decide +kernel⟩ : FullInput 8 2), 4),
      ((⟨{2, 3}, by decide +kernel⟩ : FullInput 8 2), 4),
      ((⟨{2, 5}, by decide +kernel⟩ : FullInput 8 2), 4),
      ((⟨{2, 7}, by decide +kernel⟩ : FullInput 8 2), 4),
      ((⟨{4, 5}, by decide +kernel⟩ : FullInput 8 2), 4),
      ((⟨{4, 7}, by decide +kernel⟩ : FullInput 8 2), 4),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 8 2), 4) }
  have hs : (∑ p ∈ schedules, p.2) = 40 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 40 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := offScheduleEnum 8 3
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 8 3
  have h := off_certificate_value (H := 8) (m := 2) (B := 3) (D := 1)
    (by decide +kernel) (by decide +kernel) schedules 40 hs (by decide +kernel) 12 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H8_m2_B4_D1 :
    offGameValue 8 2 4 1 (by decide +kernel) (by decide +kernel) = (5/9 : ℝ) := by
  let schedules : Finset (OffSchedule 8 4 × ℕ) :=
    { ((⟨{0, 1, 6, 7}, by decide +kernel⟩ : OffSchedule 8 4), 1),
      ((⟨{1, 2, 4, 5}, by decide +kernel⟩ : OffSchedule 8 4), 2),
      ((⟨{1, 2, 4, 7}, by decide +kernel⟩ : OffSchedule 8 4), 1),
      ((⟨{1, 2, 6, 7}, by decide +kernel⟩ : OffSchedule 8 4), 1),
      ((⟨{1, 3, 4, 7}, by decide +kernel⟩ : OffSchedule 8 4), 1),
      ((⟨{1, 4, 6, 7}, by decide +kernel⟩ : OffSchedule 8 4), 1),
      ((⟨{3, 4, 6, 7}, by decide +kernel⟩ : OffSchedule 8 4), 1),
      ((⟨{3, 5, 6, 7}, by decide +kernel⟩ : OffSchedule 8 4), 1) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 8 2), 2),
      ((⟨{1, 3}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{1, 7}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 8 2), 2),
      ((⟨{3, 7}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 8 2), 2) }
  have hs : (∑ p ∈ schedules, p.2) = 9 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 9 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := offScheduleEnum 8 4
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 8 4
  have h := off_certificate_value (H := 8) (m := 2) (B := 4) (D := 1)
    (by decide +kernel) (by decide +kernel) schedules 9 hs (by decide +kernel) 5 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H8_m2_B5_D1 :
    offGameValue 8 2 5 1 (by decide +kernel) (by decide +kernel) = (2/3 : ℝ) := by
  let schedules : Finset (OffSchedule 8 5 × ℕ) :=
    { ((⟨{0, 1, 2, 3, 5}, by decide +kernel⟩ : OffSchedule 8 5), 1),
      ((⟨{0, 1, 3, 4, 7}, by decide +kernel⟩ : OffSchedule 8 5), 1),
      ((⟨{0, 2, 3, 6, 7}, by decide +kernel⟩ : OffSchedule 8 5), 1),
      ((⟨{0, 2, 4, 5, 7}, by decide +kernel⟩ : OffSchedule 8 5), 1),
      ((⟨{0, 3, 4, 6, 7}, by decide +kernel⟩ : OffSchedule 8 5), 1),
      ((⟨{1, 2, 5, 6, 7}, by decide +kernel⟩ : OffSchedule 8 5), 2),
      ((⟨{1, 4, 5, 6, 7}, by decide +kernel⟩ : OffSchedule 8 5), 1),
      ((⟨{2, 3, 4, 6, 7}, by decide +kernel⟩ : OffSchedule 8 5), 1) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 8 2), 3),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 8 2), 3),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 8 2), 3) }
  have hs : (∑ p ∈ schedules, p.2) = 9 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 9 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := offScheduleEnum 8 5
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 8 5
  have h := off_certificate_value (H := 8) (m := 2) (B := 5) (D := 1)
    (by decide +kernel) (by decide +kernel) schedules 9 hs (by decide +kernel) 6 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H8_m2_B6_D1 :
    offGameValue 8 2 6 1 (by decide +kernel) (by decide +kernel) = (1 : ℝ) := by
  let schedules : Finset (OffSchedule 8 6 × ℕ) :=
    { ((⟨{0, 1, 3, 4, 6, 7}, by decide +kernel⟩ : OffSchedule 8 6), 1) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 8 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := offScheduleEnum 8 6
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 8 6
  have h := off_certificate_value (H := 8) (m := 2) (B := 6) (D := 1)
    (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H8_m2_B2_D1 :
    onGameValue 8 2 2 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 8 2 2 × ℕ) :=
    { ((⟨{6, 7}, by decide +kernel, by decide +kernel⟩ : OnSchedule 8 2 2), 1) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 8 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := optimizedOnScheduleEnum 8 2 2 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 8) (m := 2) (B := 2) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H8_m2_B3_D1 :
    onGameValue 8 2 3 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 8 2 3 × ℕ) :=
    { ((⟨{0, 6, 7}, by decide +kernel, by decide +kernel⟩ : OnSchedule 8 2 3), 1) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 8 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := optimizedOnScheduleEnum 8 2 3 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 8) (m := 2) (B := 3) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H8_m2_B4_D1 :
    onGameValue 8 2 4 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1/3 : ℝ) := by
  let schedules : Finset (OnSchedule 8 2 4 × ℕ) :=
    { ((⟨{1, 2, 6, 7}, by decide +kernel, by decide +kernel⟩ : OnSchedule 8 2 4), 1),
      ((⟨{1, 4, 6, 7}, by decide +kernel, by decide +kernel⟩ : OnSchedule 8 2 4), 1),
      ((⟨{3, 4, 6, 7}, by decide +kernel, by decide +kernel⟩ : OnSchedule 8 2 4), 1) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{0, 3}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{2, 3}, by decide +kernel⟩ : FullInput 8 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 3 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 3 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := optimizedOnScheduleEnum 8 2 4 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 8) (m := 2) (B := 4) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 3 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H8_m2_B5_D1 :
    onGameValue 8 2 5 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1/2 : ℝ) := by
  let schedules : Finset (OnSchedule 8 2 5 × ℕ) :=
    { ((⟨{0, 2, 3, 6, 7}, by decide +kernel, by decide +kernel⟩ : OnSchedule 8 2 5), 1),
      ((⟨{1, 2, 5, 6, 7}, by decide +kernel, by decide +kernel⟩ : OnSchedule 8 2 5), 1),
      ((⟨{1, 3, 5, 6, 7}, by decide +kernel, by decide +kernel⟩ : OnSchedule 8 2 5), 1),
      ((⟨{3, 4, 5, 6, 7}, by decide +kernel, by decide +kernel⟩ : OnSchedule 8 2 5), 1) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 8 2), 2),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 8 2), 2) }
  have hs : (∑ p ∈ schedules, p.2) = 4 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 4 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := optimizedOnScheduleEnum 8 2 5 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 8) (m := 2) (B := 5) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 4 hs (by decide +kernel) 2 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H8_m2_B6_D1 :
    onGameValue 8 2 6 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1 : ℝ) := by
  let schedules : Finset (OnSchedule 8 2 6 × ℕ) :=
    { ((⟨{0, 1, 3, 4, 6, 7}, by decide +kernel, by decide +kernel⟩ : OnSchedule 8 2 6), 1) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 8 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := optimizedOnScheduleEnum 8 2 6 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 8) (m := 2) (B := 6) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H8_m2_B2_D2 :
    offGameValue 8 2 2 2 (by decide +kernel) (by decide +kernel) = (1/6 : ℝ) := by
  let schedules : Finset (OffSchedule 8 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : OffSchedule 8 2), 1),
      ((⟨{2, 4}, by decide +kernel⟩ : OffSchedule 8 2), 1),
      ((⟨{2, 7}, by decide +kernel⟩ : OffSchedule 8 2), 1),
      ((⟨{3, 6}, by decide +kernel⟩ : OffSchedule 8 2), 1),
      ((⟨{5, 7}, by decide +kernel⟩ : OffSchedule 8 2), 1),
      ((⟨{6, 7}, by decide +kernel⟩ : OffSchedule 8 2), 1) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{0, 4}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{0, 7}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{3, 7}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 8 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 6 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 6 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := offScheduleEnum 8 2
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 8 2
  have h := off_certificate_value (H := 8) (m := 2) (B := 2) (D := 2)
    (by decide +kernel) (by decide +kernel) schedules 6 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H8_m2_B3_D2 :
    offGameValue 8 2 3 2 (by decide +kernel) (by decide +kernel) = (1/2 : ℝ) := by
  let schedules : Finset (OffSchedule 8 3 × ℕ) :=
    { ((⟨{1, 3, 5}, by decide +kernel⟩ : OffSchedule 8 3), 1),
      ((⟨{2, 3, 7}, by decide +kernel⟩ : OffSchedule 8 3), 1),
      ((⟨{2, 6, 7}, by decide +kernel⟩ : OffSchedule 8 3), 1),
      ((⟨{4, 6, 7}, by decide +kernel⟩ : OffSchedule 8 3), 1) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{1, 3}, by decide +kernel⟩ : FullInput 8 2), 2),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 8 2), 2) }
  have hs : (∑ p ∈ schedules, p.2) = 4 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 4 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := offScheduleEnum 8 3
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 8 3
  have h := off_certificate_value (H := 8) (m := 2) (B := 3) (D := 2)
    (by decide +kernel) (by decide +kernel) schedules 4 hs (by decide +kernel) 2 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H8_m2_B4_D2 :
    offGameValue 8 2 4 2 (by decide +kernel) (by decide +kernel) = (1 : ℝ) := by
  let schedules : Finset (OffSchedule 8 4 × ℕ) :=
    { ((⟨{2, 3, 6, 7}, by decide +kernel⟩ : OffSchedule 8 4), 1) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 8 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := offScheduleEnum 8 4
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 8 4
  have h := off_certificate_value (H := 8) (m := 2) (B := 4) (D := 2)
    (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H8_m2_B2_D2 :
    onGameValue 8 2 2 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 8 2 2 × ℕ) :=
    { ((⟨{6, 7}, by decide +kernel, by decide +kernel⟩ : OnSchedule 8 2 2), 1) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 8 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := optimizedOnScheduleEnum 8 2 2 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 8) (m := 2) (B := 2) (D := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H8_m2_B3_D2 :
    onGameValue 8 2 3 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 8 2 3 × ℕ) :=
    { ((⟨{0, 6, 7}, by decide +kernel, by decide +kernel⟩ : OnSchedule 8 2 3), 1) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 8 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := optimizedOnScheduleEnum 8 2 3 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 8) (m := 2) (B := 3) (D := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H8_m2_B4_D2 :
    onGameValue 8 2 4 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1 : ℝ) := by
  let schedules : Finset (OnSchedule 8 2 4 × ℕ) :=
    { ((⟨{2, 3, 6, 7}, by decide +kernel, by decide +kernel⟩ : OnSchedule 8 2 4), 1) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 8 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := optimizedOnScheduleEnum 8 2 4 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 8) (m := 2) (B := 4) (D := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H8_m2_B2_D3 :
    offGameValue 8 2 2 3 (by decide +kernel) (by decide +kernel) = (1/3 : ℝ) := by
  let schedules : Finset (OffSchedule 8 2 × ℕ) :=
    { ((⟨{2, 4}, by decide +kernel⟩ : OffSchedule 8 2), 1),
      ((⟨{3, 7}, by decide +kernel⟩ : OffSchedule 8 2), 1),
      ((⟨{6, 7}, by decide +kernel⟩ : OffSchedule 8 2), 1) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{0, 3}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{1, 7}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{5, 6}, by decide +kernel⟩ : FullInput 8 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 3 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 3 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := offScheduleEnum 8 2
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 8 2
  have h := off_certificate_value (H := 8) (m := 2) (B := 2) (D := 3)
    (by decide +kernel) (by decide +kernel) schedules 3 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H8_m2_B3_D3 :
    offGameValue 8 2 3 3 (by decide +kernel) (by decide +kernel) = (1/2 : ℝ) := by
  let schedules : Finset (OffSchedule 8 3 × ℕ) :=
    { ((⟨{1, 6, 7}, by decide +kernel⟩ : OffSchedule 8 3), 1),
      ((⟨{2, 3, 7}, by decide +kernel⟩ : OffSchedule 8 3), 1) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{1, 2}, by decide +kernel⟩ : FullInput 8 2), 1),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 8 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 2 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 2 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := offScheduleEnum 8 3
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 8 3
  have h := off_certificate_value (H := 8) (m := 2) (B := 3) (D := 3)
    (by decide +kernel) (by decide +kernel) schedules 2 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H8_m2_B4_D3 :
    offGameValue 8 2 4 3 (by decide +kernel) (by decide +kernel) = (1 : ℝ) := by
  let schedules : Finset (OffSchedule 8 4 × ℕ) :=
    { ((⟨{1, 2, 6, 7}, by decide +kernel⟩ : OffSchedule 8 4), 1) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 8 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := offScheduleEnum 8 4
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 8 4
  have h := off_certificate_value (H := 8) (m := 2) (B := 4) (D := 3)
    (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H8_m2_B2_D3 :
    onGameValue 8 2 2 3 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 8 2 2 × ℕ) :=
    { ((⟨{6, 7}, by decide +kernel, by decide +kernel⟩ : OnSchedule 8 2 2), 1) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 8 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := optimizedOnScheduleEnum 8 2 2 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 8) (m := 2) (B := 2) (D := 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H8_m2_B3_D3 :
    onGameValue 8 2 3 3 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 8 2 3 × ℕ) :=
    { ((⟨{0, 6, 7}, by decide +kernel, by decide +kernel⟩ : OnSchedule 8 2 3), 1) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 8 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := optimizedOnScheduleEnum 8 2 3 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 8) (m := 2) (B := 3) (D := 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H8_m2_B4_D3 :
    onGameValue 8 2 4 3 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1 : ℝ) := by
  let schedules : Finset (OnSchedule 8 2 4 × ℕ) :=
    { ((⟨{1, 2, 6, 7}, by decide +kernel, by decide +kernel⟩ : OnSchedule 8 2 4), 1) }
  let inputs : Finset (FullInput 8 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 8 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 8 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 2
  let cols := optimizedOnScheduleEnum 8 2 4 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 8) (m := 2) (B := 4) (D := 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H12_m2_B2_D1 :
    offGameValue 12 2 2 1 (by decide +kernel) (by decide +kernel) = (1/21 : ℝ) := by
  let schedules : Finset (OffSchedule 12 2 × ℕ) :=
    { ((⟨{0, 2}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{0, 5}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{0, 7}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{1, 3}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{1, 9}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{1, 11}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{2, 4}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{2, 6}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{2, 8}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{3, 9}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{3, 11}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{4, 5}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{4, 7}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{4, 9}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{5, 11}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{6, 7}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{6, 9}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{7, 11}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{8, 9}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{9, 11}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{10, 11}, by decide +kernel⟩ : OffSchedule 12 2), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{0, 3}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{0, 5}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{0, 7}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{0, 9}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{0, 11}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{2, 3}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{2, 5}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{2, 7}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{2, 9}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{2, 11}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{4, 5}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{4, 7}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{4, 9}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{4, 11}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{6, 9}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{6, 11}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{8, 9}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{8, 11}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{10, 11}, by decide +kernel⟩ : FullInput 12 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 21 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 21 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := offScheduleEnum 12 2
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 12 2
  have h := off_certificate_value (H := 12) (m := 2) (B := 2) (D := 1)
    (by decide +kernel) (by decide +kernel) schedules 21 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H12_m2_B3_D1 :
    offGameValue 12 2 3 1 (by decide +kernel) (by decide +kernel) = (1/7 : ℝ) := by
  let schedules : Finset (OffSchedule 12 3 × ℕ) :=
    { ((⟨{0, 2, 9}, by decide +kernel⟩ : OffSchedule 12 3), 17),
      ((⟨{0, 2, 11}, by decide +kernel⟩ : OffSchedule 12 3), 15),
      ((⟨{1, 2, 4}, by decide +kernel⟩ : OffSchedule 12 3), 4),
      ((⟨{1, 2, 5}, by decide +kernel⟩ : OffSchedule 12 3), 18),
      ((⟨{1, 2, 8}, by decide +kernel⟩ : OffSchedule 12 3), 32),
      ((⟨{1, 2, 10}, by decide +kernel⟩ : OffSchedule 12 3), 4),
      ((⟨{1, 3, 7}, by decide +kernel⟩ : OffSchedule 12 3), 18),
      ((⟨{1, 3, 11}, by decide +kernel⟩ : OffSchedule 12 3), 14),
      ((⟨{1, 4, 6}, by decide +kernel⟩ : OffSchedule 12 3), 25),
      ((⟨{1, 4, 7}, by decide +kernel⟩ : OffSchedule 12 3), 14),
      ((⟨{1, 4, 9}, by decide +kernel⟩ : OffSchedule 12 3), 15),
      ((⟨{1, 5, 11}, by decide +kernel⟩ : OffSchedule 12 3), 14),
      ((⟨{1, 6, 8}, by decide +kernel⟩ : OffSchedule 12 3), 26),
      ((⟨{1, 6, 10}, by decide +kernel⟩ : OffSchedule 12 3), 7),
      ((⟨{1, 10, 11}, by decide +kernel⟩ : OffSchedule 12 3), 47),
      ((⟨{3, 4, 6}, by decide +kernel⟩ : OffSchedule 12 3), 30),
      ((⟨{3, 4, 9}, by decide +kernel⟩ : OffSchedule 12 3), 15),
      ((⟨{3, 4, 11}, by decide +kernel⟩ : OffSchedule 12 3), 41),
      ((⟨{3, 5, 7}, by decide +kernel⟩ : OffSchedule 12 3), 4),
      ((⟨{3, 6, 9}, by decide +kernel⟩ : OffSchedule 12 3), 18),
      ((⟨{3, 6, 11}, by decide +kernel⟩ : OffSchedule 12 3), 20),
      ((⟨{3, 8, 9}, by decide +kernel⟩ : OffSchedule 12 3), 36),
      ((⟨{4, 6, 7}, by decide +kernel⟩ : OffSchedule 12 3), 12),
      ((⟨{4, 6, 11}, by decide +kernel⟩ : OffSchedule 12 3), 3),
      ((⟨{4, 7, 11}, by decide +kernel⟩ : OffSchedule 12 3), 6),
      ((⟨{4, 9, 11}, by decide +kernel⟩ : OffSchedule 12 3), 6),
      ((⟨{5, 6, 11}, by decide +kernel⟩ : OffSchedule 12 3), 20),
      ((⟨{5, 7, 9}, by decide +kernel⟩ : OffSchedule 12 3), 54),
      ((⟨{6, 8, 10}, by decide +kernel⟩ : OffSchedule 12 3), 11),
      ((⟨{6, 8, 11}, by decide +kernel⟩ : OffSchedule 12 3), 41),
      ((⟨{8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 3), 43) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 30),
      ((⟨{0, 3}, by decide +kernel⟩ : FullInput 12 2), 30),
      ((⟨{0, 5}, by decide +kernel⟩ : FullInput 12 2), 30),
      ((⟨{0, 7}, by decide +kernel⟩ : FullInput 12 2), 30),
      ((⟨{0, 9}, by decide +kernel⟩ : FullInput 12 2), 30),
      ((⟨{0, 11}, by decide +kernel⟩ : FullInput 12 2), 30),
      ((⟨{2, 3}, by decide +kernel⟩ : FullInput 12 2), 30),
      ((⟨{2, 5}, by decide +kernel⟩ : FullInput 12 2), 30),
      ((⟨{2, 7}, by decide +kernel⟩ : FullInput 12 2), 30),
      ((⟨{2, 9}, by decide +kernel⟩ : FullInput 12 2), 30),
      ((⟨{2, 11}, by decide +kernel⟩ : FullInput 12 2), 30),
      ((⟨{4, 5}, by decide +kernel⟩ : FullInput 12 2), 30),
      ((⟨{4, 7}, by decide +kernel⟩ : FullInput 12 2), 30),
      ((⟨{4, 9}, by decide +kernel⟩ : FullInput 12 2), 30),
      ((⟨{4, 11}, by decide +kernel⟩ : FullInput 12 2), 30),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 12 2), 30),
      ((⟨{6, 9}, by decide +kernel⟩ : FullInput 12 2), 30),
      ((⟨{6, 11}, by decide +kernel⟩ : FullInput 12 2), 30),
      ((⟨{8, 9}, by decide +kernel⟩ : FullInput 12 2), 30),
      ((⟨{8, 11}, by decide +kernel⟩ : FullInput 12 2), 30),
      ((⟨{10, 11}, by decide +kernel⟩ : FullInput 12 2), 30) }
  have hs : (∑ p ∈ schedules, p.2) = 630 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 630 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := offScheduleEnum 12 3
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 12 3
  have h := off_certificate_value (H := 12) (m := 2) (B := 3) (D := 1)
    (by decide +kernel) (by decide +kernel) schedules 630 hs (by decide +kernel) 90 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 12) ∈ x.1) ?_ ?_
      ·
        decide +kernel
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 12) ∈ x.1) ?_ ?_
        ·
          decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 12) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H12_m2_B4_D1 :
    offGameValue 12 2 4 1 (by decide +kernel) (by decide +kernel) = (245/872 : ℝ) := by
  let schedules : Finset (OffSchedule 12 4 × ℕ) :=
    { ((⟨{0, 2, 6, 7}, by decide +kernel⟩ : OffSchedule 12 4), 216),
      ((⟨{1, 2, 4, 5}, by decide +kernel⟩ : OffSchedule 12 4), 576),
      ((⟨{1, 2, 4, 6}, by decide +kernel⟩ : OffSchedule 12 4), 504),
      ((⟨{1, 2, 4, 9}, by decide +kernel⟩ : OffSchedule 12 4), 1008),
      ((⟨{1, 2, 4, 11}, by decide +kernel⟩ : OffSchedule 12 4), 1632),
      ((⟨{1, 2, 6, 7}, by decide +kernel⟩ : OffSchedule 12 4), 288),
      ((⟨{1, 2, 6, 11}, by decide +kernel⟩ : OffSchedule 12 4), 432),
      ((⟨{1, 2, 7, 8}, by decide +kernel⟩ : OffSchedule 12 4), 360),
      ((⟨{1, 2, 7, 9}, by decide +kernel⟩ : OffSchedule 12 4), 144),
      ((⟨{1, 2, 10, 11}, by decide +kernel⟩ : OffSchedule 12 4), 720),
      ((⟨{1, 3, 7, 9}, by decide +kernel⟩ : OffSchedule 12 4), 216),
      ((⟨{1, 4, 5, 9}, by decide +kernel⟩ : OffSchedule 12 4), 144),
      ((⟨{1, 4, 6, 7}, by decide +kernel⟩ : OffSchedule 12 4), 648),
      ((⟨{1, 4, 6, 11}, by decide +kernel⟩ : OffSchedule 12 4), 792),
      ((⟨{1, 4, 8, 9}, by decide +kernel⟩ : OffSchedule 12 4), 360),
      ((⟨{1, 5, 7, 9}, by decide +kernel⟩ : OffSchedule 12 4), 600),
      ((⟨{1, 6, 8, 9}, by decide +kernel⟩ : OffSchedule 12 4), 936),
      ((⟨{1, 6, 8, 11}, by decide +kernel⟩ : OffSchedule 12 4), 552),
      ((⟨{1, 6, 10, 11}, by decide +kernel⟩ : OffSchedule 12 4), 192),
      ((⟨{1, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 4), 1560),
      ((⟨{3, 4, 6, 7}, by decide +kernel⟩ : OffSchedule 12 4), 504),
      ((⟨{3, 4, 6, 11}, by decide +kernel⟩ : OffSchedule 12 4), 720),
      ((⟨{3, 4, 8, 9}, by decide +kernel⟩ : OffSchedule 12 4), 576),
      ((⟨{3, 4, 8, 11}, by decide +kernel⟩ : OffSchedule 12 4), 360),
      ((⟨{3, 5, 6, 11}, by decide +kernel⟩ : OffSchedule 12 4), 288),
      ((⟨{3, 5, 7, 9}, by decide +kernel⟩ : OffSchedule 12 4), 1848),
      ((⟨{3, 5, 7, 11}, by decide +kernel⟩ : OffSchedule 12 4), 144),
      ((⟨{3, 5, 9, 11}, by decide +kernel⟩ : OffSchedule 12 4), 144),
      ((⟨{3, 5, 10, 11}, by decide +kernel⟩ : OffSchedule 12 4), 216),
      ((⟨{3, 7, 8, 11}, by decide +kernel⟩ : OffSchedule 12 4), 216),
      ((⟨{3, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 4), 1008),
      ((⟨{4, 5, 10, 11}, by decide +kernel⟩ : OffSchedule 12 4), 360),
      ((⟨{5, 6, 8, 9}, by decide +kernel⟩ : OffSchedule 12 4), 120),
      ((⟨{5, 6, 8, 11}, by decide +kernel⟩ : OffSchedule 12 4), 720),
      ((⟨{5, 6, 10, 11}, by decide +kernel⟩ : OffSchedule 12 4), 504),
      ((⟨{6, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 4), 816),
      ((⟨{7, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 4), 504) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 1677),
      ((⟨{0, 3}, by decide +kernel⟩ : FullInput 12 2), 849),
      ((⟨{0, 5}, by decide +kernel⟩ : FullInput 12 2), 133),
      ((⟨{0, 6}, by decide +kernel⟩ : FullInput 12 2), 199),
      ((⟨{0, 7}, by decide +kernel⟩ : FullInput 12 2), 425),
      ((⟨{0, 8}, by decide +kernel⟩ : FullInput 12 2), 271),
      ((⟨{0, 9}, by decide +kernel⟩ : FullInput 12 2), 48),
      ((⟨{0, 11}, by decide +kernel⟩ : FullInput 12 2), 864),
      ((⟨{1, 3}, by decide +kernel⟩ : FullInput 12 2), 45),
      ((⟨{1, 5}, by decide +kernel⟩ : FullInput 12 2), 369),
      ((⟨{1, 6}, by decide +kernel⟩ : FullInput 12 2), 408),
      ((⟨{1, 7}, by decide +kernel⟩ : FullInput 12 2), 114),
      ((⟨{1, 9}, by decide +kernel⟩ : FullInput 12 2), 777),
      ((⟨{2, 3}, by decide +kernel⟩ : FullInput 12 2), 828),
      ((⟨{2, 5}, by decide +kernel⟩ : FullInput 12 2), 76),
      ((⟨{2, 6}, by decide +kernel⟩ : FullInput 12 2), 184),
      ((⟨{2, 7}, by decide +kernel⟩ : FullInput 12 2), 518),
      ((⟨{2, 8}, by decide +kernel⟩ : FullInput 12 2), 199),
      ((⟨{2, 9}, by decide +kernel⟩ : FullInput 12 2), 48),
      ((⟨{2, 10}, by decide +kernel⟩ : FullInput 12 2), 843),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 12 2), 936),
      ((⟨{3, 6}, by decide +kernel⟩ : FullInput 12 2), 145),
      ((⟨{3, 8}, by decide +kernel⟩ : FullInput 12 2), 385),
      ((⟨{3, 9}, by decide +kernel⟩ : FullInput 12 2), 253),
      ((⟨{3, 11}, by decide +kernel⟩ : FullInput 12 2), 253),
      ((⟨{4, 5}, by decide +kernel⟩ : FullInput 12 2), 967),
      ((⟨{4, 7}, by decide +kernel⟩ : FullInput 12 2), 449),
      ((⟨{4, 8}, by decide +kernel⟩ : FullInput 12 2), 18),
      ((⟨{4, 9}, by decide +kernel⟩ : FullInput 12 2), 482),
      ((⟨{4, 11}, by decide +kernel⟩ : FullInput 12 2), 521),
      ((⟨{5, 6}, by decide +kernel⟩ : FullInput 12 2), 828),
      ((⟨{5, 8}, by decide +kernel⟩ : FullInput 12 2), 91),
      ((⟨{5, 9}, by decide +kernel⟩ : FullInput 12 2), 256),
      ((⟨{5, 11}, by decide +kernel⟩ : FullInput 12 2), 589),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 12 2), 949),
      ((⟨{6, 9}, by decide +kernel⟩ : FullInput 12 2), 76),
      ((⟨{6, 11}, by decide +kernel⟩ : FullInput 12 2), 538),
      ((⟨{7, 8}, by decide +kernel⟩ : FullInput 12 2), 936),
      ((⟨{8, 9}, by decide +kernel⟩ : FullInput 12 2), 828),
      ((⟨{8, 11}, by decide +kernel⟩ : FullInput 12 2), 930),
      ((⟨{10, 11}, by decide +kernel⟩ : FullInput 12 2), 1623) }
  have hs : (∑ p ∈ schedules, p.2) = 20928 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 20928 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := offScheduleEnum 12 4
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 12 4
  have h := off_certificate_value (H := 12) (m := 2) (B := 4) (D := 1)
    (by decide +kernel) (by decide +kernel) schedules 20928 hs (by decide +kernel) 5880 inputs hi
    rows hrows (by
      refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 12) ∈ x.1) ?_ ?_
      ·
        decide +kernel
      ·
        decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 12) ∈ x.1) ?_ ?_
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 12) ∈ x.1) ?_ ?_
        ·
          decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 12) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 12) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 12) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 12) ∈ x.1) ?_ ?_
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 12) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 12) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 12) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 12) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 12) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 12) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 12) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 12) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 12) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H12_m2_B5_D1 :
    offGameValue 12 2 5 1 (by decide +kernel) (by decide +kernel) = (49/114 : ℝ) := by
  let schedules : Finset (OffSchedule 12 5 × ℕ) :=
    { ((⟨{0, 2, 3, 5, 6}, by decide +kernel⟩ : OffSchedule 12 5), 78),
      ((⟨{0, 2, 4, 10, 11}, by decide +kernel⟩ : OffSchedule 12 5), 72),
      ((⟨{1, 2, 4, 5, 7}, by decide +kernel⟩ : OffSchedule 12 5), 112),
      ((⟨{1, 2, 4, 5, 9}, by decide +kernel⟩ : OffSchedule 12 5), 40),
      ((⟨{1, 2, 4, 5, 11}, by decide +kernel⟩ : OffSchedule 12 5), 142),
      ((⟨{1, 2, 4, 6, 11}, by decide +kernel⟩ : OffSchedule 12 5), 456),
      ((⟨{1, 2, 4, 7, 8}, by decide +kernel⟩ : OffSchedule 12 5), 108),
      ((⟨{1, 2, 4, 8, 9}, by decide +kernel⟩ : OffSchedule 12 5), 162),
      ((⟨{1, 2, 4, 8, 11}, by decide +kernel⟩ : OffSchedule 12 5), 24),
      ((⟨{1, 2, 4, 9, 11}, by decide +kernel⟩ : OffSchedule 12 5), 72),
      ((⟨{1, 2, 4, 10, 11}, by decide +kernel⟩ : OffSchedule 12 5), 96),
      ((⟨{1, 2, 6, 7, 9}, by decide +kernel⟩ : OffSchedule 12 5), 174),
      ((⟨{1, 2, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 5), 228),
      ((⟨{1, 3, 5, 7, 9}, by decide +kernel⟩ : OffSchedule 12 5), 36),
      ((⟨{1, 3, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 5), 36),
      ((⟨{1, 4, 5, 7, 9}, by decide +kernel⟩ : OffSchedule 12 5), 246),
      ((⟨{1, 4, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 5), 84),
      ((⟨{1, 5, 7, 8, 11}, by decide +kernel⟩ : OffSchedule 12 5), 36),
      ((⟨{1, 6, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 5), 444),
      ((⟨{1, 7, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 5), 74),
      ((⟨{3, 4, 6, 7, 9}, by decide +kernel⟩ : OffSchedule 12 5), 168),
      ((⟨{3, 4, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 5), 234),
      ((⟨{3, 5, 6, 8, 9}, by decide +kernel⟩ : OffSchedule 12 5), 228),
      ((⟨{3, 5, 6, 10, 11}, by decide +kernel⟩ : OffSchedule 12 5), 150),
      ((⟨{3, 5, 7, 8, 11}, by decide +kernel⟩ : OffSchedule 12 5), 186),
      ((⟨{3, 7, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 5), 68),
      ((⟨{4, 5, 7, 8, 11}, by decide +kernel⟩ : OffSchedule 12 5), 72),
      ((⟨{4, 5, 7, 10, 11}, by decide +kernel⟩ : OffSchedule 12 5), 72),
      ((⟨{5, 7, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 5), 206) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 387),
      ((⟨{0, 3}, by decide +kernel⟩ : FullInput 12 2), 27),
      ((⟨{0, 4}, by decide +kernel⟩ : FullInput 12 2), 153),
      ((⟨{0, 6}, by decide +kernel⟩ : FullInput 12 2), 153),
      ((⟨{0, 8}, by decide +kernel⟩ : FullInput 12 2), 27),
      ((⟨{0, 9}, by decide +kernel⟩ : FullInput 12 2), 45),
      ((⟨{0, 10}, by decide +kernel⟩ : FullInput 12 2), 108),
      ((⟨{0, 11}, by decide +kernel⟩ : FullInput 12 2), 72),
      ((⟨{1, 8}, by decide +kernel⟩ : FullInput 12 2), 171),
      ((⟨{2, 3}, by decide +kernel⟩ : FullInput 12 2), 234),
      ((⟨{2, 6}, by decide +kernel⟩ : FullInput 12 2), 63),
      ((⟨{2, 8}, by decide +kernel⟩ : FullInput 12 2), 63),
      ((⟨{2, 9}, by decide +kernel⟩ : FullInput 12 2), 45),
      ((⟨{2, 11}, by decide +kernel⟩ : FullInput 12 2), 45),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 12 2), 216),
      ((⟨{3, 8}, by decide +kernel⟩ : FullInput 12 2), 99),
      ((⟨{3, 9}, by decide +kernel⟩ : FullInput 12 2), 63),
      ((⟨{3, 10}, by decide +kernel⟩ : FullInput 12 2), 108),
      ((⟨{3, 11}, by decide +kernel⟩ : FullInput 12 2), 90),
      ((⟨{4, 5}, by decide +kernel⟩ : FullInput 12 2), 171),
      ((⟨{5, 6}, by decide +kernel⟩ : FullInput 12 2), 360),
      ((⟨{5, 9}, by decide +kernel⟩ : FullInput 12 2), 63),
      ((⟨{5, 10}, by decide +kernel⟩ : FullInput 12 2), 63),
      ((⟨{5, 11}, by decide +kernel⟩ : FullInput 12 2), 90),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 12 2), 171),
      ((⟨{7, 8}, by decide +kernel⟩ : FullInput 12 2), 216),
      ((⟨{7, 11}, by decide +kernel⟩ : FullInput 12 2), 153),
      ((⟨{8, 9}, by decide +kernel⟩ : FullInput 12 2), 234),
      ((⟨{8, 11}, by decide +kernel⟩ : FullInput 12 2), 27),
      ((⟨{10, 11}, by decide +kernel⟩ : FullInput 12 2), 387) }
  have hs : (∑ p ∈ schedules, p.2) = 4104 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 4104 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := offScheduleEnum 12 5
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 12 5
  have h := off_certificate_value (H := 12) (m := 2) (B := 5) (D := 1)
    (by decide +kernel) (by decide +kernel) schedules 4104 hs (by decide +kernel) 1764 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 12) ∈ x.1) ?_ ?_
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 12) ∈ x.1) ?_ ?_
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 12) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 12) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 12) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 12) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 12) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 12) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 12) ∈ x.1) ?_ ?_
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 12) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 12) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 12) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 12) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 12) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 12) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 12) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 12) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 12) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
            ·
              decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H12_m2_B6_D1 :
    offGameValue 12 2 6 1 (by decide +kernel) (by decide +kernel) = (19/32 : ℝ) := by
  let schedules : Finset (OffSchedule 12 6 × ℕ) :=
    { ((⟨{0, 2, 3, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 6), 4),
      ((⟨{0, 2, 7, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 6), 4),
      ((⟨{1, 2, 4, 5, 7, 8}, by decide +kernel⟩ : OffSchedule 12 6), 4),
      ((⟨{1, 2, 4, 5, 7, 9}, by decide +kernel⟩ : OffSchedule 12 6), 6),
      ((⟨{1, 2, 4, 5, 7, 11}, by decide +kernel⟩ : OffSchedule 12 6), 7),
      ((⟨{1, 2, 4, 5, 9, 11}, by decide +kernel⟩ : OffSchedule 12 6), 3),
      ((⟨{1, 2, 4, 5, 10, 11}, by decide +kernel⟩ : OffSchedule 12 6), 4),
      ((⟨{1, 2, 4, 6, 7, 11}, by decide +kernel⟩ : OffSchedule 12 6), 2),
      ((⟨{1, 2, 4, 6, 8, 9}, by decide +kernel⟩ : OffSchedule 12 6), 3),
      ((⟨{1, 2, 4, 8, 9, 11}, by decide +kernel⟩ : OffSchedule 12 6), 1),
      ((⟨{1, 3, 4, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 6), 1),
      ((⟨{1, 3, 7, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 6), 3),
      ((⟨{1, 5, 6, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 6), 2),
      ((⟨{1, 5, 7, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 6), 5),
      ((⟨{1, 6, 7, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 6), 2),
      ((⟨{3, 4, 6, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 6), 3),
      ((⟨{3, 5, 7, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 6), 6),
      ((⟨{4, 5, 7, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 6), 4) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 4),
      ((⟨{0, 6}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{0, 8}, by decide +kernel⟩ : FullInput 12 2), 4),
      ((⟨{0, 11}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{1, 9}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{1, 11}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{2, 3}, by decide +kernel⟩ : FullInput 12 2), 6),
      ((⟨{2, 11}, by decide +kernel⟩ : FullInput 12 2), 4),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 12 2), 4),
      ((⟨{3, 11}, by decide +kernel⟩ : FullInput 12 2), 4),
      ((⟨{4, 5}, by decide +kernel⟩ : FullInput 12 2), 4),
      ((⟨{5, 6}, by decide +kernel⟩ : FullInput 12 2), 6),
      ((⟨{5, 9}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 12 2), 4),
      ((⟨{7, 8}, by decide +kernel⟩ : FullInput 12 2), 4),
      ((⟨{8, 9}, by decide +kernel⟩ : FullInput 12 2), 6),
      ((⟨{10, 11}, by decide +kernel⟩ : FullInput 12 2), 4) }
  have hs : (∑ p ∈ schedules, p.2) = 64 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 64 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := offScheduleEnum 12 6
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 12 6
  have h := off_certificate_value (H := 12) (m := 2) (B := 6) (D := 1)
    (by decide +kernel) (by decide +kernel) schedules 64 hs (by decide +kernel) 38 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 12) ∈ x.1) ?_ ?_
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 12) ∈ x.1) ?_ ?_
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 12) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 12) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 12) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 12) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 12) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 12) ∈ x.1) ?_ ?_
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 12) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 12) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 12) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 12) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 12) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H12_m2_B7_D1 :
    offGameValue 12 2 7 1 (by decide +kernel) (by decide +kernel) = (3/4 : ℝ) := by
  let schedules : Finset (OffSchedule 12 7 × ℕ) :=
    { ((⟨{0, 2, 3, 5, 6, 10, 11}, by decide +kernel⟩ : OffSchedule 12 7), 1),
      ((⟨{1, 2, 4, 5, 7, 8, 10}, by decide +kernel⟩ : OffSchedule 12 7), 1),
      ((⟨{1, 2, 4, 5, 7, 8, 11}, by decide +kernel⟩ : OffSchedule 12 7), 1),
      ((⟨{1, 2, 4, 5, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 7), 1),
      ((⟨{1, 2, 4, 7, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 7), 1),
      ((⟨{1, 2, 6, 7, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 7), 1),
      ((⟨{1, 4, 5, 7, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 7), 1),
      ((⟨{2, 4, 5, 7, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 7), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{9, 10}, by decide +kernel⟩ : FullInput 12 2), 2) }
  have hs : (∑ p ∈ schedules, p.2) = 8 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 8 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := offScheduleEnum 12 7
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 12 7
  have h := off_certificate_value (H := 12) (m := 2) (B := 7) (D := 1)
    (by decide +kernel) (by decide +kernel) schedules 8 hs (by decide +kernel) 6 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 12) ∈ x.1) ?_ ?_
      ·
        decide +kernel
      ·
        decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H12_m2_B8_D1 :
    offGameValue 12 2 8 1 (by decide +kernel) (by decide +kernel) = (1 : ℝ) := by
  let schedules : Finset (OffSchedule 12 8 × ℕ) :=
    { ((⟨{1, 2, 4, 5, 7, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 8), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := offScheduleEnum 12 8
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 12 8
  have h := off_certificate_value (H := 12) (m := 2) (B := 8) (D := 1)
    (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H12_m2_B2_D1 :
    onGameValue 12 2 2 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 12 2 2 × ℕ) :=
    { ((⟨{10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 2), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := optimizedOnScheduleEnum 12 2 2 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 12) (m := 2) (B := 2) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H12_m2_B3_D1 :
    onGameValue 12 2 3 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 12 2 3 × ℕ) :=
    { ((⟨{0, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 3), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := optimizedOnScheduleEnum 12 2 3 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 12) (m := 2) (B := 3) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H12_m2_B4_D1 :
    onGameValue 12 2 4 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1/10 : ℝ) := by
  let schedules : Finset (OnSchedule 12 2 4 × ℕ) :=
    { ((⟨{1, 2, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 4), 1),
      ((⟨{1, 4, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 4), 1),
      ((⟨{1, 6, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 4), 1),
      ((⟨{1, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 4), 1),
      ((⟨{3, 4, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 4), 1),
      ((⟨{3, 6, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 4), 1),
      ((⟨{3, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 4), 1),
      ((⟨{5, 6, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 4), 1),
      ((⟨{5, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 4), 1),
      ((⟨{7, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 4), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 2}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{0, 4}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{0, 6}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{0, 8}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{2, 3}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{2, 5}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{2, 7}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{4, 5}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{4, 7}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 12 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 10 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 10 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := optimizedOnScheduleEnum 12 2 4 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 12) (m := 2) (B := 4) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 10 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H12_m2_B5_D1 :
    onGameValue 12 2 5 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1/4 : ℝ) := by
  let schedules : Finset (OnSchedule 12 2 5 × ℕ) :=
    { ((⟨{0, 2, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 2),
      ((⟨{1, 2, 4, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 6),
      ((⟨{1, 2, 6, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 4),
      ((⟨{1, 3, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 2),
      ((⟨{1, 4, 6, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 2),
      ((⟨{1, 4, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 2),
      ((⟨{1, 5, 6, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 1),
      ((⟨{1, 5, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 1),
      ((⟨{1, 6, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 4),
      ((⟨{1, 7, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 1),
      ((⟨{2, 4, 5, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 4),
      ((⟨{3, 4, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 2),
      ((⟨{3, 5, 6, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 3),
      ((⟨{3, 5, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 1),
      ((⟨{3, 7, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 5),
      ((⟨{4, 5, 6, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 2),
      ((⟨{5, 7, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 2),
      ((⟨{5, 7, 9, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 4) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 6),
      ((⟨{0, 5}, by decide +kernel⟩ : FullInput 12 2), 6),
      ((⟨{0, 8}, by decide +kernel⟩ : FullInput 12 2), 6),
      ((⟨{2, 3}, by decide +kernel⟩ : FullInput 12 2), 6),
      ((⟨{3, 5}, by decide +kernel⟩ : FullInput 12 2), 6),
      ((⟨{3, 8}, by decide +kernel⟩ : FullInput 12 2), 6),
      ((⟨{5, 6}, by decide +kernel⟩ : FullInput 12 2), 6),
      ((⟨{7, 8}, by decide +kernel⟩ : FullInput 12 2), 6) }
  have hs : (∑ p ∈ schedules, p.2) = 48 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 48 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := optimizedOnScheduleEnum 12 2 5 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 12) (m := 2) (B := 5) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 48 hs (by decide +kernel) 12 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H12_m2_B6_D1 :
    onGameValue 12 2 6 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (5/11 : ℝ) := by
  let schedules : Finset (OnSchedule 12 2 6 × ℕ) :=
    { ((⟨{0, 2, 4, 5, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 6), 4),
      ((⟨{1, 2, 4, 6, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 6), 4),
      ((⟨{1, 2, 4, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 6), 8),
      ((⟨{1, 2, 7, 9, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 6), 4),
      ((⟨{1, 3, 4, 6, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 6), 4),
      ((⟨{1, 5, 6, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 6), 4),
      ((⟨{1, 5, 7, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 6), 4),
      ((⟨{3, 5, 7, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 6), 8),
      ((⟨{4, 5, 7, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 6), 4) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 3),
      ((⟨{0, 3}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{0, 5}, by decide +kernel⟩ : FullInput 12 2), 3),
      ((⟨{0, 6}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{0, 7}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{0, 8}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{1, 8}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{2, 3}, by decide +kernel⟩ : FullInput 12 2), 5),
      ((⟨{2, 6}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{2, 8}, by decide +kernel⟩ : FullInput 12 2), 3),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 12 2), 3),
      ((⟨{3, 8}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{4, 5}, by decide +kernel⟩ : FullInput 12 2), 5),
      ((⟨{5, 6}, by decide +kernel⟩ : FullInput 12 2), 5),
      ((⟨{7, 8}, by decide +kernel⟩ : FullInput 12 2), 5) }
  have hs : (∑ p ∈ schedules, p.2) = 44 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 44 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := optimizedOnScheduleEnum 12 2 6 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 12) (m := 2) (B := 6) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 44 hs (by decide +kernel) 20 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 12) ∈ x.1) ?_ ?_
      ·
        decide +kernel
      ·
        decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H12_m2_B7_D1 :
    onGameValue 12 2 7 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (2/3 : ℝ) := by
  let schedules : Finset (OnSchedule 12 2 7 × ℕ) :=
    { ((⟨{0, 2, 3, 5, 6, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 7), 1),
      ((⟨{1, 2, 4, 5, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 7), 1),
      ((⟨{1, 2, 4, 7, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 7), 1),
      ((⟨{1, 2, 6, 7, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 7), 1),
      ((⟨{1, 4, 5, 7, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 7), 1),
      ((⟨{3, 4, 5, 7, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 7), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{3, 5}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{7, 8}, by decide +kernel⟩ : FullInput 12 2), 2) }
  have hs : (∑ p ∈ schedules, p.2) = 6 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 6 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := optimizedOnScheduleEnum 12 2 7 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 12) (m := 2) (B := 7) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 6 hs (by decide +kernel) 4 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H12_m2_B8_D1 :
    onGameValue 12 2 8 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1 : ℝ) := by
  let schedules : Finset (OnSchedule 12 2 8 × ℕ) :=
    { ((⟨{1, 2, 4, 5, 7, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 8), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := optimizedOnScheduleEnum 12 2 8 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 12) (m := 2) (B := 8) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H12_m2_B2_D2 :
    offGameValue 12 2 2 2 (by decide +kernel) (by decide +kernel) = (1/10 : ℝ) := by
  let schedules : Finset (OffSchedule 12 2 × ℕ) :=
    { ((⟨{1, 8}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{2, 3}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{2, 6}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{2, 11}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{4, 9}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{4, 11}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{5, 6}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{7, 9}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{7, 11}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{10, 11}, by decide +kernel⟩ : OffSchedule 12 2), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{0, 4}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{0, 8}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{0, 11}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{3, 8}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{3, 11}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{6, 10}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{9, 10}, by decide +kernel⟩ : FullInput 12 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 10 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 10 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := offScheduleEnum 12 2
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 12 2
  have h := off_certificate_value (H := 12) (m := 2) (B := 2) (D := 2)
    (by decide +kernel) (by decide +kernel) schedules 10 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H12_m2_B3_D2 :
    offGameValue 12 2 3 2 (by decide +kernel) (by decide +kernel) = (1/4 : ℝ) := by
  let schedules : Finset (OffSchedule 12 3 × ℕ) :=
    { ((⟨{1, 3, 8}, by decide +kernel⟩ : OffSchedule 12 3), 2),
      ((⟨{2, 5, 11}, by decide +kernel⟩ : OffSchedule 12 3), 2),
      ((⟨{5, 6, 8}, by decide +kernel⟩ : OffSchedule 12 3), 2),
      ((⟨{8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 3), 2) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{0, 7}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{0, 11}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{4, 7}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{4, 11}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{7, 8}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{10, 11}, by decide +kernel⟩ : FullInput 12 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 8 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 8 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := offScheduleEnum 12 3
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 12 3
  have h := off_certificate_value (H := 12) (m := 2) (B := 3) (D := 2)
    (by decide +kernel) (by decide +kernel) schedules 8 hs (by decide +kernel) 2 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H12_m2_B4_D2 :
    offGameValue 12 2 4 2 (by decide +kernel) (by decide +kernel) = (5/11 : ℝ) := by
  let schedules : Finset (OffSchedule 12 4 × ℕ) :=
    { ((⟨{1, 3, 6, 9}, by decide +kernel⟩ : OffSchedule 12 4), 1),
      ((⟨{1, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 4), 1),
      ((⟨{2, 3, 6, 7}, by decide +kernel⟩ : OffSchedule 12 4), 1),
      ((⟨{2, 3, 6, 11}, by decide +kernel⟩ : OffSchedule 12 4), 2),
      ((⟨{2, 3, 10, 11}, by decide +kernel⟩ : OffSchedule 12 4), 1),
      ((⟨{2, 5, 6, 8}, by decide +kernel⟩ : OffSchedule 12 4), 1),
      ((⟨{2, 9, 10, 11}, by decide +kernel⟩ : OffSchedule 12 4), 1),
      ((⟨{4, 7, 8, 11}, by decide +kernel⟩ : OffSchedule 12 4), 1),
      ((⟨{5, 7, 10, 11}, by decide +kernel⟩ : OffSchedule 12 4), 1),
      ((⟨{6, 7, 10, 11}, by decide +kernel⟩ : OffSchedule 12 4), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{0, 4}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{0, 11}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{1, 8}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{3, 11}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{4, 5}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{7, 8}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{7, 11}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{10, 11}, by decide +kernel⟩ : FullInput 12 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 11 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 11 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := offScheduleEnum 12 4
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 12 4
  have h := off_certificate_value (H := 12) (m := 2) (B := 4) (D := 2)
    (by decide +kernel) (by decide +kernel) schedules 11 hs (by decide +kernel) 5 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 12) ∈ x.1) ?_ ?_
      ·
        decide +kernel
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 12) ∈ x.1) ?_ ?_
        ·
          decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 12) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H12_m2_B5_D2 :
    offGameValue 12 2 5 2 (by decide +kernel) (by decide +kernel) = (2/3 : ℝ) := by
  let schedules : Finset (OffSchedule 12 5 × ℕ) :=
    { ((⟨{2, 3, 6, 7, 10}, by decide +kernel⟩ : OffSchedule 12 5), 1),
      ((⟨{2, 3, 6, 7, 11}, by decide +kernel⟩ : OffSchedule 12 5), 1),
      ((⟨{2, 3, 6, 10, 11}, by decide +kernel⟩ : OffSchedule 12 5), 1),
      ((⟨{2, 3, 9, 10, 11}, by decide +kernel⟩ : OffSchedule 12 5), 1),
      ((⟨{2, 6, 7, 10, 11}, by decide +kernel⟩ : OffSchedule 12 5), 1),
      ((⟨{5, 6, 7, 10, 11}, by decide +kernel⟩ : OffSchedule 12 5), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 11}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{7, 8}, by decide +kernel⟩ : FullInput 12 2), 2) }
  have hs : (∑ p ∈ schedules, p.2) = 6 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 6 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := offScheduleEnum 12 5
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 12 5
  have h := off_certificate_value (H := 12) (m := 2) (B := 5) (D := 2)
    (by decide +kernel) (by decide +kernel) schedules 6 hs (by decide +kernel) 4 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 12) ∈ x.1) ?_ ?_
      ·
        decide +kernel
      ·
        decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H12_m2_B6_D2 :
    offGameValue 12 2 6 2 (by decide +kernel) (by decide +kernel) = (1 : ℝ) := by
  let schedules : Finset (OffSchedule 12 6 × ℕ) :=
    { ((⟨{2, 3, 6, 7, 10, 11}, by decide +kernel⟩ : OffSchedule 12 6), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := offScheduleEnum 12 6
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 12 6
  have h := off_certificate_value (H := 12) (m := 2) (B := 6) (D := 2)
    (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H12_m2_B2_D2 :
    onGameValue 12 2 2 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 12 2 2 × ℕ) :=
    { ((⟨{10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 2), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := optimizedOnScheduleEnum 12 2 2 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 12) (m := 2) (B := 2) (D := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H12_m2_B3_D2 :
    onGameValue 12 2 3 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 12 2 3 × ℕ) :=
    { ((⟨{0, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 3), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := optimizedOnScheduleEnum 12 2 3 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 12) (m := 2) (B := 3) (D := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H12_m2_B4_D2 :
    onGameValue 12 2 4 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1/6 : ℝ) := by
  let schedules : Finset (OnSchedule 12 2 4 × ℕ) :=
    { ((⟨{1, 3, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 4), 1),
      ((⟨{2, 5, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 4), 1),
      ((⟨{2, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 4), 1),
      ((⟨{5, 6, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 4), 1),
      ((⟨{5, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 4), 1),
      ((⟨{7, 9, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 4), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{0, 4}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{0, 7}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{3, 7}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 12 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 6 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 6 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := optimizedOnScheduleEnum 12 2 4 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 12) (m := 2) (B := 4) (D := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 6 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H12_m2_B5_D2 :
    onGameValue 12 2 5 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1/2 : ℝ) := by
  let schedules : Finset (OnSchedule 12 2 5 × ℕ) :=
    { ((⟨{0, 3, 4, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 1),
      ((⟨{1, 6, 7, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 1),
      ((⟨{2, 3, 7, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 1),
      ((⟨{3, 6, 7, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{4, 7}, by decide +kernel⟩ : FullInput 12 2), 2) }
  have hs : (∑ p ∈ schedules, p.2) = 4 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 4 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := optimizedOnScheduleEnum 12 2 5 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 12) (m := 2) (B := 5) (D := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 4 hs (by decide +kernel) 2 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H12_m2_B6_D2 :
    onGameValue 12 2 6 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1 : ℝ) := by
  let schedules : Finset (OnSchedule 12 2 6 × ℕ) :=
    { ((⟨{2, 3, 6, 7, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 6), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := optimizedOnScheduleEnum 12 2 6 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 12) (m := 2) (B := 6) (D := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H12_m2_B2_D3 :
    offGameValue 12 2 2 3 (by decide +kernel) (by decide +kernel) = (1/6 : ℝ) := by
  let schedules : Finset (OffSchedule 12 2 × ℕ) :=
    { ((⟨{2, 4}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{3, 7}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{3, 11}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{6, 7}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{7, 11}, by decide +kernel⟩ : OffSchedule 12 2), 1),
      ((⟨{10, 11}, by decide +kernel⟩ : OffSchedule 12 2), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 3}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{0, 7}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{2, 11}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{4, 5}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{6, 10}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{10, 11}, by decide +kernel⟩ : FullInput 12 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 6 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 6 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := offScheduleEnum 12 2
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 12 2
  have h := off_certificate_value (H := 12) (m := 2) (B := 2) (D := 3)
    (by decide +kernel) (by decide +kernel) schedules 6 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H12_m2_B3_D3 :
    offGameValue 12 2 3 3 (by decide +kernel) (by decide +kernel) = (1/3 : ℝ) := by
  let schedules : Finset (OffSchedule 12 3 × ℕ) :=
    { ((⟨{0, 4, 11}, by decide +kernel⟩ : OffSchedule 12 3), 3),
      ((⟨{2, 5, 7}, by decide +kernel⟩ : OffSchedule 12 3), 3),
      ((⟨{8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 3), 3) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{0, 6}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{1, 10}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{5, 6}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{5, 11}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{10, 11}, by decide +kernel⟩ : FullInput 12 2), 2) }
  have hs : (∑ p ∈ schedules, p.2) = 9 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 9 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := offScheduleEnum 12 3
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 12 3
  have h := off_certificate_value (H := 12) (m := 2) (B := 3) (D := 3)
    (by decide +kernel) (by decide +kernel) schedules 9 hs (by decide +kernel) 3 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H12_m2_B4_D3 :
    offGameValue 12 2 4 3 (by decide +kernel) (by decide +kernel) = (5/9 : ℝ) := by
  let schedules : Finset (OffSchedule 12 4 × ℕ) :=
    { ((⟨{0, 4, 10, 11}, by decide +kernel⟩ : OffSchedule 12 4), 1),
      ((⟨{1, 2, 8, 11}, by decide +kernel⟩ : OffSchedule 12 4), 1),
      ((⟨{1, 5, 6, 11}, by decide +kernel⟩ : OffSchedule 12 4), 1),
      ((⟨{2, 4, 7, 9}, by decide +kernel⟩ : OffSchedule 12 4), 2),
      ((⟨{3, 4, 10, 11}, by decide +kernel⟩ : OffSchedule 12 4), 1),
      ((⟨{3, 6, 10, 11}, by decide +kernel⟩ : OffSchedule 12 4), 1),
      ((⟨{5, 6, 10, 11}, by decide +kernel⟩ : OffSchedule 12 4), 2) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{0, 10}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{1, 5}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{5, 6}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{6, 11}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{10, 11}, by decide +kernel⟩ : FullInput 12 2), 2) }
  have hs : (∑ p ∈ schedules, p.2) = 9 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 9 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := offScheduleEnum 12 4
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 12 4
  have h := off_certificate_value (H := 12) (m := 2) (B := 4) (D := 3)
    (by decide +kernel) (by decide +kernel) schedules 9 hs (by decide +kernel) 5 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 12) ∈ x.1) ?_ ?_
      ·
        decide +kernel
      ·
        decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H12_m2_B5_D3 :
    offGameValue 12 2 5 3 (by decide +kernel) (by decide +kernel) = (2/3 : ℝ) := by
  let schedules : Finset (OffSchedule 12 5 × ℕ) :=
    { ((⟨{1, 3, 6, 8, 11}, by decide +kernel⟩ : OffSchedule 12 5), 1),
      ((⟨{1, 4, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 5), 1),
      ((⟨{3, 6, 9, 10, 11}, by decide +kernel⟩ : OffSchedule 12 5), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{5, 6}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{10, 11}, by decide +kernel⟩ : FullInput 12 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 3 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 3 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := offScheduleEnum 12 5
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 12 5
  have h := off_certificate_value (H := 12) (m := 2) (B := 5) (D := 3)
    (by decide +kernel) (by decide +kernel) schedules 3 hs (by decide +kernel) 2 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 12) ∈ x.1) ?_ ?_
      ·
        decide +kernel
      ·
        decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H12_m2_B6_D3 :
    offGameValue 12 2 6 3 (by decide +kernel) (by decide +kernel) = (1 : ℝ) := by
  let schedules : Finset (OffSchedule 12 6 × ℕ) :=
    { ((⟨{0, 1, 5, 6, 10, 11}, by decide +kernel⟩ : OffSchedule 12 6), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := offScheduleEnum 12 6
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 12 6
  have h := off_certificate_value (H := 12) (m := 2) (B := 6) (D := 3)
    (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H12_m2_B2_D3 :
    onGameValue 12 2 2 3 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 12 2 2 × ℕ) :=
    { ((⟨{10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 2), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := optimizedOnScheduleEnum 12 2 2 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 12) (m := 2) (B := 2) (D := 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H12_m2_B3_D3 :
    onGameValue 12 2 3 3 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 12 2 3 × ℕ) :=
    { ((⟨{0, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 3), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := optimizedOnScheduleEnum 12 2 3 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 12) (m := 2) (B := 3) (D := 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H12_m2_B4_D3 :
    onGameValue 12 2 4 3 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1/3 : ℝ) := by
  let schedules : Finset (OnSchedule 12 2 4 × ℕ) :=
    { ((⟨{1, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 4), 1),
      ((⟨{2, 4, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 4), 1),
      ((⟨{5, 7, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 4), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{0, 5}, by decide +kernel⟩ : FullInput 12 2), 1),
      ((⟨{4, 6}, by decide +kernel⟩ : FullInput 12 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 3 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 3 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := optimizedOnScheduleEnum 12 2 4 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 12) (m := 2) (B := 4) (D := 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 3 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H12_m2_B5_D3 :
    onGameValue 12 2 5 3 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1/2 : ℝ) := by
  let schedules : Finset (OnSchedule 12 2 5 × ℕ) :=
    { ((⟨{0, 2, 9, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 1),
      ((⟨{2, 4, 8, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 1),
      ((⟨{3, 5, 9, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 1),
      ((⟨{5, 6, 7, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 5), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 2),
      ((⟨{5, 6}, by decide +kernel⟩ : FullInput 12 2), 2) }
  have hs : (∑ p ∈ schedules, p.2) = 4 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 4 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := optimizedOnScheduleEnum 12 2 5 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 12) (m := 2) (B := 5) (D := 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 4 hs (by decide +kernel) 2 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H12_m2_B6_D3 :
    onGameValue 12 2 6 3 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1 : ℝ) := by
  let schedules : Finset (OnSchedule 12 2 6 × ℕ) :=
    { ((⟨{0, 1, 5, 6, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 2 6), 1) }
  let inputs : Finset (FullInput 12 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 12 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 12 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 2
  let cols := optimizedOnScheduleEnum 12 2 6 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 12) (m := 2) (B := 6) (D := 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B2_D1 :
    onGameValue 16 2 2 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 2 × ℕ) :=
    { ((⟨{14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 2), 1) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 2 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 2) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B3_D1 :
    onGameValue 16 2 3 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 3 × ℕ) :=
    { ((⟨{0, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 3), 1) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 3 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 3) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B4_D1 :
    onGameValue 16 2 4 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1/21 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 4 × ℕ) :=
    { ((⟨{1, 2, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{1, 4, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{1, 6, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{1, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{1, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{1, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{3, 4, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{3, 6, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{3, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{3, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{3, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{5, 6, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{5, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{5, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{5, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{7, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{7, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{7, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{9, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{9, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{0, 3}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{0, 5}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{0, 7}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{0, 9}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{0, 11}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{2, 3}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{2, 9}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{2, 12}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{3, 5}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{3, 7}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{4, 12}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{5, 6}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{5, 8}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{5, 10}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{6, 12}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{7, 8}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{7, 10}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{9, 10}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{9, 12}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{11, 12}, by decide +kernel⟩ : FullInput 16 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 21 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 21 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 4 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 4) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 21 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 16) ∈ x.1) ?_ ?_
      ·
        decide +kernel
      ·
        refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          decide +kernel
        ·
          decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B5_D1 :
    onGameValue 16 2 5 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (4/31 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 5 × ℕ) :=
    { ((⟨{0, 2, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 30),
      ((⟨{0, 2, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 70),
      ((⟨{1, 2, 4, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 164),
      ((⟨{1, 2, 6, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 32),
      ((⟨{1, 2, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 82),
      ((⟨{1, 2, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 86),
      ((⟨{1, 3, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 100),
      ((⟨{1, 4, 6, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 32),
      ((⟨{1, 4, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 62),
      ((⟨{1, 4, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 86),
      ((⟨{1, 4, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 20),
      ((⟨{1, 5, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 100),
      ((⟨{1, 6, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 112),
      ((⟨{1, 6, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 114),
      ((⟨{1, 6, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 74),
      ((⟨{1, 7, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 100),
      ((⟨{1, 8, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 78),
      ((⟨{1, 9, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 100),
      ((⟨{3, 4, 6, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 252),
      ((⟨{3, 4, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 44),
      ((⟨{3, 4, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 4),
      ((⟨{3, 5, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 48),
      ((⟨{3, 5, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 116),
      ((⟨{3, 6, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 16),
      ((⟨{3, 7, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 100),
      ((⟨{3, 7, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 42),
      ((⟨{3, 7, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 22),
      ((⟨{3, 8, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 164),
      ((⟨{3, 8, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 24),
      ((⟨{3, 9, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 64),
      ((⟨{3, 11, 13, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 64),
      ((⟨{4, 8, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 50),
      ((⟨{5, 6, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 68),
      ((⟨{5, 6, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 112),
      ((⟨{5, 7, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 184),
      ((⟨{5, 7, 9, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 37),
      ((⟨{5, 7, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 63),
      ((⟨{5, 9, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 63),
      ((⟨{5, 10, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 74),
      ((⟨{5, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 37),
      ((⟨{7, 9, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 59),
      ((⟨{7, 9, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 84),
      ((⟨{7, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 121),
      ((⟨{9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 242) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 174),
      ((⟨{0, 3}, by decide +kernel⟩ : FullInput 16 2), 116),
      ((⟨{0, 5}, by decide +kernel⟩ : FullInput 16 2), 116),
      ((⟨{0, 6}, by decide +kernel⟩ : FullInput 16 2), 58),
      ((⟨{0, 7}, by decide +kernel⟩ : FullInput 16 2), 58),
      ((⟨{0, 8}, by decide +kernel⟩ : FullInput 16 2), 116),
      ((⟨{0, 9}, by decide +kernel⟩ : FullInput 16 2), 58),
      ((⟨{0, 10}, by decide +kernel⟩ : FullInput 16 2), 116),
      ((⟨{0, 12}, by decide +kernel⟩ : FullInput 16 2), 174),
      ((⟨{2, 3}, by decide +kernel⟩ : FullInput 16 2), 174),
      ((⟨{2, 5}, by decide +kernel⟩ : FullInput 16 2), 58),
      ((⟨{2, 6}, by decide +kernel⟩ : FullInput 16 2), 58),
      ((⟨{2, 8}, by decide +kernel⟩ : FullInput 16 2), 116),
      ((⟨{2, 10}, by decide +kernel⟩ : FullInput 16 2), 116),
      ((⟨{2, 12}, by decide +kernel⟩ : FullInput 16 2), 116),
      ((⟨{3, 5}, by decide +kernel⟩ : FullInput 16 2), 58),
      ((⟨{3, 7}, by decide +kernel⟩ : FullInput 16 2), 58),
      ((⟨{3, 9}, by decide +kernel⟩ : FullInput 16 2), 58),
      ((⟨{3, 12}, by decide +kernel⟩ : FullInput 16 2), 58),
      ((⟨{4, 5}, by decide +kernel⟩ : FullInput 16 2), 116),
      ((⟨{4, 8}, by decide +kernel⟩ : FullInput 16 2), 116),
      ((⟨{4, 10}, by decide +kernel⟩ : FullInput 16 2), 116),
      ((⟨{4, 12}, by decide +kernel⟩ : FullInput 16 2), 116),
      ((⟨{5, 6}, by decide +kernel⟩ : FullInput 16 2), 116),
      ((⟨{5, 9}, by decide +kernel⟩ : FullInput 16 2), 58),
      ((⟨{5, 12}, by decide +kernel⟩ : FullInput 16 2), 58),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 16 2), 116),
      ((⟨{6, 9}, by decide +kernel⟩ : FullInput 16 2), 58),
      ((⟨{6, 12}, by decide +kernel⟩ : FullInput 16 2), 58),
      ((⟨{7, 8}, by decide +kernel⟩ : FullInput 16 2), 116),
      ((⟨{7, 10}, by decide +kernel⟩ : FullInput 16 2), 116),
      ((⟨{7, 12}, by decide +kernel⟩ : FullInput 16 2), 116),
      ((⟨{9, 10}, by decide +kernel⟩ : FullInput 16 2), 174),
      ((⟨{9, 12}, by decide +kernel⟩ : FullInput 16 2), 116),
      ((⟨{11, 12}, by decide +kernel⟩ : FullInput 16 2), 174) }
  have hs : (∑ p ∈ schedules, p.2) = 3596 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 3596 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 5 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 5) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 3596 hs (by decide +kernel) 464 inputs hi
    rows hrows (by
      refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 16) ∈ x.1) ?_ ?_
      ·
        decide +kernel
      ·
        refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          decide +kernel
        ·
          refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 16) ∈ x.1) ?_ ?_
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            decide +kernel
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B6_D1 :
    onGameValue 16 2 6 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (3939/16216 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 6 × ℕ) :=
    { ((⟨{1, 2, 4, 6, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 1854),
      ((⟨{1, 2, 4, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 678),
      ((⟨{1, 2, 4, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 750),
      ((⟨{1, 2, 4, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 2410),
      ((⟨{1, 2, 7, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 230),
      ((⟨{1, 2, 7, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 72),
      ((⟨{1, 2, 8, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 1740),
      ((⟨{1, 2, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 144),
      ((⟨{1, 4, 5, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 668),
      ((⟨{1, 4, 5, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 120),
      ((⟨{1, 4, 6, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 906),
      ((⟨{1, 4, 6, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 396),
      ((⟨{1, 4, 6, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 96),
      ((⟨{1, 6, 7, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 2338),
      ((⟨{1, 6, 8, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 1428),
      ((⟨{1, 6, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 72),
      ((⟨{1, 7, 8, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 270),
      ((⟨{1, 7, 9, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 216),
      ((⟨{1, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 2410),
      ((⟨{3, 4, 6, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 434),
      ((⟨{3, 4, 6, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 1002),
      ((⟨{3, 4, 9, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 750),
      ((⟨{3, 5, 6, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 40),
      ((⟨{3, 5, 6, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 230),
      ((⟨{3, 5, 7, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 370),
      ((⟨{3, 5, 7, 9, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 780),
      ((⟨{3, 5, 7, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 1428),
      ((⟨{3, 5, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 1740),
      ((⟨{3, 7, 9, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 1002),
      ((⟨{3, 7, 9, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 436),
      ((⟨{3, 8, 9, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 668),
      ((⟨{3, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 750),
      ((⟨{4, 5, 7, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 316),
      ((⟨{4, 6, 8, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 820),
      ((⟨{5, 6, 8, 9, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 396),
      ((⟨{5, 6, 8, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 330),
      ((⟨{5, 6, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 270),
      ((⟨{5, 7, 9, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 474),
      ((⟨{5, 7, 9, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 906),
      ((⟨{5, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 678),
      ((⟨{7, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 1814) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 1720),
      ((⟨{0, 2}, by decide +kernel⟩ : FullInput 16 2), 326),
      ((⟨{0, 3}, by decide +kernel⟩ : FullInput 16 2), 592),
      ((⟨{0, 4}, by decide +kernel⟩ : FullInput 16 2), 572),
      ((⟨{0, 5}, by decide +kernel⟩ : FullInput 16 2), 708),
      ((⟨{0, 6}, by decide +kernel⟩ : FullInput 16 2), 546),
      ((⟨{0, 7}, by decide +kernel⟩ : FullInput 16 2), 800),
      ((⟨{0, 8}, by decide +kernel⟩ : FullInput 16 2), 526),
      ((⟨{0, 9}, by decide +kernel⟩ : FullInput 16 2), 550),
      ((⟨{0, 10}, by decide +kernel⟩ : FullInput 16 2), 950),
      ((⟨{0, 11}, by decide +kernel⟩ : FullInput 16 2), 557),
      ((⟨{0, 12}, by decide +kernel⟩ : FullInput 16 2), 957),
      ((⟨{2, 3}, by decide +kernel⟩ : FullInput 16 2), 1128),
      ((⟨{2, 5}, by decide +kernel⟩ : FullInput 16 2), 216),
      ((⟨{2, 6}, by decide +kernel⟩ : FullInput 16 2), 546),
      ((⟨{2, 7}, by decide +kernel⟩ : FullInput 16 2), 222),
      ((⟨{2, 8}, by decide +kernel⟩ : FullInput 16 2), 540),
      ((⟨{2, 9}, by decide +kernel⟩ : FullInput 16 2), 564),
      ((⟨{2, 10}, by decide +kernel⟩ : FullInput 16 2), 372),
      ((⟨{2, 11}, by decide +kernel⟩ : FullInput 16 2), 557),
      ((⟨{2, 12}, by decide +kernel⟩ : FullInput 16 2), 393),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 16 2), 1092),
      ((⟨{3, 7}, by decide +kernel⟩ : FullInput 16 2), 564),
      ((⟨{3, 10}, by decide +kernel⟩ : FullInput 16 2), 564),
      ((⟨{3, 12}, by decide +kernel⟩ : FullInput 16 2), 550),
      ((⟨{4, 5}, by decide +kernel⟩ : FullInput 16 2), 1524),
      ((⟨{4, 7}, by decide +kernel⟩ : FullInput 16 2), 30),
      ((⟨{4, 8}, by decide +kernel⟩ : FullInput 16 2), 858),
      ((⟨{4, 10}, by decide +kernel⟩ : FullInput 16 2), 540),
      ((⟨{4, 12}, by decide +kernel⟩ : FullInput 16 2), 526),
      ((⟨{5, 6}, by decide +kernel⟩ : FullInput 16 2), 1128),
      ((⟨{5, 8}, by decide +kernel⟩ : FullInput 16 2), 30),
      ((⟨{5, 9}, by decide +kernel⟩ : FullInput 16 2), 564),
      ((⟨{5, 10}, by decide +kernel⟩ : FullInput 16 2), 222),
      ((⟨{5, 11}, by decide +kernel⟩ : FullInput 16 2), 543),
      ((⟨{5, 12}, by decide +kernel⟩ : FullInput 16 2), 257),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 16 2), 1128),
      ((⟨{6, 10}, by decide +kernel⟩ : FullInput 16 2), 546),
      ((⟨{6, 11}, by decide +kernel⟩ : FullInput 16 2), 14),
      ((⟨{6, 12}, by decide +kernel⟩ : FullInput 16 2), 532),
      ((⟨{7, 8}, by decide +kernel⟩ : FullInput 16 2), 1524),
      ((⟨{7, 10}, by decide +kernel⟩ : FullInput 16 2), 216),
      ((⟨{7, 11}, by decide +kernel⟩ : FullInput 16 2), 506),
      ((⟨{7, 12}, by decide +kernel⟩ : FullInput 16 2), 202),
      ((⟨{8, 9}, by decide +kernel⟩ : FullInput 16 2), 1092),
      ((⟨{8, 11}, by decide +kernel⟩ : FullInput 16 2), 15),
      ((⟨{8, 12}, by decide +kernel⟩ : FullInput 16 2), 557),
      ((⟨{9, 10}, by decide +kernel⟩ : FullInput 16 2), 1128),
      ((⟨{9, 12}, by decide +kernel⟩ : FullInput 16 2), 592),
      ((⟨{10, 12}, by decide +kernel⟩ : FullInput 16 2), 326),
      ((⟨{11, 12}, by decide +kernel⟩ : FullInput 16 2), 1720) }
  have hs : (∑ p ∈ schedules, p.2) = 32432 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 32432 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 6 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 6) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 32432 hs (by decide +kernel) 7878 inputs hi
    rows hrows (by
      refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 16) ∈ x.1) ?_ ?_
      ·
        decide +kernel
      ·
        refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          decide +kernel
        ·
          refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 16) ∈ x.1) ?_ ?_
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B7_D1 :
    onGameValue 16 2 7 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (709/1873 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 7 × ℕ) :=
    { ((⟨{1, 2, 4, 5, 7, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 11716),
      ((⟨{1, 2, 4, 5, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 22904),
      ((⟨{1, 2, 4, 5, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 14228),
      ((⟨{1, 2, 4, 6, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 22904),
      ((⟨{1, 2, 4, 6, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 36294),
      ((⟨{1, 2, 4, 8, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 14522),
      ((⟨{1, 2, 4, 9, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 5486),
      ((⟨{1, 2, 4, 9, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 10480),
      ((⟨{1, 2, 4, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 10480),
      ((⟨{1, 2, 6, 7, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 8790),
      ((⟨{1, 2, 7, 8, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 8676),
      ((⟨{1, 2, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 10770),
      ((⟨{1, 4, 5, 7, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 8790),
      ((⟨{1, 4, 6, 8, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 8676),
      ((⟨{1, 4, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 10770),
      ((⟨{1, 6, 7, 9, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 26528),
      ((⟨{1, 6, 7, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 8210),
      ((⟨{1, 6, 8, 9, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 8210),
      ((⟨{1, 7, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 28456),
      ((⟨{1, 8, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 21772),
      ((⟨{3, 4, 6, 7, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 18972),
      ((⟨{3, 4, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 9264),
      ((⟨{3, 5, 6, 8, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 30192),
      ((⟨{3, 5, 6, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 2574),
      ((⟨{3, 5, 7, 8, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 20308),
      ((⟨{3, 5, 7, 9, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 13324),
      ((⟨{3, 5, 7, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 10750),
      ((⟨{3, 5, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 14228),
      ((⟨{3, 8, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 17096),
      ((⟨{5, 7, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 17096),
      ((⟨{6, 8, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 15784) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 37250),
      ((⟨{0, 3}, by decide +kernel⟩ : FullInput 16 2), 3750),
      ((⟨{0, 6}, by decide +kernel⟩ : FullInput 16 2), 12375),
      ((⟨{0, 7}, by decide +kernel⟩ : FullInput 16 2), 5125),
      ((⟨{0, 8}, by decide +kernel⟩ : FullInput 16 2), 11125),
      ((⟨{0, 9}, by decide +kernel⟩ : FullInput 16 2), 9625),
      ((⟨{0, 10}, by decide +kernel⟩ : FullInput 16 2), 8750),
      ((⟨{0, 12}, by decide +kernel⟩ : FullInput 16 2), 18125),
      ((⟨{1, 2}, by decide +kernel⟩ : FullInput 16 2), 1875),
      ((⟨{1, 3}, by decide +kernel⟩ : FullInput 16 2), 8000),
      ((⟨{1, 4}, by decide +kernel⟩ : FullInput 16 2), 2500),
      ((⟨{1, 5}, by decide +kernel⟩ : FullInput 16 2), 9250),
      ((⟨{2, 3}, by decide +kernel⟩ : FullInput 16 2), 16500),
      ((⟨{2, 7}, by decide +kernel⟩ : FullInput 16 2), 10000),
      ((⟨{2, 8}, by decide +kernel⟩ : FullInput 16 2), 3625),
      ((⟨{2, 10}, by decide +kernel⟩ : FullInput 16 2), 8250),
      ((⟨{2, 12}, by decide +kernel⟩ : FullInput 16 2), 8750),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 16 2), 24750),
      ((⟨{3, 7}, by decide +kernel⟩ : FullInput 16 2), 1375),
      ((⟨{3, 9}, by decide +kernel⟩ : FullInput 16 2), 10750),
      ((⟨{3, 12}, by decide +kernel⟩ : FullInput 16 2), 10000),
      ((⟨{4, 5}, by decide +kernel⟩ : FullInput 16 2), 20625),
      ((⟨{4, 8}, by decide +kernel⟩ : FullInput 16 2), 8625),
      ((⟨{4, 9}, by decide +kernel⟩ : FullInput 16 2), 1750),
      ((⟨{4, 10}, by decide +kernel⟩ : FullInput 16 2), 3625),
      ((⟨{4, 12}, by decide +kernel⟩ : FullInput 16 2), 10750),
      ((⟨{5, 6}, by decide +kernel⟩ : FullInput 16 2), 23875),
      ((⟨{5, 8}, by decide +kernel⟩ : FullInput 16 2), 1375),
      ((⟨{5, 10}, by decide +kernel⟩ : FullInput 16 2), 10000),
      ((⟨{5, 12}, by decide +kernel⟩ : FullInput 16 2), 5125),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 16 2), 23875),
      ((⟨{6, 12}, by decide +kernel⟩ : FullInput 16 2), 12375),
      ((⟨{7, 8}, by decide +kernel⟩ : FullInput 16 2), 20625),
      ((⟨{7, 12}, by decide +kernel⟩ : FullInput 16 2), 9250),
      ((⟨{8, 9}, by decide +kernel⟩ : FullInput 16 2), 24750),
      ((⟨{8, 12}, by decide +kernel⟩ : FullInput 16 2), 2875),
      ((⟨{9, 10}, by decide +kernel⟩ : FullInput 16 2), 16500),
      ((⟨{9, 12}, by decide +kernel⟩ : FullInput 16 2), 11375),
      ((⟨{10, 12}, by decide +kernel⟩ : FullInput 16 2), 1875),
      ((⟨{11, 12}, by decide +kernel⟩ : FullInput 16 2), 37250) }
  have hs : (∑ p ∈ schedules, p.2) = 468250 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 468250 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 7 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 7) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 468250 hs (by decide +kernel) 177250 inputs hi
    rows hrows (by
      refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 16) ∈ x.1) ?_ ?_
      ·
        decide +kernel
      ·
        refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          decide +kernel
        ·
          refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 16) ∈ x.1) ?_ ?_
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel
                ·
                  refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (6 : Fin 16) ∈ x.1) ?_ ?_
                  ·
                    decide +kernel
                  ·
                    decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B8_D1 :
    onGameValue 16 2 8 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (78/149 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 8 × ℕ) :=
    { ((⟨{0, 2, 4, 5, 7, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 24),
      ((⟨{1, 2, 4, 5, 7, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 8),
      ((⟨{1, 2, 4, 5, 7, 9, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 4),
      ((⟨{1, 2, 4, 5, 7, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 4),
      ((⟨{1, 2, 4, 5, 7, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 16),
      ((⟨{1, 2, 4, 5, 9, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 8),
      ((⟨{1, 2, 4, 5, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 6),
      ((⟨{1, 2, 4, 6, 8, 9, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 14),
      ((⟨{1, 2, 4, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 46),
      ((⟨{1, 2, 6, 7, 9, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 8),
      ((⟨{1, 2, 6, 7, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 6),
      ((⟨{1, 2, 7, 8, 10, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 6),
      ((⟨{1, 2, 8, 9, 11, 13, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 6),
      ((⟨{1, 3, 5, 6, 8, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 18),
      ((⟨{1, 3, 5, 6, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 6),
      ((⟨{1, 4, 5, 7, 8, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 2),
      ((⟨{1, 6, 8, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 40),
      ((⟨{3, 4, 6, 7, 9, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 10),
      ((⟨{3, 4, 6, 7, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 8),
      ((⟨{3, 4, 8, 9, 11, 13, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 8),
      ((⟨{3, 5, 6, 8, 9, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 2),
      ((⟨{3, 5, 7, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 12),
      ((⟨{3, 5, 7, 9, 11, 13, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 2),
      ((⟨{3, 6, 8, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 8),
      ((⟨{4, 5, 7, 8, 10, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 18),
      ((⟨{5, 6, 8, 9, 11, 13, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 8) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 39),
      ((⟨{0, 3}, by decide +kernel⟩ : FullInput 16 2), 5),
      ((⟨{0, 6}, by decide +kernel⟩ : FullInput 16 2), 11),
      ((⟨{0, 9}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{1, 4}, by decide +kernel⟩ : FullInput 16 2), 3),
      ((⟨{1, 9}, by decide +kernel⟩ : FullInput 16 2), 6),
      ((⟨{1, 11}, by decide +kernel⟩ : FullInput 16 2), 10),
      ((⟨{2, 3}, by decide +kernel⟩ : FullInput 16 2), 9),
      ((⟨{2, 6}, by decide +kernel⟩ : FullInput 16 2), 3),
      ((⟨{2, 9}, by decide +kernel⟩ : FullInput 16 2), 6),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 16 2), 28),
      ((⟨{3, 9}, by decide +kernel⟩ : FullInput 16 2), 6),
      ((⟨{3, 10}, by decide +kernel⟩ : FullInput 16 2), 6),
      ((⟨{3, 12}, by decide +kernel⟩ : FullInput 16 2), 8),
      ((⟨{4, 5}, by decide +kernel⟩ : FullInput 16 2), 9),
      ((⟨{5, 6}, by decide +kernel⟩ : FullInput 16 2), 20),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 16 2), 20),
      ((⟨{6, 10}, by decide +kernel⟩ : FullInput 16 2), 3),
      ((⟨{6, 12}, by decide +kernel⟩ : FullInput 16 2), 11),
      ((⟨{7, 8}, by decide +kernel⟩ : FullInput 16 2), 9),
      ((⟨{8, 9}, by decide +kernel⟩ : FullInput 16 2), 28),
      ((⟨{8, 11}, by decide +kernel⟩ : FullInput 16 2), 3),
      ((⟨{9, 10}, by decide +kernel⟩ : FullInput 16 2), 9),
      ((⟨{9, 11}, by decide +kernel⟩ : FullInput 16 2), 5),
      ((⟨{11, 12}, by decide +kernel⟩ : FullInput 16 2), 39) }
  have hs : (∑ p ∈ schedules, p.2) = 298 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 298 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 8 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 8) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 298 hs (by decide +kernel) 156 inputs hi
    rows hrows (by
      refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 16) ∈ x.1) ?_ ?_
      ·
        decide +kernel
      ·
        refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          decide +kernel
        ·
          refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 16) ∈ x.1) ?_ ?_
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel
              ·
                refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (5 : Fin 16) ∈ x.1) ?_ ?_
                ·
                  decide +kernel
                ·
                  decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B9_D1 :
    onGameValue 16 2 9 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (15/23 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 9 × ℕ) :=
    { ((⟨{0, 2, 3, 5, 6, 12, 13, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 9), 1),
      ((⟨{0, 2, 4, 6, 7, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 9), 1),
      ((⟨{0, 2, 6, 7, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 9), 3),
      ((⟨{1, 2, 4, 5, 7, 8, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 9), 2),
      ((⟨{1, 2, 4, 5, 7, 8, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 9), 2),
      ((⟨{1, 2, 4, 5, 7, 9, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 9), 2),
      ((⟨{1, 2, 4, 6, 8, 10, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 9), 2),
      ((⟨{1, 2, 4, 6, 10, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 9), 1),
      ((⟨{1, 2, 6, 8, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 9), 1),
      ((⟨{1, 3, 4, 8, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 9), 4),
      ((⟨{3, 5, 6, 8, 9, 11, 13, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 9), 1),
      ((⟨{3, 5, 6, 8, 10, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 9), 3) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{0, 6}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{0, 9}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{0, 11}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{2, 3}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{3, 12}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{5, 6}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{8, 9}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{9, 10}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{9, 11}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{11, 12}, by decide +kernel⟩ : FullInput 16 2), 2) }
  have hs : (∑ p ∈ schedules, p.2) = 23 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 23 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 9 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 9) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 23 hs (by decide +kernel) 15 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 16) ∈ x.1) ?_ ?_
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel
            ·
              decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B10_D1 :
    onGameValue 16 2 10 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (7/9 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 10 × ℕ) :=
    { ((⟨{0, 2, 3, 5, 6, 8, 9, 13, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 10), 1),
      ((⟨{0, 2, 3, 5, 6, 8, 10, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 10), 1),
      ((⟨{0, 2, 3, 6, 8, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 10), 1),
      ((⟨{0, 2, 4, 5, 7, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 10), 1),
      ((⟨{1, 2, 4, 5, 7, 8, 11, 13, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 10), 1),
      ((⟨{1, 2, 4, 5, 8, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 10), 1),
      ((⟨{1, 2, 5, 6, 8, 10, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 10), 1),
      ((⟨{1, 4, 5, 6, 8, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 10), 1),
      ((⟨{2, 3, 5, 7, 8, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 10), 1) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{3, 12}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{5, 6}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{8, 9}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{9, 10}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{11, 12}, by decide +kernel⟩ : FullInput 16 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 9 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 9 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 10 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 10) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 9 hs (by decide +kernel) 7 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 16) ∈ x.1) ?_ ?_
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B11_D1 :
    onGameValue 16 2 11 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 11 × ℕ) :=
    { ((⟨{0, 2, 3, 5, 6, 8, 9, 11, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 11), 1) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 11 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 11) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B2_D2 :
    onGameValue 16 2 2 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 2 × ℕ) :=
    { ((⟨{14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 2), 1) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 2 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 2) (D := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B3_D2 :
    onGameValue 16 2 3 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 3 × ℕ) :=
    { ((⟨{0, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 3), 1) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 3 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 3) (D := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B4_D2 :
    onGameValue 16 2 4 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1/10 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 4 × ℕ) :=
    { ((⟨{1, 3, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{2, 5, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{2, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{2, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{4, 9, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{4, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{5, 6, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{7, 9, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{7, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{10, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{0, 5}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{0, 8}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{0, 11}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{3, 5}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{3, 8}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{3, 11}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{6, 11}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{9, 10}, by decide +kernel⟩ : FullInput 16 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 10 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 10 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 4 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 4) (D := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 10 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B5_D2 :
    onGameValue 16 2 5 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1/4 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 5 × ℕ) :=
    { ((⟨{0, 3, 4, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 2),
      ((⟨{1, 2, 9, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 2),
      ((⟨{1, 8, 9, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 2),
      ((⟨{1, 10, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 2),
      ((⟨{2, 3, 6, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 2),
      ((⟨{2, 5, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 2),
      ((⟨{2, 7, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 2),
      ((⟨{4, 7, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 2),
      ((⟨{4, 10, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 2),
      ((⟨{5, 6, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 2),
      ((⟨{5, 7, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 2),
      ((⟨{7, 10, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 2) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 3),
      ((⟨{0, 7}, by decide +kernel⟩ : FullInput 16 2), 3),
      ((⟨{0, 11}, by decide +kernel⟩ : FullInput 16 2), 3),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 16 2), 3),
      ((⟨{4, 7}, by decide +kernel⟩ : FullInput 16 2), 3),
      ((⟨{4, 11}, by decide +kernel⟩ : FullInput 16 2), 3),
      ((⟨{7, 8}, by decide +kernel⟩ : FullInput 16 2), 3),
      ((⟨{10, 11}, by decide +kernel⟩ : FullInput 16 2), 3) }
  have hs : (∑ p ∈ schedules, p.2) = 24 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 24 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 5 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 5) (D := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 24 hs (by decide +kernel) 6 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 16) ∈ x.1) ?_ ?_
      ·
        decide +kernel
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          decide +kernel
        ·
          decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B6_D2 :
    onGameValue 16 2 6 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (5/11 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 6 × ℕ) :=
    { ((⟨{0, 3, 10, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 1),
      ((⟨{1, 3, 5, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 4),
      ((⟨{1, 4, 6, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 1),
      ((⟨{1, 7, 10, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 4),
      ((⟨{2, 3, 6, 7, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 2),
      ((⟨{2, 3, 6, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 2),
      ((⟨{2, 3, 10, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 1),
      ((⟨{2, 5, 6, 9, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 1),
      ((⟨{4, 7, 8, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 2),
      ((⟨{4, 7, 10, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 2),
      ((⟨{6, 7, 10, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 1),
      ((⟨{6, 7, 10, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 1) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{0, 7}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{0, 8}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{0, 11}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{3, 10}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{4, 5}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{4, 11}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{7, 8}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{10, 11}, by decide +kernel⟩ : FullInput 16 2), 2) }
  have hs : (∑ p ∈ schedules, p.2) = 22 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 22 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 6 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 6) (D := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 22 hs (by decide +kernel) 10 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 16) ∈ x.1) ?_ ?_
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            decide +kernel
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 16) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B7_D2 :
    onGameValue 16 2 7 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (2/3 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 7 × ℕ) :=
    { ((⟨{0, 3, 4, 7, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 3),
      ((⟨{2, 3, 6, 7, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 3),
      ((⟨{2, 3, 6, 10, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 3),
      ((⟨{2, 3, 7, 10, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 3),
      ((⟨{2, 6, 7, 10, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 3),
      ((⟨{5, 6, 7, 10, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 3) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{0, 8}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{0, 11}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{3, 4}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{3, 7}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{4, 5}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{6, 7}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{10, 11}, by decide +kernel⟩ : FullInput 16 2), 4) }
  have hs : (∑ p ∈ schedules, p.2) = 18 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 18 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 7 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 7) (D := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 18 hs (by decide +kernel) 12 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 16) ∈ x.1) ?_ ?_
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 16) ∈ x.1) ?_ ?_
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 16) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B8_D2 :
    onGameValue 16 2 8 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 8 × ℕ) :=
    { ((⟨{2, 3, 6, 7, 10, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 8), 1) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 8 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 8) (D := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 16) ∈ x.1) ?_ ?_
      ·
        decide +kernel
      ·
        decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B2_D3 :
    onGameValue 16 2 2 3 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 2 × ℕ) :=
    { ((⟨{14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 2), 1) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 2 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 2) (D := 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B3_D3 :
    onGameValue 16 2 3 3 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 3 × ℕ) :=
    { ((⟨{0, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 3), 1) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 3 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 3) (D := 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B4_D3 :
    onGameValue 16 2 4 3 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1/6 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 4 × ℕ) :=
    { ((⟨{2, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{3, 4, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{3, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{5, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{6, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1),
      ((⟨{10, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 4), 1) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{0, 5}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{1, 10}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{4, 5}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{5, 10}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{9, 10}, by decide +kernel⟩ : FullInput 16 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 6 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 6 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 4 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 4) (D := 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 6 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B5_D3 :
    onGameValue 16 2 5 3 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (5/13 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 5 × ℕ) :=
    { ((⟨{0, 4, 5, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 1),
      ((⟨{1, 11, 13, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 1),
      ((⟨{2, 4, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 2),
      ((⟨{2, 9, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 1),
      ((⟨{3, 4, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 2),
      ((⟨{3, 7, 8, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 1),
      ((⟨{3, 8, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 1),
      ((⟨{5, 6, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 1),
      ((⟨{5, 9, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 5), 3) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{0, 5}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{0, 9}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{0, 10}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{4, 5}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{5, 6}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{5, 10}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{9, 10}, by decide +kernel⟩ : FullInput 16 2), 2) }
  have hs : (∑ p ∈ schedules, p.2) = 13 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 13 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 5 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 5) (D := 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 13 hs (by decide +kernel) 5 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 16) ∈ x.1) ?_ ?_
      ·
        decide +kernel
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          decide +kernel
        ·
          decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B6_D3 :
    onGameValue 16 2 6 3 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (3/5 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 6 × ℕ) :=
    { ((⟨{0, 4, 6, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 1),
      ((⟨{1, 3, 9, 11, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 1),
      ((⟨{1, 7, 9, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 1),
      ((⟨{3, 4, 8, 9, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 1),
      ((⟨{4, 5, 9, 12, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 6), 1) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 2),
      ((⟨{5, 6}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{5, 10}, by decide +kernel⟩ : FullInput 16 2), 1),
      ((⟨{9, 10}, by decide +kernel⟩ : FullInput 16 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 5 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 5 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 6 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 6) (D := 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 5 hs (by decide +kernel) 3 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 16) ∈ x.1) ?_ ?_
      ·
        decide +kernel
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 16) ∈ x.1) ?_ ?_
        ·
          decide +kernel
        ·
          decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H16_m2_B7_D3 :
    onGameValue 16 2 7 3 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1 : ℝ) := by
  let schedules : Finset (OnSchedule 16 2 7 × ℕ) :=
    { ((⟨{0, 4, 5, 9, 10, 14, 15}, by decide +kernel, by decide +kernel⟩ : OnSchedule 16 2 7), 1) }
  let inputs : Finset (FullInput 16 2 × ℕ) :=
    { ((⟨{0, 1}, by decide +kernel⟩ : FullInput 16 2), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 16 2
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 16 2
  let cols := optimizedOnScheduleEnum 16 2 7 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 16) (m := 2) (B := 7) (D := 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H8_m3_B5_D1 :
    offGameValue 8 3 5 1 (by decide +kernel) (by decide +kernel) = (1/2 : ℝ) := by
  let schedules : Finset (OffSchedule 8 5 × ℕ) :=
    { ((⟨{0, 2, 3, 4, 6}, by decide +kernel⟩ : OffSchedule 8 5), 1),
      ((⟨{0, 2, 3, 4, 7}, by decide +kernel⟩ : OffSchedule 8 5), 1),
      ((⟨{0, 2, 5, 6, 7}, by decide +kernel⟩ : OffSchedule 8 5), 1),
      ((⟨{1, 2, 3, 6, 7}, by decide +kernel⟩ : OffSchedule 8 5), 1),
      ((⟨{1, 3, 5, 6, 7}, by decide +kernel⟩ : OffSchedule 8 5), 1),
      ((⟨{2, 4, 5, 6, 7}, by decide +kernel⟩ : OffSchedule 8 5), 1) }
  let inputs : Finset (FullInput 8 3 × ℕ) :=
    { ((⟨{0, 1, 7}, by decide +kernel⟩ : FullInput 8 3), 3),
      ((⟨{3, 4, 5}, by decide +kernel⟩ : FullInput 8 3), 3) }
  have hs : (∑ p ∈ schedules, p.2) = 6 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 6 := by decide +kernel
  let rows := fullInputEnum 8 3
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 3
  let cols := offScheduleEnum 8 5
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 8 5
  have h := off_certificate_value (H := 8) (m := 3) (B := 5) (D := 1)
    (by decide +kernel) (by decide +kernel) schedules 6 hs (by decide +kernel) 3 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H8_m3_B5_D1 :
    onGameValue 8 3 5 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 8 3 5 × ℕ) :=
    { ((⟨{0, 1, 5, 6, 7}, by decide +kernel, by decide +kernel⟩ : OnSchedule 8 3 5), 1) }
  let inputs : Finset (FullInput 8 3 × ℕ) :=
    { ((⟨{0, 1, 2}, by decide +kernel⟩ : FullInput 8 3), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 8 3
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 3
  let cols := optimizedOnScheduleEnum 8 3 5 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 8) (m := 3) (B := 5) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H8_m3_B4_D2 :
    offGameValue 8 3 4 2 (by decide +kernel) (by decide +kernel) = (1/2 : ℝ) := by
  let schedules : Finset (OffSchedule 8 4 × ℕ) :=
    { ((⟨{2, 3, 4, 7}, by decide +kernel⟩ : OffSchedule 8 4), 1),
      ((⟨{2, 5, 6, 7}, by decide +kernel⟩ : OffSchedule 8 4), 1) }
  let inputs : Finset (FullInput 8 3 × ℕ) :=
    { ((⟨{0, 2, 4}, by decide +kernel⟩ : FullInput 8 3), 1),
      ((⟨{5, 6, 7}, by decide +kernel⟩ : FullInput 8 3), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 2 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 2 := by decide +kernel
  let rows := fullInputEnum 8 3
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 3
  let cols := offScheduleEnum 8 4
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 8 4
  have h := off_certificate_value (H := 8) (m := 3) (B := 4) (D := 2)
    (by decide +kernel) (by decide +kernel) schedules 2 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H8_m3_B4_D2 :
    onGameValue 8 3 4 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 8 3 4 × ℕ) :=
    { ((⟨{0, 5, 6, 7}, by decide +kernel, by decide +kernel⟩ : OnSchedule 8 3 4), 1) }
  let inputs : Finset (FullInput 8 3 × ℕ) :=
    { ((⟨{0, 1, 2}, by decide +kernel⟩ : FullInput 8 3), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 8 3
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 8 3
  let cols := optimizedOnScheduleEnum 8 3 4 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 8) (m := 3) (B := 4) (D := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H10_m4_B7_D1 :
    offGameValue 10 4 7 1 (by decide +kernel) (by decide +kernel) = (1/2 : ℝ) := by
  let schedules : Finset (OffSchedule 10 7 × ℕ) :=
    { ((⟨{0, 1, 2, 6, 7, 8, 9}, by decide +kernel⟩ : OffSchedule 10 7), 1),
      ((⟨{0, 1, 3, 4, 5, 6, 9}, by decide +kernel⟩ : OffSchedule 10 7), 1),
      ((⟨{0, 2, 3, 4, 5, 7, 8}, by decide +kernel⟩ : OffSchedule 10 7), 1),
      ((⟨{1, 2, 3, 4, 6, 8, 9}, by decide +kernel⟩ : OffSchedule 10 7), 1),
      ((⟨{1, 2, 3, 4, 7, 8, 9}, by decide +kernel⟩ : OffSchedule 10 7), 1),
      ((⟨{1, 2, 4, 6, 7, 8, 9}, by decide +kernel⟩ : OffSchedule 10 7), 1),
      ((⟨{1, 4, 5, 6, 7, 8, 9}, by decide +kernel⟩ : OffSchedule 10 7), 1),
      ((⟨{2, 3, 4, 6, 7, 8, 9}, by decide +kernel⟩ : OffSchedule 10 7), 1) }
  let inputs : Finset (FullInput 10 4 × ℕ) :=
    { ((⟨{0, 7, 8, 9}, by decide +kernel⟩ : FullInput 10 4), 4),
      ((⟨{2, 3, 4, 5}, by decide +kernel⟩ : FullInput 10 4), 4) }
  have hs : (∑ p ∈ schedules, p.2) = 8 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 8 := by decide +kernel
  let rows := fullInputEnum 10 4
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 10 4
  let cols := offScheduleEnum 10 7
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 10 7
  have h := off_certificate_value (H := 10) (m := 4) (B := 7) (D := 1)
    (by decide +kernel) (by decide +kernel) schedules 8 hs (by decide +kernel) 4 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H10_m4_B7_D1 :
    onGameValue 10 4 7 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 10 4 7 × ℕ) :=
    { ((⟨{0, 1, 2, 6, 7, 8, 9}, by decide +kernel, by decide +kernel⟩ : OnSchedule 10 4 7), 1) }
  let inputs : Finset (FullInput 10 4 × ℕ) :=
    { ((⟨{0, 1, 2, 3}, by decide +kernel⟩ : FullInput 10 4), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 10 4
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 10 4
  let cols := optimizedOnScheduleEnum 10 4 7 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 10) (m := 4) (B := 7) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H10_m4_B7_D2 :
    offGameValue 10 4 7 2 (by decide +kernel) (by decide +kernel) = (1/2 : ℝ) := by
  let schedules : Finset (OffSchedule 10 7 × ℕ) :=
    { ((⟨{0, 1, 2, 3, 6, 7, 9}, by decide +kernel⟩ : OffSchedule 10 7), 1),
      ((⟨{0, 1, 2, 3, 6, 8, 9}, by decide +kernel⟩ : OffSchedule 10 7), 1),
      ((⟨{0, 1, 3, 6, 7, 8, 9}, by decide +kernel⟩ : OffSchedule 10 7), 1),
      ((⟨{0, 2, 3, 6, 7, 8, 9}, by decide +kernel⟩ : OffSchedule 10 7), 1) }
  let inputs : Finset (FullInput 10 4 × ℕ) :=
    { ((⟨{0, 1, 2, 3}, by decide +kernel⟩ : FullInput 10 4), 2),
      ((⟨{6, 7, 8, 9}, by decide +kernel⟩ : FullInput 10 4), 2) }
  have hs : (∑ p ∈ schedules, p.2) = 4 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 4 := by decide +kernel
  let rows := fullInputEnum 10 4
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 10 4
  let cols := offScheduleEnum 10 7
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 10 7
  have h := off_certificate_value (H := 10) (m := 4) (B := 7) (D := 2)
    (by decide +kernel) (by decide +kernel) schedules 4 hs (by decide +kernel) 2 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H10_m4_B7_D2 :
    onGameValue 10 4 7 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (0 : ℝ) := by
  let schedules : Finset (OnSchedule 10 4 7 × ℕ) :=
    { ((⟨{0, 1, 2, 6, 7, 8, 9}, by decide +kernel, by decide +kernel⟩ : OnSchedule 10 4 7), 1) }
  let inputs : Finset (FullInput 10 4 × ℕ) :=
    { ((⟨{0, 1, 2, 3}, by decide +kernel⟩ : FullInput 10 4), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 1 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 1 := by decide +kernel
  let rows := fullInputEnum 10 4
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 10 4
  let cols := optimizedOnScheduleEnum 10 4 7 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 10) (m := 4) (B := 7) (D := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 1 hs (by decide +kernel) 0 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H10_m3_B7_D1 :
    offGameValue 10 3 7 1 (by decide +kernel) (by decide +kernel) = (2/3 : ℝ) := by
  let schedules : Finset (OffSchedule 10 7 × ℕ) :=
    { ((⟨{0, 2, 3, 4, 6, 7, 9}, by decide +kernel⟩ : OffSchedule 10 7), 1),
      ((⟨{0, 2, 3, 5, 7, 8, 9}, by decide +kernel⟩ : OffSchedule 10 7), 1),
      ((⟨{1, 3, 4, 6, 7, 8, 9}, by decide +kernel⟩ : OffSchedule 10 7), 1) }
  let inputs : Finset (FullInput 10 3 × ℕ) :=
    { ((⟨{0, 1, 2}, by decide +kernel⟩ : FullInput 10 3), 1),
      ((⟨{2, 8, 9}, by decide +kernel⟩ : FullInput 10 3), 1),
      ((⟨{4, 5, 6}, by decide +kernel⟩ : FullInput 10 3), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 3 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 3 := by decide +kernel
  let rows := fullInputEnum 10 3
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 10 3
  let cols := offScheduleEnum 10 7
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 10 7
  have h := off_certificate_value (H := 10) (m := 3) (B := 7) (D := 1)
    (by decide +kernel) (by decide +kernel) schedules 3 hs (by decide +kernel) 2 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H10_m3_B7_D1 :
    onGameValue 10 3 7 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1/2 : ℝ) := by
  let schedules : Finset (OnSchedule 10 3 7 × ℕ) :=
    { ((⟨{1, 2, 3, 5, 7, 8, 9}, by decide +kernel, by decide +kernel⟩ : OnSchedule 10 3 7), 1),
      ((⟨{1, 3, 4, 6, 7, 8, 9}, by decide +kernel, by decide +kernel⟩ : OnSchedule 10 3 7), 1) }
  let inputs : Finset (FullInput 10 3 × ℕ) :=
    { ((⟨{0, 1, 2}, by decide +kernel⟩ : FullInput 10 3), 1),
      ((⟨{0, 4, 5}, by decide +kernel⟩ : FullInput 10 3), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 2 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 2 := by decide +kernel
  let rows := fullInputEnum 10 3
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 10 3
  let cols := optimizedOnScheduleEnum 10 3 7 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 10) (m := 3) (B := 7) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 2 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H12_m3_B7_D2 :
    offGameValue 12 3 7 2 (by decide +kernel) (by decide +kernel) = (2/3 : ℝ) := by
  let schedules : Finset (OffSchedule 12 7 × ℕ) :=
    { ((⟨{0, 1, 4, 5, 6, 9, 11}, by decide +kernel⟩ : OffSchedule 12 7), 1),
      ((⟨{1, 2, 3, 6, 9, 10, 11}, by decide +kernel⟩ : OffSchedule 12 7), 1),
      ((⟨{2, 4, 6, 7, 9, 10, 11}, by decide +kernel⟩ : OffSchedule 12 7), 1) }
  let inputs : Finset (FullInput 12 3 × ℕ) :=
    { ((⟨{0, 1, 2}, by decide +kernel⟩ : FullInput 12 3), 1),
      ((⟨{5, 6, 9}, by decide +kernel⟩ : FullInput 12 3), 1),
      ((⟨{9, 10, 11}, by decide +kernel⟩ : FullInput 12 3), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 3 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 3 := by decide +kernel
  let rows := fullInputEnum 12 3
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 3
  let cols := offScheduleEnum 12 7
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 12 7
  have h := off_certificate_value (H := 12) (m := 3) (B := 7) (D := 2)
    (by decide +kernel) (by decide +kernel) schedules 3 hs (by decide +kernel) 2 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 12) ∈ x.1) ?_ ?_
      ·
        decide +kernel
      ·
        decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H12_m3_B7_D2 :
    onGameValue 12 3 7 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1/2 : ℝ) := by
  let schedules : Finset (OnSchedule 12 3 7 × ℕ) :=
    { ((⟨{1, 2, 4, 7, 9, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 3 7), 1),
      ((⟨{2, 5, 6, 7, 9, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 3 7), 1) }
  let inputs : Finset (FullInput 12 3 × ℕ) :=
    { ((⟨{0, 1, 2}, by decide +kernel⟩ : FullInput 12 3), 1),
      ((⟨{2, 5, 6}, by decide +kernel⟩ : FullInput 12 3), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 2 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 2 := by decide +kernel
  let rows := fullInputEnum 12 3
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 3
  let cols := optimizedOnScheduleEnum 12 3 7 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 12) (m := 3) (B := 7) (D := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 2 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H12_m4_B9_D1 :
    offGameValue 12 4 9 1 (by decide +kernel) (by decide +kernel) = (3/5 : ℝ) := by
  let schedules : Finset (OffSchedule 12 9 × ℕ) :=
    { ((⟨{0, 1, 2, 3, 5, 6, 7, 8, 11}, by decide +kernel⟩ : OffSchedule 12 9), 1),
      ((⟨{0, 1, 3, 4, 5, 6, 8, 9, 11}, by decide +kernel⟩ : OffSchedule 12 9), 1),
      ((⟨{0, 1, 3, 4, 5, 8, 9, 10, 11}, by decide +kernel⟩ : OffSchedule 12 9), 1),
      ((⟨{0, 2, 3, 4, 7, 8, 9, 10, 11}, by decide +kernel⟩ : OffSchedule 12 9), 1),
      ((⟨{1, 2, 3, 4, 6, 7, 8, 10, 11}, by decide +kernel⟩ : OffSchedule 12 9), 1),
      ((⟨{1, 2, 3, 4, 6, 7, 9, 10, 11}, by decide +kernel⟩ : OffSchedule 12 9), 1),
      ((⟨{1, 2, 3, 6, 7, 8, 9, 10, 11}, by decide +kernel⟩ : OffSchedule 12 9), 1),
      ((⟨{1, 2, 4, 5, 6, 8, 9, 10, 11}, by decide +kernel⟩ : OffSchedule 12 9), 1),
      ((⟨{1, 3, 5, 6, 7, 8, 9, 10, 11}, by decide +kernel⟩ : OffSchedule 12 9), 1),
      ((⟨{2, 3, 4, 6, 7, 8, 9, 10, 11}, by decide +kernel⟩ : OffSchedule 12 9), 1) }
  let inputs : Finset (FullInput 12 4 × ℕ) :=
    { ((⟨{0, 1, 2, 3}, by decide +kernel⟩ : FullInput 12 4), 2),
      ((⟨{0, 1, 5, 6}, by decide +kernel⟩ : FullInput 12 4), 2),
      ((⟨{3, 4, 5, 6}, by decide +kernel⟩ : FullInput 12 4), 2),
      ((⟨{8, 9, 10, 11}, by decide +kernel⟩ : FullInput 12 4), 4) }
  have hs : (∑ p ∈ schedules, p.2) = 10 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 10 := by decide +kernel
  let rows := fullInputEnum 12 4
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 4
  let cols := offScheduleEnum 12 9
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 12 9
  have h := off_certificate_value (H := 12) (m := 4) (B := 9) (D := 1)
    (by decide +kernel) (by decide +kernel) schedules 10 hs (by decide +kernel) 6 inputs hi
    rows hrows (by
      refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 12) ∈ x.1) ?_ ?_
      ·
        decide +kernel
      ·
        refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 12) ∈ x.1) ?_ ?_
        ·
          decide +kernel
        ·
          refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 12) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H12_m4_B9_D1 :
    onGameValue 12 4 9 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1/3 : ℝ) := by
  let schedules : Finset (OnSchedule 12 4 9 × ℕ) :=
    { ((⟨{0, 2, 3, 4, 6, 8, 9, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 4 9), 1),
      ((⟨{0, 2, 3, 6, 7, 8, 9, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 4 9), 1),
      ((⟨{1, 3, 4, 5, 7, 8, 9, 10, 11}, by decide +kernel, by decide +kernel⟩ : OnSchedule 12 4 9), 1) }
  let inputs : Finset (FullInput 12 4 × ℕ) :=
    { ((⟨{0, 1, 2, 3}, by decide +kernel⟩ : FullInput 12 4), 1),
      ((⟨{0, 1, 5, 6}, by decide +kernel⟩ : FullInput 12 4), 1),
      ((⟨{3, 4, 5, 6}, by decide +kernel⟩ : FullInput 12 4), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 3 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 3 := by decide +kernel
  let rows := fullInputEnum 12 4
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 12 4
  let cols := optimizedOnScheduleEnum 12 4 9 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 12) (m := 4) (B := 9) (D := 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 3 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_off_H14_m4_B9_D2 :
    offGameValue 14 4 9 2 (by decide +kernel) (by decide +kernel) = (3/5 : ℝ) := by
  let schedules : Finset (OffSchedule 14 9 × ℕ) :=
    { ((⟨{0, 1, 2, 3, 4, 6, 7, 9, 10}, by decide +kernel⟩ : OffSchedule 14 9), 2),
      ((⟨{0, 1, 3, 4, 5, 8, 9, 12, 13}, by decide +kernel⟩ : OffSchedule 14 9), 1),
      ((⟨{0, 1, 4, 5, 7, 8, 10, 11, 13}, by decide +kernel⟩ : OffSchedule 14 9), 2),
      ((⟨{0, 2, 4, 5, 7, 9, 10, 12, 13}, by decide +kernel⟩ : OffSchedule 14 9), 1),
      ((⟨{0, 2, 4, 5, 7, 9, 11, 12, 13}, by decide +kernel⟩ : OffSchedule 14 9), 1),
      ((⟨{0, 3, 5, 7, 8, 10, 11, 12, 13}, by decide +kernel⟩ : OffSchedule 14 9), 2),
      ((⟨{1, 2, 3, 4, 9, 10, 11, 12, 13}, by decide +kernel⟩ : OffSchedule 14 9), 1),
      ((⟨{1, 2, 3, 5, 7, 8, 9, 12, 13}, by decide +kernel⟩ : OffSchedule 14 9), 1),
      ((⟨{1, 2, 4, 5, 7, 10, 11, 12, 13}, by decide +kernel⟩ : OffSchedule 14 9), 3),
      ((⟨{1, 3, 4, 6, 7, 10, 11, 12, 13}, by decide +kernel⟩ : OffSchedule 14 9), 2),
      ((⟨{1, 5, 6, 7, 8, 10, 11, 12, 13}, by decide +kernel⟩ : OffSchedule 14 9), 1),
      ((⟨{2, 4, 5, 6, 9, 10, 11, 12, 13}, by decide +kernel⟩ : OffSchedule 14 9), 2),
      ((⟨{3, 6, 7, 8, 9, 10, 11, 12, 13}, by decide +kernel⟩ : OffSchedule 14 9), 1) }
  let inputs : Finset (FullInput 14 4 × ℕ) :=
    { ((⟨{0, 1, 2, 3}, by decide +kernel⟩ : FullInput 14 4), 8),
      ((⟨{6, 7, 8, 9}, by decide +kernel⟩ : FullInput 14 4), 4),
      ((⟨{6, 7, 12, 13}, by decide +kernel⟩ : FullInput 14 4), 4),
      ((⟨{10, 11, 12, 13}, by decide +kernel⟩ : FullInput 14 4), 4) }
  have hs : (∑ p ∈ schedules, p.2) = 20 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 20 := by decide +kernel
  let rows := fullInputEnum 14 4
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 14 4
  let cols := offScheduleEnum 14 9
  have hcols : cols = Finset.univ := offScheduleEnum_eq_univ 14 9
  have h := off_certificate_value (H := 14) (m := 4) (B := 9) (D := 2)
    (by decide +kernel) (by decide +kernel) schedules 20 hs (by decide +kernel) 12 inputs hi
    rows hrows (by
      refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 14) ∈ x.1) ?_ ?_
      ·
        refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 14) ∈ x.1) ?_ ?_
        ·
          decide +kernel
        ·
          refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 14) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 14) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
      ·
        refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 14) ∈ x.1) ?_ ?_
        ·
          refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 14) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 14) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
        ·
          refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 14) ∈ x.1) ?_ ?_
          ·
            refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 14) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              decide +kernel
          ·
            refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (3 : Fin 14) ∈ x.1) ?_ ?_
            ·
              decide +kernel
            ·
              refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (4 : Fin 14) ∈ x.1) ?_ ?_
              ·
                decide +kernel
              ·
                decide +kernel)
    cols hcols (by
      refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 14) ∈ x.1) ?_ ?_
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 14) ∈ x.1) ?_ ?_
        ·
          refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (2 : Fin 14) ∈ x.1) ?_ ?_
          ·
            decide +kernel
          ·
            decide +kernel
        ·
          decide +kernel
      ·
        refine colsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 14) ∈ x.1) ?_ ?_
        ·
          decide +kernel
        ·
          decide +kernel)
  norm_num at h ⊢
  exact h

theorem certificate_value_on_H14_m4_B9_D2 :
    onGameValue 14 4 9 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) = (1/3 : ℝ) := by
  let schedules : Finset (OnSchedule 14 4 9 × ℕ) :=
    { ((⟨{0, 2, 4, 5, 7, 10, 11, 12, 13}, by decide +kernel, by decide +kernel⟩ : OnSchedule 14 4 9), 1),
      ((⟨{1, 3, 6, 7, 9, 10, 11, 12, 13}, by decide +kernel, by decide +kernel⟩ : OnSchedule 14 4 9), 1),
      ((⟨{3, 4, 5, 6, 7, 10, 11, 12, 13}, by decide +kernel, by decide +kernel⟩ : OnSchedule 14 4 9), 1) }
  let inputs : Finset (FullInput 14 4 × ℕ) :=
    { ((⟨{0, 1, 2, 3}, by decide +kernel⟩ : FullInput 14 4), 1),
      ((⟨{0, 1, 6, 7}, by decide +kernel⟩ : FullInput 14 4), 1),
      ((⟨{4, 5, 6, 7}, by decide +kernel⟩ : FullInput 14 4), 1) }
  have hs : (∑ p ∈ schedules, p.2) = 3 := by decide +kernel
  have hi : (∑ p ∈ inputs, p.2) = 3 := by decide +kernel
  let rows := fullInputEnum 14 4
  have hrows : rows = Finset.univ := fullInputEnum_eq_univ 14 4
  let cols := optimizedOnScheduleEnum 14 4 9 (by decide +kernel) (by decide +kernel)
  have hcols : cols = Finset.univ := optimizedOnScheduleEnum_eq_univ (by decide +kernel) (by decide +kernel)
  have h := on_certificate_value (H := 14) (m := 4) (B := 9) (D := 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) schedules 3 hs (by decide +kernel) 1 inputs hi
    rows hrows (by
      refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (0 : Fin 14) ∈ x.1) ?_ ?_
      ·
        decide +kernel
      ·
        refine rowsCheckedOnFinset_partition _ _ _ _ (fun x => (1 : Fin 14) ∈ x.1) ?_ ?_
        ·
          decide +kernel
        ·
          decide +kernel)
    cols hcols (by
      decide +kernel)
  norm_num at h ⊢
  exact h

end TrafficShaping
