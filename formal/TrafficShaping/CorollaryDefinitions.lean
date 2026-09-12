import TrafficShaping.MainTheorem

/-! Shared arithmetic quantities used by the article's corollaries. -/

namespace TrafficShaping

/-- The budget in equation (20), with the Euclidean quotient and remainder. -/
def perfectBudget (H m D : ℕ) : ℕ :=
  m * (H / (D + m)) + min m (H % (D + m))

/-- Number of nonempty blocks of length `D + m` in the finite horizon. -/
def testBlockCount (H m D : ℕ) : ℕ :=
  H / (D + m) + if H % (D + m) = 0 then 0 else 1

/-- Last `m` slots of each full block, and the last `min m b` of the remainder. -/
def perfectSchedule (H m D : ℕ) : Trace H :=
  Finset.univ.filter (fun t =>
    min H ((t.val / (D + m) + 1) * (D + m)) - m ≤ t.val)

end TrafficShaping
