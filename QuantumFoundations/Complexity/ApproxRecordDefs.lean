import QuantumFoundations.Complexity.NormalizedBranches

/-!
# C8a — Aggregated approximate quantum records

The primary error budget is deliberately aggregated: one number bounds the
sum of the target-fixing defect and the leakage of the rejected state.  This
is exactly the combination consumed by the cross-amplitude estimate in C8b.
-/

namespace QuantumFoundations.Complexity

open Gleason

noncomputable section

/-- `P` records `target` rather than `other` with combined error at most
`η`: the target-fixing defect and rejected-state leakage share one budget. -/
def ApproxRecordFor {n : ℕ}
    (P : H n →ₗ[ℂ] H n) (target other : H n) (η : ℝ) : Prop :=
  ‖P target - target‖ + ‖P other‖ ≤ η

namespace ApproxRecordFor

/-- Increasing the combined error budget preserves an approximate record. -/
theorem mono {n : ℕ} {P : H n →ₗ[ℂ] H n} {target other : H n} {η η' : ℝ}
    (h : ApproxRecordFor P target other η) (hη : η ≤ η') :
    ApproxRecordFor P target other η' :=
  h.trans hη

end ApproxRecordFor

/-- Separate fixing and leakage estimates can be combined into the primary
aggregated record predicate. -/
theorem approxRecordFor_of_component_bounds {n : ℕ}
    {P : H n →ₗ[ℂ] H n} {target other : H n}
    {εfix εleak η : ℝ}
    (hfix : ‖P target - target‖ ≤ εfix)
    (hleak : ‖P other‖ ≤ εleak)
    (hsum : εfix + εleak ≤ η) :
    ApproxRecordFor P target other η := by
  unfold ApproxRecordFor
  linarith

/-- Exact fixing and rejection give aggregate error zero. -/
theorem approxRecordFor_zero_of_fixes_rejects {n : ℕ}
    {P : H n →ₗ[ℂ] H n} {target other : H n}
    (hfix : P target = target) (hreject : P other = 0) :
    ApproxRecordFor P target other 0 := by
  simp [ApproxRecordFor, hfix, hreject]

/-- The target-fixing defect is individually bounded by the aggregate. -/
theorem approxRecordFor_fix_le {n : ℕ}
    {P : H n →ₗ[ℂ] H n} {target other : H n} {η : ℝ}
    (h : ApproxRecordFor P target other η) :
    ‖P target - target‖ ≤ η := by
  unfold ApproxRecordFor at h
  linarith [norm_nonneg (P other)]

/-- The rejected-state leakage is individually bounded by the aggregate. -/
theorem approxRecordFor_reject_le {n : ℕ}
    {P : H n →ₗ[ℂ] H n} {target other : H n} {η : ℝ}
    (h : ApproxRecordFor P target other η) :
    ‖P other‖ ≤ η := by
  unfold ApproxRecordFor at h
  linarith [norm_nonneg (P target - target)]

/-- Any inhabited approximate-record budget is nonnegative. -/
theorem zero_le_error_of_approxRecordFor {n : ℕ}
    {P : H n →ₗ[ℂ] H n} {target other : H n} {η : ℝ}
    (h : ApproxRecordFor P target other η) : 0 ≤ η := by
  unfold ApproxRecordFor at h
  linarith [norm_nonneg (P target - target), norm_nonneg (P other)]

end


end QuantumFoundations.Complexity
