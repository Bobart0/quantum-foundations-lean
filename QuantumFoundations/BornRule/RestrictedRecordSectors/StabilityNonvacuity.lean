import QuantumFoundations.BornRule.RestrictedRecordSectors.Stability

/-!
# C17 non-vacuity

Explicit scalar examples show that the quantitative estimate applies at
strictly positive component distance, not only when the two components
coincide.
-/

namespace QuantumFoundations.BornRule.RestrictedRecordSectors

open scoped BigOperators

/-- At `u = 1` and `v = 1/2`, the squared-norm discrepancy is `3/4`, the
component distance is `1/2`, and the constant-two bound is the nonzero value
`1`. -/
theorem normSq_stability_nonzero_example :
    |‖(1 : ℝ)‖ ^ 2 - ‖(1 / 2 : ℝ)‖ ^ 2| = 3 / 4 ∧
      ‖(1 : ℝ) - (1 / 2 : ℝ)‖ = 1 / 2 ∧
      |‖(1 : ℝ)‖ ^ 2 - ‖(1 / 2 : ℝ)‖ ^ 2| ≤
        2 * ‖(1 : ℝ) - (1 / 2 : ℝ)‖ := by
  norm_num [Real.norm_eq_abs]

/-- Two copies of the same nonzero scalar perturbation give a finite-family
instance of the uniform estimate. -/
theorem normSq_stability_two_point_example :
    (∑ _ : Fin 2,
      |‖(1 : ℝ)‖ ^ 2 - ‖(1 / 2 : ℝ)‖ ^ 2|) ≤
        2 * ((Finset.univ : Finset (Fin 2)).card : ℝ) * (1 / 2 : ℝ) := by
  norm_num [Real.norm_eq_abs]

end QuantumFoundations.BornRule.RestrictedRecordSectors
