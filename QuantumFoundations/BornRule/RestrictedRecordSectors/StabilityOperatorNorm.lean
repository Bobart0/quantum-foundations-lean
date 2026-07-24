import QuantumFoundations.BornRule.RestrictedRecordSectors.Stability
import QuantumFoundations.Complexity.OperatorNorm.Approximation

/-!
# C17b — State and operator-norm stability bridges

This module derives fixed-sector and operator-approximation consequences of
the lightweight C17 norm-square estimate.  It intentionally keeps the C17
core independent of the C12 operator-norm development.
-/

namespace QuantumFoundations.BornRule.RestrictedRecordSectors

open QuantumFoundations.Complexity.OperatorNorm
open scoped InnerProductSpace

/-- On the unit ball, changing the state while keeping the sector fixed
changes the projected quadratic weight by at most twice the state distance. -/
theorem projected_weight_stability_same_sector
    (R : Submodule ℂ (Gleason.H n))
    (ψ φ : Gleason.H n)
    (hψ : ‖ψ‖ ≤ 1)
    (hφ : ‖φ‖ ≤ 1) :
    |‖R.starProjection ψ‖ ^ 2 - ‖R.starProjection φ‖ ^ 2|
      ≤ 2 * ‖ψ - φ‖ := by
  have hRψ : ‖R.starProjection ψ‖ ≤ 1 :=
    (R.norm_starProjection_apply_le ψ).trans hψ
  have hRφ : ‖R.starProjection φ‖ ≤ 1 :=
    (R.norm_starProjection_apply_le φ).trans hφ
  calc
    |‖R.starProjection ψ‖ ^ 2 - ‖R.starProjection φ‖ ^ 2|
        ≤ 2 * ‖R.starProjection ψ - R.starProjection φ‖ :=
      abs_norm_sq_sub_norm_sq_le_two_mul _ _ hRψ hRφ
    _ = 2 * ‖R.starProjection (ψ - φ)‖ := by
      rw [ContinuousLinearMap.map_sub]
    _ ≤ 2 * ‖ψ - φ‖ :=
      mul_le_mul_of_nonneg_left
        (R.norm_starProjection_apply_le (ψ - φ)) (by norm_num)

/-- Normalized-state specialization of
`projected_weight_stability_same_sector`. -/
theorem projected_weight_stability_same_sector_of_normalized
    (R : Submodule ℂ (Gleason.H n))
    (ψ φ : Gleason.H n)
    (hψ : ‖ψ‖ = 1)
    (hφ : ‖φ‖ = 1) :
    |‖R.starProjection ψ‖ ^ 2 - ‖R.starProjection φ‖ ^ 2|
      ≤ 2 * ‖ψ - φ‖ :=
  projected_weight_stability_same_sector R ψ φ hψ.le hφ.le

/-- Operator-norm approximation controls the quadratic output weights on a
unit input whenever both outputs lie in the unit ball. -/
theorem quadratic_weight_stability_of_operator_approximation
    {A B : Gleason.H n →L[ℂ] Gleason.H n}
    {ψ : Gleason.H n} {ε : ℝ}
    (hAB : ApproximatesOperator A B ε)
    (hψ : ‖ψ‖ = 1)
    (hA : ‖A ψ‖ ≤ 1)
    (hB : ‖B ψ‖ ≤ 1) :
    |‖A ψ‖ ^ 2 - ‖B ψ‖ ^ 2| ≤ 2 * ε := by
  calc
    |‖A ψ‖ ^ 2 - ‖B ψ‖ ^ 2| ≤ 2 * ‖A ψ - B ψ‖ :=
      abs_norm_sq_sub_norm_sq_le_two_mul _ _ hA hB
    _ ≤ 2 * ε :=
      mul_le_mul_of_nonneg_left
        (norm_apply_sub_le_of_unit hAB hψ) (by norm_num)

/-- Operator-norm-close orthogonal projections give close quadratic weights
on every normalized state. -/
theorem projected_weight_stability_of_projection_approximation
    (R S : Submodule ℂ (Gleason.H n))
    (ψ : Gleason.H n)
    (hψ : ‖ψ‖ = 1)
    {ε : ℝ}
    (hRS :
      ApproximatesOperator R.starProjection S.starProjection ε) :
    |‖R.starProjection ψ‖ ^ 2 - ‖S.starProjection ψ‖ ^ 2|
      ≤ 2 * ε :=
  quadratic_weight_stability_of_operator_approximation hRS hψ
    ((R.norm_starProjection_apply_le ψ).trans hψ.le)
    ((S.norm_starProjection_apply_le ψ).trans hψ.le)

/-- Direct operator-norm form of projection stability. -/
theorem projected_weight_stability_of_projection_opNorm
    (R S : Submodule ℂ (Gleason.H n))
    (ψ : Gleason.H n)
    (hψ : ‖ψ‖ = 1)
    {ε : ℝ}
    (hRS : ‖R.starProjection - S.starProjection‖ ≤ ε) :
    |‖R.starProjection ψ‖ ^ 2 - ‖S.starProjection ψ‖ ^ 2|
      ≤ 2 * ε :=
  projected_weight_stability_of_projection_approximation R S ψ hψ hRS

/-- Simultaneous state and sector perturbation.  The sector discrepancy is
expressed by an operator-norm approximation certificate, not by a new metric
on subspaces. -/
theorem projected_weight_stability_of_state_and_projection_approximation
    (R S : Submodule ℂ (Gleason.H n))
    (ψ φ : Gleason.H n)
    (hψ : ‖ψ‖ ≤ 1)
    (hφ : ‖φ‖ ≤ 1)
    {ε : ℝ}
    (hRS :
      ApproximatesOperator R.starProjection S.starProjection ε) :
    |‖R.starProjection ψ‖ ^ 2 - ‖S.starProjection φ‖ ^ 2|
      ≤ 2 * (‖ψ - φ‖ + ε) := by
  have hε : 0 ≤ ε := by
    exact (norm_nonneg (R.starProjection - S.starProjection)).trans hRS
  have hRψ : ‖R.starProjection ψ‖ ≤ 1 :=
    (R.norm_starProjection_apply_le ψ).trans hψ
  have hSφ : ‖S.starProjection φ‖ ≤ 1 :=
    (S.norm_starProjection_apply_le φ).trans hφ
  have hcomponent :
      ‖R.starProjection ψ - S.starProjection φ‖ ≤ ‖ψ - φ‖ + ε := by
    calc
      ‖R.starProjection ψ - S.starProjection φ‖
          = ‖R.starProjection (ψ - φ) +
              (R.starProjection φ - S.starProjection φ)‖ := by
            rw [ContinuousLinearMap.map_sub]
            congr 1
            abel
      _ ≤ ‖R.starProjection (ψ - φ)‖ +
            ‖R.starProjection φ - S.starProjection φ‖ :=
        norm_add_le _ _
      _ ≤ ‖ψ - φ‖ + ε * ‖φ‖ :=
        add_le_add
          (R.norm_starProjection_apply_le (ψ - φ))
          (norm_apply_sub_le_of_approximatesOperator hRS φ)
      _ ≤ ‖ψ - φ‖ + ε := by
        exact add_le_add (le_refl _)
          (by simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hφ hε)
  calc
    |‖R.starProjection ψ‖ ^ 2 - ‖S.starProjection φ‖ ^ 2|
        ≤ 2 * ‖R.starProjection ψ - S.starProjection φ‖ :=
      abs_norm_sq_sub_norm_sq_le_two_mul _ _ hRψ hSφ
    _ ≤ 2 * (‖ψ - φ‖ + ε) :=
      mul_le_mul_of_nonneg_left hcomponent (by norm_num)

end QuantumFoundations.BornRule.RestrictedRecordSectors
