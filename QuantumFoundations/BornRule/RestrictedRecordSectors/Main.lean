import QuantumFoundations.BornRule.RestrictedRecordSectors.Profiles

/-!
# C15f–g — Restricted record-sector quadratic uniqueness

The abstract theorem identifies every refinement-stable, profile-invariant
weight as a non-negative multiple of squared magnitude.  Null behavior is a
consequence.  A finite normalization fixes the coefficient globally.
-/

namespace QuantumFoundations.BornRule.RestrictedRecordSectors

open scoped NNReal BigOperators

variable {σ : Type*}

/-- **C15, unnormalized form.** A refinement-stable weight invariant under
internal binary profiles is quadratic in magnitude. -/
theorem exists_quadratic_coefficient
    (S : BinaryRefinementSystem σ)
    (W : σ → ℝ≥0)
    (hrealized : AllMagnitudesRealized S)
    (hsaturated : BinarySaturated S)
    (hstable : RefinementStable S W)
    (hequiv : InternalEquivalence S W) :
    ∃ c : ℝ≥0, ∀ x : σ, W x = c * S.magnitude x ^ 2 := by
  obtain ⟨c, hc⟩ :=
    exists_profileFunction_quadratic hrealized hsaturated hstable hequiv
  refine ⟨c, fun x => ?_⟩
  rw [weight_eq_profileFunction hrealized hsaturated hequiv x]
  exact hc (S.magnitude x)

/-- A zero-magnitude situation has zero weight; no separate null premise is
needed. -/
theorem weight_eq_zero_of_magnitude_eq_zero
    (S : BinaryRefinementSystem σ)
    (W : σ → ℝ≥0)
    (hrealized : AllMagnitudesRealized S)
    (hsaturated : BinarySaturated S)
    (hstable : RefinementStable S W)
    (hequiv : InternalEquivalence S W)
    {x : σ}
    (hx : S.magnitude x = 0) :
    W x = 0 := by
  obtain ⟨c, hc⟩ :=
    exists_quadratic_coefficient S W hrealized hsaturated hstable hequiv
  rw [hc x, hx]
  norm_num

/-- **C15, normalized form.** Matching finite normalizations of weight and
squared magnitude force the global coefficient to be one, hence the Born
quadratic formula holds for every admissible situation. -/
theorem weight_eq_sq_magnitude_of_normalized
    (S : BinaryRefinementSystem σ)
    (W : σ → ℝ≥0)
    (hrealized : AllMagnitudesRealized S)
    (hsaturated : BinarySaturated S)
    (hstable : RefinementStable S W)
    (hequiv : InternalEquivalence S W)
    (family : Finset σ)
    (hWeightNorm : ∑ x ∈ family, W x = 1)
    (hMagnitudeNorm : ∑ x ∈ family, S.magnitude x ^ 2 = 1) :
    ∀ x : σ, W x = S.magnitude x ^ 2 := by
  obtain ⟨c, hc⟩ :=
    exists_quadratic_coefficient S W hrealized hsaturated hstable hequiv
  have hc_one : c = 1 := by
    have hsum :
        (∑ x ∈ family, W x) =
          ∑ x ∈ family, c * S.magnitude x ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hc x]
    calc
      c = c * 1 := (mul_one c).symm
      _ = c * ∑ x ∈ family, S.magnitude x ^ 2 := by rw [hMagnitudeNorm]
      _ = ∑ x ∈ family, c * S.magnitude x ^ 2 := by
        rw [Finset.mul_sum]
      _ = ∑ x ∈ family, W x := hsum.symm
      _ = 1 := hWeightNorm
  intro x
  rw [hc x, hc_one, one_mul]

end QuantumFoundations.BornRule.RestrictedRecordSectors
