import QuantumFoundations.BornRule.RestrictedRecordSectors.Main
import Gleason.Operator

/-!
# C15h — Hilbert-facing restricted record layer

An admissible occurrence may carry arbitrary contextual or record metadata.
Only its state, sector, refinement relation, and projected-component
magnitude are exposed to the abstract C15 theorem.
-/

namespace QuantumFoundations.BornRule.RestrictedRecordSectors

open scoped NNReal InnerProductSpace BigOperators

variable {σ : Type*} {n : ℕ}

noncomputable section

/-- A Hilbert-facing layer of admissible state-sector occurrences. -/
structure HilbertRecordLayer (σ : Type*) (n : ℕ) where
  state : σ → Gleason.H n
  sector : σ → Submodule ℂ (Gleason.H n)
  refines : σ → σ → σ → Prop
  pythagorean :
    ∀ {parent left right},
      refines parent left right →
        ‖(sector parent).starProjection (state parent)‖₊ ^ 2 =
          ‖(sector left).starProjection (state left)‖₊ ^ 2 +
            ‖(sector right).starProjection (state right)‖₊ ^ 2

namespace HilbertRecordLayer

/-- The canonical abstract refinement system underlying a Hilbert record
layer. -/
def toBinaryRefinementSystem (L : HilbertRecordLayer σ n) :
    BinaryRefinementSystem σ where
  magnitude x := ‖(L.sector x).starProjection (L.state x)‖₊
  refines := L.refines
  pythagorean := L.pythagorean

end HilbertRecordLayer

/-- Restricted record-sector weights are non-negative multiples of squared
projected norm. -/
theorem restricted_record_sector_weight_eq_quadratic
    (L : HilbertRecordLayer σ n)
    (W : σ → ℝ≥0)
    (hrealized : AllMagnitudesRealized L.toBinaryRefinementSystem)
    (hsaturated : BinarySaturated L.toBinaryRefinementSystem)
    (hstable : RefinementStable L.toBinaryRefinementSystem W)
    (hequiv : InternalEquivalence L.toBinaryRefinementSystem W) :
    ∃ c : ℝ≥0, ∀ x : σ,
      W x = c * ‖(L.sector x).starProjection (L.state x)‖₊ ^ 2 := by
  exact exists_quadratic_coefficient L.toBinaryRefinementSystem W
    hrealized hsaturated hstable hequiv

/-- Finite normalization fixes the restricted-sector coefficient to one. -/
theorem restricted_record_sector_born
    (L : HilbertRecordLayer σ n)
    (W : σ → ℝ≥0)
    (hrealized : AllMagnitudesRealized L.toBinaryRefinementSystem)
    (hsaturated : BinarySaturated L.toBinaryRefinementSystem)
    (hstable : RefinementStable L.toBinaryRefinementSystem W)
    (hequiv : InternalEquivalence L.toBinaryRefinementSystem W)
    (family : Finset σ)
    (hWeightNorm : ∑ x ∈ family, W x = 1)
    (hMagnitudeNorm :
      ∑ x ∈ family,
        ‖(L.sector x).starProjection (L.state x)‖₊ ^ 2 = 1) :
    ∀ x : σ,
      W x = ‖(L.sector x).starProjection (L.state x)‖₊ ^ 2 := by
  exact weight_eq_sq_magnitude_of_normalized L.toBinaryRefinementSystem W
    hrealized hsaturated hstable hequiv family hWeightNorm hMagnitudeNorm

/-- Real-valued coercion of the normalized restricted-sector formula. -/
theorem restricted_record_sector_born_real
    (L : HilbertRecordLayer σ n)
    (W : σ → ℝ≥0)
    (hrealized : AllMagnitudesRealized L.toBinaryRefinementSystem)
    (hsaturated : BinarySaturated L.toBinaryRefinementSystem)
    (hstable : RefinementStable L.toBinaryRefinementSystem W)
    (hequiv : InternalEquivalence L.toBinaryRefinementSystem W)
    (family : Finset σ)
    (hWeightNorm : ∑ x ∈ family, W x = 1)
    (hMagnitudeNorm :
      ∑ x ∈ family,
        ‖(L.sector x).starProjection (L.state x)‖₊ ^ 2 = 1) :
    ∀ x : σ,
      (W x : ℝ) = ‖(L.sector x).starProjection (L.state x)‖ ^ 2 := by
  intro x
  have hx := restricted_record_sector_born L W hrealized hsaturated hstable
    hequiv family hWeightNorm hMagnitudeNorm x
  have hreal := congrArg NNReal.toReal hx
  simpa only [NNReal.coe_pow, coe_nnnorm] using hreal

end

end QuantumFoundations.BornRule.RestrictedRecordSectors
