import QuantumFoundations.BornRule.RestrictedRecordSectors.Additive

/-!
# C15b — Abstract binary refinement systems

The carrier consists only of admissible record situations.  Magnitude,
refinement, stability, realization, and saturation are kept as separate
notions so that the uniqueness theorem exposes exactly what it uses.
-/

namespace QuantumFoundations.BornRule.RestrictedRecordSectors

open scoped NNReal

variable {σ : Type*}

/-- An admissible binary refinement system with Pythagorean magnitudes. -/
structure BinaryRefinementSystem (σ : Type*) where
  magnitude : σ → ℝ≥0
  refines : σ → σ → σ → Prop
  pythagorean :
    ∀ {parent left right},
      refines parent left right →
        magnitude parent ^ 2 = magnitude left ^ 2 + magnitude right ^ 2

/-- The weight of a parent is the sum of the weights of its two refinements. -/
def RefinementStable (S : BinaryRefinementSystem σ) (W : σ → ℝ≥0) : Prop :=
  ∀ {parent left right}, S.refines parent left right → W parent = W left + W right

/-- Every non-negative magnitude occurs among the admissible situations. -/
def AllMagnitudesRealized (S : BinaryRefinementSystem σ) : Prop :=
  ∀ r : ℝ≥0, ∃ x : σ, S.magnitude x = r

/-- Every Pythagorean binary split of a parent's magnitude is realizable. -/
def BinarySaturated (S : BinaryRefinementSystem σ) : Prop :=
  ∀ (parent : σ) (r₁ r₂ : ℝ≥0),
    r₁ ^ 2 + r₂ ^ 2 = S.magnitude parent ^ 2 →
      ∃ left right : σ,
        S.refines parent left right ∧
          S.magnitude left = r₁ ∧ S.magnitude right = r₂

/-- Optional positive-scaling interface for realizing all magnitudes. -/
structure PositiveScalingClosure (S : BinaryRefinementSystem σ) where
  scale : ℝ≥0 → σ → σ
  magnitude_scale :
    ∀ r x, S.magnitude (scale r x) = r * S.magnitude x

/-- A unit-magnitude witness and scaling closure realize every magnitude. -/
theorem allMagnitudesRealized_of_positiveScalingClosure
    (S : BinaryRefinementSystem σ)
    (C : PositiveScalingClosure S)
    (unit : σ)
    (hunit : S.magnitude unit = 1) :
    AllMagnitudesRealized S := by
  intro r
  refine ⟨C.scale r unit, ?_⟩
  rw [C.magnitude_scale, hunit, mul_one]

end QuantumFoundations.BornRule.RestrictedRecordSectors
