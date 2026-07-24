import QuantumFoundations.BornRule.RestrictedRecordSectors.Hilbert
import QuantumFoundations.BornRule.RestrictedRecordSectors.Continuation

/-!
# C15 non-vacuity

The saturated scalar model is genuinely non-trivial and jointly realizes all
assumptions of the abstract theorem.  Separate lightweight witnesses cover
the Hilbert and continuation-bundle structures; these are not claims about a
microscopic record model.
-/

namespace QuantumFoundations.BornRule.RestrictedRecordSectors

open scoped NNReal BigOperators Classical

noncomputable section

/-! ## The non-trivial saturated scalar model -/

/-- Canonical scalar refinement: a parent refines exactly when its square is
the sum of the two child squares. -/
def scalarRefinementSystem : BinaryRefinementSystem ℝ≥0 where
  magnitude x := x
  refines parent left right := parent ^ 2 = left ^ 2 + right ^ 2
  pythagorean href := href

/-- Quadratic scalar weight with arbitrary non-negative coefficient. -/
def scalarWeight (c : ℝ≥0) (x : ℝ≥0) : ℝ≥0 :=
  c * x ^ 2

theorem scalarRefinementSystem_allMagnitudesRealized :
    AllMagnitudesRealized scalarRefinementSystem :=
  fun r => ⟨r, rfl⟩

theorem scalarRefinementSystem_binarySaturated :
    BinarySaturated scalarRefinementSystem := by
  intro parent r₁ r₂ hsplit
  exact ⟨r₁, r₂, hsplit.symm, rfl, rfl⟩

/-- Scaling closure gives the source theorem's realization argument in the
canonical model. -/
def scalarPositiveScalingClosure :
    PositiveScalingClosure scalarRefinementSystem where
  scale r x := r * x
  magnitude_scale _ _ := rfl

theorem scalarWeight_refinementStable (c : ℝ≥0) :
    RefinementStable scalarRefinementSystem (scalarWeight c) := by
  intro parent left right href
  unfold scalarWeight
  rw [href, mul_add]

theorem scalarWeight_internalEquivalence (c : ℝ≥0) :
    InternalEquivalence scalarRefinementSystem (scalarWeight c) := by
  intro x y hprofile
  have hxy :=
    (binaryProfile_eq_iff_magnitude_eq
      scalarRefinementSystem_binarySaturated).1 hprofile
  change x = y at hxy
  unfold scalarWeight
  rw [hxy]

/-- All abstract C15 assumptions are jointly satisfiable, for every
coefficient. -/
theorem scalarModel_jointly_satisfiable (c : ℝ≥0) :
    AllMagnitudesRealized scalarRefinementSystem ∧
      BinarySaturated scalarRefinementSystem ∧
      RefinementStable scalarRefinementSystem (scalarWeight c) ∧
      InternalEquivalence scalarRefinementSystem (scalarWeight c) :=
  ⟨scalarRefinementSystem_allMagnitudesRealized,
    scalarRefinementSystem_binarySaturated,
    scalarWeight_refinementStable c,
    scalarWeight_internalEquivalence c⟩

/-- At coefficient one, the singleton family `{1}` supplies both finite
normalizations and the normalized conclusion holds globally. -/
theorem scalarModel_one_normalized :
    (∑ x ∈ ({1} : Finset ℝ≥0), scalarWeight 1 x) = 1 ∧
      (∑ x ∈ ({1} : Finset ℝ≥0),
        scalarRefinementSystem.magnitude x ^ 2) = 1 ∧
      ∀ x : ℝ≥0,
        scalarWeight 1 x = scalarRefinementSystem.magnitude x ^ 2 := by
  constructor
  · norm_num [scalarWeight]
  constructor
  · norm_num [scalarRefinementSystem]
  · intro x
    simp only [scalarWeight, scalarRefinementSystem, one_mul]

/-! ## Lightweight Hilbert-structure inhabitant -/

/-- A minimal Hilbert-layer inhabitant with no refinements.  The substantive
non-vacuity witness for saturation remains the scalar model above. -/
noncomputable def minimalHilbertRecordLayer (n : ℕ) :
    HilbertRecordLayer PUnit n where
  state _ := 0
  sector _ := ⊥
  refines _ _ _ := False
  pythagorean href := False.elim href

/-! ## A non-zero finite continuation-bundle example -/

/-- Cardinality is an extensive valuation on sets over a finite carrier. -/
def finiteCardValuation (Ω : Type*) [Finite Ω] :
    ExtensiveBundleValuation Ω where
  value A := A.ncard
  union_of_disjoint h := by
    norm_cast
    exact Set.ncard_union_eq h

/-- A three-situation system with one genuine binary refinement. -/
def finiteContinuationRefinementSystem :
    BinaryRefinementSystem (Option Bool) where
  magnitude
    | none => NNReal.sqrt 2
    | some _ => 1
  refines parent left right :=
    parent = none ∧ left = some false ∧ right = some true
  pythagorean := by
    intro parent left right href
    rcases href with ⟨rfl, rfl, rfl⟩
    simp only [NNReal.sq_sqrt]
    norm_num

/-- The parent bundle `{false, true}` is partitioned into its two singleton
child bundles. -/
def finiteContinuationBundleSystem :
    ContinuationBundleSystem finiteContinuationRefinementSystem Bool where
  bundle
    | none => Set.univ
    | some false => {false}
    | some true => {true}
  partition := by
    intro parent left right href
    rcases href with ⟨rfl, rfl, rfl⟩
    constructor
    · simp only [Set.disjoint_singleton]
      decide
    · ext b
      cases b <;> simp

/-- The finite example has non-zero induced parent weight and satisfies
refinement stability. -/
theorem finiteContinuationModel_nonzero_and_stable :
    inducedWeight (finiteCardValuation Bool) finiteContinuationBundleSystem none = 2 ∧
      RefinementStable finiteContinuationRefinementSystem
        (inducedWeight (finiteCardValuation Bool) finiteContinuationBundleSystem) := by
  constructor
  · norm_num [inducedWeight, finiteCardValuation, finiteContinuationBundleSystem]
  · exact inducedWeight_refinementStable
      (finiteCardValuation Bool) finiteContinuationBundleSystem

end

end QuantumFoundations.BornRule.RestrictedRecordSectors
