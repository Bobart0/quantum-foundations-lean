import QuantumFoundations.BornRule.RestrictedRecordSectors.Basic

/-!
# C15i — Continuation-bundle additivity adapter

Finite additivity on disjoint continuation bundles induces refinement
stability on record situations.  No measure-theoretic structure is needed.
-/

namespace QuantumFoundations.BornRule.RestrictedRecordSectors

open scoped NNReal

variable {σ Ω : Type*}

/-- A finitely additive non-negative valuation on continuation bundles. -/
structure ExtensiveBundleValuation (Ω : Type*) where
  value : Set Ω → ℝ≥0
  union_of_disjoint :
    ∀ {A B : Set Ω}, Disjoint A B → value (A ∪ B) = value A + value B

/-- Bundle semantics in which every binary refinement partitions the parent
bundle into two disjoint child bundles. -/
structure ContinuationBundleSystem
    (S : BinaryRefinementSystem σ) (Ω : Type*) where
  bundle : σ → Set Ω
  partition :
    ∀ {parent left right},
      S.refines parent left right →
        Disjoint (bundle left) (bundle right) ∧
          bundle parent = bundle left ∪ bundle right

/-- The weight induced on situations by a continuation-bundle valuation. -/
def inducedWeight
    {S : BinaryRefinementSystem σ}
    (V : ExtensiveBundleValuation Ω)
    (C : ContinuationBundleSystem S Ω)
    (x : σ) : ℝ≥0 :=
  V.value (C.bundle x)

/-- Disjoint bundle additivity induces refinement stability. -/
theorem inducedWeight_refinementStable
    {S : BinaryRefinementSystem σ}
    (V : ExtensiveBundleValuation Ω)
    (C : ContinuationBundleSystem S Ω) :
    RefinementStable S (inducedWeight V C) := by
  intro parent left right href
  obtain ⟨hdisjoint, hpartition⟩ := C.partition href
  change V.value (C.bundle parent) =
    V.value (C.bundle left) + V.value (C.bundle right)
  rw [hpartition]
  exact V.union_of_disjoint hdisjoint

end QuantumFoundations.BornRule.RestrictedRecordSectors
