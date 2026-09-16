import QuantumFoundations.BornRule.RefinementConsistency
import QuantumFoundations.BornRule.Nonvacuity

/-!
# Elementary binary refinement consistency

The publication-facing refinement condition is stated on a single binary split,
not on an arbitrary finite refinement.  This file keeps that elementary notion
separate from `AxRC`, the finite-refinement closure already exposed in
`RefinementConsistency.lean`.

Normalization and positivity are deliberately not part of the weight type.
This permits their roles to be tested independently.
-/

namespace QuantumFoundations.BornRule

open scoped Classical InnerProductSpace

noncomputable section

variable {n : ℕ}

/-- `D'` is obtained from `D` by splitting exactly one coarse cell into two
fine cells while leaving every other coarse cell literally present.

The equality of the split cell with the orthogonal sum of its two children is
a consequence of `Refines` together with the perspective axioms; the existing
`refine_filter_sup_eq` theorem records that coverage fact for arbitrary finite
refinements. -/
def IsBinarySplit (D' D : Perspective n) : Prop :=
  Refines D' D ∧
    ∃ q : Submodule ℂ (H n),
      q ∈ D.cells ∧
      q ∉ D'.cells ∧
      (∀ c ∈ D.cells, c ≠ q → c ∈ D'.cells) ∧
      (D'.cells.filter (· ≤ q)).card = 2

/-- Elementary refinement consistency: under a binary split, every unchanged
cell keeps the same contextual weight. -/
def AxSplitRC (Est : Perspective n → Submodule ℂ (H n) → ℝ) : Prop :=
  ∀ D' D : Perspective n, IsBinarySplit D' D →
    ∀ c : Submodule ℂ (H n), c ∈ D.cells → c ∈ D'.cells →
      Est D c = Est D' c

/-- Finite refinement consistency implies elementary split consistency. -/
theorem axRC_implies_axSplitRC
    (Est : Perspective n → Submodule ℂ (H n) → ℝ)
    (hRC : AxRC Est) : AxSplitRC Est := by
  intro D' D hSplit c hcD hcD'
  exact hRC D' D hSplit.1 c hcD hcD'

/-- Grain coherence implies elementary split consistency without normalization.
This is the easy direction of the refinement-consistency comparison. -/
theorem axGrain_implies_axSplitRC
    (Est : Perspective n → Submodule ℂ (H n) → ℝ)
    (hGrain : AxGrain Est) : AxSplitRC Est :=
  axRC_implies_axSplitRC Est (axGrain_implies_axRC Est hGrain)

/-- In a binary split, the two fine children below the split cell cover that
cell.  This packages the existing arbitrary-refinement coverage theorem in the
exact form used by the split-generation argument. -/
theorem binarySplit_children_cover
    {D' D : Perspective n} (hSplit : IsBinarySplit D' D) :
    ∃ q : Submodule ℂ (H n),
      q ∈ D.cells ∧
      q ∉ D'.cells ∧
      (D'.cells.filter (· ≤ q)).card = 2 ∧
      sSup (((D'.cells.filter (· ≤ q) : Finset (Submodule ℂ (H n))) :
        Set (Submodule ℂ (H n)))) = q := by
  rcases hSplit.2 with ⟨q, hqD, hqD', hkeep, hcard⟩
  refine ⟨q, hqD, hqD', hcard, ?_⟩
  exact refine_filter_sup_eq D' D hSplit.1 q hqD

end

end QuantumFoundations.BornRule
