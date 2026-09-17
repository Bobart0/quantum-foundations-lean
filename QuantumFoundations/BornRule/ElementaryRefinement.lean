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
open Gleason

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
      (D'.cells.filter (· ≤ q)).sup id = q := by
  rcases hSplit.2 with ⟨q, hqD, hqD', hkeep, hcard⟩
  refine ⟨q, hqD, hqD', hcard, ?_⟩
  exact refine_filter_sup_eq D' D hSplit.1 q hqD

/-- Outside the split cell, the fine perspective consists exactly of the
unchanged coarse cells. -/
theorem binarySplit_outside_eq_erase
    {D' D : Perspective n} (hSplit : IsBinarySplit D' D)
    {q : Submodule ℂ (H n)}
    (hqD : q ∈ D.cells)
    (hkeep : ∀ c ∈ D.cells, c ≠ q → c ∈ D'.cells) :
    D'.cells.filter (fun c => ¬ c ≤ q) = D.cells.erase q := by
  ext c
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hcD', hcle⟩
    obtain ⟨p, hpD, hcp⟩ := hSplit.1 c hcD'
    have hpq : p ≠ q := by
      intro hpq
      subst p
      exact hcle hcp
    have hpD' : p ∈ D'.cells := hkeep p hpD hpq
    have hcp_eq : c = p :=
      D'.unique_parent hcD' hpD' (D'.nz c hcD') (le_refl c) hcp
    subst c
    exact ⟨hpq, hpD⟩
  · rintro ⟨hcq, hcD⟩
    have hcD' : c ∈ D'.cells := hkeep c hcD hcq
    refine ⟨hcD', ?_⟩
    intro hc_le_q
    have hc_eq_q : c = q :=
      D.unique_parent hcD hqD (D.nz c hcD) (le_refl c) hc_le_q
    exact hcq hc_eq_q

/-- On a single binary split, refinement consistency plus normalization forces
additivity on the split cell.  RC alone only controls the cells that remain
unchanged; normalization is the ingredient that converts that lateral
stability into conservation of the split cell's total weight. -/
theorem binarySplit_additivity_of_rc_norm
    (Est : Perspective n → Submodule ℂ (H n) → ℝ)
    (hRC : AxSplitRC Est) (hNorm : AxNorm Est)
    {D' D : Perspective n} (hSplit : IsBinarySplit D' D) :
    ∃ q : Submodule ℂ (H n), q ∈ D.cells ∧
      Est D q = ∑ c ∈ D'.cells.filter (· ≤ q), Est D' c := by
  rcases hSplit.2 with ⟨q, hqD, hqD', hkeep, hcard⟩
  refine ⟨q, hqD, ?_⟩
  have hout := binarySplit_outside_eq_erase hSplit hqD hkeep
  have hsame :
      (∑ c ∈ D.cells.erase q, Est D c) =
        ∑ c ∈ D.cells.erase q, Est D' c := by
    apply Finset.sum_congr rfl
    intro c hc
    have hcD : c ∈ D.cells := (Finset.mem_erase.mp hc).2
    have hcq : c ≠ q := (Finset.mem_erase.mp hc).1
    have hcD' : c ∈ D'.cells := hkeep c hcD hcq
    exact hRC D' D hSplit c hcD hcD'
  have hcoarse_split :
      (∑ c ∈ D.cells.erase q, Est D c) + Est D q = 1 := by
    calc
      (∑ c ∈ D.cells.erase q, Est D c) + Est D q =
          ∑ c ∈ D.cells, Est D c :=
        Finset.sum_erase_add D.cells (fun c => Est D c) hqD
      _ = 1 := hNorm D
  have hfine := hNorm D'
  have hpartition :
      (∑ c ∈ D'.cells, Est D' c) =
        (∑ c ∈ D'.cells.filter (· ≤ q), Est D' c) +
          ∑ c ∈ D'.cells.filter (fun c => ¬ c ≤ q), Est D' c := by
    rw [← Finset.sum_filter_add_sum_filter_not]
  rw [hpartition, hout, ← hsame] at hfine
  linarith

end

end QuantumFoundations.BornRule
