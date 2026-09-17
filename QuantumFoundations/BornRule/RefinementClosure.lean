import QuantumFoundations.BornRule.RefinementConsistency
import QuantumFoundations.BornRule.Nonvacuity

/-!
# Closure under refining one cell

For an arbitrary refinement `D'` of `D` and a chosen coarse cell `q`, this
file builds the hybrid perspective obtained by keeping every coarse cell other
than `q` and replacing `q` by exactly its fine children from `D'`.

This closure construction gives a direct proof that finite refinement
consistency plus normalization implies Grain additivity.  It is independent of
the later binary-split generation argument.
-/

namespace QuantumFoundations.BornRule

open scoped Classical InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ}

namespace Perspective

/-- Replace one coarse cell `q` by all of its children in an arbitrary finer
perspective `D'`, leaving the other coarse cells unchanged. -/
noncomputable def refineOneCell
    (D' D : Perspective n) (hRef : Refines D' D)
    (q : Submodule ℂ (H n)) (hq : q ∈ D.cells) : Perspective n where
  cells := D.cells.erase q ∪ D'.cells.filter (· ≤ q)
  nz := by
    intro c hc
    simp only [Finset.mem_union] at hc
    rcases hc with hc | hc
    · exact D.nz c (Finset.mem_of_mem_erase hc)
    · exact D'.nz c (Finset.mem_filter.mp hc).1
  ortho := by
    intro c hc c' hc' hne
    simp only [Finset.mem_union] at hc hc'
    rcases hc with hcOld | hcFine <;> rcases hc' with hcOld' | hcFine'
    · exact D.ortho c (Finset.mem_of_mem_erase hcOld)
        c' (Finset.mem_of_mem_erase hcOld') hne
    · have hcD : c ∈ D.cells := Finset.mem_of_mem_erase hcOld
      have hcq : c ≠ q := (Finset.mem_erase.mp hcOld).1
      have hc'le : c' ≤ q := (Finset.mem_filter.mp hcFine').2
      have hcoarse : c ≤ qᗮ := D.ortho c hcD q hq hcq
      exact hcoarse.trans (Submodule.orthogonal_le hc'le)
    · have hc'D : c' ∈ D.cells := Finset.mem_of_mem_erase hcOld'
      have hc'q : c' ≠ q := (Finset.mem_erase.mp hcOld').1
      have hcle : c ≤ q := (Finset.mem_filter.mp hcFine).2
      have hcoarse : q ≤ c'ᗮ := D.ortho q hq c' hc'D (Ne.symm hc'q)
      exact hcle.trans hcoarse
    · exact D'.ortho c (Finset.mem_filter.mp hcFine).1
        c' (Finset.mem_filter.mp hcFine').1 hne
  span := by
    apply le_antisymm le_top
    rw [← D.span]
    apply sSup_le
    intro c hc
    simp only [Finset.mem_coe] at hc
    by_cases hcq : c = q
    · subst c
      rw [← refine_filter_sup_eq D' D hRef q hq]
      apply sSup_le_sSup
      intro x hx
      simp only [Finset.mem_coe] at hx ⊢
      exact Finset.mem_union_right _ hx
    · rw [← sSup_singleton c]
      apply sSup_le_sSup
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      simp only [Finset.mem_coe]
      exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hcq, hc⟩)

/-- The hybrid perspective still refines the original coarse perspective. -/
theorem refineOneCell_refines_coarse
    (D' D : Perspective n) (hRef : Refines D' D)
    (q : Submodule ℂ (H n)) (hq : q ∈ D.cells) :
    Refines (refineOneCell D' D hRef q hq) D := by
  intro c hc
  simp only [refineOneCell, Finset.mem_union] at hc
  rcases hc with hcOld | hcFine
  · have hcD : c ∈ D.cells := Finset.mem_of_mem_erase hcOld
    exact ⟨c, hcD, le_refl c⟩
  · exact ⟨q, hq, (Finset.mem_filter.mp hcFine).2⟩

/-- The original fine perspective refines the hybrid perspective. -/
theorem fine_refines_refineOneCell
    (D' D : Perspective n) (hRef : Refines D' D)
    (q : Submodule ℂ (H n)) (hq : q ∈ D.cells) :
    Refines D' (refineOneCell D' D hRef q hq) := by
  intro c hcD'
  obtain ⟨p, hpD, hcp⟩ := hRef c hcD'
  by_cases hpq : p = q
  · subst p
    refine ⟨c, ?_, le_refl c⟩
    simp only [refineOneCell, Finset.mem_union]
    exact Or.inr (Finset.mem_filter.mpr ⟨hcD', hcp⟩)
  · refine ⟨p, ?_, hcp⟩
    simp only [refineOneCell, Finset.mem_union]
    exact Or.inl (Finset.mem_erase.mpr ⟨hpq, hpD⟩)

end Perspective

/-- Finite refinement consistency together with normalization yields the full
Grain additivity law for arbitrary finite refinements.

The proof compares the coarse perspective with a hybrid in which only the
chosen coarse cell has been refined, then compares the hybrid with the original
fine perspective on the shared child cells. -/
theorem axRC_norm_implies_axGrain
    (Est : Perspective n → Submodule ℂ (H n) → ℝ)
    (hRC : AxRC Est) (hNorm : AxNorm Est) : AxGrain Est := by
  intro D' D hRef q hq
  let M := Perspective.refineOneCell D' D hRef q hq
  have hMD : Refines M D := Perspective.refineOneCell_refines_coarse D' D hRef q hq
  have hD'M : Refines D' M := Perspective.fine_refines_refineOneCell D' D hRef q hq
  have hMcells : M.cells = D.cells.erase q ∪ D'.cells.filter (· ≤ q) := rfl
  have hdisj : Disjoint (D.cells.erase q) (D'.cells.filter (· ≤ q)) := by
    rw [Finset.disjoint_left]
    intro c hcOld hcFine
    have hcD : c ∈ D.cells := (Finset.mem_erase.mp hcOld).2
    have hcq : c ≠ q := (Finset.mem_erase.mp hcOld).1
    have hcle : c ≤ q := (Finset.mem_filter.mp hcFine).2
    have hceq : c = q :=
      D.unique_parent hcD hq (D.nz c hcD) (le_refl c) hcle
    exact hcq hceq
  have hsameOld :
      (∑ c ∈ D.cells.erase q, Est D c) =
        ∑ c ∈ D.cells.erase q, Est M c := by
    apply Finset.sum_congr rfl
    intro c hc
    have hcD : c ∈ D.cells := (Finset.mem_erase.mp hc).2
    have hcM : c ∈ M.cells := by
      rw [hMcells]
      exact Finset.mem_union_left _ hc
    exact hRC M D hMD c hcD hcM
  have hsameChildren :
      (∑ c ∈ D'.cells.filter (· ≤ q), Est M c) =
        ∑ c ∈ D'.cells.filter (· ≤ q), Est D' c := by
    apply Finset.sum_congr rfl
    intro c hc
    have hcD' : c ∈ D'.cells := (Finset.mem_filter.mp hc).1
    have hcM : c ∈ M.cells := by
      rw [hMcells]
      exact Finset.mem_union_right _ hc
    exact hRC D' M hD'M c hcM hcD'
  have hcoarse := hNorm D
  have hmid := hNorm M
  rw [← Finset.sum_erase_add _ hq] at hcoarse
  rw [hMcells, Finset.sum_union hdisj] at hmid
  rw [← hsameOld, hsameChildren] at hmid
  linarith

end

end QuantumFoundations.BornRule
