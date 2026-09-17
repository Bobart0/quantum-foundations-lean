import QuantumFoundations.BornRule.Perspective

/-!
# Refinement consistency for contextual real weights

This file introduces a finite-refinement stability predicate on contextual real
weight assignments.  It is deliberately stated on the pre-probabilistic
interface: normalization and positivity are not built into the type of the
assignment.

`AxRC` is the finite-refinement closure of the elementary unchanged-outcome
stability condition used in refinement-based probability arguments.  The first
result below records the easy direction needed by the existing library:
Grain coherence implies this stability without any normalization assumption.
-/

namespace QuantumFoundations.BornRule

open scoped Classical InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ}

/-- Finite refinement consistency: a cell that is literally present before and
after a refinement keeps the same weight.

This predicate is intentionally exposed independently of normalization and
positivity, so that those assumptions can be audited separately. -/
def AxRC (Est : Perspective n → Submodule ℂ (H n) → ℝ) : Prop :=
  ∀ D' D : Perspective n, Refines D' D →
    ∀ c : Submodule ℂ (H n), c ∈ D.cells → c ∈ D'.cells →
      Est D c = Est D' c

/-- Grain coherence implies finite refinement consistency, with no use of
normalization.  If a coarse cell is also a fine cell, it is the unique fine
cell lying below itself. -/
theorem axGrain_implies_axRC
    (Est : Perspective n → Submodule ℂ (H n) → ℝ)
    (hGrain : AxGrain Est) : AxRC Est := by
  intro D' D hRef c hcD hcD'
  have hgrain := hGrain D' D hRef c hcD
  have hfilter : D'.cells.filter (· ≤ c) = {c} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hcD', le_refl c⟩, ?_⟩
    intro c' hc'
    obtain ⟨hc'mem, hc'le⟩ := Finset.mem_filter.mp hc'
    exact D'.unique_parent hc'mem hcD' (D'.nz c' hc'mem)
      (le_refl c') hc'le
  rw [hfilter, Finset.sum_singleton] at hgrain
  exact hgrain

end

end QuantumFoundations.BornRule
