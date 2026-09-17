import QuantumFoundations.BornRule.ElementaryRefinement
import QuantumFoundations.BornRule.Nonvacuity

/-!
# Sharpness witnesses for RC-based Born calibration

This file collects publication-facing countermodels for the four exposed
conditions.  The first two witnesses are included here: normalization fixes the
overall scale, while projective null support fixes the target state.  The
remaining RC and positivity witnesses are added in subsequent sections.
-/

namespace QuantumFoundations.BornRule

open scoped Classical InnerProductSpace
open Gleason

noncomputable section

/-! ## Common dimension-three geometry -/

def rcE0 : H 3 := EuclideanSpace.single (0 : Fin 3) (1 : ℂ)
def rcE1 : H 3 := EuclideanSpace.single (1 : Fin 3) (1 : ℂ)

theorem rcE0_norm : ‖rcE0‖ = 1 := by simp [rcE0]
theorem rcE1_norm : ‖rcE1‖ = 1 := by simp [rcE1]

private theorem rcE0_ne_zero : rcE0 ≠ 0 := by
  intro h
  have hn := rcE0_norm
  rw [h, norm_zero] at hn
  norm_num at hn

def rcLine0 : Submodule ℂ (H 3) := ℂ ∙ rcE0

theorem rcLine0_ne_bot : rcLine0 ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  exact ⟨rcE0, Submodule.mem_span_singleton_self rcE0, rcE0_ne_zero⟩

theorem rcLine0_ne_top : rcLine0 ≠ ⊤ := by
  intro htop
  have h1 : Module.finrank ℂ rcLine0 = 1 := by
    unfold rcLine0
    exact finrank_span_singleton rcE0_ne_zero
  rw [htop, finrank_top] at h1
  simp at h1

private theorem inner_rcE0_rcE1 : ⟪rcE0, rcE1⟫_ℂ = 0 := by
  unfold rcE0 rcE1
  rw [EuclideanSpace.inner_single_left]
  norm_num

private theorem rcE1_mem_rcLine0_orthogonal : rcE1 ∈ rcLine0ᗮ := by
  unfold rcLine0
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr inner_rcE0_rcE1

private theorem projL_rcLine0_rcE0 : projL rcLine0 rcE0 = rcE0 := by
  unfold projL rcLine0
  rw [ContinuousLinearMap.coe_coe]
  exact Submodule.starProjection_eq_self_iff.mpr
    (Submodule.mem_span_singleton_self rcE0)

private theorem projL_rcLine0_rcE1 : projL rcLine0 rcE1 = 0 := by
  unfold projL
  rw [ContinuousLinearMap.coe_coe,
    (Submodule.starProjection_apply_eq_zero_iff rcLine0).mpr rcE1_mem_rcLine0_orthogonal]

/-! ## W1 — removing normalization restores a global scale -/

/-- Twice the pure-state Born weight.  This is regular, positive and
context-independent; it differs from Born only by its global scale. -/
def doubleBornWeight3 : Perspective 3 → Submodule ℂ (H 3) → ℝ :=
  fun _ c => 2 * ‖projL c rcE0‖ ^ 2

theorem doubleBornWeight3_axSplitRC : AxSplitRC doubleBornWeight3 := by
  intro D' D hSplit c hcD hcD'
  rfl

theorem doubleBornWeight3_axPos : AxPos doubleBornWeight3 := by
  intro D c hc
  exact mul_nonneg (by norm_num) (sq_nonneg _)

theorem doubleBornWeight3_axNul : AxNul doubleBornWeight3 rcE0 := by
  intro D c hc hv
  have h0 := E₀_isNul rcE0 D c hc hv
  change ‖projL c rcE0‖ ^ 2 = 0 at h0
  simp only [doubleBornWeight3]
  rw [h0]
  norm_num

theorem doubleBornWeight3_not_axNorm : ¬ AxNorm doubleBornWeight3 := by
  intro hNorm
  let D := basisPerspective (EuclideanSpace.basisFun (Fin 3) ℂ)
  have h := hNorm D
  have hBorn := E₀_isNorm rcE0 rcE0_norm D
  change ∑ c ∈ D.cells, 2 * ‖projL c rcE0‖ ^ 2 = 1 at h
  change ∑ c ∈ D.cells, ‖projL c rcE0‖ ^ 2 = 1 at hBorn
  rw [← Finset.mul_sum, hBorn] at h
  norm_num at h

theorem doubleBornWeight3_not_born_on_line0 :
    doubleBornWeight3
        (Perspective.binary rcLine0 rcLine0_ne_bot rcLine0_ne_top) rcLine0 ≠
      ‖projL rcLine0 rcE0‖ ^ 2 := by
  simp only [doubleBornWeight3]
  rw [projL_rcLine0_rcE0, rcE0_norm]
  norm_num

/-- Removing normalization leaves the other three publication-facing
conditions intact while allowing a nontrivial global rescaling of Born. -/
theorem sharpness_remove_norm :
    AxSplitRC doubleBornWeight3 ∧
    AxPos doubleBornWeight3 ∧
    AxNul doubleBornWeight3 rcE0 ∧
    ¬ AxNorm doubleBornWeight3 ∧
    ∃ (D : Perspective 3) (c : Submodule ℂ (H 3)),
      c ∈ D.cells ∧
      doubleBornWeight3 D c ≠ ‖projL c rcE0‖ ^ 2 := by
  refine ⟨doubleBornWeight3_axSplitRC, doubleBornWeight3_axPos,
    doubleBornWeight3_axNul, doubleBornWeight3_not_axNorm, ?_⟩
  refine ⟨Perspective.binary rcLine0 rcLine0_ne_bot rcLine0_ne_top,
    rcLine0, Finset.mem_insert_self _ _, doubleBornWeight3_not_born_on_line0⟩

/-! ## W2 — removing projective null support restores the choice of state -/

theorem born_rcE0_not_axNul_rcE1 : ¬ AxNul (E₀ rcE0) rcE1 := by
  intro hNul
  have h := hNul
    (Perspective.binary rcLine0 rcLine0_ne_bot rcLine0_ne_top)
    rcLine0 (Finset.mem_insert_self _ _) rcE1_mem_rcLine0_orthogonal
  change ‖projL rcLine0 rcE0‖ ^ 2 = 0 at h
  rw [projL_rcLine0_rcE0, rcE0_norm] at h
  norm_num at h

theorem born_rcE0_not_born_for_rcE1_on_line0 :
    E₀ rcE0
        (Perspective.binary rcLine0 rcLine0_ne_bot rcLine0_ne_top) rcLine0 ≠
      ‖projL rcLine0 rcE1‖ ^ 2 := by
  change ‖projL rcLine0 rcE0‖ ^ 2 ≠ ‖projL rcLine0 rcE1‖ ^ 2
  rw [projL_rcLine0_rcE0, projL_rcLine0_rcE1, rcE0_norm]
  norm_num

/-- Removing projective null support permits the ordinary Born rule of a
different pure state while RC, normalization and positivity remain valid. -/
theorem sharpness_remove_null :
    AxSplitRC (E₀ rcE0) ∧
    AxNorm (E₀ rcE0) ∧
    AxPos (E₀ rcE0) ∧
    ¬ AxNul (E₀ rcE0) rcE1 ∧
    ∃ (D : Perspective 3) (c : Submodule ℂ (H 3)),
      c ∈ D.cells ∧
      E₀ rcE0 D c ≠ ‖projL c rcE1‖ ^ 2 := by
  refine ⟨axGrain_implies_axSplitRC (E₀ rcE0) (E₀_isGrain rcE0),
    E₀_isNorm rcE0 rcE0_norm, E₀_isPos rcE0,
    born_rcE0_not_axNul_rcE1, ?_⟩
  refine ⟨Perspective.binary rcLine0 rcLine0_ne_bot rcLine0_ne_top,
    rcLine0, Finset.mem_insert_self _ _, born_rcE0_not_born_for_rcE1_on_line0⟩

end

end QuantumFoundations.BornRule
