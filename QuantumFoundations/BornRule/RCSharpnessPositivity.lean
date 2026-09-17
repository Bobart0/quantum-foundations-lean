import QuantumFoundations.BornRule.RCSharpness

/-!
# Sharpness of positivity

A Hermitian trace-one but non-positive operator gives a contextual real weight
that is refinement-consistent, normalized, and null on all cells orthogonal to
the target state, yet differs from the pure-state Born rule.
-/

namespace QuantumFoundations.BornRule

open scoped Classical InnerProductSpace
open Gleason

noncomputable section

private theorem rc_span_ne_bot_of_norm_one {z : H 3} (hz : ‖z‖ = 1) :
    (ℂ ∙ z : Submodule ℂ (H 3)) ≠ ⊥ := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    norm_num at hz
  rw [Submodule.ne_bot_iff]
  exact ⟨z, Submodule.mem_span_singleton_self z, hz0⟩

private theorem rc_span_ne_top_of_norm_one {z : H 3} (hz : ‖z‖ = 1) :
    (ℂ ∙ z : Submodule ℂ (H 3)) ≠ ⊤ := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    norm_num at hz
  intro htop
  have h1 : Module.finrank ℂ (ℂ ∙ z : Submodule ℂ (H 3)) = 1 :=
    finrank_span_singleton hz0
  rw [htop, finrank_top] at h1
  simp at h1

/-- Hermitian trace-one operator with matrix `[[1,1],[1,0]]` on the first two
computational basis directions. -/
def rcRho : H 3 →ₗ[ℂ] H 3 :=
  (InnerProductSpace.rankOne ℂ rcE0 rcE0 : H 3 →ₗ[ℂ] H 3) +
  (InnerProductSpace.rankOne ℂ rcE0 rcE1 : H 3 →ₗ[ℂ] H 3) +
  (InnerProductSpace.rankOne ℂ rcE1 rcE0 : H 3 →ₗ[ℂ] H 3)

/-- Context-independent real trace weight induced by `rcRho`. -/
def rcRhoWeight3 : Perspective 3 → Submodule ℂ (H 3) → ℝ :=
  fun _ c => Gleason.bornValue rcRho c

/-- Since the trace weight ignores the ambient perspective, unchanged cells
are automatically stable under every binary split. -/
theorem rcRhoWeight3_axSplitRC : AxSplitRC rcRhoWeight3 := by
  intro D' D hSplit c hcD hcD'
  rfl

private theorem rcRho_trace_one : LinearMap.trace ℂ (H 3) rcRho = 1 := by
  unfold rcRho
  simp only [map_add, InnerProductSpace.trace_rankOne]
  simp [rcE0, rcE1, EuclideanSpace.inner_single_left]

private theorem rcRho_bornValue_top :
    Gleason.bornValue rcRho (⊤ : Submodule ℂ (H 3)) = 1 := by
  unfold Gleason.bornValue
  have hproj : projL (⊤ : Submodule ℂ (H 3)) = LinearMap.id := by
    unfold projL
    rw [Submodule.starProjection_top]
    rfl
  rw [hproj]
  have hcomp : rcRho ∘ₗ (LinearMap.id : H 3 →ₗ[ℂ] H 3) = rcRho := by
    ext z
    rfl
  rw [hcomp, rcRho_trace_one]
  norm_num

theorem rcRhoWeight3_axNorm : AxNorm rcRhoWeight3 := by
  intro D
  have htop : D.cells.sup id = (⊤ : Submodule ℂ (H 3)) := by
    rw [Finset.sup_id_eq_sSup]
    exact D.span
  have hsum := Gleason.bornValue_sum_of_pairwise_isOrtho rcRho D.cells id
    (fun c hc c' hc' hne => D.ortho c hc c' hc' hne)
  rw [htop, rcRho_bornValue_top] at hsum
  simpa [rcRhoWeight3] using hsum.symm

private theorem rc_rankOne_comp_projL (a b : H 3) (c : Submodule ℂ (H 3)) :
    (InnerProductSpace.rankOne ℂ a b : H 3 →ₗ[ℂ] H 3) ∘ₗ projL c =
      (InnerProductSpace.rankOne ℂ a (projL c b) : H 3 →ₗ[ℂ] H 3) := by
  ext1 z
  simp only [LinearMap.comp_apply, projL, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply]
  have hsymm :
      ⟪b, c.starProjection z⟫_ℂ = ⟪c.starProjection b, z⟫_ℂ := by
    simpa only [ContinuousLinearMap.coe_coe] using
      (Submodule.starProjection_isSymmetric c b z).symm
  rw [hsymm]

theorem rcRhoWeight3_axNul : AxNul rcRhoWeight3 rcE0 := by
  intro D c hc hv
  show Gleason.bornValue rcRho c = 0
  have hpv : projL c rcE0 = 0 := by
    change c.starProjection rcE0 = 0
    exact (Submodule.starProjection_apply_eq_zero_iff c).mpr hv
  have hpw_mem : projL c rcE1 ∈ c := by
    change c.starProjection rcE1 ∈ c
    exact Submodule.starProjection_apply_mem c rcE1
  have hcross : ⟪projL c rcE1, rcE0⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal c rcE0).mp hv _ hpw_mem
  unfold Gleason.bornValue
  have hcomp :
      rcRho ∘ₗ projL c =
        ((InnerProductSpace.rankOne ℂ rcE0 rcE0 : H 3 →ₗ[ℂ] H 3) ∘ₗ projL c) +
        ((InnerProductSpace.rankOne ℂ rcE0 rcE1 : H 3 →ₗ[ℂ] H 3) ∘ₗ projL c) +
        ((InnerProductSpace.rankOne ℂ rcE1 rcE0 : H 3 →ₗ[ℂ] H 3) ∘ₗ projL c) := by
    ext z
    simp [rcRho, LinearMap.comp_apply]
  rw [hcomp,
    rc_rankOne_comp_projL rcE0 rcE0 c,
    rc_rankOne_comp_projL rcE0 rcE1 c,
    rc_rankOne_comp_projL rcE1 rcE0 c]
  simp only [map_add, InnerProductSpace.trace_rankOne, Complex.add_re]
  rw [hpv, hcross]
  simp

/-- Unit direction on which the quadratic form of `rcRho` is negative. -/
def rcU : H 3 := (3 / 5 : ℂ) • rcE0 - (4 / 5 : ℂ) • rcE1

private theorem rcU_zero : rcU 0 = (3 / 5 : ℂ) := by
  norm_num [rcU, rcE0, rcE1]

private theorem rcU_one : rcU 1 = (-4 / 5 : ℂ) := by
  norm_num [rcU, rcE0, rcE1]

private theorem rcU_two : rcU 2 = 0 := by
  simp [rcU, rcE0, rcE1,
    show (2 : Fin 3) ≠ (0 : Fin 3) by decide,
    show (2 : Fin 3) ≠ (1 : Fin 3) by decide]

theorem rcU_norm : ‖rcU‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, rcU_zero, rcU_one, rcU_two]
  norm_num

private theorem inner_rcE0_rcU : ⟪rcE0, rcU⟫_ℂ = (3 / 5 : ℂ) := by
  unfold rcE0
  rw [EuclideanSpace.inner_single_left, rcU_zero]
  norm_num

private theorem inner_rcE1_rcU : ⟪rcE1, rcU⟫_ℂ = (-4 / 5 : ℂ) := by
  unfold rcE1
  rw [EuclideanSpace.inner_single_left, rcU_one]
  norm_num

private theorem rcRho_quadratic_u :
    (⟪rcRho rcU, rcU⟫_ℂ).re = -3 / 5 := by
  simp only [rcRho, LinearMap.add_apply, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, inner_add_left, inner_smul_left]
  rw [inner_rcE0_rcU, inner_rcE1_rcU]
  simp only [starRingEnd_apply, star_natCast]
  norm_num

theorem rcRhoWeight3_not_axPos : ¬ AxPos rcRhoWeight3 := by
  intro hPos
  have h := hPos
    (Perspective.binary (ℂ ∙ rcU) (rc_span_ne_bot_of_norm_one rcU_norm)
      (rc_span_ne_top_of_norm_one rcU_norm))
    (ℂ ∙ rcU) (Finset.mem_insert_self _ _)
  change 0 ≤ Gleason.bornValue rcRho (ℂ ∙ rcU) at h
  rw [Gleason.bornValue_span_singleton rcRho rcU rcU_norm,
    rcRho_quadratic_u] at h
  norm_num at h

/-- Unit direction giving a concrete mismatch with Born for `rcE0`. -/
def rcX : H 3 := (3 / 5 : ℂ) • rcE0 + (4 / 5 : ℂ) • rcE1

private theorem rcX_zero : rcX 0 = (3 / 5 : ℂ) := by
  norm_num [rcX, rcE0, rcE1]

private theorem rcX_one : rcX 1 = (4 / 5 : ℂ) := by
  norm_num [rcX, rcE0, rcE1]

private theorem rcX_two : rcX 2 = 0 := by
  simp [rcX, rcE0, rcE1,
    show (2 : Fin 3) ≠ (0 : Fin 3) by decide,
    show (2 : Fin 3) ≠ (1 : Fin 3) by decide]

theorem rcX_norm : ‖rcX‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, rcX_zero, rcX_one, rcX_two]
  norm_num

private theorem inner_rcE0_rcX : ⟪rcE0, rcX⟫_ℂ = (3 / 5 : ℂ) := by
  unfold rcE0
  rw [EuclideanSpace.inner_single_left, rcX_zero]
  norm_num

private theorem inner_rcE1_rcX : ⟪rcE1, rcX⟫_ℂ = (4 / 5 : ℂ) := by
  unfold rcE1
  rw [EuclideanSpace.inner_single_left, rcX_one]
  norm_num

private theorem inner_rcX_rcE0 : ⟪rcX, rcE0⟫_ℂ = (3 / 5 : ℂ) := by
  rw [show ⟪rcX, rcE0⟫_ℂ = starRingEnd ℂ ⟪rcE0, rcX⟫_ℂ from
    (inner_conj_symm rcX rcE0).symm]
  rw [inner_rcE0_rcX]
  simp only [starRingEnd_apply, star_natCast]
  norm_num

private theorem rcRho_quadratic_x :
    (⟪rcRho rcX, rcX⟫_ℂ).re = 33 / 25 := by
  simp only [rcRho, LinearMap.add_apply, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, inner_add_left, inner_smul_left]
  rw [inner_rcE0_rcX, inner_rcE1_rcX]
  simp only [starRingEnd_apply, star_natCast]
  norm_num

private theorem projL_rcX_rcE0 :
    projL (ℂ ∙ rcX) rcE0 = (3 / 5 : ℂ) • rcX := by
  unfold projL
  rw [ContinuousLinearMap.coe_coe,
    Submodule.starProjection_unit_singleton ℂ rcX_norm rcE0,
    inner_rcX_rcE0]

private theorem born_rcX_for_rcE0 :
    ‖projL (ℂ ∙ rcX) rcE0‖ ^ 2 = 9 / 25 := by
  rw [projL_rcX_rcE0, norm_smul, rcX_norm]
  norm_num

theorem rcRhoWeight3_not_born_on_rcX :
    rcRhoWeight3
        (Perspective.binary (ℂ ∙ rcX) (rc_span_ne_bot_of_norm_one rcX_norm)
          (rc_span_ne_top_of_norm_one rcX_norm))
        (ℂ ∙ rcX) ≠
      ‖projL (ℂ ∙ rcX) rcE0‖ ^ 2 := by
  change Gleason.bornValue rcRho (ℂ ∙ rcX) ≠ ‖projL (ℂ ∙ rcX) rcE0‖ ^ 2
  rw [Gleason.bornValue_span_singleton rcRho rcX rcX_norm,
    rcRho_quadratic_x, born_rcX_for_rcE0]
  norm_num

/-- Removing positivity leaves RC, normalization and null support intact but
permits Hermitian cross terms that move the weights away from Born. -/
theorem sharpness_remove_pos :
    AxSplitRC rcRhoWeight3 ∧
    AxNorm rcRhoWeight3 ∧
    AxNul rcRhoWeight3 rcE0 ∧
    ¬ AxPos rcRhoWeight3 ∧
    ∃ (D : Perspective 3) (c : Submodule ℂ (H 3)),
      c ∈ D.cells ∧ rcRhoWeight3 D c ≠ ‖projL c rcE0‖ ^ 2 := by
  refine ⟨rcRhoWeight3_axSplitRC, rcRhoWeight3_axNorm,
    rcRhoWeight3_axNul, rcRhoWeight3_not_axPos, ?_⟩
  exact ⟨Perspective.binary (ℂ ∙ rcX) (rc_span_ne_bot_of_norm_one rcX_norm)
      (rc_span_ne_top_of_norm_one rcX_norm),
    (ℂ ∙ rcX), Finset.mem_insert_self _ _, rcRhoWeight3_not_born_on_rcX⟩

end

end QuantumFoundations.BornRule
