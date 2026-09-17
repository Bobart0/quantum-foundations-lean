import QuantumFoundations.BornRule.RCSharpness

/-!
# Sharpness of refinement consistency

The normalized-amplitude rule is positive, normalized, and has projective null
support, but changes the weight of an unchanged outcome when another outcome is
split.  This gives a direct elementary-RC countermodel in dimension three.
-/

namespace QuantumFoundations.BornRule

open scoped Classical InnerProductSpace
open Gleason

noncomputable section

/-- Third computational-basis vector. -/
def rcE2 : H 3 := EuclideanSpace.single (2 : Fin 3) (1 : ℂ)

def rcLine1 : Submodule ℂ (H 3) := ℂ ∙ rcE1
def rcLine2 : Submodule ℂ (H 3) := ℂ ∙ rcE2

theorem rcE2_norm : ‖rcE2‖ = 1 := by simp [rcE2]

/-- Canonical orthonormal basis of `H 3`. -/
def rcBasis3 : OrthonormalBasis (Fin 3) ℂ (H 3) :=
  EuclideanSpace.basisFun (Fin 3) ℂ

private theorem rcBasis3_apply (i : Fin 3) :
    (rcBasis3 i : H 3) = EuclideanSpace.single i (1 : ℂ) := by
  simp [rcBasis3]

private theorem rcBasis3_line_zero :
    (ℂ ∙ (rcBasis3 (0 : Fin 3) : H 3)) = rcLine0 := by
  simp [rcBasis3_apply, rcLine0, rcE0]

private theorem rcBasis3_line_one :
    (ℂ ∙ (rcBasis3 (1 : Fin 3) : H 3)) = rcLine1 := by
  simp [rcBasis3_apply, rcLine1, rcE1]

private theorem rcBasis3_line_two :
    (ℂ ∙ (rcBasis3 (2 : Fin 3) : H 3)) = rcLine2 := by
  simp [rcBasis3_apply, rcLine2, rcE2]

/-- Fine perspective resolving the three computational lines. -/
def rcFine : Perspective 3 := basisPerspective rcBasis3

/-- Coarse perspective resolving only the first line and its complement. -/
def rcCoarse : Perspective 3 :=
  Perspective.binary rcLine0 rcLine0_ne_bot rcLine0_ne_top

private theorem rcLine0_mem_fine : rcLine0 ∈ rcFine.cells := by
  change rcLine0 ∈ Finset.univ.image
    (fun i : Fin 3 => ℂ ∙ (rcBasis3 i : H 3))
  rw [Finset.mem_image]
  exact ⟨0, Finset.mem_univ _, rcBasis3_line_zero⟩

private theorem rcLine1_mem_fine : rcLine1 ∈ rcFine.cells := by
  change rcLine1 ∈ Finset.univ.image
    (fun i : Fin 3 => ℂ ∙ (rcBasis3 i : H 3))
  rw [Finset.mem_image]
  exact ⟨1, Finset.mem_univ _, rcBasis3_line_one⟩

private theorem rcLine2_mem_fine : rcLine2 ∈ rcFine.cells := by
  change rcLine2 ∈ Finset.univ.image
    (fun i : Fin 3 => ℂ ∙ (rcBasis3 i : H 3))
  rw [Finset.mem_image]
  exact ⟨2, Finset.mem_univ _, rcBasis3_line_two⟩

private theorem rcLine0_mem_coarse : rcLine0 ∈ rcCoarse.cells :=
  Finset.mem_insert_self _ _

private theorem rcLine0orth_mem_coarse : rcLine0ᗮ ∈ rcCoarse.cells :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

private theorem inner_rcE0_rcE1_resolution : ⟪rcE0, rcE1⟫_ℂ = 0 := by
  unfold rcE0 rcE1
  rw [EuclideanSpace.inner_single_left]
  norm_num

private theorem inner_rcE0_rcE2 : ⟪rcE0, rcE2⟫_ℂ = 0 := by
  unfold rcE0 rcE2
  rw [EuclideanSpace.inner_single_left]
  norm_num [show (0 : Fin 3) ≠ (2 : Fin 3) by decide]

private theorem rcE1_mem_rcLine0_orthogonal_resolution : rcE1 ∈ rcLine0ᗮ := by
  unfold rcLine0
  rw [Submodule.mem_orthogonal]
  intro x hx
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [inner_smul_left, inner_rcE0_rcE1_resolution, mul_zero]

private theorem rcE2_mem_rcLine0_orthogonal : rcE2 ∈ rcLine0ᗮ := by
  unfold rcLine0
  rw [Submodule.mem_orthogonal]
  intro x hx
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [inner_smul_left, inner_rcE0_rcE2, mul_zero]

private theorem rcLine1_le_rcLine0orth : rcLine1 ≤ rcLine0ᗮ := by
  unfold rcLine1
  rw [Submodule.span_singleton_le_iff_mem]
  exact rcE1_mem_rcLine0_orthogonal_resolution

private theorem rcLine2_le_rcLine0orth : rcLine2 ≤ rcLine0ᗮ := by
  unfold rcLine2
  rw [Submodule.span_singleton_le_iff_mem]
  exact rcE2_mem_rcLine0_orthogonal

/-- The standard three-line perspective refines the binary perspective. -/
theorem rcFine_refines_rcCoarse : Refines rcFine rcCoarse := by
  intro c hc
  change c ∈ Finset.univ.image
    (fun i : Fin 3 => ℂ ∙ (rcBasis3 i : H 3)) at hc
  rw [Finset.mem_image] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi_cases with h0 | h1 | h2
  · refine ⟨rcLine0, rcLine0_mem_coarse, ?_⟩
    rw [h0, rcBasis3_line_zero]
  · refine ⟨rcLine0ᗮ, rcLine0orth_mem_coarse, ?_⟩
    rw [h1, rcBasis3_line_one]
    exact rcLine1_le_rcLine0orth
  · refine ⟨rcLine0ᗮ, rcLine0orth_mem_coarse, ?_⟩
    rw [h2, rcBasis3_line_two]
    exact rcLine2_le_rcLine0orth

private theorem rcLine1_ne_rcLine2 : rcLine1 ≠ rcLine2 := by
  intro h
  have hinj := line_injective rcBasis3
  have h12 :
      (ℂ ∙ (rcBasis3 (1 : Fin 3) : H 3) : Submodule ℂ (H 3)) =
        ℂ ∙ (rcBasis3 (2 : Fin 3) : H 3) := by
    rw [rcBasis3_line_one, rcBasis3_line_two]
    exact h
  have hi : (1 : Fin 3) = (2 : Fin 3) :=
    hinj (by simp) (by simp) h12
  exact (by decide : (1 : Fin 3) ≠ (2 : Fin 3)) hi

private theorem not_rcLine0_le_orthogonal : ¬ rcLine0 ≤ rcLine0ᗮ := by
  intro hle
  have he0_mem : rcE0 ∈ rcLine0 := Submodule.mem_span_singleton_self _
  have he0_perp : rcE0 ∈ rcLine0ᗮ := hle he0_mem
  have hz : ⟪rcE0, rcE0⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal rcLine0 rcE0).mp he0_perp rcE0 he0_mem
  have he0zero : rcE0 = 0 := inner_self_eq_zero.mp hz
  have hn := rcE0_norm
  rw [he0zero, norm_zero] at hn
  norm_num at hn

private theorem rcFine_filter_line0orth :
    rcFine.cells.filter (· ≤ rcLine0ᗮ) = {rcLine1, rcLine2} := by
  ext c
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hcFine, hcle⟩
    change c ∈ Finset.univ.image
      (fun i : Fin 3 => ℂ ∙ (rcBasis3 i : H 3)) at hcFine
    rw [Finset.mem_image] at hcFine
    obtain ⟨i, hi, rfl⟩ := hcFine
    have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi_cases with h0 | h1 | h2
    · exfalso
      rw [h0, rcBasis3_line_zero] at hcle
      exact not_rcLine0_le_orthogonal hcle
    · left
      rw [h1, rcBasis3_line_one]
    · right
      rw [h2, rcBasis3_line_two]
  · intro hc
    rcases hc with rfl | rfl
    · exact ⟨rcLine1_mem_fine, rcLine1_le_rcLine0orth⟩
    · exact ⟨rcLine2_mem_fine, rcLine2_le_rcLine0orth⟩

private theorem rcLine0orth_not_mem_fine : rcLine0ᗮ ∉ rcFine.cells := by
  intro hqFine
  have hqFilter : rcLine0ᗮ ∈ rcFine.cells.filter (· ≤ rcLine0ᗮ) :=
    Finset.mem_filter.mpr ⟨hqFine, le_refl _⟩
  rw [rcFine_filter_line0orth] at hqFilter
  simp only [Finset.mem_insert, Finset.mem_singleton] at hqFilter
  rcases hqFilter with hq1 | hq2
  · have h1 : rcLine1 = rcLine0ᗮ := hq1.symm
    have h2 : rcLine2 = rcLine0ᗮ := by
      exact rcFine.unique_parent rcLine2_mem_fine hqFine
        (rcFine.nz rcLine2 rcLine2_mem_fine) (le_refl rcLine2)
        rcLine2_le_rcLine0orth
    exact rcLine1_ne_rcLine2 (h1.trans h2.symm)
  · have h2 : rcLine2 = rcLine0ᗮ := hq2.symm
    have h1 : rcLine1 = rcLine0ᗮ := by
      exact rcFine.unique_parent rcLine1_mem_fine hqFine
        (rcFine.nz rcLine1 rcLine1_mem_fine) (le_refl rcLine1)
        rcLine1_le_rcLine0orth
    exact rcLine1_ne_rcLine2 (h1.trans h2.symm)

private theorem rcCoarse_keep_line0 :
    ∀ c ∈ rcCoarse.cells, c ≠ rcLine0ᗮ → c ∈ rcFine.cells := by
  intro c hc hne
  simp only [rcCoarse, Perspective.binary, Finset.mem_insert,
    Finset.mem_singleton] at hc
  rcases hc with rfl | hq
  · exact rcLine0_mem_fine
  · exact (hne hq).elim

/-- The concrete fine perspective is exactly one binary split of the coarse
complement cell. -/
theorem rcFine_isBinarySplit_rcCoarse : IsBinarySplit rcFine rcCoarse := by
  refine ⟨rcFine_refines_rcCoarse, rcLine0ᗮ, rcLine0orth_mem_coarse,
    rcLine0orth_not_mem_fine, rcCoarse_keep_line0, ?_⟩
  rw [rcFine_filter_line0orth]
  simp [rcLine1_ne_rcLine2]

/-! ## Normalized-amplitude rule -/

def rcAmplitudeDenom (v : H 3) (D : Perspective 3) : ℝ :=
  ∑ c ∈ D.cells, ‖projL c v‖

def rcAmplitudeWeight (v : H 3) :
    Perspective 3 → Submodule ℂ (H 3) → ℝ :=
  fun D c => ‖projL c v‖ / rcAmplitudeDenom v D

private theorem rc_projL_top_apply (v : H 3) :
    projL (⊤ : Submodule ℂ (H 3)) v = v := by
  unfold projL
  rw [Submodule.starProjection_top]
  rfl

private theorem rc_sum_sq_projL_cells_eq_one {v : H 3}
    (hv : ‖v‖ = 1) (D : Perspective 3) :
    ∑ c ∈ D.cells, ‖projL c v‖ ^ 2 = 1 := by
  have htop : D.cells.sup id = (⊤ : Submodule ℂ (H 3)) := by
    rw [Finset.sup_id_eq_sSup]
    exact D.span
  have h := sum_sq_projL_of_pairwise_isOrtho D.cells
    (fun c hc c' hc' hne => D.ortho c hc c' hc' hne) v
  rw [htop, rc_projL_top_apply, hv] at h
  norm_num at h
  exact h.symm

private theorem rcAmplitudeDenom_pos {v : H 3} (hv : ‖v‖ = 1)
    (D : Perspective 3) : 0 < rcAmplitudeDenom v D := by
  have hnonneg : 0 ≤ rcAmplitudeDenom v D := by
    unfold rcAmplitudeDenom
    exact Finset.sum_nonneg (fun c _ => norm_nonneg (projL c v))
  have hne : rcAmplitudeDenom v D ≠ 0 := by
    intro hzero
    have hterm : ∀ c ∈ D.cells, ‖projL c v‖ = 0 := by
      intro c hc
      have hle : ‖projL c v‖ ≤ rcAmplitudeDenom v D := by
        unfold rcAmplitudeDenom
        exact Finset.single_le_sum (fun d _ => norm_nonneg (projL d v)) hc
      rw [hzero] at hle
      exact le_antisymm hle (norm_nonneg _)
    have hsquares_zero : ∑ c ∈ D.cells, ‖projL c v‖ ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      rw [hterm c hc]
      norm_num
    rw [rc_sum_sq_projL_cells_eq_one hv D] at hsquares_zero
    norm_num at hsquares_zero
  exact lt_of_le_of_ne hnonneg hne.symm

theorem rcAmplitudeWeight_axNorm {v : H 3} (hv : ‖v‖ = 1) :
    AxNorm (rcAmplitudeWeight v) := by
  intro D
  change (∑ c ∈ D.cells, ‖projL c v‖ / rcAmplitudeDenom v D) = 1
  rw [← Finset.sum_div]
  change rcAmplitudeDenom v D / rcAmplitudeDenom v D = 1
  exact div_self (ne_of_gt (rcAmplitudeDenom_pos hv D))

theorem rcAmplitudeWeight_axPos {v : H 3} (hv : ‖v‖ = 1) :
    AxPos (rcAmplitudeWeight v) := by
  intro D c hc
  exact div_nonneg (norm_nonneg _) (le_of_lt (rcAmplitudeDenom_pos hv D))

theorem rcAmplitudeWeight_axNul {v : H 3} (hv : ‖v‖ = 1) :
    AxNul (rcAmplitudeWeight v) v := by
  intro D c hc horth
  have hp : projL c v = 0 := by
    change c.starProjection v = 0
    exact (Submodule.starProjection_apply_eq_zero_iff c).mpr horth
  simp [rcAmplitudeWeight, hp]

/-- Unit state with amplitudes `3/5`, `12/25`, and `16/25`. -/
def rcVResolution : H 3 :=
  (3 / 5 : ℂ) • rcE0 + (12 / 25 : ℂ) • rcE1 + (16 / 25 : ℂ) • rcE2

private theorem rcVResolution_zero : rcVResolution 0 = (3 / 5 : ℂ) := by
  norm_num [rcVResolution, rcE0, rcE1, rcE2,
    show (0 : Fin 3) ≠ (1 : Fin 3) by decide,
    show (0 : Fin 3) ≠ (2 : Fin 3) by decide]

private theorem rcVResolution_one : rcVResolution 1 = (12 / 25 : ℂ) := by
  norm_num [rcVResolution, rcE0, rcE1, rcE2,
    show (1 : Fin 3) ≠ (0 : Fin 3) by decide,
    show (1 : Fin 3) ≠ (2 : Fin 3) by decide]

private theorem rcVResolution_two : rcVResolution 2 = (16 / 25 : ℂ) := by
  norm_num [rcVResolution, rcE0, rcE1, rcE2,
    show (2 : Fin 3) ≠ (0 : Fin 3) by decide,
    show (2 : Fin 3) ≠ (1 : Fin 3) by decide]

theorem rcVResolution_norm : ‖rcVResolution‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three,
    rcVResolution_zero, rcVResolution_one, rcVResolution_two]
  norm_num

private theorem inner_rcE0_rcVResolution :
    ⟪rcE0, rcVResolution⟫_ℂ = (3 / 5 : ℂ) := by
  unfold rcE0
  rw [EuclideanSpace.inner_single_left, rcVResolution_zero]
  norm_num

private theorem inner_rcE1_rcVResolution :
    ⟪rcE1, rcVResolution⟫_ℂ = (12 / 25 : ℂ) := by
  unfold rcE1
  rw [EuclideanSpace.inner_single_left, rcVResolution_one]
  norm_num

private theorem inner_rcE2_rcVResolution :
    ⟪rcE2, rcVResolution⟫_ℂ = (16 / 25 : ℂ) := by
  unfold rcE2
  rw [EuclideanSpace.inner_single_left, rcVResolution_two]
  norm_num

private theorem projL_rcLine0_rcVResolution :
    projL rcLine0 rcVResolution = (3 / 5 : ℂ) • rcE0 := by
  unfold projL rcLine0
  rw [ContinuousLinearMap.coe_coe,
    Submodule.starProjection_unit_singleton ℂ rcE0_norm rcVResolution,
    inner_rcE0_rcVResolution]

private theorem projL_rcLine1_rcVResolution :
    projL rcLine1 rcVResolution = (12 / 25 : ℂ) • rcE1 := by
  unfold projL rcLine1
  rw [ContinuousLinearMap.coe_coe,
    Submodule.starProjection_unit_singleton ℂ rcE1_norm rcVResolution,
    inner_rcE1_rcVResolution]

private theorem projL_rcLine2_rcVResolution :
    projL rcLine2 rcVResolution = (16 / 25 : ℂ) • rcE2 := by
  unfold projL rcLine2
  rw [ContinuousLinearMap.coe_coe,
    Submodule.starProjection_unit_singleton ℂ rcE2_norm rcVResolution,
    inner_rcE2_rcVResolution]

private theorem projL_rcLine0_rcVResolution_norm :
    ‖projL rcLine0 rcVResolution‖ = 3 / 5 := by
  rw [projL_rcLine0_rcVResolution, norm_smul, rcE0_norm]
  norm_num

private theorem projL_rcLine1_rcVResolution_norm :
    ‖projL rcLine1 rcVResolution‖ = 12 / 25 := by
  rw [projL_rcLine1_rcVResolution, norm_smul, rcE1_norm]
  norm_num

private theorem projL_rcLine2_rcVResolution_norm :
    ‖projL rcLine2 rcVResolution‖ = 16 / 25 := by
  rw [projL_rcLine2_rcVResolution, norm_smul, rcE2_norm]
  norm_num

private theorem projL_rcLine0orth_rcVResolution_norm :
    ‖projL rcLine0ᗮ rcVResolution‖ = 4 / 5 := by
  have h := Submodule.norm_sq_eq_add_norm_sq_starProjection rcVResolution rcLine0
  change ‖rcVResolution‖ ^ 2 =
    ‖projL rcLine0 rcVResolution‖ ^ 2 + ‖projL rcLine0ᗮ rcVResolution‖ ^ 2 at h
  rw [rcVResolution_norm, projL_rcLine0_rcVResolution_norm] at h
  have hn := norm_nonneg (projL rcLine0ᗮ rcVResolution)
  nlinarith

private theorem rcLine0_ne_rcLine0orth : rcLine0 ≠ rcLine0ᗮ := by
  intro heq
  have hmem : rcE0 ∈ rcLine0 := Submodule.mem_span_singleton_self rcE0
  have horth : rcE0 ∈ rcLine0ᗮ := by rwa [← heq]
  have hz : ⟪rcE0, rcE0⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal rcLine0 rcE0).mp horth rcE0 hmem
  have he0 : rcE0 = 0 := inner_self_eq_zero.mp hz
  have hn := rcE0_norm
  rw [he0, norm_zero] at hn
  norm_num at hn

private theorem rcAmplitudeDenom_coarse :
    rcAmplitudeDenom rcVResolution rcCoarse = 7 / 5 := by
  change Finset.sum ({rcLine0, rcLine0ᗮ} : Finset (Submodule ℂ (H 3)))
    (fun c => ‖projL c rcVResolution‖) = 7 / 5
  have hnotmem : rcLine0 ∉ ({rcLine0ᗮ} : Finset (Submodule ℂ (H 3))) := by
    simpa using rcLine0_ne_rcLine0orth
  rw [Finset.sum_insert hnotmem, Finset.sum_singleton,
    projL_rcLine0_rcVResolution_norm, projL_rcLine0orth_rcVResolution_norm]
  norm_num

private theorem rcAmplitudeDenom_fine :
    rcAmplitudeDenom rcVResolution rcFine = 43 / 25 := by
  change Finset.sum (Finset.univ.image
      (fun i : Fin 3 => ℂ ∙ (rcBasis3 i : H 3)))
      (fun c => ‖projL c rcVResolution‖) = 43 / 25
  rw [Finset.sum_image (line_injective rcBasis3)]
  rw [Fin.sum_univ_three]
  rw [rcBasis3_line_zero, rcBasis3_line_one, rcBasis3_line_two,
    projL_rcLine0_rcVResolution_norm, projL_rcLine1_rcVResolution_norm,
    projL_rcLine2_rcVResolution_norm]
  norm_num

private theorem rcAmplitudeWeight_coarse_line0 :
    rcAmplitudeWeight rcVResolution rcCoarse rcLine0 = 3 / 7 := by
  rw [rcAmplitudeWeight, projL_rcLine0_rcVResolution_norm, rcAmplitudeDenom_coarse]
  norm_num

private theorem rcAmplitudeWeight_fine_line0 :
    rcAmplitudeWeight rcVResolution rcFine rcLine0 = 15 / 43 := by
  rw [rcAmplitudeWeight, projL_rcLine0_rcVResolution_norm, rcAmplitudeDenom_fine]
  norm_num

/-- Direct elementary-RC failure: `rcLine0` is unchanged by the split, but its
weight changes from `3/7` to `15/43`. -/
theorem rcAmplitudeWeight_not_axSplitRC :
    ¬ AxSplitRC (rcAmplitudeWeight rcVResolution) := by
  intro hRC
  have h := hRC rcFine rcCoarse rcFine_isBinarySplit_rcCoarse
    rcLine0 rcLine0_mem_coarse rcLine0_mem_fine
  rw [rcAmplitudeWeight_coarse_line0, rcAmplitudeWeight_fine_line0] at h
  norm_num at h

private theorem rcAmplitudeWeight_not_born_on_line0 :
    rcAmplitudeWeight rcVResolution rcCoarse rcLine0 ≠
      ‖projL rcLine0 rcVResolution‖ ^ 2 := by
  rw [rcAmplitudeWeight_coarse_line0, projL_rcLine0_rcVResolution_norm]
  norm_num

/-- Removing refinement consistency restores context/resolution dependence while
normalization, positivity and projective null support remain valid. -/
theorem sharpness_remove_rc :
    AxNorm (rcAmplitudeWeight rcVResolution) ∧
    AxPos (rcAmplitudeWeight rcVResolution) ∧
    AxNul (rcAmplitudeWeight rcVResolution) rcVResolution ∧
    ¬ AxSplitRC (rcAmplitudeWeight rcVResolution) ∧
    ∃ (D : Perspective 3) (c : Submodule ℂ (H 3)),
      c ∈ D.cells ∧
      rcAmplitudeWeight rcVResolution D c ≠ ‖projL c rcVResolution‖ ^ 2 := by
  refine ⟨rcAmplitudeWeight_axNorm rcVResolution_norm,
    rcAmplitudeWeight_axPos rcVResolution_norm,
    rcAmplitudeWeight_axNul rcVResolution_norm,
    rcAmplitudeWeight_not_axSplitRC, ?_⟩
  exact ⟨rcCoarse, rcLine0, rcLine0_mem_coarse,
    rcAmplitudeWeight_not_born_on_line0⟩

end

end QuantumFoundations.BornRule
