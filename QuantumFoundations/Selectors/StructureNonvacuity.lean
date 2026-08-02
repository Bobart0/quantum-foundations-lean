import QuantumFoundations.Selectors.PerspectiveClassification

/-!
**FR.** # Selectors — Module B, non-vacuité

Les classifications `cellwiseInvariant_density_iff_blockScalar` et
`setwiseInvariant_density_iff_blockScalar_orbitConstant`
(`PerspectiveClassification.lean`) ne portent pas sur un ensemble vide :
pour TOUTE perspective `D`, l'état maximalement mélangé
`(1/n) • id` (`maximallyMixed_isDensityOperator`) est un opérateur densité
trivialement invariant sous N'IMPORTE QUEL sous-groupe
(`maximallyMixed_isInvariantUnder`), donc en particulier sous les deux
stabilisateurs de `D`.

**EN.** # Selectors — Module B, nonvacuity

The classifications `cellwiseInvariant_density_iff_blockScalar` and
`setwiseInvariant_density_iff_blockScalar_orbitConstant`
(`PerspectiveClassification.lean`) do not range over an empty set: for
EVERY perspective `D`, the maximally mixed state `(1/n) • id`
(`maximallyMixed_isDensityOperator`) is a density operator trivially
invariant under ANY subgroup (`maximallyMixed_isInvariantUnder`), hence in
particular under both of `D`'s stabilizers.
-/

namespace QuantumFoundations.Selector

open scoped InnerProductSpace
open Gleason
open QuantumFoundations.BornRule
open scoped Classical

noncomputable section

variable {n : ℕ}

/-- The maximally mixed state `(1/n) • id` is a density operator, for any
nonzero dimension `n`. -/
theorem maximallyMixed_isDensityOperator (hn : 0 < n) :
    IsDensityOperator (((n:ℝ)⁻¹ : ℂ) • (LinearMap.id : H n →ₗ[ℂ] H n)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    show ⟪(((n:ℝ)⁻¹:ℂ) • x), y⟫_ℂ = ⟪x, ((n:ℝ)⁻¹:ℂ) • y⟫_ℂ
    rw [inner_smul_left, inner_smul_right,
      show starRingEnd ℂ (((n:ℝ)⁻¹:ℂ)) = ((n:ℝ)⁻¹:ℂ) from by rw [map_inv₀, Complex.conj_ofReal]]
  · intro x
    show 0 ≤ (⟪((n:ℝ)⁻¹:ℂ) • x, x⟫_ℂ).re
    rw [inner_smul_left]
    rw [show starRingEnd ℂ (((n:ℝ)⁻¹:ℂ)) = ((n:ℝ)⁻¹:ℂ) from by rw [map_inv₀, Complex.conj_ofReal]]
    rw [← Complex.ofReal_inv, Complex.re_ofReal_mul]
    have h1 := Submodule.re_inner_starProjection_nonneg (⊤ : Submodule ℂ (H n)) x
    have h2 : (⊤ : Submodule ℂ (H n)).starProjection x = x :=
      Submodule.starProjection_eq_self_iff.mpr Submodule.mem_top
    rw [h2] at h1
    exact mul_nonneg (by positivity) h1
  · show LinearMap.trace ℂ (H n) (((n:ℝ)⁻¹ : ℂ) • (LinearMap.id : H n →ₗ[ℂ] H n)) = 1
    rw [map_smul (LinearMap.trace ℂ (H n)) (((n:ℝ)⁻¹ : ℂ)) LinearMap.id, LinearMap.trace_id]
    have hfr : Module.finrank ℂ (H n) = n := by simp
    rw [hfr, smul_eq_mul]
    have hnC : ((n:ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    norm_cast

/-- A scalar multiple of the identity is invariant under EVERY subgroup of
isometries, since conjugation fixes it pointwise. -/
theorem maximallyMixed_isInvariantUnder (G : Subgroup (H n ≃ₗᵢ[ℂ] H n)) :
    IsInvariantUnder G (((n:ℝ)⁻¹ : ℂ) • (LinearMap.id : H n →ₗ[ℂ] H n)) := by
  intro U _
  apply LinearMap.ext
  intro x
  show U ((((n:ℝ)⁻¹:ℂ) • (LinearMap.id : H n →ₗ[ℂ] H n)) (U.symm x))
    = (((n:ℝ)⁻¹:ℂ) • (LinearMap.id : H n →ₗ[ℂ] H n)) x
  rw [LinearMap.smul_apply, LinearMap.id_apply, map_smul, U.apply_symm_apply, LinearMap.smul_apply,
    LinearMap.id_apply]

/-- Nonvacuity of the cellwise classification: `D`'s cellwise-invariant
densities always contain the maximally mixed state. -/
theorem cellwiseInvariant_density_nonvacuous (D : Perspective n) (hn : 0 < n) :
    IsDensityOperator (((n:ℝ)⁻¹ : ℂ) • (LinearMap.id : H n →ₗ[ℂ] H n)) ∧
      IsInvariantUnder (PerspectiveCellwiseStabilizer D) (((n:ℝ)⁻¹ : ℂ) • (LinearMap.id : H n →ₗ[ℂ] H n)) :=
  ⟨maximallyMixed_isDensityOperator hn, maximallyMixed_isInvariantUnder _⟩

/-- Nonvacuity of the setwise classification: `D`'s setwise-invariant
densities always contain the maximally mixed state. -/
theorem setwiseInvariant_density_nonvacuous (D : Perspective n) (hn : 0 < n) :
    IsDensityOperator (((n:ℝ)⁻¹ : ℂ) • (LinearMap.id : H n →ₗ[ℂ] H n)) ∧
      IsInvariantUnder (PerspectiveSetwiseStabilizer D) (((n:ℝ)⁻¹ : ℂ) • (LinearMap.id : H n →ₗ[ℂ] H n)) :=
  ⟨maximallyMixed_isDensityOperator hn, maximallyMixed_isInvariantUnder _⟩

end

end QuantumFoundations.Selector
