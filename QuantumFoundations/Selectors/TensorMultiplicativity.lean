import QuantumFoundations.Selectors.AncillaNeutrality

namespace QuantumFoundations.Selector

open QuantumFoundations
open QuantumFoundations.FiniteTensor
open QuantumFoundations.Uhlhorn (projL_singleton_unit)
open Gleason
open scoped InnerProductSpace

noncomputable section

def isotropicResidual (d : ℕ) (t : ℝ) : ℝ := (1 - t) / ((d : ℝ) - 1)

theorem isotropicResidual_at_one (d : ℕ) : isotropicResidual d 1 = 0 := by
  unfold isotropicResidual
  norm_num

theorem tDensity_apply_orthogonal
    (hd : 2 ≤ d) {t : ℝ} {ψ x : H d}
    (hψ : ‖ψ‖ = 1) (horth : ⟪ψ, x⟫_ℂ = 0) :
    tDensity d t ψ x = (((isotropicResidual d t : ℝ) : ℂ) • x) := by
  unfold tDensity isotropicResidual
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
  rw [projL_singleton_unit ψ x hψ, horth]
  simp only [smul_zero, zero_smul, zero_add]
  have hsum := congrArg (fun A : H d →ₗ[ℂ] H d => A x)
    (projL_add_projL_compl (ℂ ∙ ψ))
  simp only [LinearMap.add_apply, LinearMap.id_apply] at hsum
  rw [projL_singleton_unit ψ x hψ, horth] at hsum
  simp only [smul_zero, zero_smul, zero_add] at hsum
  rw [hsum]

theorem isotropicDensity_apply_orthogonal
    {n a : ℕ} (hd : 2 ≤ n * a) {t : ℝ}
    {ψ x : BipartiteSpace n a}
    (hψ : ‖ψ‖ = 1) (horth : ⟪ψ, x⟫_ℂ = 0) :
    isotropicDensity (𝕜 := ℂ) (n * a) t ψ x =
      (((isotropicResidual (n * a) t : ℝ) : ℂ) • x) := by
  unfold isotropicDensity isotropicResidual
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
  have hp : (ℂ ∙ ψ).starProjection.toLinearMap x = 0 := by
    change (ℂ ∙ ψ).starProjection x = 0
    rw [Submodule.starProjection_unit_singleton ℂ hψ x, horth]
    simp
  have hpcom : (ℂ ∙ ψ)ᗮ.starProjection.toLinearMap x = x := by
    change (ℂ ∙ ψ)ᗮ.starProjection x = x
    have hsum := Submodule.starProjection_add_starProjection_orthogonal
      (K := ℂ ∙ ψ) x
    have hsum' : (ℂ ∙ ψ)ᗮ.starProjection x +
        (ℂ ∙ ψ).starProjection x = x := by
      simpa [add_comm] using hsum
    rw [Submodule.starProjection_unit_singleton ℂ hψ x, horth] at hsum'
    simpa using hsum'
  rw [hp, hpcom]
  simp

private theorem real_scalar_eq_of_smul_eq {n a : ℕ}
    {c d : ℝ} {z : BipartiteSpace n a} (hz : ‖z‖ = 1)
    (h : ((c : ℝ) : ℂ) • z = ((d : ℝ) : ℂ) • z) : c = d := by
  have h' := congrArg (fun y : BipartiteSpace n a => ⟪z, y⟫_ℂ) h
  rw [inner_smul_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hz] at h'
  norm_num at h'
  exact_mod_cast h'

private theorem parameter_equations_of_operator_mult
    (hn : 2 ≤ n) (ha : 2 ≤ a) (D : TensorDecomposition n a) {t u : ℝ}
    (hMult :
      ∀ (ψ : H n) (η : H a), ‖ψ‖ = 1 → ‖η‖ = 1 →
        D.toCoordinatesOperator
            (tDensity (n * a) (t * u) (D.productState ψ η)) =
          tensorOperator (tDensity n t ψ) (tDensity a u η)) :
    isotropicResidual (n * a) (t * u) = t * isotropicResidual a u ∧
      isotropicResidual (n * a) (t * u) = isotropicResidual n t * u ∧
      isotropicResidual (n * a) (t * u) =
        isotropicResidual n t * isotropicResidual a u := by
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by have h := hn; omega⟩
  let j0 : Fin a := ⟨0, by omega⟩
  let j1 : Fin a := ⟨1, by have h := ha; omega⟩
  let ψ0 : H n := stdKet i0
  let ψ1 : H n := stdKet i1
  let η0 : H a := stdKet j0
  let η1 : H a := stdKet j1
  have hi : i0 ≠ i1 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv
  have hj : j0 ≠ j1 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv
  have hψ0 : ‖ψ0‖ = 1 := by dsimp [ψ0]; exact stdKet_norm _
  have hψ1 : ‖ψ1‖ = 1 := by dsimp [ψ1]; exact stdKet_norm _
  have hη0 : ‖η0‖ = 1 := by dsimp [η0]; exact stdKet_norm _
  have hη1 : ‖η1‖ = 1 := by dsimp [η1]; exact stdKet_norm _
  have h01 : ⟪productStateCoordinates ψ0 η0,
      productStateCoordinates ψ0 η1⟫_ℂ = 0 := by
    rw [inner_productStateCoordinates]
    dsimp [ψ0, ψ1, η0, η1]
    rw [stdKet_inner, stdKet_inner]
    simp [hj]
  have h10 : ⟪productStateCoordinates ψ0 η0,
      productStateCoordinates ψ1 η0⟫_ℂ = 0 := by
    rw [inner_productStateCoordinates]
    dsimp [ψ0, ψ1, η0, η1]
    rw [stdKet_inner, stdKet_inner]
    simp [hi]
  have h11 : ⟪productStateCoordinates ψ0 η0,
      productStateCoordinates ψ1 η1⟫_ℂ = 0 := by
    rw [inner_productStateCoordinates]
    dsimp [ψ0, ψ1, η0, η1]
    rw [stdKet_inner, stdKet_inner]
    simp [hi, hj]
  have hz01 : ‖productStateCoordinates ψ0 η1‖ = 1 :=
    productStateCoordinates_norm_one hψ0 hη1
  have hz10 : ‖productStateCoordinates ψ1 η0‖ = 1 :=
    productStateCoordinates_norm_one hψ1 hη0
  have hz11 : ‖productStateCoordinates ψ1 η1‖ = 1 :=
    productStateCoordinates_norm_one hψ1 hη1
  have hM01 := hMult ψ0 η0 hψ0 hη0
  have hM10 := hMult ψ0 η0 hψ0 hη0
  have hM11 := hMult ψ0 η0 hψ0 hη0
  rw [D.toCoordinates_tDensity_productState] at hM01
  rw [D.toCoordinates_tDensity_productState] at hM10
  rw [D.toCoordinates_tDensity_productState] at hM11
  have heq01 : isotropicResidual (n * a) (t * u) =
      t * isotropicResidual a u := by
    have hv := congrArg
      (fun A : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a =>
        A (productStateCoordinates ψ0 η1)) hM01
    rw [isotropicDensity_apply_orthogonal (n := n) (a := a)
      (mul_dimension_ge_two hn ha)
      (productStateCoordinates_norm_one hψ0 hη0) h01] at hv
    rw [tensorOperator_apply_productState,
      tDensity_apply_self hψ0 t,
      tDensity_apply_orthogonal ha hη0 (by
        dsimp [η0, η1]
        rw [stdKet_inner]
        simp [hj])] at hv
    rw [productStateCoordinates_smul_left,
      productStateCoordinates_smul_right, smul_smul] at hv
    apply real_scalar_eq_of_smul_eq hz01
    simpa only [Complex.ofReal_mul] using hv
  have heq10 : isotropicResidual (n * a) (t * u) =
      isotropicResidual n t * u := by
    have hv := congrArg
      (fun A : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a =>
        A (productStateCoordinates ψ1 η0)) hM10
    rw [isotropicDensity_apply_orthogonal (n := n) (a := a)
      (mul_dimension_ge_two hn ha)
      (productStateCoordinates_norm_one hψ0 hη0) h10] at hv
    rw [tensorOperator_apply_productState,
      tDensity_apply_orthogonal hn hψ0 (by
        dsimp [ψ0, ψ1]
        rw [stdKet_inner]
        simp [hi]),
      tDensity_apply_self hη0 u] at hv
    rw [productStateCoordinates_smul_left,
      productStateCoordinates_smul_right, smul_smul] at hv
    apply real_scalar_eq_of_smul_eq hz10
    simpa only [Complex.ofReal_mul] using hv
  have heq11 : isotropicResidual (n * a) (t * u) =
      isotropicResidual n t * isotropicResidual a u := by
    have hv := congrArg
      (fun A : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a =>
        A (productStateCoordinates ψ1 η1)) hM11
    rw [isotropicDensity_apply_orthogonal (n := n) (a := a)
      (mul_dimension_ge_two hn ha)
      (productStateCoordinates_norm_one hψ0 hη0) h11] at hv
    rw [tensorOperator_apply_productState,
      tDensity_apply_orthogonal hn hψ0 (by
        dsimp [ψ0, ψ1]
        rw [stdKet_inner]
        simp [hi]),
      tDensity_apply_orthogonal ha hη0 (by
        dsimp [η0, η1]
        rw [stdKet_inner]
        simp [hj])] at hv
    rw [productStateCoordinates_smul_left,
      productStateCoordinates_smul_right, smul_smul] at hv
    apply real_scalar_eq_of_smul_eq hz11
    simpa only [Complex.ofReal_mul] using hv
  exact ⟨heq01, heq10, heq11⟩

theorem tensorMultiplicative_parameter_equations
    (hn : 2 ≤ n) (ha : 2 ≤ a) (D : TensorDecomposition n a)
    {t u : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hMult :
      TensorMultiplicativeUnder D
        (tSelector n hn t ht0 ht1)
        (tSelector a ha u hu0 hu1)
        (tSelector (n * a) (mul_dimension_ge_two hn ha) (t * u)
          (mul_nonneg ht0 hu0)
          (mul_unit_interval_le_one ht0 ht1 hu0 hu1))) :
    isotropicResidual (n * a) (t * u) = t * isotropicResidual a u ∧
      isotropicResidual (n * a) (t * u) = isotropicResidual n t * u ∧
      isotropicResidual (n * a) (t * u) =
        isotropicResidual n t * isotropicResidual a u := by
  apply parameter_equations_of_operator_mult hn ha D
  intro ψ η hψ hη
  exact hMult ψ η hψ hη

end
end QuantumFoundations.Selector
