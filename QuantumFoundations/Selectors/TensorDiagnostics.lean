import QuantumFoundations.Selectors.TensorMultiplicativityTheorems

namespace QuantumFoundations.Selector

open QuantumFoundations
open QuantumFoundations.FiniteTensor
open Gleason
open scoped InnerProductSpace

noncomputable section

private theorem real_scalar_eq_of_smul_eq_diag {n a : ℕ}
    {c d : ℝ} {z : BipartiteSpace n a} (hz : ‖z‖ = 1)
    (h : ((c : ℝ) : ℂ) • z = ((d : ℝ) : ℂ) • z) : c = d := by
  have h' := congrArg (fun y : BipartiteSpace n a => ⟪z, y⟫_ℂ) h
  rw [inner_smul_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hz] at h'
  norm_num at h'
  exact_mod_cast h'

theorem mul_unitInterval_le_one {t u : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : t * u ≤ 1 :=
  mul_unit_interval_le_one ht0 ht1 hu0 hu1

theorem isotropicDensity_apply_self {d : ℕ} {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] {t : ℝ} {ψ : V}
    (hψ : ‖ψ‖ = 1) : isotropicDensity (𝕜 := ℂ) d t ψ ψ = ((t : ℝ) : ℂ) • ψ := by
  unfold isotropicDensity
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply]
  have hp1 : (ℂ ∙ ψ).starProjection ψ = ψ := by
    rw [Submodule.starProjection_unit_singleton ℂ hψ ψ,
      inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  have hp2 : (ℂ ∙ ψ)ᗮ.starProjection ψ = 0 := by
    have hsum := Submodule.starProjection_add_starProjection_orthogonal
      (K := ℂ ∙ ψ) ψ
    have hsum' : (ℂ ∙ ψ).starProjection ψ + (ℂ ∙ ψ)ᗮ.starProjection ψ = ψ := by
      simpa [add_comm] using hsum
    rw [hp1] at hsum'
    exact add_left_cancel (hsum'.trans (add_zero ψ).symm)
  have hp1' : (ℂ ∙ ψ).starProjection.toLinearMap ψ = ψ := hp1
  have hp2' : (ℂ ∙ ψ)ᗮ.starProjection.toLinearMap ψ = 0 := hp2
  rw [hp1', hp2', smul_zero, add_zero]
  rfl

theorem tSelector_tensorMult_iff_t_eq_one_or_inv_dim
    (hn : 2 ≤ n) (D : TensorDecomposition n n) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    TensorMultiplicativeUnder D (tSelector n hn t ht0 ht1) (tSelector n hn t ht0 ht1)
      (tSelector (n * n) (mul_dimension_ge_two hn hn) (t * t)
        (mul_nonneg ht0 ht0) (mul_unit_interval_le_one ht0 ht1 ht0 ht1)) ↔
      (t = 1 ∨ t = 1 / (n : ℝ)) := by
  have h := tSelectors_tensorMultiplicative_iff (n := n) (a := n)
    hn hn D ht0 ht1 ht0 ht1
  constructor
  · intro hm
    rcases h.mp hm with ⟨ht', _⟩ | ⟨ht', _⟩
    · exact Or.inl ht'
    · exact Or.inr ht'
  · intro ht
    rcases ht with ht | ht
    · exact h.mpr (Or.inl ⟨ht, ht⟩)
    · exact h.mpr (Or.inr ⟨ht, ht⟩)

theorem tSelector_tensorMult_iff_t_mem
    (hn : 2 ≤ n) (D : TensorDecomposition n n) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    TensorMultiplicativeUnder D (tSelector n hn t ht0 ht1) (tSelector n hn t ht0 ht1)
      (tSelector (n * n) (mul_dimension_ge_two hn hn) (t * t)
        (mul_nonneg ht0 ht0) (mul_unit_interval_le_one ht0 ht1 ht0 ht1)) ↔
      t ∈ ({1, 1 / (n : ℝ)} : Set ℝ) := by
  rw [tSelector_tensorMult_iff_t_eq_one_or_inv_dim hn D ht0 ht1]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem tSelector_sameParameterComposite_tensorMult_iff_t_eq_one
    (hn : 2 ≤ n) (ha : 2 ≤ a) (D : TensorDecomposition n a) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    TensorMultiplicativeUnder D (tSelector n hn t ht0 ht1) (tSelector a ha t ht0 ht1)
      (tSelector (n * a) (mul_dimension_ge_two hn ha) t ht0 ht1) ↔ t = 1 := by
  constructor
  · intro hMult
    let i0 : Fin n := ⟨0, by omega⟩
    let j0 : Fin a := ⟨0, by omega⟩
    let j1 : Fin a := ⟨1, by have h := ha; omega⟩
    let ψ0 : H n := stdKet i0
    let η0 : H a := stdKet j0
    let η1 : H a := stdKet j1
    have hj : j0 ≠ j1 := by
      intro h; have hv := congrArg Fin.val h; norm_num at hv
    have hψ0 : ‖ψ0‖ = 1 := by dsimp [ψ0]; exact stdKet_norm _
    have hη0 : ‖η0‖ = 1 := by dsimp [η0]; exact stdKet_norm _
    have hη1 : ‖η1‖ = 1 := by dsimp [η1]; exact stdKet_norm _
    have horth : ⟪productStateCoordinates ψ0 η0, productStateCoordinates ψ0 η1⟫_ℂ = 0 := by
      rw [inner_productStateCoordinates]
      dsimp [ψ0, η0, η1]
      rw [stdKet_inner, stdKet_inner]
      simp [hj]
    have hz00 : ‖productStateCoordinates ψ0 η0‖ = 1 := productStateCoordinates_norm_one hψ0 hη0
    have hz01 : ‖productStateCoordinates ψ0 η1‖ = 1 := productStateCoordinates_norm_one hψ0 hη1
    have hM := hMult ψ0 η0 hψ0 hη0
    dsimp [tSelector] at hM
    rw [D.toCoordinates_tDensity_productState] at hM
    have hself : t = t * t := by
      have hv := congrArg (fun A : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a =>
        A (productStateCoordinates ψ0 η0)) hM
      change isotropicDensity (n * a) t (productStateCoordinates ψ0 η0)
          (productStateCoordinates ψ0 η0) =
        tensorOperator (tDensity n t ψ0) (tDensity a t η0)
          (productStateCoordinates ψ0 η0) at hv
      rw [isotropicDensity_apply_self hz00] at hv
      rw [tensorOperator_apply_productState, tDensity_apply_self hψ0 t,
        tDensity_apply_self hη0 t] at hv
      rw [productStateCoordinates_smul_left, productStateCoordinates_smul_right, smul_smul] at hv
      apply real_scalar_eq_of_smul_eq_diag hz00
      simpa only [Complex.ofReal_mul] using hv
    have horthEq : isotropicResidual (n * a) t = t * isotropicResidual a t := by
      have hv := congrArg (fun A : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a =>
        A (productStateCoordinates ψ0 η1)) hM
      change isotropicDensity (n * a) t (productStateCoordinates ψ0 η0)
          (productStateCoordinates ψ0 η1) =
        tensorOperator (tDensity n t ψ0) (tDensity a t η0)
          (productStateCoordinates ψ0 η1) at hv
      rw [isotropicDensity_apply_orthogonal (n := n) (a := a)
        (mul_dimension_ge_two hn ha) hz00 horth] at hv
      rw [tensorOperator_apply_productState, tDensity_apply_self hψ0 t,
        tDensity_apply_orthogonal ha hη0 (by
          dsimp [η0, η1]
          rw [stdKet_inner]
          simp [hj])] at hv
      rw [productStateCoordinates_smul_left, productStateCoordinates_smul_right, smul_smul] at hv
      apply real_scalar_eq_of_smul_eq_diag hz01
      simpa only [Complex.ofReal_mul] using hv
    have ht_cases : t = 0 ∨ t = 1 := by
      by_cases ht : t = 0
      · exact Or.inl ht
      · right
        have hfactor : t * (1 - t) = 0 := by nlinarith [hself]
        have hone : 1 - t = 0 := (mul_eq_zero.mp hfactor).resolve_left ht
        linarith
    rcases ht_cases with ht | ht
    · have hzero : isotropicResidual (n * a) 0 = 0 := by simpa [ht] using horthEq
      have hpos : 0 < isotropicResidual (n * a) 0 := by
        unfold isotropicResidual
        exact div_pos (by norm_num) (dimension_sub_one_pos (mul_dimension_ge_two hn ha))
      exact (False.elim ((ne_of_gt hpos) hzero))
    · exact ht
  · intro ht
    subst t
    intro ψ η hψ hη
    dsimp [tSelector]
    change D.toCoordinatesOperator (tDensity (n * a) 1 (D.productState ψ η)) =
      tensorOperator (tDensity n 1 ψ) (tDensity a 1 η)
    rw [D.toCoordinates_tDensity_productState, tDensity_at_one, tDensity_at_one]
    change isotropicDensity (n * a) 1 (productStateCoordinates ψ η) = _
    unfold isotropicDensity
    norm_num
    exact (tensorOperator_projL_singletons hψ hη).symm

theorem tensorMultiplicative_not_implies_nsnc1
    (hn : 2 ≤ n) (ha : 2 ≤ a) (D : TensorDecomposition n a) :
    TensorMultiplicativeUnder D
      (tSelector n hn (1 / (n : ℝ)) (inv_dim_nonneg hn) (inv_dim_le_one hn))
      (tSelector a ha (1 / (a : ℝ)) (inv_dim_nonneg ha) (inv_dim_le_one ha))
      (tSelector (n * a) (mul_dimension_ge_two hn ha)
        (1 / ((n : ℝ) * (a : ℝ)))
        (by simpa [Nat.cast_mul] using inv_dim_nonneg (mul_dimension_ge_two hn ha))
        (by simpa [Nat.cast_mul] using inv_dim_le_one (mul_dimension_ge_two hn ha))) ∧
      ¬ NSNC1 (tSelector n hn (1 / (n : ℝ)) (inv_dim_nonneg hn) (inv_dim_le_one hn)) := by
  constructor
  · exact maximallyMixed_tensorMultiplicative hn ha D
  · intro hns
    have heq := (tSelector_nsnc1_iff_t_eq_one hn
      (inv_dim_nonneg hn) (inv_dim_le_one hn)).mp hns
    have hlt : 1 / (n : ℝ) < 1 := by
      have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
      exact (div_lt_iff₀ (dimension_cast_pos hn)).2 (by linarith)
    linarith

end
end QuantumFoundations.Selector
