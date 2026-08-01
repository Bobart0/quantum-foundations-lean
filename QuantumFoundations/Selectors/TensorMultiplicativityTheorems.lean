import QuantumFoundations.Selectors.TensorClassification

namespace QuantumFoundations.Selector

open QuantumFoundations
open QuantumFoundations.FiniteTensor
open Gleason
open scoped InnerProductSpace

noncomputable section

theorem tensorOperator_smul_id_smul_id {n a : ℕ} (c d : ℂ) :
    tensorOperator (c • (LinearMap.id : H n →ₗ[ℂ] H n))
        (d • (LinearMap.id : H a →ₗ[ℂ] H a)) =
      (c * d) • (LinearMap.id : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a) := by
  apply linearMap_ext_productStdKet
  intro j i
  change tensorOperator (c • (LinearMap.id : H n →ₗ[ℂ] H n))
      (d • (LinearMap.id : H a →ₗ[ℂ] H a))
      (productStateCoordinates (stdKet i) (stdKet j)) = _
  rw [tensorOperator_apply_productState]
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [productStateCoordinates_smul_left,
    productStateCoordinates_smul_right, smul_smul]
  change (c * d) • productStateCoordinates (stdKet i) (stdKet j) =
    (c * d) • productStateCoordinates (stdKet i) (stdKet j)
  rfl

theorem isotropicDensity_at_inv_dim_general {d : ℕ} (hd : 2 ≤ d)
    {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    {v : V} (hv : ‖v‖ = 1) :
    isotropicDensity (𝕜 := ℂ) d (1 / (d : ℝ)) v =
      ((1 / (d : ℝ) : ℝ) : ℂ) • (LinearMap.id : V →ₗ[ℂ] V) := by
  have hc : (1 - 1 / (d : ℝ)) / ((d : ℝ) - 1) = 1 / (d : ℝ) :=
    one_sub_inv_dim_div_sub_one hd
  have hsum : (ℂ ∙ v).starProjection.toLinearMap +
      (ℂ ∙ v)ᗮ.starProjection.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (ℂ ∙ v).starProjection x + (ℂ ∙ v)ᗮ.starProjection x = x
    have hx := Submodule.starProjection_add_starProjection_orthogonal
      (K := ℂ ∙ v) x
    simpa [add_comm] using hx
  unfold isotropicDensity
  rw [hc, ← smul_add, hsum]
  rfl

theorem born_tensorMultiplicative
    (hn : 2 ≤ n) (ha : 2 ≤ a) (D : TensorDecomposition n a) :
    TensorMultiplicativeUnder D (bornSelector n) (bornSelector a)
      (bornSelector (n * a)) := by
  intro ψ η hψ hη
  change D.toCoordinatesOperator
      (projL (ℂ ∙ D.productState ψ η)) =
    tensorOperator (projL (ℂ ∙ ψ)) (projL (ℂ ∙ η))
  rw [D.toCoordinatesOperator_projL_span, D.toBipartite_productState]
  exact (tensorOperator_projL_singletons hψ hη).symm

theorem maximallyMixed_tensorMultiplicative
    (hn : 2 ≤ n) (ha : 2 ≤ a) (D : TensorDecomposition n a) :
    TensorMultiplicativeUnder D
      (tSelector n hn (1 / (n : ℝ)) (inv_dim_nonneg hn) (inv_dim_le_one hn))
      (tSelector a ha (1 / (a : ℝ)) (inv_dim_nonneg ha) (inv_dim_le_one ha))
      (tSelector (n * a) (mul_dimension_ge_two hn ha)
        (1 / ((n : ℝ) * (a : ℝ)))
        (by simpa [Nat.cast_mul] using inv_dim_nonneg (mul_dimension_ge_two hn ha))
        (by simpa [Nat.cast_mul] using inv_dim_le_one (mul_dimension_ge_two hn ha))) := by
  intro ψ η hψ hη
  change D.toCoordinatesOperator
      (tDensity (n * a) (1 / ((n : ℝ) * (a : ℝ))) (D.productState ψ η)) =
    tensorOperator
      (tDensity n (1 / (n : ℝ)) ψ)
      (tDensity a (1 / (a : ℝ)) η)
  rw [D.toCoordinates_tDensity_productState]
  change isotropicDensity (n * a) (1 / ((n : ℝ) * (a : ℝ)))
      (productStateCoordinates ψ η) = _
  have hprod : (1 / ((n : ℝ) * (a : ℝ))) = 1 / ((n * a : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
  rw [hprod, isotropicDensity_at_inv_dim_general (mul_dimension_ge_two hn ha)
    (productStateCoordinates_norm_one hψ hη)]
  rw [tDensity_at_inv_dim hn hψ, tDensity_at_inv_dim ha hη,
    tensorOperator_smul_id_smul_id]
  congr 1
  have hscalar : (1 / ((n * a : ℕ) : ℝ)) =
      (1 / (n : ℝ)) * (1 / (a : ℝ)) := by
    rw [Nat.cast_mul]
    field_simp [ne_of_gt (dimension_cast_pos hn), ne_of_gt (dimension_cast_pos ha)]
  rw [hscalar, Complex.ofReal_mul]

theorem tSelectors_tensorMultiplicative_iff
    (hn : 2 ≤ n) (ha : 2 ≤ a) (D : TensorDecomposition n a)
    {t u : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    TensorMultiplicativeUnder D
      (tSelector n hn t ht0 ht1)
      (tSelector a ha u hu0 hu1)
      (tSelector (n * a) (mul_dimension_ge_two hn ha) (t * u)
        (mul_nonneg ht0 hu0)
        (mul_unit_interval_le_one ht0 ht1 hu0 hu1)) ↔
      ((t = 1 ∧ u = 1) ∨
        (t = 1 / (n : ℝ) ∧ u = 1 / (a : ℝ))) := by
  constructor
  · intro h
    have heq := tensorMultiplicative_parameter_equations hn ha D
      ht0 ht1 hu0 hu1 h
    exact isotropic_tensor_parameter_classification hn ha ht0 ht1 hu0 hu1
      heq.1 heq.2.1 heq.2.2
  · rintro (⟨ht, hu⟩ | ⟨ht, hu⟩)
    · subst t
      subst u
      intro ψ η hψ hη
      dsimp [tSelector]
      rw [one_mul]
      change D.toCoordinatesOperator
          (tDensity (n * a) 1 (D.productState ψ η)) =
        tensorOperator (tDensity n 1 ψ) (tDensity a 1 η)
      rw [D.toCoordinates_tDensity_productState, tDensity_at_one,
        tDensity_at_one]
      change isotropicDensity (n * a) 1 (productStateCoordinates ψ η) = _
      unfold isotropicDensity
      norm_num
      exact (tensorOperator_projL_singletons hψ hη).symm
    · subst t
      subst u
      have hparam : (1 / (n : ℝ)) * (1 / (a : ℝ)) =
          1 / ((n : ℝ) * (a : ℝ)) := by
        field_simp [ne_of_gt (dimension_cast_pos hn),
          ne_of_gt (dimension_cast_pos ha)]
      intro ψ η hψ hη
      dsimp [tSelector]
      rw [hparam]
      exact (maximallyMixed_tensorMultiplicative hn ha D) ψ η hψ hη

end
end QuantumFoundations.Selector
