import QuantumFoundations.Selectors.TensorMultiplicativity

namespace QuantumFoundations.Selector

open QuantumFoundations
open QuantumFoundations.FiniteTensor

noncomputable section

theorem subparameter_eq_zero_iff_t_eq_one {d : ℕ} (hd : 2 ≤ d) {t : ℝ} :
    isotropicResidual d t = 0 ↔ t = 1 := by
  unfold isotropicResidual
  have hden : 0 < (d : ℝ) - 1 := dimension_sub_one_pos hd
  constructor
  · intro h
    have hnum := (div_eq_zero_iff.mp h).resolve_right (ne_of_gt hden)
    linarith
  · intro h
    subst t
    norm_num

theorem parameter_eq_subparameter_iff_t_eq_inv_dim {d : ℕ} (hd : 2 ≤ d) {t : ℝ} :
    t = isotropicResidual d t ↔ t = 1 / (d : ℝ) := by
  have hden : 0 < (d : ℝ) - 1 := dimension_sub_one_pos hd
  have hdim : 0 < (d : ℝ) := dimension_cast_pos hd
  constructor
  · intro h
    unfold isotropicResidual at h
    have hden0 : (d : ℝ) - 1 ≠ 0 := ne_of_gt hden
    field_simp [hden0] at h
    apply (eq_div_iff (ne_of_gt hdim)).2
    nlinarith [h]
  · intro h
    subst t
    unfold isotropicResidual
    have hden0 : (d : ℝ) - 1 ≠ 0 := ne_of_gt hden
    field_simp [hden0, ne_of_gt hdim]

theorem mul_eq_one_of_unitInterval {t u : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (h : t * u = 1) : t = 1 ∧ u = 1 := by
  have htu_le_t : t * u ≤ t := by
    simpa using mul_le_mul_of_nonneg_left hu1 ht0
  have htu_le_u : t * u ≤ u := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_left ht1 hu0
  constructor <;> nlinarith

theorem isotropic_tensor_parameter_classification
    (hn : 2 ≤ n) (ha : 2 ≤ a) {t u : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (h1 : isotropicResidual (n * a) (t * u) =
      t * isotropicResidual a u)
    (h2 : isotropicResidual (n * a) (t * u) =
      isotropicResidual n t * u)
    (h3 : isotropicResidual (n * a) (t * u) =
      isotropicResidual n t * isotropicResidual a u) :
    (t = 1 ∧ u = 1) ∨
      (t = 1 / (n : ℝ) ∧ u = 1 / (a : ℝ)) := by
  have e1 : (t - isotropicResidual n t) * isotropicResidual a u = 0 := by
    nlinarith [h2, h3]
  have e2 : isotropicResidual n t *
      (u - isotropicResidual a u) = 0 := by
    nlinarith [h1, h3]
  by_cases hA : isotropicResidual a u = 0
  · have hu : u = 1 :=
      (subparameter_eq_zero_iff_t_eq_one ha).mp hA
    have hNA : isotropicResidual (n * a) (t * u) = 0 := by
      rw [h1, hA]
      ring
    have htu : t * u = 1 :=
      (subparameter_eq_zero_iff_t_eq_one (mul_dimension_ge_two hn ha)).mp hNA
    exact Or.inl (mul_eq_one_of_unitInterval ht0 ht1 hu0 hu1 htu)
  · have htres : t = isotropicResidual n t := by
      have hz := (mul_eq_zero.mp e1).resolve_right hA
      linarith
    by_cases hN : isotropicResidual n t = 0
    · have ht : t = 1 :=
        (subparameter_eq_zero_iff_t_eq_one hn).mp hN
      have hzero : isotropicResidual (n * a) (t * u) = 0 := by
        rw [h3, hN]
        ring
      have hA' : isotropicResidual a u = 0 := by
        calc
          isotropicResidual a u = 1 * isotropicResidual a u := by ring
          _ = t * isotropicResidual a u := by rw [ht]
          _ = isotropicResidual (n * a) (t * u) := h1.symm
          _ = 0 := hzero
      exact (hA hA').elim
    · have hures : u = isotropicResidual a u := by
        have hz := (mul_eq_zero.mp e2).resolve_left hN
        linarith
      exact Or.inr ⟨
        (parameter_eq_subparameter_iff_t_eq_inv_dim hn).mp htres,
        (parameter_eq_subparameter_iff_t_eq_inv_dim ha).mp hures⟩

end
end QuantumFoundations.Selector
