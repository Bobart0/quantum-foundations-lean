import QuantumFoundations.Selectors.BridgeNonvacuity
import QuantumFoundations.Selectors.Nonvacuity

namespace QuantumFoundations.Selector

open QuantumFoundations
open QuantumFoundations.FiniteTensor

theorem covariance_without_nsnc1 :
    IsCovariant (tSelector 2 (by norm_num) (1 / 2) (by norm_num) (by norm_num)) ∧
      ¬ NSNC1 (tSelector 2 (by norm_num) (1 / 2) (by norm_num) (by norm_num)) := by
  exact tSelector_half_covariant_not_nsnc1

theorem covariant_and_tensorMultiplicative_not_implies_nsnc1
    (hn : 2 ≤ n) (ha : 2 ≤ a) (D : TensorDecomposition n a) :
    (IsCovariant
        (tSelector n hn (1 / (n : ℝ)) (inv_dim_nonneg hn) (inv_dim_le_one hn)) ∧
      IsCovariant
        (tSelector a ha (1 / (a : ℝ)) (inv_dim_nonneg ha) (inv_dim_le_one ha)) ∧
      TensorMultiplicativeUnder D
        (tSelector n hn (1 / (n : ℝ)) (inv_dim_nonneg hn) (inv_dim_le_one hn))
        (tSelector a ha (1 / (a : ℝ)) (inv_dim_nonneg ha) (inv_dim_le_one ha))
        (tSelector (n * a) (mul_dimension_ge_two hn ha)
          (1 / ((n : ℝ) * (a : ℝ)))
          (by simpa [Nat.cast_mul] using inv_dim_nonneg (mul_dimension_ge_two hn ha))
          (by simpa [Nat.cast_mul] using inv_dim_le_one (mul_dimension_ge_two hn ha))) ∧
      ¬ NSNC1
        (tSelector n hn (1 / (n : ℝ)) (inv_dim_nonneg hn) (inv_dim_le_one hn))) := by
  refine ⟨tSelector_isCovariant hn (inv_dim_nonneg hn) (inv_dim_le_one hn),
    tSelector_isCovariant ha (inv_dim_nonneg ha) (inv_dim_le_one ha), ?_, ?_⟩
  · exact maximallyMixed_tensorMultiplicative hn ha D
  · exact maximallyMixed_tSelector_not_nsnc1 hn

theorem tSelector_not_ancillaNeutral_of_ne_one
    (hn : 2 ≤ n) (ha : 2 ≤ a) (D : TensorDecomposition n a)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ht : t ≠ 1) :
    ¬ AncillaNeutralUnder D
      (tSelector (n * a) (mul_dimension_ge_two hn ha) t ht0 ht1)
      (tSelector n hn t ht0 ht1) := by
  intro h
  exact ht ((tSelector_ancillaNeutral_iff_t_eq_one hn ha D ht0 ht1).mp h)

theorem tSelector_half_not_ancillaNeutral
    (D : TensorDecomposition 2 2) :
    ¬ AncillaNeutralUnder D
      (tSelector 4 (by norm_num) (1 / 2) (by norm_num) (by norm_num))
      (tSelector 2 (by norm_num) (1 / 2) (by norm_num) (by norm_num)) := by
  exact tSelector_not_ancillaNeutral_of_ne_one (by norm_num) (by norm_num) D
    (by norm_num) (by norm_num) (by norm_num)

end QuantumFoundations.Selector
