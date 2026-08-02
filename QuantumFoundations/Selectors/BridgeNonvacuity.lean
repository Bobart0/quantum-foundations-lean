import QuantumFoundations.Selectors.AncillaNeutrality
import QuantumFoundations.Selectors.TensorDiagnostics

namespace QuantumFoundations.Selector

open QuantumFoundations.FiniteTensor

theorem bridge_tensor_decomposition_nonempty {n a : ℕ} :
    Nonempty (TensorDecomposition n a) := tensorDecomposition_nonempty n a

theorem bornSelector_nsnc1 (n : ℕ) : NSNC1 (bornSelector n) := by
  exact (nsnc1_iff_born (bornSelector n)).mpr (fun _ _ => rfl)

theorem bornSelector_tensorMultiplicative
    (hn : 2 ≤ n) (ha : 2 ≤ a) (D : TensorDecomposition n a) :
    TensorMultiplicativeUnder D (bornSelector n) (bornSelector a)
      (bornSelector (n * a)) :=
  born_tensorMultiplicative hn ha D

theorem maximallyMixed_tSelector_not_nsnc1 (hn : 2 ≤ n) :
    ¬ NSNC1
      (tSelector n hn (1 / (n : ℝ)) (inv_dim_nonneg hn) (inv_dim_le_one hn)) := by
  intro h
  have heq := (tSelector_nsnc1_iff_t_eq_one hn
    (inv_dim_nonneg hn) (inv_dim_le_one hn)).mp h
  have hlt : 1 / (n : ℝ) < 1 := by
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    exact (div_lt_iff₀ (dimension_cast_pos hn)).2 (by linarith)
  linarith

theorem ancillaNeutral_nonempty
    (hn : 2 ≤ n) (ha : 2 ≤ a) (D : TensorDecomposition n a) :
    ∃ σSA : Selector (n * a), ∃ σS : Selector n,
      AncillaNeutralUnder D σSA σS :=
  ⟨bornSelector (n * a), bornSelector n,
    QuantumFoundations.Selector.bornSelector_ancillaNeutral hn ha D⟩

theorem tensorMultiplicative_nonempty
    (hn : 2 ≤ n) (ha : 2 ≤ a) (D : TensorDecomposition n a) :
    ∃ σS : Selector n, ∃ σA : Selector a, ∃ σSA : Selector (n * a),
      TensorMultiplicativeUnder D σS σA σSA :=
  ⟨bornSelector n, bornSelector a, bornSelector (n * a),
    born_tensorMultiplicative hn ha D⟩

theorem tensorMultiplicative_nonBorn_nonempty
    (hn : 2 ≤ n) (ha : 2 ≤ a) (D : TensorDecomposition n a) :
    ∃ σS : Selector n, ∃ σA : Selector a, ∃ σSA : Selector (n * a),
      TensorMultiplicativeUnder D σS σA σSA ∧ ¬ NSNC1 σS := by
  let σS := tSelector n hn (1 / (n : ℝ)) (inv_dim_nonneg hn) (inv_dim_le_one hn)
  let σA := tSelector a ha (1 / (a : ℝ)) (inv_dim_nonneg ha) (inv_dim_le_one ha)
  let σSA := tSelector (n * a) (mul_dimension_ge_two hn ha)
    (1 / ((n : ℝ) * (a : ℝ)))
    (by simpa [Nat.cast_mul] using inv_dim_nonneg (mul_dimension_ge_two hn ha))
    (by simpa [Nat.cast_mul] using inv_dim_le_one (mul_dimension_ge_two hn ha))
  exact ⟨σS, σA, σSA, maximallyMixed_tensorMultiplicative hn ha D,
    maximallyMixed_tSelector_not_nsnc1 hn⟩

theorem covariant_tensorMultiplicative_not_nsnc1_nonempty
    (hn : 2 ≤ n) (ha : 2 ≤ a) (D : TensorDecomposition n a) :
    ∃ σS : Selector n, ∃ σA : Selector a, ∃ σSA : Selector (n * a),
      IsCovariant σS ∧ IsCovariant σA ∧
      TensorMultiplicativeUnder D σS σA σSA ∧ ¬ NSNC1 σS := by
  let σS := tSelector n hn (1 / (n : ℝ)) (inv_dim_nonneg hn) (inv_dim_le_one hn)
  let σA := tSelector a ha (1 / (a : ℝ)) (inv_dim_nonneg ha) (inv_dim_le_one ha)
  let σSA := tSelector (n * a) (mul_dimension_ge_two hn ha)
    (1 / ((n : ℝ) * (a : ℝ)))
    (by simpa [Nat.cast_mul] using inv_dim_nonneg (mul_dimension_ge_two hn ha))
    (by simpa [Nat.cast_mul] using inv_dim_le_one (mul_dimension_ge_two hn ha))
  exact ⟨σS, σA, σSA,
    tSelector_isCovariant hn (inv_dim_nonneg hn) (inv_dim_le_one hn),
    tSelector_isCovariant ha (inv_dim_nonneg ha) (inv_dim_le_one ha),
    maximallyMixed_tensorMultiplicative hn ha D,
    maximallyMixed_tSelector_not_nsnc1 hn⟩

end QuantumFoundations.Selector
