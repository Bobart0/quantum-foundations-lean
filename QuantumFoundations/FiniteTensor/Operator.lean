import QuantumFoundations.FiniteTensor.ProductState
namespace QuantumFoundations.FiniteTensor
open QuantumFoundations
open Gleason
open scoped InnerProductSpace
noncomputable section
def stdKet {d : ℕ} (i : Fin d) : H d := (EuclideanSpace.basisFun (Fin d) ℂ) i
@[simp] theorem stdKet_apply {d : ℕ} (i j : Fin d) : stdKet i j = if j = i then 1 else 0 := by simp [stdKet, EuclideanSpace.basisFun_apply, PiLp.single_apply]
theorem stdKet_norm {d : ℕ} (i : Fin d) : ‖stdKet i‖ = 1 := by simp [stdKet, EuclideanSpace.basisFun_apply, PiLp.norm_single]
theorem stdKet_orthonormal {d : ℕ} : Orthonormal ℂ (stdKet : Fin d → H d) := (EuclideanSpace.basisFun (Fin d) ℂ).orthonormal
theorem stdKet_inner {d : ℕ} (i j : Fin d) : ⟪stdKet i, stdKet j⟫_ℂ = if i = j then 1 else 0 := by
  rw [PiLp.inner_apply]
  simp [stdKet, EuclideanSpace.basisFun_apply, PiLp.single_apply, RCLike.inner_apply, starRingEnd_apply, eq_comm]
def operatorEntry {d : ℕ} (A : H d →ₗ[ℂ] H d) (i j : Fin d) : ℂ := ⟪stdKet i, A (stdKet j)⟫_ℂ
theorem operator_apply_eq_sum_entries {d : ℕ} (A : H d →ₗ[ℂ] H d) (x : H d) : A x = ∑ i : Fin d, ∑ j : Fin d, (operatorEntry A i j * x j) • stdKet i := by
  let b := EuclideanSpace.basisFun (Fin d) ℂ
  calc
    A x = A (∑ j : Fin d, (b.repr x).ofLp j • b j) := by rw [b.sum_repr]
    _ = ∑ j : Fin d, (b.repr x).ofLp j • A (b j) := by rw [map_sum]; simp only [map_smul]
    _ = ∑ j : Fin d, ∑ i : Fin d, (operatorEntry A i j * x j) • stdKet i := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← b.sum_repr (A (b j)), Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hcoeff : (b.repr x).ofLp j = x j := by rfl
      have hA : (b.repr (A (b j))).ofLp i = operatorEntry A i j := by rw [OrthonormalBasis.repr_apply_apply]; rfl
      rw [hcoeff, hA, smul_smul, mul_comm]
      rfl
    _ = ∑ i : Fin d, ∑ j : Fin d, (operatorEntry A i j * x j) • stdKet i := by rw [Finset.sum_comm]
noncomputable def tensorOperator {n a : ℕ} (A : H n →ₗ[ℂ] H n) (B : H a →ₗ[ℂ] H a) : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a :=
  ∑ j : Fin a, ∑ k : Fin a, operatorEntry B j k • (ancillaBlockSingle (n := n) j ∘ₗ A ∘ₗ ancillaBlockCoord (n := n) k)
theorem tensorOperator_apply {n a : ℕ} (A : H n →ₗ[ℂ] H n) (B : H a →ₗ[ℂ] H a) (z : BipartiteSpace n a) : tensorOperator A B z = ∑ j : Fin a, ∑ k : Fin a, operatorEntry B j k • ancillaBlockSingle (n := n) j (A (ancillaBlockCoord (n := n) k z)) := by simp [tensorOperator, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
theorem ancillaBlockCoord_tensorOperator {n a : ℕ} (A : H n →ₗ[ℂ] H n) (B : H a →ₗ[ℂ] H a) (j : Fin a) (z : BipartiteSpace n a) : ancillaBlockCoord (n := n) j (tensorOperator A B z) = ∑ k : Fin a, operatorEntry B j k • A (ancillaBlockCoord (n := n) k z) := by
  rw [tensorOperator_apply]
  simp only [map_sum, map_smul]
  have hcomp : ∀ (j' k : Fin a), ancillaBlockCoord (n := n) j (ancillaBlockSingle (n := n) j' (A (ancillaBlockCoord (n := n) k z))) = if j = j' then A (ancillaBlockCoord (n := n) k z) else 0 := by
    intro j' k
    have h := LinearMap.congr_fun (ancillaBlockCoord_comp_single (n := n) j j') (A (ancillaBlockCoord (n := n) k z))
    simp only [LinearMap.comp_apply] at h
    by_cases hj : j = j'
    · subst j'; simpa using h
    · rw [if_neg hj] at h; simpa [hj] using h
  simp_rw [hcomp]
  simp [Finset.sum_ite_eq', mul_comm]
theorem tensorOperator_zero_left {n a : ℕ} (B : H a →ₗ[ℂ] H a) : tensorOperator (0 : H n →ₗ[ℂ] H n) B = 0 := by ext z; simp [tensorOperator, LinearMap.sum_apply]
theorem tensorOperator_zero_right {n a : ℕ} (A : H n →ₗ[ℂ] H n) : tensorOperator A (0 : H a →ₗ[ℂ] H a) = 0 := by ext z; simp [tensorOperator, operatorEntry, LinearMap.sum_apply]
end
end QuantumFoundations.FiniteTensor
