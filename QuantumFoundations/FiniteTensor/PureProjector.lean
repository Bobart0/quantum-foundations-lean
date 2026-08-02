import QuantumFoundations.FiniteTensor.Operator
import QuantumFoundations.Uhlhorn.Defs
namespace QuantumFoundations.FiniteTensor
open QuantumFoundations
open QuantumFoundations.Uhlhorn
open Gleason
open scoped InnerProductSpace
noncomputable section
def productStdKet {n a : ℕ} (j : Fin a) (i : Fin n) : BipartiteSpace n a := productStateCoordinates (stdKet i) (stdKet j)
theorem productStdKet_eq_blockSingle {n a : ℕ} (j : Fin a) (i : Fin n) : productStdKet j i = ancillaBlockSingle j (stdKet i) := by
  ext p
  cases p with
  | mk j2 i2 =>
    by_cases hj : j2 = j <;> by_cases hi : i2 = i <;>
      simp [productStdKet, productStateCoordinates, ancillaBlockSingle, QuantumFoundations.Naimark.BinaryImpl.blockSingle, stdKet, EuclideanSpace.basisFun_apply, PiLp.single_apply, hj, hi]
theorem productStdKet_norm {n a : ℕ} (j : Fin a) (i : Fin n) : ‖productStdKet j i‖ = 1 := by
  change ‖productStateCoordinates (stdKet i) (stdKet j)‖ = 1
  rw [norm_productStateCoordinates, stdKet_norm, stdKet_norm, one_mul]
theorem productStdKet_orthonormal {n a : ℕ} : Orthonormal ℂ (fun p : Fin a × Fin n => productStdKet p.1 p.2) := by
  constructor
  · intro p
    cases p with
    | mk j i => exact productStdKet_norm j i
  · intro p q hpq
    cases p with
    | mk j1 i1 =>
      cases q with
      | mk j2 i2 =>
        change ⟪productStateCoordinates (stdKet i1) (stdKet j1), productStateCoordinates (stdKet i2) (stdKet j2)⟫_ℂ = 0
        rw [inner_productStateCoordinates, stdKet_inner, stdKet_inner]
        by_cases hj : j1 = j2
        · subst j2
          have hi : i1 ≠ i2 := by
            intro h
            apply hpq
            simp [h]
          simp [hi]
        · simp [hj]
private theorem coordinates_expand_stdKet {n : ℕ} (x : H n) : x = ∑ i : Fin n, x i • stdKet i := by
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  calc
    x = ∑ i : Fin n, (b.repr x).ofLp i • b i := (b.sum_repr x).symm
    _ = ∑ i : Fin n, x i • stdKet i := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
theorem linearMap_ext_productStdKet {n a : ℕ} (A B : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a)
    (h : ∀ (j : Fin a) (i : Fin n), A (productStdKet j i) = B (productStdKet j i)) : A = B := by
  apply LinearMap.ext
  intro z
  rw [← ancillaBlock_decomposition z]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hexpand (T : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a) : T (ancillaBlockSingle j (ancillaBlockCoord j z)) = ∑ i : Fin n, ancillaBlockCoord j z i • T (productStdKet j i) := by
    calc
      T (ancillaBlockSingle j (ancillaBlockCoord j z)) = T (ancillaBlockSingle j (∑ i : Fin n, ancillaBlockCoord j z i • stdKet i)) := by exact congrArg (fun x => T (ancillaBlockSingle j x)) (coordinates_expand_stdKet _)
      _ = ∑ i : Fin n, ancillaBlockCoord j z i • T (ancillaBlockSingle j (stdKet i)) := by simp only [map_sum, map_smul]
      _ = ∑ i : Fin n, ancillaBlockCoord j z i • T (productStdKet j i) := by apply Finset.sum_congr rfl; intro i hi; rw [productStdKet_eq_blockSingle]
  rw [hexpand A, hexpand B]
  apply Finset.sum_congr rfl
  intro i hi
  rw [h j i]
theorem tensorOperator_projL_singletons {n a : ℕ} {ψ : H n} {η : H a} (hψ : ‖ψ‖ = 1) (hη : ‖η‖ = 1) : tensorOperator (Gleason.projL (ℂ ∙ ψ)) (Gleason.projL (ℂ ∙ η)) = (ℂ ∙ productStateCoordinates ψ η).starProjection.toLinearMap := by
  apply linearMap_ext_productStdKet
  intro j i
  change tensorOperator (Gleason.projL (ℂ ∙ ψ)) (Gleason.projL (ℂ ∙ η)) (productStateCoordinates (stdKet i) (stdKet j)) = _
  rw [tensorOperator_apply_productState]
  rw [projL_singleton_unit ψ (stdKet i) hψ]
  rw [projL_singleton_unit η (stdKet j) hη]
  rw [productStateCoordinates_smul_left, productStateCoordinates_smul_right, smul_smul]
  change (⟪ψ, stdKet i⟫_ℂ * ⟪η, stdKet j⟫_ℂ) • productStateCoordinates ψ η = (ℂ ∙ productStateCoordinates ψ η).starProjection (productStateCoordinates (stdKet i) (stdKet j))
  rw [Submodule.starProjection_unit_singleton ℂ (productStateCoordinates_norm_one hψ hη)]
  rw [inner_productStateCoordinates]
end
end QuantumFoundations.FiniteTensor
