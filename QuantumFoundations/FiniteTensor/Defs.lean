import QuantumFoundations.Naimark.BinaryImpl.ReplicatedAncilla

/-! Finite coordinate factorizations. -/
namespace QuantumFoundations.FiniteTensor

open QuantumFoundations
open Gleason
open scoped InnerProductSpace

noncomputable section

abbrev BipartiteIndex (n a : ℕ) := Fin a × Fin n
abbrev BipartiteSpace (n a : ℕ) := EuclideanSpace ℂ (BipartiteIndex n a)

abbrev ancillaBlockSingle {n a : ℕ} (j : Fin a) :
    H n →ₗ[ℂ] BipartiteSpace n a :=
  QuantumFoundations.Naimark.BinaryImpl.blockSingle (Fin n) j

abbrev ancillaBlockCoord {n a : ℕ} (j : Fin a) :
    BipartiteSpace n a →ₗ[ℂ] H n :=
  QuantumFoundations.Naimark.BinaryImpl.blockCoord (Fin n) j

theorem adjoint_ancillaBlockSingle {n a : ℕ} (j : Fin a) :
    LinearMap.adjoint (ancillaBlockSingle (n := n) j) = ancillaBlockCoord (n := n) j := by
  exact QuantumFoundations.Naimark.BinaryImpl.adjoint_blockSingle j

theorem adjoint_ancillaBlockCoord {n a : ℕ} (j : Fin a) :
    LinearMap.adjoint (ancillaBlockCoord (n := n) j) = ancillaBlockSingle (n := n) j := by
  exact QuantumFoundations.Naimark.BinaryImpl.adjoint_blockCoord j

theorem ancillaBlockCoord_comp_single {n a : ℕ} (j k : Fin a) :
    ancillaBlockCoord (n := n) j ∘ₗ ancillaBlockSingle (n := n) k =
      if j = k then LinearMap.id else 0 := by
  exact QuantumFoundations.Naimark.BinaryImpl.blockCoord_blockSingle j k

theorem ancillaBlock_decomposition {n a : ℕ} (z : BipartiteSpace n a) :
    (∑ j : Fin a, ancillaBlockSingle (n := n) j (ancillaBlockCoord (n := n) j z)) = z := by
  ext p
  classical
  simp [ancillaBlockSingle, ancillaBlockCoord,
    QuantumFoundations.Naimark.BinaryImpl.blockSingle,
    QuantumFoundations.Naimark.BinaryImpl.blockCoord]

structure TensorDecomposition (n a : ℕ) where
  toBipartite : H (n * a) ≃ₗᵢ[ℂ] BipartiteSpace n a

namespace TensorDecomposition

variable {n a : ℕ} (D : TensorDecomposition n a)

def toCoordinatesOperator (A : H (n * a) →ₗ[ℂ] H (n * a)) :
    BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a :=
  D.toBipartite.toLinearMap ∘ₗ A ∘ₗ D.toBipartite.symm.toLinearMap

def fromCoordinatesOperator (A : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a) :
    H (n * a) →ₗ[ℂ] H (n * a) :=
  D.toBipartite.symm.toLinearMap ∘ₗ A ∘ₗ D.toBipartite.toLinearMap

theorem toCoordinatesOperator_id : D.toCoordinatesOperator LinearMap.id = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp [toCoordinatesOperator]

theorem toCoordinatesOperator_zero : D.toCoordinatesOperator 0 = 0 := by
  ext x
  simp [toCoordinatesOperator]

theorem toCoordinatesOperator_add (A B : H (n * a) →ₗ[ℂ] H (n * a)) :
    D.toCoordinatesOperator (A + B) = D.toCoordinatesOperator A + D.toCoordinatesOperator B := by
  ext x
  simp [toCoordinatesOperator, LinearMap.add_apply]

theorem toCoordinatesOperator_smul (c : ℂ) (A : H (n * a) →ₗ[ℂ] H (n * a)) :
    D.toCoordinatesOperator (c • A) = c • D.toCoordinatesOperator A := by
  ext x
  simp [toCoordinatesOperator, LinearMap.smul_apply]

theorem toCoordinatesOperator_comp (A B : H (n * a) →ₗ[ℂ] H (n * a)) :
    D.toCoordinatesOperator (A ∘ₗ B) = D.toCoordinatesOperator A ∘ₗ D.toCoordinatesOperator B := by
  ext x
  simp [toCoordinatesOperator, LinearMap.comp_apply, LinearMap.comp_assoc]

theorem toCoordinatesOperator_adjoint (A : H (n * a) →ₗ[ℂ] H (n * a)) :
    D.toCoordinatesOperator (LinearMap.adjoint A) = LinearMap.adjoint (D.toCoordinatesOperator A) := by
  simp only [toCoordinatesOperator, LinearMap.adjoint_comp]
  rw [show LinearMap.adjoint D.toBipartite.toLinearMap = D.toBipartite.symm.toLinearMap by
    symm
    apply (LinearMap.eq_adjoint_iff _ _).2
    intro x y
    exact D.toBipartite.symm.inner_map_eq_flip x y]
  rw [show LinearMap.adjoint D.toBipartite.symm.toLinearMap = D.toBipartite.toLinearMap by
    symm
    apply (LinearMap.eq_adjoint_iff _ _).2
    intro x y
    exact D.toBipartite.inner_map_eq_flip x y]
  simp only [LinearMap.adjoint_adjoint, LinearMap.comp_assoc]

theorem from_to_coordinates_operator (A : H (n * a) →ₗ[ℂ] H (n * a)) :
    D.fromCoordinatesOperator (D.toCoordinatesOperator A) = A := by
  ext x
  simp [fromCoordinatesOperator, toCoordinatesOperator, LinearMap.comp_apply]

theorem to_from_coordinates_operator (A : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a) :
    D.toCoordinatesOperator (D.fromCoordinatesOperator A) = A := by
  ext x
  simp [fromCoordinatesOperator, toCoordinatesOperator, LinearMap.comp_apply]

end TensorDecomposition
end
end QuantumFoundations.FiniteTensor
