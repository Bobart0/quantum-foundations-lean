import QuantumFoundations.FiniteTensor.Defs

namespace QuantumFoundations.FiniteTensor

open QuantumFoundations
open Gleason
open scoped InnerProductSpace

noncomputable section

def reindexUnitary {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) :
    EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ β :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

@[simp] theorem reindexUnitary_apply {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (x : EuclideanSpace ℂ α) (j : β) :
    reindexUnitary e x j = x (e.symm j) := by
  rfl

@[simp] theorem reindexUnitary_symm_apply {α β : Type} [Fintype α] [Fintype β]
    (e : α ≃ β) (x : EuclideanSpace ℂ β) (i : α) :
    (reindexUnitary e).symm x i = x (e i) := by
  simp [reindexUnitary, LinearIsometryEquiv.piLpCongrLeft_symm]

def canonicalBipartiteIndexEquiv (n a : ℕ) : Fin (n * a) ≃ BipartiteIndex n a :=
  Fintype.equivOfCardEq (by simp [Nat.mul_comm])

def canonicalTensorDecomposition (n a : ℕ) : TensorDecomposition n a :=
  ⟨reindexUnitary (canonicalBipartiteIndexEquiv n a)⟩

theorem tensorDecomposition_nonempty (n a : ℕ) : Nonempty (TensorDecomposition n a) :=
  ⟨canonicalTensorDecomposition n a⟩

end
end QuantumFoundations.FiniteTensor
