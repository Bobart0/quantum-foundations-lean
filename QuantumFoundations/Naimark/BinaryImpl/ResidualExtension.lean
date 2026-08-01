import QuantumFoundations.Naimark.BinaryImpl.StrictClassification
import QuantumFoundations.Naimark.BinaryImpl.SumCoordinates

namespace QuantumFoundations.Naimark.BinaryImpl

open QuantumFoundations Gleason
open scoped InnerProductSpace

noncomputable section

variable {n : ℕ} {E : H n →ₗ[ℂ] H n}
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The block-diagonal operator on a binary Euclidean sum. -/
def blockDiagonal
    (A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (B : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ) :
    EuclideanSpace ℂ (Sum ι κ) →ₗ[ℂ] EuclideanSpace ℂ (Sum ι κ) :=
  euclideanSumInl ι κ ∘ₗ A ∘ₗ euclideanSumFst ι κ +
    euclideanSumInr ι κ ∘ₗ B ∘ₗ euclideanSumSnd ι κ

theorem blockDiagonal_apply_decomposition
    (A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (B : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ)
    (z : EuclideanSpace ℂ (Sum ι κ)) :
    blockDiagonal A B z =
      euclideanSumInl ι κ (A (euclideanSumFst ι κ z)) +
        euclideanSumInr ι κ (B (euclideanSumSnd ι κ z)) := rfl

theorem blockDiagonal_inl
    (A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (B : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ)
    (x : EuclideanSpace ℂ ι) :
    blockDiagonal A B (euclideanSumInl ι κ x) =
      euclideanSumInl ι κ (A x) := by
  rw [blockDiagonal_apply_decomposition, euclideanSumFst_inl_apply,
    euclideanSumSnd_inl_apply, map_zero, map_zero, add_zero]

theorem blockDiagonal_inr
    (A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (B : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ)
    (y : EuclideanSpace ℂ κ) :
    blockDiagonal A B (euclideanSumInr ι κ y) =
      euclideanSumInr ι κ (B y) := by
  rw [blockDiagonal_apply_decomposition, euclideanSumFst_inr_apply,
    euclideanSumSnd_inr_apply, map_zero, map_zero, zero_add]

theorem blockDiagonal_comp_inl
    (A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (B : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ) :
    blockDiagonal A B ∘ₗ euclideanSumInl ι κ =
      euclideanSumInl ι κ ∘ₗ A := by
  apply LinearMap.ext
  intro x
  exact blockDiagonal_inl A B x

theorem blockDiagonal_comp_inr
    (A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (B : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ) :
    blockDiagonal A B ∘ₗ euclideanSumInr ι κ =
      euclideanSumInr ι κ ∘ₗ B := by
  apply LinearMap.ext
  intro y
  exact blockDiagonal_inr A B y

theorem blockDiagonal_comp
    (A A' : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (B B' : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ) :
    blockDiagonal A B ∘ₗ blockDiagonal A' B' =
      blockDiagonal (A ∘ₗ A') (B ∘ₗ B') := by
  apply LinearMap.ext
  intro z
  rw [show z = euclideanSumInl ι κ (euclideanSumFst ι κ z) +
      euclideanSumInr ι κ (euclideanSumSnd ι κ z) from
      (euclideanSum_decomposition z).symm]
  simp only [map_add, blockDiagonal_inl, blockDiagonal_inr,
    blockDiagonal_apply_decomposition, euclideanSumFst_inl_apply,
    euclideanSumFst_inr_apply, euclideanSumSnd_inl_apply,
    euclideanSumSnd_inr_apply, map_zero, add_zero, zero_add,
    LinearMap.comp_apply]

theorem blockDiagonal_idempotent
    {A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι}
    {B : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ}
    (hA : A ∘ₗ A = A) (hB : B ∘ₗ B = B) :
    blockDiagonal A B ∘ₗ blockDiagonal A B = blockDiagonal A B := by
  rw [blockDiagonal_comp, hA, hB]

theorem blockDiagonal_isSymmetric
    {A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι}
    {B : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    (blockDiagonal A B).IsSymmetric := by
  intro z z'
  rw [show z = euclideanSumInl ι κ (euclideanSumFst ι κ z) +
      euclideanSumInr ι κ (euclideanSumSnd ι κ z) from
      (euclideanSum_decomposition z).symm,
    show z' = euclideanSumInl ι κ (euclideanSumFst ι κ z') +
      euclideanSumInr ι κ (euclideanSumSnd ι κ z') from
      (euclideanSum_decomposition z').symm]
  simp only [map_add, blockDiagonal_inl, blockDiagonal_inr,
    inner_add_left, inner_add_right, inner_euclideanSumInl,
    inner_euclideanSumInr, euclideanSumFst_inl_apply,
    euclideanSumFst_inr_apply, euclideanSumSnd_inl_apply,
    euclideanSumSnd_inr_apply, map_zero, inner_zero_left,
    inner_zero_right, zero_add, add_zero]
  rw [hA, hB]

theorem blockDiagonal_isSymmetricProjection
    {A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι}
    {B : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ}
    (hA : A.IsSymmetricProjection) (hB : B.IsSymmetricProjection) :
    (blockDiagonal A B).IsSymmetricProjection :=
  ⟨blockDiagonal_idempotent hA.isIdempotentElem hB.isIdempotentElem,
    blockDiagonal_isSymmetric hA.isSymmetric hB.isSymmetric⟩

noncomputable def residualExtension
    (I : BinaryImpl n E ι)
    (Q : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ)
    (hQ : Q.IsSymmetricProjection) :
    BinaryImpl n E (Sum ι κ) where
  encoding := euclideanSumInl ι κ ∘ₗ I.encoding
  cell := blockDiagonal I.cell Q
  encoding_isometry := by
    simp only [LinearMap.adjoint_comp, adjoint_euclideanSumInl,
      LinearMap.comp_assoc, euclideanSumFst_comp_inl,
      LinearMap.comp_id]
    exact I.encoding_isometry
  cell_isProjection := blockDiagonal_isSymmetricProjection
    I.cell_isProjection hQ
  realizes := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.adjoint_comp]
    rw [blockDiagonal_inl, adjoint_euclideanSumInl,
      euclideanSumFst_inl_apply]
    exact LinearMap.congr_fun I.realizes x

theorem residualExtension_encoding (I : BinaryImpl n E ι)
    (Q : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ)
    (hQ : Q.IsSymmetricProjection) :
    (residualExtension I Q hQ).encoding =
      euclideanSumInl ι κ ∘ₗ I.encoding := rfl

theorem residualExtension_cell (I : BinaryImpl n E ι)
    (Q : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ)
    (hQ : Q.IsSymmetricProjection) :
    (residualExtension I Q hQ).cell = blockDiagonal I.cell Q := rfl

theorem residualExtension_realizes_same_effect (I : BinaryImpl n E ι)
    (Q : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ)
    (hQ : Q.IsSymmetricProjection) :
    LinearMap.adjoint (residualExtension I Q hQ).encoding ∘ₗ
        (residualExtension I Q hQ).cell ∘ₗ
        (residualExtension I Q hQ).encoding = E :=
  (residualExtension I Q hQ).realizes

private theorem id_isSymmetricProjection (α : Type) [Fintype α] [DecidableEq α] :
    (LinearMap.id : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α).IsSymmetricProjection :=
  ⟨by
    change LinearMap.id ∘ₗ LinearMap.id = LinearMap.id
    simp, by intro x y; simp⟩

private theorem zero_isSymmetricProjection (α : Type) [Fintype α] [DecidableEq α] :
    (0 : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α).IsSymmetricProjection :=
  ⟨by
    change (0 : EuclideanSpace ℂ α →ₗ[ℂ] EuclideanSpace ℂ α) ∘ₗ 0 = 0
    apply LinearMap.ext
    intro x
    simp, by intro x y; simp⟩

noncomputable def eventResidualExtension
    (I : BinaryImpl n E ι) (r : ℕ) :
    BinaryImpl n E (Sum ι (Fin r)) :=
  residualExtension I LinearMap.id (id_isSymmetricProjection (Fin r))

noncomputable def complementResidualExtension
    (I : BinaryImpl n E ι) (s : ℕ) :
    BinaryImpl n E (Sum ι (Fin s)) :=
  residualExtension I 0 (zero_isSymmetricProjection (Fin s))

noncomputable def twoSidedResidualExtension
    (I : BinaryImpl n E ι) (r s : ℕ) :=
  complementResidualExtension (eventResidualExtension I r) s

end

end QuantumFoundations.Naimark.BinaryImpl




