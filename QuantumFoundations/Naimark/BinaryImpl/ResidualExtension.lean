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

private theorem finrank_map_eq_of_leftInverse
    {R M N : Type*} [DivisionRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [FiniteDimensional R M] [FiniteDimensional R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (hgf : g ∘ₗ f = LinearMap.id)
    (p : Submodule R M) :
    Module.finrank R (Submodule.map f p) = Module.finrank R p := by
  have hmap : Submodule.map g (Submodule.map f p) = p := by
    apply le_antisymm
    · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      rw [← LinearMap.comp_apply, hgf]
      exact hz
    · intro x hx
      exact ⟨f x, ⟨x, hx, rfl⟩, by
        rw [← LinearMap.comp_apply, hgf]
        simp⟩
  apply le_antisymm
  · exact Submodule.finrank_map_le f p
  · have h := Submodule.finrank_map_le g (Submodule.map f p)
    rw [hmap] at h
    exact h

private theorem finrank_range_comp_inl
    (A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι) :
    Module.finrank ℂ (LinearMap.range
        (euclideanSumInl ι κ ∘ₗ A)) =
      Module.finrank ℂ (LinearMap.range A) := by
  rw [LinearMap.range_comp]
  exact finrank_map_eq_of_leftInverse (euclideanSumInl ι κ)
    (euclideanSumFst ι κ) (euclideanSumFst_comp_inl (α := ι) (β := κ)) _

private theorem finrank_range_comp_inr
    (B : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ) :
    Module.finrank ℂ (LinearMap.range
        (euclideanSumInr ι κ ∘ₗ B)) =
      Module.finrank ℂ (LinearMap.range B) := by
  rw [LinearMap.range_comp]
  exact finrank_map_eq_of_leftInverse (euclideanSumInr ι κ)
    (euclideanSumSnd ι κ) (euclideanSumSnd_comp_inr (α := ι) (β := κ)) _

private theorem range_blockDiagonal
    (A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (B : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ) :
    LinearMap.range (blockDiagonal A B) =
      LinearMap.range (euclideanSumInl ι κ ∘ₗ A) ⊔
        LinearMap.range (euclideanSumInr ι κ ∘ₗ B) := by
  apply le_antisymm
  · rintro z ⟨w, rfl⟩
    rw [blockDiagonal_apply_decomposition]
    apply Submodule.add_mem
    · exact Submodule.mem_sup_left ⟨_, rfl⟩
    · exact Submodule.mem_sup_right ⟨_, rfl⟩
  · intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    refine ⟨euclideanSumInl ι κ x + euclideanSumInr ι κ y, ?_⟩
    rw [blockDiagonal_apply_decomposition]
    simp only [euclideanSumFst_inl_apply, euclideanSumFst_inr_apply,
      euclideanSumSnd_inl_apply, euclideanSumSnd_inr_apply,
      map_zero, zero_add, add_zero, LinearMap.comp_apply, map_add]

private theorem blockDiagonal_range_inf_eq_bot
    (A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (B : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ) :
    LinearMap.range (euclideanSumInl ι κ ∘ₗ A) ⊓
        LinearMap.range (euclideanSumInr ι κ ∘ₗ B) = ⊥ := by
  have horth :
      LinearMap.range (euclideanSumInl ι κ ∘ₗ A) ≤
        (LinearMap.range (euclideanSumInr ι κ ∘ₗ B))ᗮ := by
    intro z hz
    rw [Submodule.mem_orthogonal]
    intro w hw
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, rfl⟩ := hw
    exact inner_sumInr_sumInl_eq_zero (α := ι) (β := κ) _ _
  rw [Submodule.eq_bot_iff]
  intro z hz
  have hz0 := horth hz.1
  rw [Submodule.mem_orthogonal] at hz0
  have hz0' := hz0 z hz.2
  rw [inner_self_eq_zero] at hz0'
  exact hz0'

theorem ambientDim_residualExtension_fin (I : BinaryImpl n E ι)
    (Q : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ)
    (hQ : Q.IsSymmetricProjection) :
    (residualExtension I Q hQ).ambientDim =
      Fintype.card ι + Fintype.card κ := by
  change Fintype.card (Sum ι κ) = Fintype.card ι + Fintype.card κ
  simp only [Fintype.card_sum]

theorem projectorRank_residualExtension (I : BinaryImpl n E ι)
    (Q : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ)
    (hQ : Q.IsSymmetricProjection) :
    (residualExtension I Q hQ).projectorRank =
      I.projectorRank + Module.finrank ℂ (LinearMap.range Q) := by
  change Module.finrank ℂ (LinearMap.range (blockDiagonal I.cell Q)) = _
  rw [range_blockDiagonal]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (euclideanSumInl ι κ ∘ₗ I.cell))
    (LinearMap.range (euclideanSumInr ι κ ∘ₗ Q))
  rw [blockDiagonal_range_inf_eq_bot, finrank_bot] at hdim
  rw [finrank_range_comp_inl, finrank_range_comp_inr] at hdim
  rw [show Module.finrank ℂ (LinearMap.range I.cell) = I.projectorRank from rfl] at hdim
  exact hdim

theorem projectorNullity_residualExtension (I : BinaryImpl n E ι)
    (Q : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ)
    (hQ : Q.IsSymmetricProjection) :
    (residualExtension I Q hQ).projectorNullity =
      I.projectorNullity + Module.finrank ℂ (LinearMap.ker Q) := by
  have hJ := (residualExtension I Q hQ).projectorRank_add_nullity
  have hI := I.projectorRank_add_nullity
  have hR := projectorRank_residualExtension I Q hQ
  have hQ' : Module.finrank ℂ (LinearMap.range Q) +
      Module.finrank ℂ (LinearMap.ker Q) = Fintype.card κ := by
    rw [LinearMap.finrank_range_add_finrank_ker]
    exact finrank_euclideanSpace
  have hA := ambientDim_residualExtension_fin I Q hQ
  change I.projectorRank + I.projectorNullity = Fintype.card ι at hI
  omega

theorem eventLeg_residualExtension (I : BinaryImpl n E ι)
    (Q : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ)
    (hQ : Q.IsSymmetricProjection) :
    eventLeg (residualExtension I Q hQ) =
      euclideanSumInl ι κ ∘ₗ eventLeg I := by
  apply LinearMap.ext
  intro x
  simp only [eventLeg, residualExtension, LinearMap.comp_apply, blockDiagonal_inl]

theorem complementLeg_residualExtension (I : BinaryImpl n E ι)
    (Q : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ)
    (hQ : Q.IsSymmetricProjection) :
    complementLeg (residualExtension I Q hQ) =
      euclideanSumInl ι κ ∘ₗ complementLeg I := by
  apply LinearMap.ext
  intro x
  simp only [complementLeg, residualExtension, BinaryImpl.complementCell,
    LinearMap.comp_apply]
  rw [show (1 - blockDiagonal I.cell Q)
      (euclideanSumInl ι κ (I.encoding x)) =
        euclideanSumInl ι κ (I.encoding x) -
          blockDiagonal I.cell Q (euclideanSumInl ι κ (I.encoding x)) by rfl,
    blockDiagonal_inl]
  change euclideanSumInl ι κ (I.encoding x) -
      euclideanSumInl ι κ (I.cell (I.encoding x)) =
    euclideanSumInl ι κ (I.encoding x - I.cell (I.encoding x))
  rw [← map_sub]

theorem combinedLeg_residualExtension (I : BinaryImpl n E ι)
    (Q : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ)
    (hQ : Q.IsSymmetricProjection) :
    combinedLeg (residualExtension I Q hQ) =
      euclideanSumInl ι κ ∘ₗ combinedLeg I := by
  apply LinearMap.ext
  intro w
  change eventLeg (residualExtension I Q hQ) (coordL n 2 0 w) +
      complementLeg (residualExtension I Q hQ) (coordL n 2 1 w) =
    euclideanSumInl ι κ (combinedLeg I w)
  rw [eventLeg_residualExtension, complementLeg_residualExtension]
  simp only [LinearMap.comp_apply, map_add, combinedLeg_apply]

theorem minimalSubspace_finrank_residualExtension (I : BinaryImpl n E ι)
    (Q : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ)
    (hQ : Q.IsSymmetricProjection) :
    Module.finrank ℂ (minimalSubspace (residualExtension I Q hQ)) =
      Module.finrank ℂ (minimalSubspace I) := by
  rw [← range_combinedLeg (residualExtension I Q hQ),
    ← range_combinedLeg I, combinedLeg_residualExtension,
    LinearMap.range_comp]
  exact finrank_map_eq_of_leftInverse (euclideanSumInl ι κ)
    (euclideanSumFst ι κ) (euclideanSumFst_comp_inl (α := ι) (β := κ)) _

theorem eventGenerated_finrank_residualExtension (I : BinaryImpl n E ι)
    (Q : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ)
    (hQ : Q.IsSymmetricProjection) :
    Module.finrank ℂ (eventGenerated (residualExtension I Q hQ)) =
      Module.finrank ℂ (eventGenerated I) := by
  rw [eventGenerated, eventLeg_residualExtension, LinearMap.range_comp]
  exact finrank_map_eq_of_leftInverse (euclideanSumInl ι κ)
    (euclideanSumFst ι κ) (euclideanSumFst_comp_inl (α := ι) (β := κ)) _

theorem complementGenerated_finrank_residualExtension (I : BinaryImpl n E ι)
    (Q : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ)
    (hQ : Q.IsSymmetricProjection) :
    Module.finrank ℂ (complementGenerated (residualExtension I Q hQ)) =
      Module.finrank ℂ (complementGenerated I) := by
  rw [complementGenerated, complementLeg_residualExtension, LinearMap.range_comp]
  exact finrank_map_eq_of_leftInverse (euclideanSumInl ι κ)
    (euclideanSumFst ι κ) (euclideanSumFst_comp_inl (α := ι) (β := κ)) _

theorem excessEventDim_residualExtension (I : BinaryImpl n E ι)
    (Q : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ)
    (hQ : Q.IsSymmetricProjection) :
    excessEventDim (residualExtension I Q hQ) =
      excessEventDim I + Module.finrank ℂ (LinearMap.range Q) := by
  have h1 := projectorRank_decomposition (residualExtension I Q hQ)
  have h2 := projectorRank_decomposition I
  have h3 := projectorRank_residualExtension I Q hQ
  have h4 := eventGenerated_finrank_residualExtension I Q hQ
  unfold excessEventDim at h1 h2 ⊢
  omega

theorem excessComplementDim_residualExtension (I : BinaryImpl n E ι)
    (Q : EuclideanSpace ℂ κ →ₗ[ℂ] EuclideanSpace ℂ κ)
    (hQ : Q.IsSymmetricProjection) :
    excessComplementDim (residualExtension I Q hQ) =
      excessComplementDim I + Module.finrank ℂ (LinearMap.ker Q) := by
  have h1 := projectorNullity_decomposition (residualExtension I Q hQ)
  have h2 := projectorNullity_decomposition I
  have h3 := projectorNullity_residualExtension I Q hQ
  have h4 := complementGenerated_finrank_residualExtension I Q hQ
  unfold excessComplementDim at h1 h2 ⊢
  omega


private theorem finrank_range_id_fin (r : ℕ) :
    Module.finrank ℂ (LinearMap.range
      (LinearMap.id : EuclideanSpace ℂ (Fin r) →ₗ[ℂ] EuclideanSpace ℂ (Fin r))) = r := by
  rw [LinearMap.range_id, finrank_top]
  simpa using (finrank_euclideanSpace (𝕜 := ℂ) (ι := Fin r))

private theorem finrank_ker_id_fin (r : ℕ) :
    Module.finrank ℂ (LinearMap.ker
      (LinearMap.id : EuclideanSpace ℂ (Fin r) →ₗ[ℂ] EuclideanSpace ℂ (Fin r))) = 0 := by
  rw [LinearMap.ker_id, finrank_bot]

private theorem finrank_ker_zero_fin (r : ℕ) :
    Module.finrank ℂ (LinearMap.ker
      (0 : EuclideanSpace ℂ (Fin r) →ₗ[ℂ] EuclideanSpace ℂ (Fin r))) = r := by
  rw [LinearMap.ker_zero, finrank_top]
  simpa using (finrank_euclideanSpace (𝕜 := ℂ) (ι := Fin r))

private theorem finrank_range_zero_fin (r : ℕ) :
    Module.finrank ℂ (LinearMap.range
      (0 : EuclideanSpace ℂ (Fin r) →ₗ[ℂ] EuclideanSpace ℂ (Fin r))) = 0 := by
  rw [LinearMap.range_zero, finrank_bot]

theorem excessEventDim_eventResidualExtension (I : BinaryImpl n E ι) (r : ℕ) :
    excessEventDim (eventResidualExtension I r) =
      excessEventDim I + r := by
  have h := excessEventDim_residualExtension I
    (LinearMap.id : EuclideanSpace ℂ (Fin r) →ₗ[ℂ] EuclideanSpace ℂ (Fin r))
    (id_isSymmetricProjection (Fin r))
  simpa [eventResidualExtension, finrank_range_id_fin] using h

theorem excessComplementDim_eventResidualExtension (I : BinaryImpl n E ι) (r : ℕ) :
    excessComplementDim (eventResidualExtension I r) =
      excessComplementDim I := by
  have h := excessComplementDim_residualExtension I
    (LinearMap.id : EuclideanSpace ℂ (Fin r) →ₗ[ℂ] EuclideanSpace ℂ (Fin r))
    (id_isSymmetricProjection (Fin r))
  have hz := finrank_ker_id_fin r
  rw [hz, add_zero] at h
  simpa [eventResidualExtension] using h

theorem excessEventDim_complementResidualExtension (I : BinaryImpl n E ι) (s : ℕ) :
    excessEventDim (complementResidualExtension I s) =
      excessEventDim I := by
  have h := excessEventDim_residualExtension I
    (0 : EuclideanSpace ℂ (Fin s) →ₗ[ℂ] EuclideanSpace ℂ (Fin s))
    (zero_isSymmetricProjection (Fin s))
  simpa [complementResidualExtension, finrank_range_zero_fin] using h

theorem excessComplementDim_complementResidualExtension (I : BinaryImpl n E ι) (s : ℕ) :
    excessComplementDim (complementResidualExtension I s) =
      excessComplementDim I + s := by
  have h := excessComplementDim_residualExtension I
    (0 : EuclideanSpace ℂ (Fin s) →ₗ[ℂ] EuclideanSpace ℂ (Fin s))
    (zero_isSymmetricProjection (Fin s))
  simpa [complementResidualExtension, finrank_ker_zero_fin] using h

private theorem IsMinimal.excessEventDim_eq_zero
    {M : BinaryImpl n E ι} (hM : IsMinimal M) :
    excessEventDim M = 0 := by
  have hdim : minimalDim M = M.ambientDim := by
    unfold minimalDim
    rw [hM, finrank_top]
    exact finrank_euclideanSpace
  have hsum := ambientDim_sub_minimalDim_eq M
  rw [hdim] at hsum
  omega

private theorem IsMinimal.excessComplementDim_eq_zero
    {M : BinaryImpl n E ι} (hM : IsMinimal M) :
    excessComplementDim M = 0 := by
  have hdim : minimalDim M = M.ambientDim := by
    unfold minimalDim
    rw [hM, finrank_top]
    exact finrank_euclideanSpace
  have hsum := ambientDim_sub_minimalDim_eq M
  rw [hdim] at hsum
  omega

theorem excessEventDim_twoSidedResidualExtension
    (M : BinaryImpl n E ι) (r s : ℕ) (hM : IsMinimal M) :
    excessEventDim (twoSidedResidualExtension M r s) = r := by
  rw [twoSidedResidualExtension,
    excessEventDim_complementResidualExtension,
    excessEventDim_eventResidualExtension,
    hM.excessEventDim_eq_zero]
  simp

theorem excessComplementDim_twoSidedResidualExtension
    (M : BinaryImpl n E ι) (r s : ℕ) (hM : IsMinimal M) :
    excessComplementDim (twoSidedResidualExtension M r s) = s := by
  rw [twoSidedResidualExtension,
    excessComplementDim_complementResidualExtension,
    excessComplementDim_eventResidualExtension,
    hM.excessComplementDim_eq_zero]
  simp


end

end QuantumFoundations.Naimark.BinaryImpl
















