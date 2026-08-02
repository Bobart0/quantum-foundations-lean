import QuantumFoundations.Naimark.BinaryImpl.ResidualExtension

namespace QuantumFoundations.Naimark.BinaryImpl

open QuantumFoundations Gleason
open scoped InnerProductSpace

noncomputable section

variable {n : ℕ} {E : H n →ₗ[ℂ] H n}
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def minimalCoordinates (I : BinaryImpl n E ι) :
    SubspaceCoordinates (minimalSubspace I) :=
  ofFinrank (minimalSubspace I)

def minimalCoreDim (I : BinaryImpl n E ι) : ℕ :=
  (minimalCoordinates I).dim

noncomputable def minimalCore (I : BinaryImpl n E ι) :
    BinaryImpl n E (Fin ((minimalCoordinates I).dim)) where
  encoding := (minimalCoordinates I).coord ∘ₗ I.encoding
  cell := (minimalCoordinates I).coord ∘ₗ I.cell ∘ₗ (minimalCoordinates I).embed
  encoding_isometry := by
    change LinearMap.adjoint ((minimalCoordinates I).coord ∘ₗ I.encoding) ∘ₗ
      (minimalCoordinates I).coord ∘ₗ I.encoding = LinearMap.id
    let C := minimalCoordinates I
    have hAdj : LinearMap.adjoint C.coord = C.embed := by
      rw [← C.adjoint_embed, LinearMap.adjoint_adjoint]
    have hEnc : C.embed ∘ₗ C.coord ∘ₗ I.encoding = I.encoding := by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply]
      exact C.embed_apply_coord_of_mem (encoding_mem_minimalSubspace I x)
    rw [LinearMap.adjoint_comp, hAdj]
    simp only [LinearMap.comp_assoc]
    rw [hEnc]
    simpa using I.encoding_isometry
  cell_isProjection := by
    let C := minimalCoordinates I
    have hmem (x : H C.dim) : C.embed x ∈ minimalSubspace I := by
      have hx : C.embed x ∈ LinearMap.range C.embed := ⟨x, rfl⟩
      rw [C.range_embed] at hx
      exact hx
    have hcell (x : H C.dim) : I.cell (C.embed x) ∈ minimalSubspace I :=
      cell_maps_minimalSubspace I (C.embed x) (hmem x)
    have hSym : (C.coord ∘ₗ I.cell ∘ₗ C.embed).IsSymmetric := by
      intro x y
      simp only [LinearMap.comp_apply]
      calc
        ⟪C.coord (I.cell (C.embed x)), y⟫_ℂ =
            ⟪C.embed (C.coord (I.cell (C.embed x))), C.embed y⟫_ℂ := by
              rw [C.embed_isometry]
        _ = ⟪I.cell (C.embed x), C.embed y⟫_ℂ := by
              rw [C.embed_apply_coord_of_mem (hcell x)]
        _ = ⟪C.embed x, I.cell (C.embed y)⟫_ℂ := I.cell_symmetric _ _
        _ = ⟪x, C.coord (I.cell (C.embed y))⟫_ℂ := by
              rw [← C.adjoint_embed, LinearMap.adjoint_inner_right]
    have hIdem : (C.coord ∘ₗ I.cell ∘ₗ C.embed) ∘ₗ
        (C.coord ∘ₗ I.cell ∘ₗ C.embed) =
        C.coord ∘ₗ I.cell ∘ₗ C.embed := by
      apply LinearMap.ext
      intro x
      simp only [LinearMap.comp_apply]
      rw [C.embed_apply_coord_of_mem (hcell x)]
      have h := LinearMap.congr_fun I.cell_idempotent (C.embed x)
      simpa using congrArg C.coord h
    exact ⟨hIdem, hSym⟩
  realizes := by
    change LinearMap.adjoint ((minimalCoordinates I).coord ∘ₗ I.encoding) ∘ₗ
      ((minimalCoordinates I).coord ∘ₗ I.cell ∘ₗ (minimalCoordinates I).embed) ∘ₗ
      ((minimalCoordinates I).coord ∘ₗ I.encoding) = E
    let C := minimalCoordinates I
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.adjoint_comp]
    have hAdj : LinearMap.adjoint C.coord = C.embed := by
      rw [← C.adjoint_embed, LinearMap.adjoint_adjoint]
    rw [hAdj]
    have hEnc : C.embed (C.coord (I.encoding x)) = I.encoding x :=
      C.embed_apply_coord_of_mem (encoding_mem_minimalSubspace I x)
    rw [hEnc]
    have hCell : C.embed (C.coord (I.cell (I.encoding x))) =
        I.cell (I.encoding x) :=
      C.embed_apply_coord_of_mem
        (cell_maps_minimalSubspace I (I.encoding x)
          (encoding_mem_minimalSubspace I x))
    rw [hCell]
    exact LinearMap.congr_fun I.realizes x

theorem minimalCore_encoding (I : BinaryImpl n E ι) :
    (minimalCore I).encoding = (minimalCoordinates I).coord ∘ₗ I.encoding := rfl

theorem minimalCore_cell (I : BinaryImpl n E ι) :
    (minimalCore I).cell =
      (minimalCoordinates I).coord ∘ₗ I.cell ∘ₗ (minimalCoordinates I).embed := rfl

theorem combinedLeg_minimalCore (I : BinaryImpl n E ι) :
    combinedLeg (minimalCore I) =
      (minimalCoordinates I).coord ∘ₗ combinedLeg I := by
  apply LinearMap.ext
  intro w
  let C := minimalCoordinates I
  change (minimalCore I).cell ((minimalCore I).encoding (coordL n 2 0 w)) +
      (minimalCore I).complementCell
        ((minimalCore I).encoding (coordL n 2 1 w)) =
    C.coord (combinedLeg I w)
  simp only [minimalCore, BinaryImpl.complementCell, eventLeg, complementLeg,
    LinearMap.comp_apply, combinedLeg_apply, map_add]
  dsimp [C] at *
  have h0 : (minimalCoordinates I).embed
      ((minimalCoordinates I).coord (I.encoding (coordL n 2 0 w))) =
      I.encoding (coordL n 2 0 w) :=
    (minimalCoordinates I).embed_apply_coord_of_mem
      (encoding_mem_minimalSubspace I (coordL n 2 0 w))
  have h1 : (minimalCoordinates I).embed
      ((minimalCoordinates I).coord (I.encoding (coordL n 2 1 w))) =
      I.encoding (coordL n 2 1 w) :=
    (minimalCoordinates I).embed_apply_coord_of_mem
      (encoding_mem_minimalSubspace I (coordL n 2 1 w))
  rw [h0, h1, map_sub]

theorem minimalCore_isMinimal (I : BinaryImpl n E ι) :
    IsMinimal (minimalCore I) := by
  unfold IsMinimal
  rw [← range_combinedLeg (minimalCore I)]
  apply LinearMap.range_eq_top.mpr
  intro y
  have hy : (minimalCoordinates I).embed y ∈ minimalSubspace I := by
    have hx : (minimalCoordinates I).embed y ∈
        LinearMap.range (minimalCoordinates I).embed := ⟨y, rfl⟩
    rw [(minimalCoordinates I).range_embed] at hx
    exact hx
  have hyRange : (minimalCoordinates I).embed y ∈ LinearMap.range (combinedLeg I) := by
    exact (range_combinedLeg I).symm ▸ hy
  obtain ⟨w, hw⟩ := hyRange
  refine ⟨w, ?_⟩
  rw [combinedLeg_minimalCore]
  change (minimalCoordinates I).coord (combinedLeg I w) = y
  rw [hw]
  exact (minimalCoordinates I).coord_apply_embed y


theorem minimalCore_strictIso_of_strictIso
    {I : BinaryImpl n E ι} {J : BinaryImpl n E κ}
    (h : BinaryImpl.StrictIso I J) :
    BinaryImpl.StrictIso (minimalCore I) (minimalCore J) :=
  minimal_strictIso (minimalCore_isMinimal I) (minimalCore_isMinimal J)

theorem minimalCore_unique_up_to_strictIso
    (I : BinaryImpl n E ι) (J : BinaryImpl n E κ) :
    BinaryImpl.StrictIso (minimalCore I) (minimalCore J) :=
  minimal_strictIso (minimalCore_isMinimal I) (minimalCore_isMinimal J)

noncomputable def normalForm (I : BinaryImpl n E ι) :=
  twoSidedResidualExtension (minimalCore I)
    (excessEventDim I) (excessComplementDim I)

theorem normalForm_excessEventDim (I : BinaryImpl n E ι) :
    excessEventDim (normalForm I) = excessEventDim I := by
  unfold normalForm
  exact excessEventDim_twoSidedResidualExtension (minimalCore I)
    (excessEventDim I) (excessComplementDim I) (minimalCore_isMinimal I)

theorem normalForm_excessComplementDim (I : BinaryImpl n E ι) :
    excessComplementDim (normalForm I) = excessComplementDim I := by
  unfold normalForm
  exact excessComplementDim_twoSidedResidualExtension (minimalCore I)
    (excessEventDim I) (excessComplementDim I) (minimalCore_isMinimal I)

theorem strictIso_normalForm (I : BinaryImpl n E ι) :
    BinaryImpl.StrictIso I (normalForm I) := by
  apply strictIso_of_residualDims_eq
  · rw [normalForm_excessEventDim]
  · rw [normalForm_excessComplementDim]

theorem minimalImpl_nonempty (hE : Gleason.IsEffect E) :
    ∃ I : BinaryImpl n E
      (Fin ((minimalCoordinates (canonicalBinaryImpl E hE)).dim)), IsMinimal I :=
  ⟨minimalCore (canonicalBinaryImpl E hE),
    minimalCore_isMinimal (canonicalBinaryImpl E hE)⟩

end

end QuantumFoundations.Naimark.BinaryImpl

