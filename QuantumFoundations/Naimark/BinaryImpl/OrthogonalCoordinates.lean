import QuantumFoundations.Naimark.BinaryImpl.Residual
namespace QuantumFoundations.Naimark.BinaryImpl
open QuantumFoundations Gleason
open scoped InnerProductSpace
noncomputable section

structure SubspaceCoordinates {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Submodule ℂ (EuclideanSpace ℂ ι)) where
  dim : ℕ
  finrank_eq : Module.finrank ℂ S = dim
  embed : H dim →ₗ[ℂ] EuclideanSpace ℂ ι
  coord : EuclideanSpace ℂ ι →ₗ[ℂ] H dim
  adjoint_embed : LinearMap.adjoint embed = coord
  coord_comp_embed : coord ∘ₗ embed = LinearMap.id
  range_embed : LinearMap.range embed = S
  embed_comp_coord : embed ∘ₗ coord = S.starProjection

namespace SubspaceCoordinates
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {S : Submodule ℂ (EuclideanSpace ℂ ι)}
theorem embed_surjective_onto (C : SubspaceCoordinates S) : ∀ y : S, ∃ x, C.embed x = y := by
  intro y
  have hy : (y : EuclideanSpace ℂ ι) ∈ LinearMap.range C.embed := by rw [C.range_embed]; exact y.property
  exact hy
theorem coord_apply_embed (C : SubspaceCoordinates S) (x : H C.dim) : C.coord (C.embed x) = x := by
  have h := LinearMap.congr_fun C.coord_comp_embed x
  simpa using h
theorem embed_apply_coord_of_mem (C : SubspaceCoordinates S) {y : EuclideanSpace ℂ ι} (hy : y ∈ S) :
    C.embed (C.coord y) = y := by
  have h := LinearMap.congr_fun C.embed_comp_coord y
  change C.embed (C.coord y) = S.starProjection y at h
  rw [h, Submodule.starProjection_eq_self_iff.mpr hy]
theorem coord_surjective (C : SubspaceCoordinates S) : Function.Surjective C.coord := by
  intro x
  exact ⟨C.embed x, C.coord_apply_embed x⟩
theorem embed_isometry (C : SubspaceCoordinates S) (x y : H C.dim) :
    ⟪C.embed x, C.embed y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [← LinearMap.adjoint_inner_right C.embed x (C.embed y), C.adjoint_embed]
  have h := LinearMap.congr_fun C.coord_comp_embed y
  simpa using congrArg (fun z => ⟪x, z⟫_ℂ) h
theorem coord_inner (C : SubspaceCoordinates S) {x y : EuclideanSpace ℂ ι}
    (hx : x ∈ S) (hy : y ∈ S) : ⟪C.coord x, C.coord y⟫_ℂ = ⟪x, y⟫_ℂ := by
  obtain ⟨x', rfl⟩ := C.embed_surjective_onto ⟨x, hx⟩
  obtain ⟨y', rfl⟩ := C.embed_surjective_onto ⟨y, hy⟩
  rw [C.coord_apply_embed, C.coord_apply_embed, C.embed_isometry]
end SubspaceCoordinates

variable {ι : Type} [Fintype ι] [DecidableEq ι]
private def canonicalEmbed (S : Submodule ℂ (EuclideanSpace ℂ ι)) :
    H (Module.finrank ℂ S) →ₗ[ℂ] EuclideanSpace ℂ ι :=
  S.subtype.comp (stdOrthonormalBasis ℂ S).repr.symm.toLinearMap
private theorem canonicalEmbed_inner (S : Submodule ℂ (EuclideanSpace ℂ ι))
    (x y : H (Module.finrank ℂ S)) : ⟪canonicalEmbed S x, canonicalEmbed S y⟫_ℂ = ⟪x, y⟫_ℂ := by
  change ⟪((stdOrthonormalBasis ℂ S).repr.symm x : S), ((stdOrthonormalBasis ℂ S).repr.symm y : S)⟫_ℂ = ⟪x, y⟫_ℂ
  exact (stdOrthonormalBasis ℂ S).repr.symm.inner_map_map x y
private theorem canonical_coord_comp_embed (S : Submodule ℂ (EuclideanSpace ℂ ι)) :
    LinearMap.adjoint (canonicalEmbed S) ∘ₗ canonicalEmbed S = LinearMap.id := by
  apply LinearMap.ext; intro x; apply ext_inner_left ℂ; intro y
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  exact canonicalEmbed_inner S y x
private theorem canonical_range_embed (S : Submodule ℂ (EuclideanSpace ℂ ι)) :
    LinearMap.range (canonicalEmbed S) = S := by
  have hs : Function.Surjective ((stdOrthonormalBasis ℂ S).repr.symm.toLinearMap) :=
    (stdOrthonormalBasis ℂ S).repr.symm.surjective
  rw [canonicalEmbed, LinearMap.range_comp, LinearMap.range_eq_top.mpr hs, Submodule.map_top]
  exact Submodule.range_subtype S
private theorem canonical_embed_comp_coord (S : Submodule ℂ (EuclideanSpace ℂ ι)) :
    canonicalEmbed S ∘ₗ LinearMap.adjoint (canonicalEmbed S) = S.starProjection := by
  apply LinearMap.ext; intro x; symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := S)
  · change canonicalEmbed S (LinearMap.adjoint (canonicalEmbed S) x) ∈ S
    have hmem : canonicalEmbed S (LinearMap.adjoint (canonicalEmbed S) x) ∈ LinearMap.range (canonicalEmbed S) := ⟨_, rfl⟩
    exact (congrArg (fun T : Submodule ℂ (EuclideanSpace ℂ ι) =>
      canonicalEmbed S (LinearMap.adjoint (canonicalEmbed S) x) ∈ T) (canonical_range_embed S)).mp hmem
  · intro y hy
    have hy' : y ∈ LinearMap.range (canonicalEmbed S) := by
      rw [canonical_range_embed S]
      exact hy
    obtain ⟨z, hz⟩ := hy'
    rw [← hz]
    rw [sub_eq_add_neg, inner_add_left, inner_neg_left]
    change ⟪x, canonicalEmbed S z⟫_ℂ -
      ⟪canonicalEmbed S (LinearMap.adjoint (canonicalEmbed S) x), canonicalEmbed S z⟫_ℂ = 0
    rw [← LinearMap.adjoint_inner_left (canonicalEmbed S) z x,
      ← LinearMap.adjoint_inner_right (canonicalEmbed S)
        (LinearMap.adjoint (canonicalEmbed S) x) (canonicalEmbed S z)]
    have h := LinearMap.congr_fun (canonical_coord_comp_embed S) z
    have hz' : LinearMap.adjoint (canonicalEmbed S) (canonicalEmbed S z) = z := by
      simpa [LinearMap.comp_apply] using h
    rw [hz', sub_self]
noncomputable def ofFinrank (S : Submodule ℂ (EuclideanSpace ℂ ι)) : SubspaceCoordinates S where
  dim := Module.finrank ℂ S
  finrank_eq := rfl
  embed := canonicalEmbed S
  coord := LinearMap.adjoint (canonicalEmbed S)
  adjoint_embed := rfl
  coord_comp_embed := canonical_coord_comp_embed S
  range_embed := canonical_range_embed S
  embed_comp_coord := canonical_embed_comp_coord S
noncomputable def subspaceCoordinatesOfFinrankEq
    (S : Submodule ℂ (EuclideanSpace ℂ ι)) (r : ℕ)
    (hr : Module.finrank ℂ S = r) : SubspaceCoordinates S := by
  subst r
  exact ofFinrank S
end
end QuantumFoundations.Naimark.BinaryImpl
