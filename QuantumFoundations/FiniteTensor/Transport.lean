import QuantumFoundations.FiniteTensor.PartialTrace
import QuantumFoundations.FiniteTensor.PureProjectorTrace
import QuantumFoundations.Selectors.Defs
namespace QuantumFoundations.FiniteTensor
open QuantumFoundations
open QuantumFoundations.Selector
open Gleason
open scoped InnerProductSpace
noncomputable section

theorem conjugate_projL {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V] [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
    (U : V ≃ₗᵢ[𝕜] W) (S : Submodule 𝕜 V) :
    U.toLinearMap ∘ₗ S.starProjection.toLinearMap ∘ₗ U.symm.toLinearMap =
      (S.map U.toLinearMap).starProjection.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact (Submodule.starProjection_map_apply U S x).symm

theorem map_span_singleton_equiv {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    (U : V ≃ₗᵢ[𝕜] W) (v : V) :
    (𝕜 ∙ v).map U.toLinearMap = 𝕜 ∙ U v := by
  rw [Submodule.map_span, Set.image_singleton]
  rfl

theorem map_orthogonal_equiv {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    (U : V ≃ₗᵢ[𝕜] W) (S : Submodule 𝕜 V) :
    Sᗮ.map U.toLinearMap = (S.map U.toLinearMap)ᗮ :=
  Submodule.map_orthogonal_equiv S U

theorem starProjection_toLinearMap_congr {𝕜 V : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    {S T : Submodule 𝕜 V} [S.HasOrthogonalProjection] [T.HasOrthogonalProjection]
    (h : S = T) :
    S.starProjection.toLinearMap = T.starProjection.toLinearMap := by
  cases h
  rfl

theorem projL_congr {d : ℕ} {S T : Submodule ℂ (H d)} (h : S = T) :
    Gleason.projL S = Gleason.projL T := by
  cases h
  rfl

theorem projL_compl_eq_id_sub {d : ℕ} (S : Submodule ℂ (H d)) :
    Gleason.projL Sᗮ = LinearMap.id - Gleason.projL S := by
  have h := QuantumFoundations.Selector.projL_add_projL_compl S
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun A : H d →ₗ[ℂ] H d => A x) h
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply] at hx ⊢
  apply eq_sub_of_add_eq
  simpa [add_comm] using hx

theorem starProjection_compl_toLinearMap_eq_id_sub {𝕜 V : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    {S : Submodule 𝕜 V} [S.HasOrthogonalProjection] :
    Sᗮ.starProjection.toLinearMap =
      LinearMap.id - S.starProjection.toLinearMap := by
  apply LinearMap.ext
  intro x
  have hx := Submodule.starProjection_add_starProjection_orthogonal (K := S) x
  have hx' : Sᗮ.starProjection x + S.starProjection x = x := by
    simpa [add_comm] using hx
  have hval := eq_sub_of_add_eq hx'
  change Sᗮ.starProjection x = x - S.starProjection x
  exact hval

theorem conjugate_projL_span {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V] [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
    (U : V ≃ₗᵢ[𝕜] W) (v : V) :
    U.toLinearMap ∘ₗ (𝕜 ∙ v).starProjection.toLinearMap ∘ₗ U.symm.toLinearMap =
      (𝕜 ∙ U v).starProjection.toLinearMap := by
  calc
    U.toLinearMap ∘ₗ (𝕜 ∙ v).starProjection.toLinearMap ∘ₗ U.symm.toLinearMap =
        ((𝕜 ∙ v).map U.toLinearMap).starProjection.toLinearMap :=
      conjugate_projL U (𝕜 ∙ v)
    _ = (𝕜 ∙ U v).starProjection.toLinearMap :=
      starProjection_toLinearMap_congr (map_span_singleton_equiv U v)

def isotropicDensity {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
    [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    (d : ℕ) (t : ℝ) (v : V) : V →ₗ[𝕜] V :=
  (t : 𝕜) • (𝕜 ∙ v).starProjection.toLinearMap +
    (((1 - t) / ((d : ℝ) - 1) : ℝ) : 𝕜) • (𝕜 ∙ v)ᗮ.starProjection.toLinearMap

theorem tDensity_eq_projL_add_id_sub {d : ℕ} (t : ℝ) (v : H d) :
    tDensity d t v =
      (t : ℂ) • Gleason.projL (ℂ ∙ v) +
        ((((1 - t) / ((d : ℝ) - 1) : ℝ) : ℂ) •
          (LinearMap.id - Gleason.projL (ℂ ∙ v))) := by
  unfold tDensity
  rw [projL_compl_eq_id_sub]

theorem isotropicDensity_eq_projL_add_id_sub {𝕜 V : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    (d : ℕ) (t : ℝ) (v : V) :
    isotropicDensity d t v =
      (t : 𝕜) • (𝕜 ∙ v).starProjection.toLinearMap +
        ((((1 - t) / ((d : ℝ) - 1) : ℝ) : 𝕜) •
          (LinearMap.id - (𝕜 ∙ v).starProjection.toLinearMap)) := by
  unfold isotropicDensity
  rw [starProjection_compl_toLinearMap_eq_id_sub]

theorem TensorDecomposition.toCoordinatesOperator_sub {n a : ℕ}
    (D : TensorDecomposition n a) (A B : H (n * a) →ₗ[ℂ] H (n * a)) :
    D.toCoordinatesOperator (A - B) =
      D.toCoordinatesOperator A - D.toCoordinatesOperator B := by
  ext x
  simp [TensorDecomposition.toCoordinatesOperator, LinearMap.sub_apply]

theorem TensorDecomposition.toCoordinatesOperator_projL_span {n a : ℕ}
    (D : TensorDecomposition n a) (v : H (n * a)) :
    D.toCoordinatesOperator (Gleason.projL (ℂ ∙ v)) =
      (ℂ ∙ D.toBipartite v).starProjection.toLinearMap := by
  change D.toBipartite.toLinearMap ∘ₗ (ℂ ∙ v).starProjection.toLinearMap ∘ₗ
      D.toBipartite.symm.toLinearMap = _
  exact conjugate_projL_span D.toBipartite v

theorem TensorDecomposition.toCoordinates_tDensity_productState
    {n a : ℕ} (D : TensorDecomposition n a) (t : ℝ) (ψ : H n) (η : H a) :
    D.toCoordinatesOperator
        (tDensity (n * a) t (D.productState ψ η)) =
      isotropicDensity (n * a) t (productStateCoordinates ψ η) := by
  rw [tDensity_eq_projL_add_id_sub]
  rw [TensorDecomposition.toCoordinatesOperator_add,
    TensorDecomposition.toCoordinatesOperator_smul,
    TensorDecomposition.toCoordinatesOperator_smul,
    TensorDecomposition.toCoordinatesOperator_sub,
    TensorDecomposition.toCoordinatesOperator_id,
    TensorDecomposition.toCoordinatesOperator_projL_span]
  rw [D.toBipartite_productState]
  rw [isotropicDensity_eq_projL_add_id_sub]
  rfl

theorem partialTraceAncilla_sub {n a : ℕ}
    (A B : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a) :
    partialTraceAncilla (A - B) = partialTraceAncilla A - partialTraceAncilla B := by
  rw [sub_eq_add_neg, partialTraceAncilla_add]
  rw [show (-B) = (-1 : ℂ) • B by simp, partialTraceAncilla_smul]
  simpa [sub_eq_add_neg]

theorem partialTrace_isotropicDensity_product {n a : ℕ}
    (hn : 2 ≤ n) (ha : 2 ≤ a) {ψ : H n} {η : H a}
    (hψ : ‖ψ‖ = 1) (hη : ‖η‖ = 1) (t : ℝ) :
    partialTraceAncilla
        (isotropicDensity (n * a) t (productStateCoordinates ψ η)) =
      (t : ℂ) • Gleason.projL (ℂ ∙ ψ) +
        ((((1 - t) / ((n * a : ℝ) - 1) : ℝ) : ℂ) •
          ((a : ℂ) • (LinearMap.id : H n →ₗ[ℂ] H n) -
            Gleason.projL (ℂ ∙ ψ))) := by
  rw [isotropicDensity_eq_projL_add_id_sub]
  rw [partialTraceAncilla_add, partialTraceAncilla_smul,
    partialTraceAncilla_smul, partialTraceAncilla_sub,
    partialTraceAncilla_productProjection hψ hη, partialTraceAncilla_id]
  simp only [Nat.cast_mul]
  rfl

theorem partialTrace_tDensity_product {n a : ℕ}
    (hn : 2 ≤ n) (ha : 2 ≤ a) (D : TensorDecomposition n a)
    {ψ : H n} {η : H a} (hψ : ‖ψ‖ = 1) (hη : ‖η‖ = 1) (t : ℝ) :
    partialTraceAncilla
        (D.toCoordinatesOperator
          (tDensity (n * a) t (D.productState ψ η))) =
      (t : ℂ) • Gleason.projL (ℂ ∙ ψ) +
        ((((1 - t) / ((n * a : ℝ) - 1) : ℝ) : ℂ) •
          ((a : ℂ) • (LinearMap.id : H n →ₗ[ℂ] H n) -
            Gleason.projL (ℂ ∙ ψ))) := by
  rw [D.toCoordinates_tDensity_productState]
  exact partialTrace_isotropicDensity_product hn ha hψ hη t

theorem isotropicDensity_eq_tDensity {d : ℕ} (t : ℝ) (v : H d) :
    isotropicDensity d t v = tDensity d t v := rfl

end
end QuantumFoundations.FiniteTensor
