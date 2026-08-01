import QuantumFoundations.FiniteTensor.PartialTrace
import QuantumFoundations.Selectors.Defs
namespace QuantumFoundations.FiniteTensor
open QuantumFoundations
open QuantumFoundations.Selector
open Gleason
open scoped InnerProductSpace
noncomputable section
theorem conjugate_projL {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V] [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W]
    (U : V ≃ₗᵢ[𝕜] W) (S : Submodule 𝕜 V) : U.toLinearMap ∘ₗ S.starProjection.toLinearMap ∘ₗ U.symm.toLinearMap = (S.map U.toLinearMap).starProjection.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact (Submodule.starProjection_map_apply U S x).symm
theorem map_span_singleton_equiv {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    (U : V ≃ₗᵢ[𝕜] W) (v : V) : (𝕜 ∙ v).map U.toLinearMap = 𝕜 ∙ U v := by rw [Submodule.map_span, Set.image_singleton]; rfl
theorem map_orthogonal_equiv {𝕜 V W : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    (U : V ≃ₗᵢ[𝕜] W) (S : Submodule 𝕜 V) : Sᗮ.map U.toLinearMap = (S.map U.toLinearMap)ᗮ := Submodule.map_orthogonal_equiv S U
def isotropicDensity {𝕜 V : Type*} [RCLike 𝕜] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    (d : ℕ) (t : ℝ) (v : V) : V →ₗ[𝕜] V := (t : 𝕜) • (𝕜 ∙ v).starProjection.toLinearMap + (((1 - t) / ((d : ℝ) - 1) : ℝ) : 𝕜) • (𝕜 ∙ v)ᗮ.starProjection.toLinearMap
theorem isotropicDensity_eq_tDensity {d : ℕ} (t : ℝ) (v : H d) : isotropicDensity d t v = tDensity d t v := rfl
end
end QuantumFoundations.FiniteTensor
