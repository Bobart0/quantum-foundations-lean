import QuantumFoundations.FiniteTensor.Transport
import QuantumFoundations.FiniteTensor.PureProjectorTrace
import QuantumFoundations.Selectors.Defs
namespace QuantumFoundations.FiniteTensor
open QuantumFoundations
open QuantumFoundations.Selector
open Gleason
open scoped InnerProductSpace
noncomputable section
theorem partialTraceAncilla_sub {n a : ℕ} (A B : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a) : partialTraceAncilla (A - B) = partialTraceAncilla A - partialTraceAncilla B := by
  rw [sub_eq_add_neg, partialTraceAncilla_add]
  rw [show (-B) = (-1 : ℂ) • B by simp, partialTraceAncilla_smul]
  simpa [sub_eq_add_neg]
theorem partialTrace_isotropicDensity_product {n a : ℕ} (hn : 2 ≤ n) (ha : 2 ≤ a) {ψ : H n} {η : H a} (hψ : ‖ψ‖ = 1) (hη : ‖η‖ = 1) (t : ℝ) :
    partialTraceAncilla (isotropicDensity (n * a) t (productStateCoordinates ψ η)) =
      (t : ℂ) • Gleason.projL (ℂ ∙ ψ) + ((((1 - t) / ((n * a : ℝ) - 1) : ℝ) : ℂ) • ((a : ℂ) • (LinearMap.id : H n →ₗ[ℂ] H n) - Gleason.projL (ℂ ∙ ψ))) := by
  rw [isotropicDensity_eq_projL_add_id_sub]
  rw [partialTraceAncilla_add, partialTraceAncilla_smul, partialTraceAncilla_smul, partialTraceAncilla_sub, partialTraceAncilla_productProjection hψ hη, partialTraceAncilla_id]
  simp only [Nat.cast_mul]
  rfl
theorem partialTrace_tDensity_product {n a : ℕ} (hn : 2 ≤ n) (ha : 2 ≤ a) (D : TensorDecomposition n a) {ψ : H n} {η : H a} (hψ : ‖ψ‖ = 1) (hη : ‖η‖ = 1) (t : ℝ) :
    partialTraceAncilla (D.toCoordinatesOperator (tDensity (n * a) t (D.productState ψ η))) =
      (t : ℂ) • Gleason.projL (ℂ ∙ ψ) + ((((1 - t) / ((n * a : ℝ) - 1) : ℝ) : ℂ) • ((a : ℂ) • (LinearMap.id : H n →ₗ[ℂ] H n) - Gleason.projL (ℂ ∙ ψ))) := by
  rw [D.toCoordinates_tDensity_productState]
  exact partialTrace_isotropicDensity_product hn ha hψ hη t
end
end QuantumFoundations.FiniteTensor
