import QuantumFoundations.FiniteTensor.PureProjector
import QuantumFoundations.FiniteTensor.PartialTrace
import QuantumFoundations.Selectors.Defs
namespace QuantumFoundations.FiniteTensor
open QuantumFoundations
open QuantumFoundations.Selector
open Gleason
open scoped InnerProductSpace
noncomputable section
theorem partialTraceAncilla_productProjection {n a : ℕ} {ψ : H n} {η : H a}
    (hψ : ‖ψ‖ = 1) (hη : ‖η‖ = 1) :
    partialTraceAncilla ((ℂ ∙ productStateCoordinates ψ η).starProjection.toLinearMap) =
      Gleason.projL (ℂ ∙ ψ) := by
  rw [← tensorOperator_projL_singletons hψ hη]
  rw [partialTraceAncilla_tensorOperator]
  rw [QuantumFoundations.Selector.trace_projL_singleton hη]
  simp
end
end QuantumFoundations.FiniteTensor
