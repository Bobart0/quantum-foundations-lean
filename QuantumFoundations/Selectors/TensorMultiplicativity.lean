import QuantumFoundations.Selectors.BridgeDefs
namespace QuantumFoundations.Selector
open QuantumFoundations
open QuantumFoundations.FiniteTensor
noncomputable section
def isotropicResidual (d : ℕ) (t : ℝ) : ℝ := (1 - t) / ((d : ℝ) - 1)
theorem isotropicResidual_at_one (d : ℕ) : isotropicResidual d 1 = 0 := by
  unfold isotropicResidual
  norm_num
end
end QuantumFoundations.Selector
