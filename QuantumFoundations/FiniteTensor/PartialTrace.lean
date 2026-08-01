import QuantumFoundations.FiniteTensor.Operator
namespace QuantumFoundations.FiniteTensor
open QuantumFoundations
open Gleason
open scoped InnerProductSpace
noncomputable section
def partialTraceAncilla {n a : ℕ} (A : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a) : H n →ₗ[ℂ] H n :=
  ∑ j : Fin a, ancillaBlockCoord (n := n) j ∘ₗ A ∘ₗ ancillaBlockSingle (n := n) j
theorem partialTraceAncilla_zero {n a : ℕ} : partialTraceAncilla (0 : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a) = 0 := by
  ext x
  simp [partialTraceAncilla]
theorem partialTraceAncilla_add {n a : ℕ} (A B : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a) :
    partialTraceAncilla (A + B) = partialTraceAncilla A + partialTraceAncilla B := by
  simp only [partialTraceAncilla, LinearMap.add_comp, LinearMap.comp_add, Finset.sum_add_distrib]
theorem partialTraceAncilla_smul {n a : ℕ} (c : ℂ) (A : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a) :
    partialTraceAncilla (c • A) = c • partialTraceAncilla A := by
  simp only [partialTraceAncilla, LinearMap.smul_comp, LinearMap.comp_smul, Finset.smul_sum]
theorem partialTraceAncilla_id {n a : ℕ} :
    partialTraceAncilla (LinearMap.id : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a) =
      (a : ℂ) • (LinearMap.id : H n →ₗ[ℂ] H n) := by
  ext x
  simp [partialTraceAncilla, LinearMap.sum_apply, ancillaBlockCoord_comp_single]
end
end QuantumFoundations.FiniteTensor
