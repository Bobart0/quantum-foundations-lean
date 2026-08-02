import QuantumFoundations.FiniteTensor.Main
import QuantumFoundations.FiniteTensor.SuppliedFactorization
import QuantumFoundations.FiniteTensor.SystemEnvironment

/-! Public additive facade for finite tensor coordinates and reductions. -/
namespace QuantumFoundations.FiniteTensorAPI

abbrev TensorDecomposition := QuantumFoundations.FiniteTensor.TensorDecomposition
abbrev SuppliedBipartiteFactorization :=
  QuantumFoundations.FiniteTensor.SuppliedBipartiteFactorization
abbrev SystemEnvironmentFactorization :=
  QuantumFoundations.FiniteTensor.SystemEnvironmentFactorization

export Gleason (H projL)

export QuantumFoundations.FiniteTensor
  (BipartiteIndex BipartiteSpace canonicalTensorDecomposition
   tensorDecomposition_nonempty productStateCoordinates inner_productStateCoordinates
   norm_productStateCoordinates stdKet stdKet_apply stdKet_norm stdKet_orthonormal
   operatorEntry tensorOperator tensorOperator_apply_productState
   tensorOperator_projL_singletons partialTraceAncilla partialTraceAncilla_zero
   partialTraceAncilla_add partialTraceAncilla_sub partialTraceAncilla_smul
   partialTraceAncilla_id partialTraceAncilla_tensorOperator
   partialTraceAncilla_productProjection projL_congr projL_compl_eq_id_sub
   SystemEnvironmentSpace systemEnvironmentIndexSwap systemEnvironmentSwapUnitary
   systemEnvironmentSwapUnitary_apply systemEnvironmentSwapUnitary_symm_apply
   systemEnvironmentSwapUnitary_norm systemEnvironmentProductStateCoordinates
   systemEnvironmentProductStateCoordinates_apply systemEnvironmentSwap_productState
   inner_systemEnvironmentProductStateCoordinates
   norm_systemEnvironmentProductStateCoordinates canonicalSystemEnvironmentFactorization
   canonicalSystemEnvironmentFactorization_compatibility EnvironmentPartialTrace
   partialTraceEnvironment)

namespace TensorDecomposition
export QuantumFoundations.FiniteTensor.TensorDecomposition
  (productState toCoordinatesOperator fromCoordinatesOperator
   toCoordinatesOperator_id toCoordinatesOperator_zero toCoordinatesOperator_add
   toCoordinatesOperator_sub toCoordinatesOperator_smul toCoordinatesOperator_comp
   toCoordinatesOperator_adjoint from_to_coordinates_operator to_from_coordinates_operator
   toSuppliedFactorization toTensorDecomposition_toSupplied productState_eq_supplied
   toCoordinatesOperator_eq_supplied reducedOperator_eq_supplied)
end TensorDecomposition

namespace SuppliedBipartiteFactorization
export QuantumFoundations.FiniteTensor.SuppliedBipartiteFactorization
  (toCoordinates fromCoordinates from_toCoordinates to_fromCoordinates
   norm_toCoordinates norm_fromCoordinates toCoordinates_injective
   fromCoordinates_injective toCoordinatesOperator fromCoordinatesOperator
   toCoordinatesOperator_id toCoordinatesOperator_zero toCoordinatesOperator_add
   toCoordinatesOperator_sub toCoordinatesOperator_smul toCoordinatesOperator_comp
   toCoordinatesOperator_adjoint from_toCoordinatesOperator to_fromCoordinatesOperator
   productState toCoordinates_productState norm_productState productState_norm_one
   reducedSystemOperator reducedOperator reducedSystemOperator_zero
   reducedSystemOperator_add reducedSystemOperator_sub reducedSystemOperator_smul
   reducedSystemOperator_id toCoordinatesOperator_projL_productState
   reducedSystemOperator_productProjection toCoordinates_tDensity_productState
   reducedSystemOperator_tDensity_product toTensorDecomposition
   toSupplied_toTensorDecomposition toSystemEnvironment toSupplied_toSystemEnvironment)
end SuppliedBipartiteFactorization

namespace SystemEnvironmentFactorization
export QuantumFoundations.FiniteTensor.SystemEnvironmentFactorization
  (toSystemEnvironment toSuppliedBipartite productState toCoordinatesOperator
   fromCoordinatesOperator reducedSystemOperator reducedOperator
   toCoordinatesOperator_compatibility fromCoordinatesOperator_compatibility
   reducedSystemOperator_compatibility toSystemEnvironment_productState
   toSystemEnvironment_toSupplied)
end SystemEnvironmentFactorization

end QuantumFoundations.FiniteTensorAPI

namespace QuantumFoundations.FiniteTensorAPI

open QuantumFoundations
open QuantumFoundations.FiniteTensor
open Gleason
open scoped InnerProductSpace

noncomputable section

export QuantumFoundations.Selector (tDensity)

/-- Scalar tensor products transport to scalar multiplication of the identity. -/
theorem tensorOperator_smul_id_smul_id {n a : ℕ} (c d : ℂ) :
    tensorOperator (c • (LinearMap.id : H n →ₗ[ℂ] H n))
        (d • (LinearMap.id : H a →ₗ[ℂ] H a)) =
      (c * d) • (LinearMap.id : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a) := by
  apply linearMap_ext_productStdKet
  intro j i
  change tensorOperator (c • (LinearMap.id : H n →ₗ[ℂ] H n))
      (d • (LinearMap.id : H a →ₗ[ℂ] H a))
      (productStateCoordinates (stdKet i) (stdKet j)) = _
  rw [tensorOperator_apply_productState]
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [productStateCoordinates_smul_left,
    productStateCoordinates_smul_right, smul_smul]
  change (c * d) • productStateCoordinates (stdKet i) (stdKet j) =
    (c * d) • productStateCoordinates (stdKet i) (stdKet j)
  rfl

end
end QuantumFoundations.FiniteTensorAPI
