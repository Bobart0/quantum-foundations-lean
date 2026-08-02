import QuantumFoundations.FiniteTensorAPI

namespace QuantumFoundations.FiniteTensorAPIContract

open QuantumFoundations.FiniteTensorAPI
open Gleason
open scoped InnerProductSpace

noncomputable section

def canonical : SystemEnvironmentFactorization 4 2 2 :=
  canonicalSystemEnvironmentFactorization 2 2

def supplied : SuppliedBipartiteFactorization 4 2 2 :=
  QuantumFoundations.FiniteTensor.SystemEnvironmentFactorization.toSuppliedBipartite canonical

def ψ : H 2 := QuantumFoundations.FiniteTensor.stdKet 0
def η : H 2 := QuantumFoundations.FiniteTensor.stdKet 0

example : QuantumFoundations.FiniteTensor.SystemEnvironmentFactorization.toSuppliedBipartite
    canonical = supplied := by rfl

example : QuantumFoundations.FiniteTensor.SuppliedBipartiteFactorization.productState supplied ψ η =
    QuantumFoundations.FiniteTensor.SystemEnvironmentFactorization.productState canonical ψ η := by
  rfl

example : QuantumFoundations.FiniteTensor.SuppliedBipartiteFactorization.reducedSystemOperator supplied
    (projL (ℂ ∙ QuantumFoundations.FiniteTensor.SuppliedBipartiteFactorization.productState supplied ψ η)) =
      projL (ℂ ∙ ψ) := by
  exact QuantumFoundations.FiniteTensor.SuppliedBipartiteFactorization.reducedSystemOperator_productProjection
    supplied (QuantumFoundations.FiniteTensor.stdKet_norm 0)
      (QuantumFoundations.FiniteTensor.stdKet_norm 0)

example : QuantumFoundations.FiniteTensor.SuppliedBipartiteFactorization.toCoordinatesOperator supplied
    (projL (ℂ ∙ QuantumFoundations.FiniteTensor.SuppliedBipartiteFactorization.productState supplied ψ η)) =
      (ℂ ∙ QuantumFoundations.FiniteTensor.productStateCoordinates ψ η).starProjection.toLinearMap := by
  exact QuantumFoundations.FiniteTensor.SuppliedBipartiteFactorization.toCoordinatesOperator_projL_productState supplied

#check SystemEnvironmentFactorization
#check SuppliedBipartiteFactorization
#check QuantumFoundations.FiniteTensor.SystemEnvironmentFactorization.toSuppliedBipartite
#check QuantumFoundations.FiniteTensor.SuppliedBipartiteFactorization.toSystemEnvironment
#check QuantumFoundations.FiniteTensor.SuppliedBipartiteFactorization.toCoordinates
#check QuantumFoundations.FiniteTensor.SuppliedBipartiteFactorization.fromCoordinates
#check QuantumFoundations.FiniteTensor.SuppliedBipartiteFactorization.toCoordinatesOperator
#check QuantumFoundations.FiniteTensor.SuppliedBipartiteFactorization.fromCoordinatesOperator
#check QuantumFoundations.FiniteTensor.SystemEnvironmentFactorization.productState
#check QuantumFoundations.FiniteTensor.SystemEnvironmentFactorization.toCoordinatesOperator
#check QuantumFoundations.FiniteTensor.SystemEnvironmentFactorization.fromCoordinatesOperator
#check QuantumFoundations.FiniteTensor.SystemEnvironmentFactorization.reducedSystemOperator
#check EnvironmentPartialTrace
#check partialTraceEnvironment
#check productStateCoordinates
#check tensorOperator
#check partialTraceAncilla

#print axioms QuantumFoundations.FiniteTensor.SuppliedBipartiteFactorization.reducedSystemOperator_productProjection
#print axioms QuantumFoundations.FiniteTensor.SuppliedBipartiteFactorization.reducedSystemOperator_tDensity_product

end
end QuantumFoundations.FiniteTensorAPIContract

#check QuantumFoundations.FiniteTensorAPI.tDensity
#check QuantumFoundations.FiniteTensorAPI.tensorOperator_smul_id_smul_id
