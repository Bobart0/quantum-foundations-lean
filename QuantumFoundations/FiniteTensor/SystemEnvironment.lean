import QuantumFoundations.FiniteTensor.SuppliedFactorization

/-!
# System-first coordinates as an adapter

The implementation convention remains environment-first.  This file provides
the system-first coordinate space and factorization only as a transparent
adapter for downstream developments.
-/
namespace QuantumFoundations.FiniteTensor

open QuantumFoundations
open Gleason
open scoped InnerProductSpace

noncomputable section

/-- System-first coordinate space, provided only as a convention adapter. -/
abbrev SystemEnvironmentSpace (system environment : ℕ) :=
  EuclideanSpace ℂ (Fin system × Fin environment)

def systemEnvironmentIndexSwap (system environment : ℕ) :
    (Fin system × Fin environment) ≃ (Fin environment × Fin system) :=
  Equiv.prodComm _ _

noncomputable def systemEnvironmentSwapUnitary (system environment : ℕ) :
    SystemEnvironmentSpace system environment ≃ₗᵢ[ℂ] BipartiteSpace system environment :=
  reindexUnitary (systemEnvironmentIndexSwap system environment)

@[simp] theorem systemEnvironmentSwapUnitary_apply
    (system environment : ℕ) (x : SystemEnvironmentSpace system environment)
    (j : Fin environment) (i : Fin system) :
    systemEnvironmentSwapUnitary system environment x (j, i) = x (i, j) := by
  rfl

@[simp] theorem systemEnvironmentSwapUnitary_symm_apply
    (system environment : ℕ) (x : BipartiteSpace system environment)
    (i : Fin system) (j : Fin environment) :
    (systemEnvironmentSwapUnitary system environment).symm x (i, j) = x (j, i) := by
  rfl

theorem systemEnvironmentSwapUnitary_norm
    (system environment : ℕ) (x : SystemEnvironmentSpace system environment) :
    ‖systemEnvironmentSwapUnitary system environment x‖ = ‖x‖ := by
  exact (systemEnvironmentSwapUnitary system environment).norm_map x

def systemEnvironmentProductStateCoordinates
    {system environment : ℕ} (ψ : H system) (η : H environment) :
    SystemEnvironmentSpace system environment :=
  WithLp.toLp 2 (fun p : Fin system × Fin environment => ψ p.1 * η p.2)

@[simp] theorem systemEnvironmentProductStateCoordinates_apply
    {system environment : ℕ} (ψ : H system) (η : H environment)
    (i : Fin system) (j : Fin environment) :
    systemEnvironmentProductStateCoordinates ψ η (i, j) = ψ i * η j := by
  rfl

theorem systemEnvironmentSwap_productState
    {system environment : ℕ} (ψ : H system) (η : H environment) :
    systemEnvironmentSwapUnitary system environment
        (systemEnvironmentProductStateCoordinates ψ η) =
      productStateCoordinates ψ η := by
  ext p
  rcases p with ⟨j, i⟩
  simp [systemEnvironmentProductStateCoordinates, productStateCoordinates, mul_comm]

theorem inner_systemEnvironmentProductStateCoordinates
    {system environment : ℕ} (ψ ψ' : H system) (η η' : H environment) :
    ⟪systemEnvironmentProductStateCoordinates ψ η,
      systemEnvironmentProductStateCoordinates ψ' η'⟫_ℂ =
      ⟪ψ, ψ'⟫_ℂ * ⟪η, η'⟫_ℂ := by
  rw [← inner_productStateCoordinates ψ ψ' η η']
  rw [← systemEnvironmentSwap_productState ψ η,
    ← systemEnvironmentSwap_productState ψ' η']
  exact (systemEnvironmentSwapUnitary system environment).inner_map_map _ _ |>.symm

theorem norm_systemEnvironmentProductStateCoordinates
    {system environment : ℕ} (ψ : H system) (η : H environment) :
    ‖systemEnvironmentProductStateCoordinates ψ η‖ = ‖ψ‖ * ‖η‖ := by
  rw [← norm_productStateCoordinates ψ η]
  rw [← systemEnvironmentSwap_productState ψ η]
  exact (systemEnvironmentSwapUnitary system environment).norm_map _ |>.symm

structure SystemEnvironmentFactorization (ambient system environment : ℕ) where
  toSystemEnvironment :
    H ambient ≃ₗᵢ[ℂ] SystemEnvironmentSpace system environment

def SuppliedBipartiteFactorization.toSystemEnvironment
    {ambient system environment : ℕ}
    (F : SuppliedBipartiteFactorization ambient system environment) :
    SystemEnvironmentFactorization ambient system environment :=
  ⟨F.toBipartite.trans (systemEnvironmentSwapUnitary system environment).symm⟩

namespace SystemEnvironmentFactorization

variable {ambient system environment : ℕ}
variable (F : SystemEnvironmentFactorization ambient system environment)

def toSuppliedBipartite :
    SuppliedBipartiteFactorization ambient system environment :=
  ⟨F.toSystemEnvironment.trans (systemEnvironmentSwapUnitary system environment)⟩

theorem toSystemEnvironment_toSupplied :
    F.toSuppliedBipartite.toSystemEnvironment = F := by
  cases F with
  | mk u =>
    apply congrArg SystemEnvironmentFactorization.mk
    ext x
    simp [toSuppliedBipartite, SuppliedBipartiteFactorization.toSystemEnvironment]

def productState (ψ : H system) (η : H environment) : H ambient :=
  F.toSuppliedBipartite.productState ψ η

def toCoordinatesOperator (A : H ambient →ₗ[ℂ] H ambient) :
    BipartiteSpace system environment →ₗ[ℂ] BipartiteSpace system environment :=
  F.toSuppliedBipartite.toCoordinatesOperator A

def fromCoordinatesOperator
    (A : BipartiteSpace system environment →ₗ[ℂ] BipartiteSpace system environment) :
    H ambient →ₗ[ℂ] H ambient :=
  F.toSuppliedBipartite.fromCoordinatesOperator A

def reducedSystemOperator (A : H ambient →ₗ[ℂ] H ambient) :
    H system →ₗ[ℂ] H system :=
  F.toSuppliedBipartite.reducedSystemOperator A

abbrev reducedOperator
    (F : SystemEnvironmentFactorization ambient system environment)
    (A : H ambient →ₗ[ℂ] H ambient) := F.reducedSystemOperator A

theorem toCoordinatesOperator_compatibility (A : H ambient →ₗ[ℂ] H ambient) :
    F.toCoordinatesOperator A = F.toSuppliedBipartite.toCoordinatesOperator A := rfl

theorem fromCoordinatesOperator_compatibility
    (A : BipartiteSpace system environment →ₗ[ℂ] BipartiteSpace system environment) :
    F.fromCoordinatesOperator A = F.toSuppliedBipartite.fromCoordinatesOperator A := rfl

theorem reducedSystemOperator_compatibility (A : H ambient →ₗ[ℂ] H ambient) :
    F.reducedSystemOperator A = F.toSuppliedBipartite.reducedSystemOperator A := rfl

theorem toSystemEnvironment_productState (ψ : H system) (η : H environment) :
    F.toSystemEnvironment (F.productState ψ η) =
      systemEnvironmentProductStateCoordinates ψ η := by
  have hswap :
      (systemEnvironmentSwapUnitary system environment).symm
          (productStateCoordinates ψ η) =
        systemEnvironmentProductStateCoordinates ψ η := by
    rw [← systemEnvironmentSwap_productState ψ η]
    simp
  simp [productState, toSuppliedBipartite,
    SuppliedBipartiteFactorization.productState, hswap]

end SystemEnvironmentFactorization

theorem SuppliedBipartiteFactorization.toSupplied_toSystemEnvironment
    {ambient system environment : ℕ}
    (F : SuppliedBipartiteFactorization ambient system environment) :
    F.toSystemEnvironment.toSuppliedBipartite = F := by
  cases F with
  | mk u =>
    apply congrArg SuppliedBipartiteFactorization.mk
    ext x
    simp [SuppliedBipartiteFactorization.toSystemEnvironment,
      SystemEnvironmentFactorization.toSuppliedBipartite]

def canonicalSystemEnvironmentFactorization (system environment : ℕ) :
    SystemEnvironmentFactorization (system * environment) system environment :=
  (canonicalTensorDecomposition system environment).toSuppliedFactorization.toSystemEnvironment

theorem canonicalSystemEnvironmentFactorization_compatibility
    (system environment : ℕ) :
    (canonicalSystemEnvironmentFactorization system environment).toSuppliedBipartite =
      (canonicalTensorDecomposition system environment).toSuppliedFactorization := by
  exact SuppliedBipartiteFactorization.toSupplied_toSystemEnvironment _

abbrev EnvironmentPartialTrace {n a : ℕ}
    (A : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a) : H n →ₗ[ℂ] H n :=
  partialTraceAncilla A

abbrev partialTraceEnvironment {n a : ℕ}
    (A : BipartiteSpace n a →ₗ[ℂ] BipartiteSpace n a) : H n →ₗ[ℂ] H n :=
  partialTraceAncilla A

end
end QuantumFoundations.FiniteTensor
