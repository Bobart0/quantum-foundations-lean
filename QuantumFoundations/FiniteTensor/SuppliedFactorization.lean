import QuantumFoundations.FiniteTensor.Main

/-!
# Explicitly supplied finite bipartite factorizations

This file adds a generic transport layer around the existing coordinate
construction.  A `SuppliedBipartiteFactorization` is explicitly supplied by
the caller; no existence, uniqueness, or physical preference is asserted.
-/
namespace QuantumFoundations.FiniteTensor

open QuantumFoundations
open QuantumFoundations.Selector
open Gleason
open scoped InnerProductSpace

noncomputable section

structure SuppliedBipartiteFactorization (ambient system environment : ℕ) where
  /-- An explicitly supplied factorization. No existence, uniqueness, or
  physical preference is asserted. -/
  toBipartite : H ambient ≃ₗᵢ[ℂ] BipartiteSpace system environment

namespace SuppliedBipartiteFactorization

variable {ambient system environment : ℕ}
variable (F : SuppliedBipartiteFactorization ambient system environment)

def toCoordinates (x : H ambient) : BipartiteSpace system environment :=
  F.toBipartite x

def fromCoordinates (z : BipartiteSpace system environment) : H ambient :=
  F.toBipartite.symm z

theorem from_toCoordinates (x : H ambient) : F.fromCoordinates (F.toCoordinates x) = x := by
  simp [toCoordinates, fromCoordinates]

theorem to_fromCoordinates (z : BipartiteSpace system environment) :
    F.toCoordinates (F.fromCoordinates z) = z := by
  simp [toCoordinates, fromCoordinates]

theorem norm_toCoordinates (x : H ambient) : ‖F.toCoordinates x‖ = ‖x‖ := by
  exact F.toBipartite.norm_map x

theorem norm_fromCoordinates (z : BipartiteSpace system environment) :
    ‖F.fromCoordinates z‖ = ‖z‖ := by
  exact F.toBipartite.symm.norm_map z

theorem toCoordinates_injective : Function.Injective F.toCoordinates := by
  exact F.toBipartite.injective

theorem fromCoordinates_injective : Function.Injective F.fromCoordinates := by
  exact F.toBipartite.symm.injective

def toCoordinatesOperator (A : H ambient →ₗ[ℂ] H ambient) :
    BipartiteSpace system environment →ₗ[ℂ] BipartiteSpace system environment :=
  F.toBipartite.toLinearMap ∘ₗ A ∘ₗ F.toBipartite.symm.toLinearMap

def fromCoordinatesOperator
    (A : BipartiteSpace system environment →ₗ[ℂ] BipartiteSpace system environment) :
    H ambient →ₗ[ℂ] H ambient :=
  F.toBipartite.symm.toLinearMap ∘ₗ A ∘ₗ F.toBipartite.toLinearMap

theorem toCoordinatesOperator_id :
    F.toCoordinatesOperator LinearMap.id = LinearMap.id := by
  ext z
  simp [toCoordinatesOperator]

theorem toCoordinatesOperator_zero :
    F.toCoordinatesOperator 0 = 0 := by
  ext z
  simp [toCoordinatesOperator]

theorem toCoordinatesOperator_add (A B : H ambient →ₗ[ℂ] H ambient) :
    F.toCoordinatesOperator (A + B) =
      F.toCoordinatesOperator A + F.toCoordinatesOperator B := by
  ext z
  simp [toCoordinatesOperator, LinearMap.add_apply]

theorem toCoordinatesOperator_sub (A B : H ambient →ₗ[ℂ] H ambient) :
    F.toCoordinatesOperator (A - B) =
      F.toCoordinatesOperator A - F.toCoordinatesOperator B := by
  ext z
  simp [toCoordinatesOperator, LinearMap.sub_apply]

theorem toCoordinatesOperator_smul (c : ℂ) (A : H ambient →ₗ[ℂ] H ambient) :
    F.toCoordinatesOperator (c • A) = c • F.toCoordinatesOperator A := by
  ext z
  simp [toCoordinatesOperator, LinearMap.smul_apply]

theorem toCoordinatesOperator_comp (A B : H ambient →ₗ[ℂ] H ambient) :
    F.toCoordinatesOperator (A ∘ₗ B) =
      F.toCoordinatesOperator A ∘ₗ F.toCoordinatesOperator B := by
  ext z
  simp [toCoordinatesOperator, LinearMap.comp_apply, LinearMap.comp_assoc]

theorem toCoordinatesOperator_adjoint (A : H ambient →ₗ[ℂ] H ambient) :
    F.toCoordinatesOperator (LinearMap.adjoint A) =
      LinearMap.adjoint (F.toCoordinatesOperator A) := by
  simp only [toCoordinatesOperator, LinearMap.adjoint_comp]
  rw [show LinearMap.adjoint F.toBipartite.toLinearMap =
      F.toBipartite.symm.toLinearMap by
    symm
    apply (LinearMap.eq_adjoint_iff _ _).2
    intro x y
    exact F.toBipartite.symm.inner_map_eq_flip x y]
  rw [show LinearMap.adjoint F.toBipartite.symm.toLinearMap =
      F.toBipartite.toLinearMap by
    symm
    apply (LinearMap.eq_adjoint_iff _ _).2
    intro x y
    exact F.toBipartite.inner_map_eq_flip x y]
  simp only [LinearMap.comp_assoc]

theorem from_toCoordinatesOperator (A : H ambient →ₗ[ℂ] H ambient) :
    F.fromCoordinatesOperator (F.toCoordinatesOperator A) = A := by
  ext x
  simp [fromCoordinatesOperator, toCoordinatesOperator, LinearMap.comp_apply]

theorem to_fromCoordinatesOperator
    (A : BipartiteSpace system environment →ₗ[ℂ] BipartiteSpace system environment) :
    F.toCoordinatesOperator (F.fromCoordinatesOperator A) = A := by
  ext z
  simp [fromCoordinatesOperator, toCoordinatesOperator, LinearMap.comp_apply]

def productState (ψ : H system) (η : H environment) : H ambient :=
  F.toBipartite.symm (productStateCoordinates ψ η)

theorem toCoordinates_productState (ψ : H system) (η : H environment) :
    F.toCoordinates (F.productState ψ η) = productStateCoordinates ψ η := by
  simp [productState, toCoordinates]

theorem norm_productState (ψ : H system) (η : H environment) :
    ‖F.productState ψ η‖ = ‖ψ‖ * ‖η‖ := by
  rw [productState, LinearIsometryEquiv.norm_map, norm_productStateCoordinates]

theorem productState_norm_one {ψ : H system} {η : H environment}
    (hψ : ‖ψ‖ = 1) (hη : ‖η‖ = 1) : ‖F.productState ψ η‖ = 1 := by
  rw [norm_productState, hψ, hη, one_mul]

def reducedSystemOperator (A : H ambient →ₗ[ℂ] H ambient) :
    H system →ₗ[ℂ] H system :=
  partialTraceAncilla (F.toCoordinatesOperator A)

abbrev reducedOperator
    (F : SuppliedBipartiteFactorization ambient system environment)
    (A : H ambient →ₗ[ℂ] H ambient) := F.reducedSystemOperator A

theorem reducedSystemOperator_zero :
    F.reducedSystemOperator 0 = 0 := by
  rw [reducedSystemOperator, F.toCoordinatesOperator_zero, partialTraceAncilla_zero]

theorem reducedSystemOperator_add (A B : H ambient →ₗ[ℂ] H ambient) :
    F.reducedSystemOperator (A + B) =
      F.reducedSystemOperator A + F.reducedSystemOperator B := by
  rw [reducedSystemOperator, F.toCoordinatesOperator_add, partialTraceAncilla_add]
  rfl

theorem reducedSystemOperator_sub (A B : H ambient →ₗ[ℂ] H ambient) :
    F.reducedSystemOperator (A - B) =
      F.reducedSystemOperator A - F.reducedSystemOperator B := by
  rw [reducedSystemOperator, F.toCoordinatesOperator_sub, partialTraceAncilla_sub]
  rfl

theorem reducedSystemOperator_smul (c : ℂ) (A : H ambient →ₗ[ℂ] H ambient) :
    F.reducedSystemOperator (c • A) = c • F.reducedSystemOperator A := by
  rw [reducedSystemOperator, F.toCoordinatesOperator_smul, partialTraceAncilla_smul]
  rfl

theorem reducedSystemOperator_id :
    F.reducedSystemOperator LinearMap.id =
      (environment : ℂ) • (LinearMap.id : H system →ₗ[ℂ] H system) := by
  rw [reducedSystemOperator, F.toCoordinatesOperator_id, partialTraceAncilla_id]

theorem toCoordinatesOperator_projL_productState
    {ψ : H system} {η : H environment} :
    F.toCoordinatesOperator (Gleason.projL (ℂ ∙ F.productState ψ η)) =
      (ℂ ∙ productStateCoordinates ψ η).starProjection.toLinearMap := by
  change F.toBipartite.toLinearMap ∘ₗ
      (ℂ ∙ F.productState ψ η).starProjection.toLinearMap ∘ₗ
        F.toBipartite.symm.toLinearMap = _
  calc
    F.toBipartite.toLinearMap ∘ₗ
          (ℂ ∙ F.productState ψ η).starProjection.toLinearMap ∘ₗ
            F.toBipartite.symm.toLinearMap =
        ((ℂ ∙ F.productState ψ η).map F.toBipartite.toLinearMap).starProjection.toLinearMap :=
      conjugate_projL F.toBipartite (ℂ ∙ F.productState ψ η)
    _ = (ℂ ∙ productStateCoordinates ψ η).starProjection.toLinearMap := by
      apply starProjection_toLinearMap_congr
      rw [map_span_singleton_equiv]
      exact congrArg (fun x => ℂ ∙ x) (F.toCoordinates_productState ψ η)

theorem reducedSystemOperator_productProjection
    {ψ : H system} {η : H environment} (hψ : ‖ψ‖ = 1) (hη : ‖η‖ = 1) :
    F.reducedSystemOperator (Gleason.projL (ℂ ∙ F.productState ψ η)) =
      Gleason.projL (ℂ ∙ ψ) := by
  rw [reducedSystemOperator, F.toCoordinatesOperator_projL_productState]
  exact partialTraceAncilla_productProjection hψ hη

theorem toCoordinates_tDensity_productState (t : ℝ)
    (ψ : H system) (η : H environment) :
    F.toCoordinatesOperator
        (tDensity ambient t (F.productState ψ η)) =
      isotropicDensity ambient t (productStateCoordinates ψ η) := by
  rw [tDensity_eq_projL_add_id_sub]
  rw [F.toCoordinatesOperator_add,
    F.toCoordinatesOperator_smul,
    F.toCoordinatesOperator_smul,
    F.toCoordinatesOperator_sub,
    F.toCoordinatesOperator_id]
  rw [F.toCoordinatesOperator_projL_productState]
  rw [isotropicDensity_eq_projL_add_id_sub]
  rfl

theorem reducedSystemOperator_tDensity_product
    {ψ : H system} {η : H environment} (hψ : ‖ψ‖ = 1) (hη : ‖η‖ = 1)
    (t : ℝ) :
    F.reducedSystemOperator (tDensity ambient t (F.productState ψ η)) =
      (t : ℂ) • Gleason.projL (ℂ ∙ ψ) +
        ((((1 - t) / ((ambient : ℝ) - 1) : ℝ) : ℂ) •
          ((environment : ℂ) • (LinearMap.id : H system →ₗ[ℂ] H system) -
            Gleason.projL (ℂ ∙ ψ))) := by
  rw [reducedSystemOperator, F.toCoordinates_tDensity_productState]
  rw [isotropicDensity_eq_projL_add_id_sub]
  rw [partialTraceAncilla_add, partialTraceAncilla_smul,
    partialTraceAncilla_smul, partialTraceAncilla_sub,
    partialTraceAncilla_productProjection hψ hη, partialTraceAncilla_id]
  rfl

end SuppliedBipartiteFactorization

def TensorDecomposition.toSuppliedFactorization
    {system environment : ℕ} (D : TensorDecomposition system environment) :
    SuppliedBipartiteFactorization (system * environment) system environment :=
  ⟨D.toBipartite⟩

def SuppliedBipartiteFactorization.toTensorDecomposition
    {system environment : ℕ}
    (F : SuppliedBipartiteFactorization (system * environment) system environment) :
    TensorDecomposition system environment :=
  ⟨F.toBipartite⟩

theorem TensorDecomposition.toTensorDecomposition_toSupplied
    {system environment : ℕ} (D : TensorDecomposition system environment) :
    D.toSuppliedFactorization.toTensorDecomposition = D := by
  cases D
  rfl

theorem SuppliedBipartiteFactorization.toSupplied_toTensorDecomposition
    {system environment : ℕ}
    (F : SuppliedBipartiteFactorization (system * environment) system environment) :
    F.toTensorDecomposition.toSuppliedFactorization = F := by
  cases F
  rfl

theorem TensorDecomposition.productState_eq_supplied
    {system environment : ℕ} (D : TensorDecomposition system environment)
    (ψ : H system) (η : H environment) :
    D.productState ψ η = D.toSuppliedFactorization.productState ψ η := rfl

theorem TensorDecomposition.toCoordinatesOperator_eq_supplied
    {system environment : ℕ} (D : TensorDecomposition system environment)
    (A : H (system * environment) →ₗ[ℂ] H (system * environment)) :
    D.toCoordinatesOperator A = D.toSuppliedFactorization.toCoordinatesOperator A := rfl

theorem TensorDecomposition.reducedOperator_eq_supplied
    {system environment : ℕ} (D : TensorDecomposition system environment)
    (A : H (system * environment) →ₗ[ℂ] H (system * environment)) :
    partialTraceAncilla (D.toCoordinatesOperator A) =
      D.toSuppliedFactorization.reducedOperator A := rfl

end
end QuantumFoundations.FiniteTensor
