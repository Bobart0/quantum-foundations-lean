import QuantumFoundations.Complexity.Models.MeasurementGeneration.ConcreteGeneration

/-!
# C12a — Finite-dimensional continuous-linear-map view

Every linear map out of a finite-dimensional complex normed space is
automatically continuous (`LinearMap.continuous_of_finiteDimensional`).
Mathlib packages this fact as a linear *equivalence*
`LinearMap.toContinuousLinearMap : (E →ₗ[𝕜] F) ≃ₗ[𝕜] (E →L[𝕜] F)` between the
plain and continuous linear-map spaces, valid whenever the domain `E` is
finite-dimensional over a complete field.  `toContinuousLinearMapFD` is a
thin, repository-local name for this existing equivalence, specialized to
`ℂ`; it introduces no new mathematics and does not touch any existing
`LinearMap` API (`Circuit.eval`, `Circuit.evalOnH`, `recordPhaseFlip`, and
every C0–C11 declaration built from them are left entirely unchanged).  This
view exists solely so that C12 can state an *operator-norm* (`ContinuousLinearMap`
norm) error budget alongside the untouched exact `LinearMap` layer.
-/

namespace QuantumFoundations.Complexity.OperatorNorm

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity

noncomputable section

/-! ## C12a.1 — Generic finite-dimensional conversion -/

/-- The canonical continuous-linear-map view of a linear map out of a
finite-dimensional complex normed space, via Mathlib's automatic-continuity
equivalence `LinearMap.toContinuousLinearMap`. -/
noncomputable def toContinuousLinearMapFD
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (T : E →ₗ[ℂ] F) : E →L[ℂ] F :=
  LinearMap.toContinuousLinearMap T

variable {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] [FiniteDimensional ℂ G]

@[simp] theorem toContinuousLinearMapFD_apply (T : E →ₗ[ℂ] F) (x : E) :
    toContinuousLinearMapFD T x = T x := rfl

theorem toContinuousLinearMapFD_coe (T : E →ₗ[ℂ] F) :
    (toContinuousLinearMapFD T : E → F) = (T : E → F) := by
  funext x
  rfl

@[simp] theorem toContinuousLinearMapFD_zero :
    toContinuousLinearMapFD (0 : E →ₗ[ℂ] F) = 0 := by
  unfold toContinuousLinearMapFD
  exact map_zero _

theorem toContinuousLinearMapFD_add (S T : E →ₗ[ℂ] F) :
    toContinuousLinearMapFD (S + T) =
      toContinuousLinearMapFD S + toContinuousLinearMapFD T := by
  unfold toContinuousLinearMapFD
  exact map_add _ _ _

theorem toContinuousLinearMapFD_sub (S T : E →ₗ[ℂ] F) :
    toContinuousLinearMapFD (S - T) =
      toContinuousLinearMapFD S - toContinuousLinearMapFD T := by
  unfold toContinuousLinearMapFD
  exact map_sub _ _ _

theorem toContinuousLinearMapFD_smul (c : ℂ) (T : E →ₗ[ℂ] F) :
    toContinuousLinearMapFD (c • T) = c • toContinuousLinearMapFD T := by
  unfold toContinuousLinearMapFD
  exact map_smul _ _ _

theorem toContinuousLinearMapFD_comp (S : F →ₗ[ℂ] G) (T : E →ₗ[ℂ] F) :
    toContinuousLinearMapFD (S ∘ₗ T) =
      (toContinuousLinearMapFD S).comp (toContinuousLinearMapFD T) := by
  unfold toContinuousLinearMapFD
  ext x
  simp

/-! ## C12a.2 — Specialization to the repository's circuit and record maps -/

/-- The continuous-linear-map view of a finite circuit's transported
evaluation on `H (d ^ N)`.  `Circuit.evalOnH` itself is untouched: this is
purely an additional operator-norm-bearing view of the same linear map. -/
noncomputable def circuitCLMOnH {N d : ℕ}
    (C : Circuit N d) (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) :
    H (d ^ N) →L[ℂ] H (d ^ N) :=
  toContinuousLinearMapFD (Circuit.evalOnH C e)

/-- The continuous-linear-map view of the exact record phase flip
`recordPhaseFlip`.  `recordPhaseFlip` itself is untouched. -/
noncomputable def recordPhaseFlipCLM {n K : ℕ}
    (Λ : LabeledResolution n K) (j : Fin K) :
    H n →L[ℂ] H n :=
  toContinuousLinearMapFD (recordPhaseFlip Λ j)

@[simp] theorem circuitCLMOnH_apply {N d : ℕ}
    (C : Circuit N d) (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (x : H (d ^ N)) :
    circuitCLMOnH C e x = Circuit.evalOnH C e x := rfl

@[simp] theorem recordPhaseFlipCLM_apply {n K : ℕ}
    (Λ : LabeledResolution n K) (j : Fin K) (x : H n) :
    recordPhaseFlipCLM Λ j x = recordPhaseFlip Λ j x := rfl

#print axioms toContinuousLinearMapFD_comp
#print axioms circuitCLMOnH_apply
#print axioms recordPhaseFlipCLM_apply

end

end QuantumFoundations.Complexity.OperatorNorm
