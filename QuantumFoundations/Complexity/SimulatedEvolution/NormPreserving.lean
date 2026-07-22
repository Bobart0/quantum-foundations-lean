import QuantumFoundations.Complexity.OperatorNorm.Composition
import QuantumFoundations.Complexity.ProxyTransport

/-!
# C13a — Norm-preserving operators

`IsNormPreserving U` is a lightweight, unbundled predicate on a continuous
linear map: it says nothing about surjectivity or invertibility, only that
`U` preserves every vector's norm. This is exactly what circuit evaluation
already satisfies (`Circuit.evalOnH_norm`), and exactly what a "target"
norm-preserving evolution `U` (Hamiltonian or otherwise) is assumed to
satisfy in the rest of C13 — no isometry/equiv bundling is introduced, since
none of the downstream arguments need anything beyond the norm equality.
-/

namespace QuantumFoundations.Complexity.SimulatedEvolution

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.OperatorNorm

noncomputable section

/-! ## C13a.1 — The generic predicate -/

/-- `U` preserves the norm of every vector. -/
def IsNormPreserving {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : E →L[ℂ] E) : Prop :=
  ∀ x, ‖U x‖ = ‖x‖

namespace IsNormPreserving

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem norm_apply {U : E →L[ℂ] E} (h : IsNormPreserving U) (x : E) :
    ‖U x‖ = ‖x‖ :=
  h x

/-- A norm-preserving operator has operator norm at most `1`. -/
theorem operator_norm_le_one {U : E →L[ℂ] E} (h : IsNormPreserving U) :
    ‖U‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound U (by norm_num)
  intro x
  rw [h x, one_mul]

/-- On a nontrivial space, a norm-preserving operator has operator norm
exactly `1`. -/
theorem operator_norm_eq_one [Nontrivial E] {U : E →L[ℂ] E}
    (h : IsNormPreserving U) : ‖U‖ = 1 := by
  have hle := h.operator_norm_le_one
  obtain ⟨x0, hx0⟩ := exists_ne (0 : E)
  have hxpos : 0 < ‖x0‖ := norm_pos_iff.mpr hx0
  have hb := ContinuousLinearMap.le_opNorm U x0
  rw [h x0] at hb
  have hb' : 1 * ‖x0‖ ≤ ‖U‖ * ‖x0‖ := by rwa [one_mul]
  have hge : (1 : ℝ) ≤ ‖U‖ := le_of_mul_le_mul_right hb' hxpos
  linarith

end IsNormPreserving

/-! ## C13a.2 — Circuit evaluation is norm preserving -/

/-- Finite circuit evaluation, viewed through the C12 continuous-linear-map
lens, is norm preserving: an immediate reuse of `Circuit.evalOnH_norm`
(circuit unitarity), no coordinate-level reproof. -/
theorem circuitCLMOnH_isNormPreserving {N d : ℕ}
    (C : Circuit N d) (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) :
    IsNormPreserving (circuitCLMOnH C e) := by
  intro x
  rw [circuitCLMOnH_apply]
  exact Circuit.evalOnH_norm C e x

/-! ## C13a.3 — Operator-norm approximation between norm-preserving maps -/

/-- On a unit vector, an operator-norm approximation between `U` and `V`
bounds the pointwise discrepancy directly: a direct reuse of C12's
`norm_apply_sub_le_of_unit`. -/
theorem norm_image_sub_image_le {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    {U V : E →L[ℂ] F} {ε : ℝ} {x : E}
    (hUV : ApproximatesOperator U V ε) (hx : ‖x‖ = 1) :
    ‖U x - V x‖ ≤ ε :=
  norm_apply_sub_le_of_unit hUV hx

#print axioms circuitCLMOnH_isNormPreserving
#print axioms IsNormPreserving.operator_norm_eq_one

end

end QuantumFoundations.Complexity.SimulatedEvolution
