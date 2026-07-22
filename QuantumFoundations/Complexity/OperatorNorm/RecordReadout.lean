import QuantumFoundations.Complexity.OperatorNorm.Approximation
import QuantumFoundations.Complexity.ApproxRecordDistinguishability

/-!
# C12c — Operator-norm record-phase-flip approximation

`ApproximatesRecordPhaseFlipOp` is the operator-norm analogue of C8's
pointwise `ApproximatesRecordPhaseFlipOn`: a single uniform bound on the
whole readout circuit's operator-norm distance to the exact record phase
flip, rather than a bound supplied separately for each of the two states of
interest.  `opApprox_implies_pointwise_phaseFlip` is the pointwise-error
bridge: an operator-norm budget `ε` implies the pointwise C8 budget `2 * ε`
on any pair of unit states, by a direct specialization of
`sum_two_apply_errors_le`.
-/

namespace QuantumFoundations.Complexity.OperatorNorm

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity

noncomputable section

/-! ## C12c.1 — The operator-norm record-readout predicate -/

/-- A supplied circuit `D` approximates the exact record phase flip in
operator norm, with error budget `ε`. -/
def ApproximatesRecordPhaseFlipOp {N d K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (D : Circuit N d)
    (Λ : LabeledResolution (d ^ N) K) (j : Fin K) (ε : ℝ) : Prop :=
  ApproximatesOperator (circuitCLMOnH D e) (recordPhaseFlipCLM Λ j) ε

namespace ApproximatesRecordPhaseFlipOp

/-- Increasing the operator-norm error budget preserves the approximation. -/
theorem mono {N d K : ℕ}
    {e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d} {D : Circuit N d}
    {Λ : LabeledResolution (d ^ N) K} {j : Fin K} {ε ε' : ℝ}
    (h : ApproximatesRecordPhaseFlipOp e D Λ j ε) (hε : ε ≤ ε') :
    ApproximatesRecordPhaseFlipOp e D Λ j ε' :=
  ApproximatesOperator.mono h hε

end ApproximatesRecordPhaseFlipOp

/-- An exact circuit implementation of the record phase flip has operator-
norm error exactly zero. -/
theorem implementsRecordPhaseFlip_implies_opApprox_zero {N d K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (D : Circuit N d)
    (Λ : LabeledResolution (d ^ N) K) (j : Fin K)
    (hD : ImplementsRecordPhaseFlip e D Λ j) :
    ApproximatesRecordPhaseFlipOp e D Λ j 0 := by
  unfold ApproximatesRecordPhaseFlipOp ApproximatesOperator
  have heq : circuitCLMOnH D e = recordPhaseFlipCLM Λ j := by
    unfold circuitCLMOnH recordPhaseFlipCLM
    rw [hD]
  rw [heq, sub_self, norm_zero]

/-! ## C12c.2 — The pointwise-error bridge -/

/-- The central C12 bridge: an operator-norm readout error budget `ε`
implies a pointwise (C8-style) error budget `2 * ε` on any pair of unit
states.  A direct specialization of `sum_two_apply_errors_le`. -/
theorem opApprox_implies_pointwise_phaseFlip {N d K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (D : Circuit N d)
    (Λ : LabeledResolution (d ^ N) K) (j : Fin K)
    (a b : H (d ^ N)) (ε : ℝ)
    (hOp : ApproximatesRecordPhaseFlipOp e D Λ j ε)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ApproximatesRecordPhaseFlipOn e D Λ j a b (2 * ε) := by
  unfold ApproximatesRecordPhaseFlipOn
  simpa using sum_two_apply_errors_le hOp ha hb

/-- The individual left-state pointwise estimate. -/
theorem opApprox_phaseFlip_apply_left {N d K : ℕ}
    {e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d} {D : Circuit N d}
    {Λ : LabeledResolution (d ^ N) K} {j : Fin K}
    {a : H (d ^ N)} {ε : ℝ}
    (hOp : ApproximatesRecordPhaseFlipOp e D Λ j ε) (ha : ‖a‖ = 1) :
    ‖Circuit.evalOnH D e a - recordPhaseFlip Λ j a‖ ≤ ε := by
  simpa using norm_apply_sub_le_of_unit hOp ha

/-- The individual right-state pointwise estimate. -/
theorem opApprox_phaseFlip_apply_right {N d K : ℕ}
    {e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d} {D : Circuit N d}
    {Λ : LabeledResolution (d ^ N) K} {j : Fin K}
    {b : H (d ^ N)} {ε : ℝ}
    (hOp : ApproximatesRecordPhaseFlipOp e D Λ j ε) (hb : ‖b‖ = 1) :
    ‖Circuit.evalOnH D e b - recordPhaseFlip Λ j b‖ ≤ ε := by
  simpa using norm_apply_sub_le_of_unit hOp hb

/-- Regression: an exact circuit implementation recovers pointwise error
exactly zero along the operator-norm route (the `ε = 0` case of
`opApprox_implies_pointwise_phaseFlip`), matching the existing
`implementsRecordPhaseFlip_gives_approximation_zero` from C8 (which needs no
unit-norm hypothesis at all, since exact operator equality gives zero
pointwise error on every vector). -/
theorem exact_phaseFlip_recovers_pointwise_zero {N d K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (D : Circuit N d)
    (Λ : LabeledResolution (d ^ N) K) (j : Fin K)
    (a b : H (d ^ N)) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hD : ImplementsRecordPhaseFlip e D Λ j) :
    ApproximatesRecordPhaseFlipOn e D Λ j a b 0 := by
  have h := opApprox_implies_pointwise_phaseFlip e D Λ j a b 0
    (implementsRecordPhaseFlip_implies_opApprox_zero e D Λ j hD) ha hb
  simpa using h

#print axioms implementsRecordPhaseFlip_implies_opApprox_zero
#print axioms opApprox_implies_pointwise_phaseFlip

end

end QuantumFoundations.Complexity.OperatorNorm
