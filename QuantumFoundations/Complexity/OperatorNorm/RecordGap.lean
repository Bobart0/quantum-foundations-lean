import QuantumFoundations.Complexity.OperatorNorm.RecordReadout

/-!
# C12d — Robust distinguishability from operator-norm error

Reuses C8's own analytic distinguishability estimate
(`approx_record_phase_flip_distinguishesAt`) unchanged: the operator-norm
readout threshold is exactly `2 * δ + 2 * ηj + 2 * ε ≤ 2`, i.e. the C8
pointwise threshold `2 * δ + 2 * ηj + ξ ≤ 2` specialized at `ξ = 2 * ε`. No
new analytic estimate is introduced here.
-/

namespace QuantumFoundations.Complexity.OperatorNorm

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity

noncomputable section

/-- An operator-norm readout error budget `ε`, combined with an approximate
record on the target label, distinguishes two unit states at threshold `δ`
whenever `2 * δ + 2 * ηj + 2 * ε ≤ 2`.  A direct reuse of C8's
`approx_record_phase_flip_distinguishesAt`. -/
theorem opApprox_record_phase_flip_distinguishesAt {N d K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (D : Circuit N d)
    (Λ : LabeledResolution (d ^ N) K) (j : Fin K)
    (a b : H (d ^ N)) (ηj ε δ : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hrecord : ApproxRecordFor (rproj Λ j) b a ηj)
    (hOp : ApproximatesRecordPhaseFlipOp e D Λ j ε)
    (hthreshold : 2 * δ + 2 * ηj + 2 * ε ≤ 2) :
    DistinguishesAt e a b δ D :=
  approx_record_phase_flip_distinguishesAt e D Λ j a b ηj (2 * ε) δ ha hb hrecord
    (opApprox_implies_pointwise_phaseFlip e D Λ j a b ε hOp ha hb) hthreshold

/-- The supplied operator-norm-approximate circuit is an explicit
distinguishability upper-bound witness. -/
theorem opApprox_record_phase_flip_gives_upper_bound {N d K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (D : Circuit N d)
    (Λ : LabeledResolution (d ^ N) K) (j : Fin K)
    (a b : H (d ^ N)) (ηj ε δ : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hrecord : ApproxRecordFor (rproj Λ j) b a ηj)
    (hOp : ApproximatesRecordPhaseFlipOp e D Λ j ε)
    (hthreshold : 2 * δ + 2 * ηj + 2 * ε ≤ 2) :
    HasDistinguishabilityUpperBound e a b δ (Circuit.length D) :=
  ⟨D, le_rfl, opApprox_record_phase_flip_distinguishesAt
    e D Λ j a b ηj ε δ ha hb hrecord hOp hthreshold⟩

/-- The same operator-norm-approximate circuit upper-bounds the actual
minimum distinguishability complexity. -/
theorem opApprox_record_phase_flip_complexity_upper_bound {N d K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (D : Circuit N d)
    (Λ : LabeledResolution (d ^ N) K) (j : Fin K)
    (a b : H (d ^ N)) (ηj ε δ : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hrecord : ApproxRecordFor (rproj Λ j) b a ηj)
    (hOp : ApproximatesRecordPhaseFlipOp e D Λ j ε)
    (hthreshold : 2 * δ + 2 * ηj + 2 * ε ≤ 2) :
    distinguishabilityComplexity e a b δ ≤ (Circuit.length D : WithTop ℕ) := by
  apply complexity_le_of_distinguishabilityUpperBound
  exact opApprox_record_phase_flip_gives_upper_bound
    e D Λ j a b ηj ε δ ha hb hrecord hOp hthreshold

/-- Regression: at operator-norm error `ε = 0`, the threshold reduces to the
exact phase-flip threshold `2 * δ + 2 * ηj ≤ 2`. -/
theorem exact_opApprox_record_phase_flip_distinguishesAt {N d K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (D : Circuit N d)
    (Λ : LabeledResolution (d ^ N) K) (j : Fin K)
    (a b : H (d ^ N)) (ηj δ : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hrecord : ApproxRecordFor (rproj Λ j) b a ηj)
    (hD : ImplementsRecordPhaseFlip e D Λ j)
    (hthreshold : 2 * δ + 2 * ηj ≤ 2) :
    DistinguishesAt e a b δ D := by
  apply opApprox_record_phase_flip_distinguishesAt e D Λ j a b ηj 0 δ ha hb hrecord
    (implementsRecordPhaseFlip_implies_opApprox_zero e D Λ j hD)
  linarith

#print axioms opApprox_record_phase_flip_distinguishesAt
#print axioms opApprox_record_phase_flip_complexity_upper_bound

end

end QuantumFoundations.Complexity.OperatorNorm
