import QuantumFoundations.Complexity.OperatorNorm.GeneratedBranches

/-!
# C12 — Non-vacuity of the operator-norm error-budget API

Every exact circuit implementation already inhabits the operator-norm
predicates at error `0`, and monotonicity extends this to every nonnegative
budget — in particular to the concrete `1/20` witness and to C11's
dynamically generated branches. None of this constructs a circuit with
genuinely nonzero operator-norm error: it demonstrates that the C12
error-budget API is inhabited, not that any specific physical
implementation has a specific nonzero error.
-/

namespace QuantumFoundations.Complexity.OperatorNorm

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.RepetitionModel
open QuantumFoundations.Complexity.NoisyRepetitionModel
open QuantumFoundations.Complexity.MeasurementGeneration

/-- An exact circuit implementation of the record phase flip has operator-
norm error exactly zero. -/
example {N d K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (D : Circuit N d)
    (Λ : LabeledResolution (d ^ N) K) (j : Fin K)
    (hD : ImplementsRecordPhaseFlip e D Λ j) :
    ApproximatesRecordPhaseFlipOp e D Λ j 0 :=
  implementsRecordPhaseFlip_implies_opApprox_zero e D Λ j hD

/-- Zero operator-norm error inhabits every larger nonnegative budget. -/
example {N d K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (D : Circuit N d)
    (Λ : LabeledResolution (d ^ N) K) (j : Fin K) (ε : ℝ) (hε : 0 ≤ ε)
    (hD : ImplementsRecordPhaseFlip e D Λ j) :
    ApproximatesRecordPhaseFlipOp e D Λ j ε :=
  (implementsRecordPhaseFlip_implies_opApprox_zero e D Λ j hD).mono hε

/-- The C10 exact one-gate readout inhabits the operator-norm
record-readout predicate, at error `0`. -/
example (R : ℕ) [NeZero R] :
    ApproximatesRecordPhaseFlipOp
      (sitesEquivR (R + 1)) (noisyReadoutCircuit R) (noisyRecords R 0) 1 0 :=
  implementsRecordPhaseFlip_implies_opApprox_zero
    (sitesEquivR (R + 1)) (noisyReadoutCircuit R) (noisyRecords R 0) 1
    (noisyReadoutCircuit_implements R)

/-- The concrete `1/20` error-budget theorem has an inhabited premise: the
exact C10 readout, at error `0`, satisfies the `1/20` operator-norm budget
by monotonicity. -/
example (R : ℕ) [NeZero R]
    (g : ℕ) (hgap : (noisyReadoutCircuit R).length + g ≤ ceilHalf R) :
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      (noisyZeroBranch rationalNoiseProfile R)
      (noisyOneBranch rationalNoiseProfile R) (1 / 2 : ℝ) g :=
  concrete_generated_branches_tolerate_opNorm_error R (noisyReadoutCircuit R)
    ((implementsRecordPhaseFlip_implies_opApprox_zero
        (sitesEquivR (R + 1)) (noisyReadoutCircuit R) (noisyRecords R 0) 1
        (noisyReadoutCircuit_implements R)).mono (by norm_num))
    g hgap

/-- C11's dynamically generated branches instantiate the C12 operator-norm
robust-gap theorem, at the exact readout (error `0`). -/
example (R : ℕ) [NeZero R] (q : SourceAmplitudeProfile)
    (g : ℕ) (hgap : (noisyReadoutCircuit R).length + g ≤ ceilHalf R) :
    Circuit.evalOnH (noisyMeasurementCircuit rationalNoiseProfile R)
        (sitesEquivR (R + 1)) (noisySourceInputState q R) =
      q.amp0 • noisyZeroBranch rationalNoiseProfile R
        + q.amp1 • noisyOneBranch rationalNoiseProfile R
    ∧
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      (noisyZeroBranch rationalNoiseProfile R)
      (noisyOneBranch rationalNoiseProfile R) (1 / 2 : ℝ) g :=
  generated_branches_have_opNorm_robust_gap rationalNoiseProfile
    rationalNoiseProfile_isRobust q R (noisyReadoutCircuit R) 0
    (implementsRecordPhaseFlip_implies_opApprox_zero
      (sitesEquivR (R + 1)) (noisyReadoutCircuit R) (noisyRecords R 0) 1
      (noisyReadoutCircuit_implements R))
    (by norm_num [rationalNoiseProfile_leak, norm_div]) g hgap

end QuantumFoundations.Complexity.OperatorNorm
