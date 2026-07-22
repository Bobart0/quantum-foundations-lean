import QuantumFoundations.Complexity.ApproxRecordPersistence
import QuantumFoundations.Complexity.Models.Repetition.Persistence
import QuantumFoundations.Complexity.Models.NoisyRepetition.ConcreteNoise
import QuantumFoundations.Complexity.Models.MeasurementGeneration.ConcreteGeneration
import QuantumFoundations.Complexity.OperatorNorm.Nonvacuity

/-!
# C0/C6/C7/C8/C9/C10/C11/C12 — Non-vacuity

The empty circuit exists for every finite site system.  In addition, the
identity is an exact gate with empty support, so the gate structure itself is
inhabited without any physical assumption.  C7's reversible-evolution
certificate is inhabited by the empty circuit in both directions.
Exact record and phase-flip hypotheses also inhabit their C8 approximate
counterparts at error zero, and monotonicity enlarges any such error budget.
C9 supplies the concrete repetition-record model: exact records, a one-gate
readout, and a finite interference witness all coexist in one explicit family.
C10 supplies a *nonzero-noise* family on `R + 1` sites (one source qubit plus
`R` record qubits): its records are only approximate (the C8 predicate is
genuinely inhabited by nonzero error), yet the robust threshold
`4 * ‖leak‖ < 1` still yields the same qualitative separation as C9 — a
constant-cost readout, a linear-length interference witness, and a proxy gap
growing with the record count.  C10 does not claim identity with the C9
model: it uses `R + 1` sites because of the extra source qubit.
C11 supplies an explicit finite circuit of 1- and 2-local gates that
*dynamically generates* the source-record branching from an initially
uncorrelated source qubit and blank record qubits, rather than assuming the
branched state as given: a concrete nonzero-amplitude source profile, paired
with C10's concrete nonzero-noise profile, exhibits the full
generation-to-persistence pipeline with no side hypotheses.
C12 supplies a finite-dimensional operator-norm bridge from a single global
operator-norm error budget to the pointwise readout hypotheses used by
C8–C11: exact circuit implementations inhabit the new operator-norm
predicates at error zero, monotonicity extends this to every nonnegative
budget (in particular to a concrete nonzero `1/20` budget), and the same
robust proxy-gap and persistence conclusions follow for both the static C10
noisy model and C11's dynamically generated branches.
-/

namespace QuantumFoundations.Complexity

open scoped InnerProductSpace

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- The identity gate, declared local to the empty region. -/
noncomputable def identityGate (N d : ℕ) : TwoLocalGate N d where
  unitary := LinearIsometryEquiv.refl ℂ (Sites N d)
  support := ∅
  locality := Circuit.isLocalTo_id_empty
  support_card_le_two := by simp

/-- The empty circuit has length zero and evaluates to the identity. -/
example :
    Circuit.length ([] : Circuit N d) = 0 ∧
      Circuit.eval ([] : Circuit N d) = LinearMap.id := by
  simp

/-- A singleton identity circuit is a concrete nonempty circuit. -/
example : Circuit.eval [identityGate N d] = LinearMap.id := by
  ext x
  rfl

/-- Threshold-zero distinguishability is inhabited by the empty circuit. -/
example (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N)) :
    DistinguishesAt e a b 0 ([] : Circuit N d) := by
  unfold DistinguishesAt
  simp only [mul_zero]
  exact norm_nonneg
    (⟪a, Circuit.evalOnH ([] : Circuit N d) e a⟫_ℂ -
      ⟪b, Circuit.evalOnH ([] : Circuit N d) e b⟫_ℂ)

/-- Threshold-zero interference is inhabited by the empty circuit. -/
example (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N)) :
    InterferesAt e a b 0 ([] : Circuit N d) := by
  unfold InterferesAt
  simpa using add_nonneg
    (norm_nonneg ⟪a, Circuit.evalOnH ([] : Circuit N d) e b⟫_ℂ)
    (norm_nonneg ⟪b, Circuit.evalOnH ([] : Circuit N d) e a⟫_ℂ)

/-- An impossible circuit predicate has infinite minimum length. -/
example : minCircuitLength (fun _ : Circuit N d => False) = ⊤ := by
  apply minCircuitLength_eq_top_of_no_witness
  simp

/-- A predicate witnessed by the empty circuit has minimum length zero. -/
example : minCircuitLength (fun _ : Circuit N d => True) = 0 := by
  apply le_antisymm
  · simpa using minCircuitLength_le_of_witness
      ([] : Circuit N d) (show True from trivial)
  · exact bot_le

/-- The empty forward/backward pair is a reversible evolution with zero
conjugation overhead. -/
example :
    (ReversibleCircuitEvolution.reversibleEmptyEvolution N d).overhead = 0 := by
  rfl

/-- Canonical inversion is non-vacuous already on the empty circuit. -/
example : Circuit.inverse ([] : Circuit N d) = [] := by
  rfl

/-- Unitary circuit evolution preserves a supplied unit-norm hypothesis, so
evolved normalized branches do not require renormalization. -/
example (E : Circuit N d) (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (a : H (d ^ N)) (ha : ‖a‖ = 1) :
    ‖Circuit.evalOnH E e a‖ = 1 := by
  exact Circuit.evalOnH_unit E e ha

/-- Exact fixing and rejection are an approximate record with zero error. -/
example (P : H n →ₗ[ℂ] H n) (target other : H n)
    (hfix : P target = target) (hreject : P other = 0) :
    ApproxRecordFor P target other 0 :=
  approxRecordFor_zero_of_fixes_rejects hfix hreject

/-- Any nonnegative budget weakens the preceding exact witness. -/
example (P : H n →ₗ[ℂ] H n) (target other : H n)
    (hfix : P target = target) (hreject : P other = 0)
    (η : ℝ) (hη : 0 ≤ η) : ApproxRecordFor P target other η := by
  exact (approxRecordFor_zero_of_fixes_rejects hfix hreject).mono hη

/-- An exact record phase flip is an approximate implementation at error
zero. -/
example (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (D : Circuit N d)
    (Λ : LabeledResolution (d ^ N) K) (j : Fin K)
    (a b : H (d ^ N)) (hD : ImplementsRecordPhaseFlip e D Λ j) :
    ApproximatesRecordPhaseFlipOn e D Λ j a b 0 :=
  implementsRecordPhaseFlip_gives_approximation_zero e D Λ j a b hD

namespace RepetitionModel

/-- The explicit coherent repetition state satisfies every exact record in
its singleton family. -/
example (R : ℕ) [NeZero R] :
    IsRecordedOn (repetitionState R) (repetitionRecords R) :=
  repetitionState_isRecordedOn R

/-- The abstract readout-circuit assumption is inhabited by the concrete
one-gate reflection. -/
example (R : ℕ) [NeZero R] :
    ImplementsRecordPhaseFlip (sitesEquivR R) (recordReadoutCircuit R)
      (repetitionRecords R (firstSite R)) 1 :=
  recordReadoutCircuit_implements_phase_flip R

/-- Interference at threshold one has the explicit finite witness of length
`R`. -/
example (R : ℕ) :
    InterferesAt (sitesEquivR R) (zeroBranch R) (oneBranch R) 1
      (allBitFlipCircuit R) :=
  repetition_interferesAt_one R

/-- Consequently the explicit model's interference minimum is finite. -/
example (R : ℕ) :
    interferenceComplexity
      (sitesEquivR R) (zeroBranch R) (oneBranch R) 1 ≠ ⊤ :=
  repetition_interferenceComplexity_ne_top R

/-- The exact repetition records inhabit the approximate framework with
zero error in both label orientations. -/
example (R : ℕ) [NeZero R] :
    ApproxRecordedPairOn (repetitionRecords R)
      (zeroBranch R) (oneBranch R) 0 1 0 0 :=
  repetition_approxRecordedPair_zero R

end RepetitionModel

namespace NoisyRepetitionModel

open QuantumFoundations.Complexity.RepetitionModel

/-- The concrete rational profile's leakage is nonzero: C10's approximate
records are genuinely inhabited by nonzero error, not merely by the C9
zero-error regression. -/
example : rationalNoiseProfile.leak ≠ 0 := rationalNoiseProfile_leak_ne_zero

/-- The concrete profile satisfies the robust-noise threshold
`4 * ‖leak‖ < 1`. -/
example : rationalNoiseProfile.IsRobust := rationalNoiseProfile_isRobust

/-- The noisy records instantiate the C8 approximate-record pair predicate
with nonzero aggregate error `2 * ‖leak‖`, not the exact `IsRecordedOn`
predicate. -/
example (R : ℕ) [NeZero R] :
    ApproxRecordedPairOn (noisyRecords R)
      (noisyZeroBranch rationalNoiseProfile R) (noisyOneBranch rationalNoiseProfile R)
      0 1 (2 * ‖rationalNoiseProfile.leak‖) (2 * ‖rationalNoiseProfile.leak‖) :=
  noisy_repetition_approxRecordedPairOn rationalNoiseProfile R

/-- The one-gate readout implements the exact record phase flip at the
embedded record site. -/
example (R : ℕ) [NeZero R] :
    ImplementsRecordPhaseFlip (sitesEquivR (R + 1)) (noisyReadoutCircuit R)
      (noisyRecords R 0) 1 :=
  noisyReadoutCircuit_implements R

/-- The concrete robust distinguishability complexity is exactly one gate. -/
example (R : ℕ) [NeZero R] :
    distinguishabilityComplexity (sitesEquivR (R + 1))
        (noisyZeroBranch rationalNoiseProfile R) (noisyOneBranch rationalNoiseProfile R)
        (1 / 2 : ℝ)
      = (1 : WithTop ℕ) :=
  concrete_noisy_distinguishabilityComplexity_eq_one R

/-- The all-bit-flip circuit gives a finite interference witness, so the
noisy model's interference minimum is finite. -/
example (p : NoiseProfile) (R : ℕ) [NeZero R] :
    interferenceComplexity (sitesEquivR (R + 1))
        (noisyZeroBranch p R) (noisyOneBranch p R) (1 / 2 : ℝ) ≠ ⊤ :=
  noisy_repetition_interference_ne_top p R

/-- Positive proxy gaps are certified whenever the finite record budget
permits: e.g. `R = 3` record qubits already give gap `1`. -/
example : HasProxyGapAtLeast (sitesEquivR (3 + 1))
    (noisyZeroBranch rationalNoiseProfile 3) (noisyOneBranch rationalNoiseProfile 3)
    (1 / 2 : ℝ) 1 :=
  noisy_repetition_positive_gap rationalNoiseProfile rationalNoiseProfile_isRobust 3 (by norm_num)

/-- The robust proxy gap persists conditionally through a supplied finite
circuit, as long as the record budget also covers the conjugation
overhead. -/
example (R : ℕ) [NeZero R] (E : Circuit (R + 1) 2) (g : ℕ)
    (hbudget : 1 + 4 * E.length + g ≤ ceilHalf R) :
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      (Circuit.evalOnH E (sitesEquivR (R + 1)) (noisyZeroBranch rationalNoiseProfile R))
      (Circuit.evalOnH E (sitesEquivR (R + 1)) (noisyOneBranch rationalNoiseProfile R))
      (1 / 2 : ℝ) g :=
  concrete_noisy_repetition_gap_persists R E g hbudget

/-- Zero-leak regression: `exactProfile` recovers exact record identities
(zero aggregate error) from the same noisy construction. -/
example (R : ℕ) [NeZero R] :
    ApproxRecordedPairOn (noisyRecords R)
      (noisyZeroBranch exactProfile R) (noisyOneBranch exactProfile R) 0 1 0 0 :=
  exactProfile_approxRecordedPairOn_zero R

end NoisyRepetitionModel

namespace MeasurementGeneration

open QuantumFoundations.Complexity.Gates
open QuantumFoundations.Complexity.RepetitionModel
open QuantumFoundations.Complexity.NoisyRepetitionModel

/-- The controlled-bit-flip gate is a genuine `2`-local gate: its declared
support really does have cardinality at most two, with the locality witness
constructed explicitly rather than assumed. -/
example (control target : Fin N) (hne : control ≠ target) :
    (controlledBitFlipGate control target hne).support.card ≤ 2 :=
  (controlledBitFlipGate control target hne).support_card_le_two

/-- The ideal source-controlled fanout circuit unitarily turns a blank-record
source superposition into the branching decomposition: computational-basis
fanout, not cloning of an arbitrary state. -/
example (α β : ℂ) (R : ℕ) :
    Circuit.evalOnH (idealFanoutCircuit R) (sitesEquivR (R + 1)) (idealInputState α β R) =
      idealOutputState α β R :=
  idealFanout_generates_branching α β R

/-- The canonical amplitude-mixing preparation gate is constructed for every
`NoiseProfile`, with no supplied-gate hypothesis anywhere. -/
example (p : NoiseProfile) (R : ℕ) [NeZero R] : ImplementsNoisePreparation p R :=
  profilePreparationImplementation p R

/-- Amplitude preservation: the two squared component weights extracted from
the ideal generated state sum to one, for the concrete equal-norm source
profile. -/
example (R : ℕ) :
    ‖rproj (sourceResolution R) 0 (idealGeneratedState equalSourceProfile R)‖ ^ 2 +
        ‖rproj (sourceResolution R) 1 (idealGeneratedState equalSourceProfile R)‖ ^ 2 = 1 :=
  component_norm_squares_sum_one equalSourceProfile R

/-- The fully concrete generation circuit — built from the `3/5, 4/5`
source profile and C10's `99/101, 20/101` noise profile — unitarily turns
blank records into the noisy branching decomposition. -/
example (R : ℕ) [NeZero R] :
    Circuit.evalOnH (noisyMeasurementCircuit rationalNoiseProfile R) (sitesEquivR (R + 1))
        (noisySourceInputState concreteSourceProfile R) =
      noisySourceGeneratedState concreteSourceProfile rationalNoiseProfile R :=
  concrete_unitary_generation_produces_noisy_branches R

/-- Zero-leak regression: at the exact profile, the noisy generation
circuit's action collapses to the ideal fanout's branching. -/
example (α β : ℂ) (R : ℕ) [NeZero R] :
    Circuit.evalOnH (noisyMeasurementCircuit exactProfile R) (sitesEquivR (R + 1))
        (noisyInputState α β R) =
      idealOutputState α β R :=
  noisyMeasurement_exactProfile α β R

/-- The concretely generated branches carry a nonzero robust proxy gap: e.g.
`R = 3` record qubits already give gap `1`. -/
example :
    HasProxyGapAtLeast (sitesEquivR (3 + 1))
      (Circuit.evalOnH (noisyMeasurementCircuit rationalNoiseProfile 3) (sitesEquivR (3 + 1))
        (basis00 3))
      (Circuit.evalOnH (noisyMeasurementCircuit rationalNoiseProfile 3) (sitesEquivR (3 + 1))
        (basis10 3))
      (1 / 2 : ℝ) 1 :=
  concrete_generated_branches_have_gap 3 1 (by unfold ceilHalf; omega)

/-- That concrete robust proxy gap persists conditionally through a
supplied finite further circuit, as long as the record budget also covers
the conjugation overhead. -/
example (R : ℕ) [NeZero R] (E : Circuit (R + 1) 2) (g : ℕ)
    (hbudget : 1 + 4 * E.length + g ≤ ceilHalf R) :
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      (Circuit.evalOnH E (sitesEquivR (R + 1))
        (Circuit.evalOnH (noisyMeasurementCircuit rationalNoiseProfile R) (sitesEquivR (R + 1))
          (basis00 R)))
      (Circuit.evalOnH E (sitesEquivR (R + 1))
        (Circuit.evalOnH (noisyMeasurementCircuit rationalNoiseProfile R) (sitesEquivR (R + 1))
          (basis10 R)))
      (1 / 2 : ℝ) g :=
  concrete_generated_branches_persist R E g hbudget

end MeasurementGeneration

namespace OperatorNorm

open QuantumFoundations.Complexity.RepetitionModel
open QuantumFoundations.Complexity.NoisyRepetitionModel
open QuantumFoundations.Complexity.MeasurementGeneration

/-- Every exact circuit implementation of the record phase flip inhabits the
new operator-norm predicate at error exactly zero; see
`QuantumFoundations/Complexity/OperatorNorm/Nonvacuity.lean` for the full
non-vacuity account, including the concrete `1/20` budget and C11's
dynamically generated branches. -/
example (R : ℕ) [NeZero R] :
    ApproximatesRecordPhaseFlipOp
      (sitesEquivR (R + 1)) (noisyReadoutCircuit R) (noisyRecords R 0) 1 0 :=
  implementsRecordPhaseFlip_implies_opApprox_zero
    (sitesEquivR (R + 1)) (noisyReadoutCircuit R) (noisyRecords R 0) 1
    (noisyReadoutCircuit_implements R)

/-- The concrete `1/20` operator-norm error budget already has a robust
proxy-gap consequence, using only the exact C10 readout and monotonicity. -/
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

end OperatorNorm

end

end QuantumFoundations.Complexity
