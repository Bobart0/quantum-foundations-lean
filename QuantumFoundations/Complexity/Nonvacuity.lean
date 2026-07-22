import QuantumFoundations.Complexity.ApproxRecordPersistence
import QuantumFoundations.Complexity.Models.Repetition.Persistence
import QuantumFoundations.Complexity.Models.NoisyRepetition.ConcreteNoise

/-!
# C0/C6/C7/C8/C9/C10 — Non-vacuity

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

end

end QuantumFoundations.Complexity
