import QuantumFoundations.Complexity.OperatorNorm.RecordReadout
import QuantumFoundations.Complexity.ApproxRecordPersistence

/-!
# C12d/C12e — Robust distinguishability and proxy gaps from operator-norm error

C12d reuses C8's own analytic distinguishability estimate
(`approx_record_phase_flip_distinguishesAt`) unchanged: the operator-norm
readout threshold is exactly `2 * δ + 2 * ηj + 2 * ε ≤ 2`, i.e. the C8
pointwise threshold `2 * δ + 2 * ηj + ξ ≤ 2` specialized at `ξ = 2 * ε`. No
new analytic estimate is introduced here.

C12e combines this with C8's approximate redundant-record interference lower
bound (`approximate_records_give_interference_lower_bound`) and the existing
proxy-gap/persistence certificates
(`approximate_records_give_proxy_gap_certificate`,
`approximate_records_gap_persists_under_circuit_evolution`), again by direct
specialization at pointwise error `ξ = 2 * ε` — `minCircuitLength` and the C7
conjugation machinery are reused unchanged, not reimplemented.
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

/-! ## C12e — Approximate-record proxy gaps with operator-norm readout -/

/-- Approximate redundant records and a supplied operator-norm-approximate
readout circuit certify a subtraction-free proxy gap.  A direct
specialization of `approximate_records_give_proxy_gap_certificate` at
pointwise error `ξ = 2 * ε`, via `opApprox_implies_pointwise_phaseFlip`. No
`i ≠ j` hypothesis is needed: the underlying C8 certificate does not use
it. -/
theorem approximate_records_opNorm_readout_give_proxy_gap
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K)
    (a b : H (d ^ N))
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (i j : Fin K)
    (ηi ηj ε δ : ℝ)
    (happrox : ApproxRecordedPairOn recs a b i j ηi ηj)
    (hlocal_i : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) i) (regions r))
    (hlocal_j : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : ∀ r r', r ≠ r' → Disjoint (regions r) (regions r'))
    (hinterference : ηi + ηj < 2 * δ)
    (r₀ : Fin R)
    (D : Circuit N d)
    (hOp : ApproximatesRecordPhaseFlipOp e D (recs r₀) j ε)
    (hreadout : 2 * δ + 2 * ηj + 2 * ε ≤ 2)
    (g : ℕ)
    (hgap : Circuit.length D + g ≤ ceilHalf R) :
    HasProxyGapAtLeast e a b δ g :=
  approximate_records_give_proxy_gap_certificate
    e regions recs a b r₀ i j ηi ηj (2 * ε) δ ha hb happrox hlocal_i hlocal_j
    hpairwise hinterference D
    (opApprox_implies_pointwise_phaseFlip e D (recs r₀) j a b ε hOp ha hb)
    hreadout g hgap

/-- The same robust gap holds for the actual exact circuit minima in
`WithTop ℕ`.  Reuses `approximate_records_complexity_gap`; `minCircuitLength`
is not reimplemented. -/
theorem approximate_records_opNorm_readout_complexity_gap
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K)
    (a b : H (d ^ N))
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (i j : Fin K)
    (ηi ηj ε δ : ℝ)
    (happrox : ApproxRecordedPairOn recs a b i j ηi ηj)
    (hlocal_i : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) i) (regions r))
    (hlocal_j : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : ∀ r r', r ≠ r' → Disjoint (regions r) (regions r'))
    (hinterference : ηi + ηj < 2 * δ)
    (r₀ : Fin R)
    (D : Circuit N d)
    (hOp : ApproximatesRecordPhaseFlipOp e D (recs r₀) j ε)
    (hreadout : 2 * δ + 2 * ηj + 2 * ε ≤ 2)
    (g : ℕ)
    (hgap : Circuit.length D + g ≤ ceilHalf R) :
    distinguishabilityComplexity e a b δ + (g : WithTop ℕ) ≤
      interferenceComplexity e a b δ :=
  approximate_records_complexity_gap
    e regions recs a b r₀ i j ηi ηj (2 * ε) δ ha hb happrox hlocal_i hlocal_j
    hpairwise hinterference D
    (opApprox_implies_pointwise_phaseFlip e D (recs r₀) j a b ε hOp ha hb)
    hreadout g hgap

/-! ### C12e.1 — Conditional persistence -/

/-- The robust proxy gap persists through a further finite `2`-local circuit
`E`, given the extra budget `4 * E.length`.  Built in two steps exactly as
prescribed: the initial gap certificate uses the new operator-norm readout
theorem, then the existing C7/C8 persistence machinery
(`approximate_records_gap_persists_under_circuit_evolution`) transports it.
The approximate readout operator itself is never evolved or conjugated; only
the resulting gap certificate is transported. -/
theorem approximate_records_opNorm_gap_persists_under_circuit
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K)
    (a b : H (d ^ N))
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (i j : Fin K)
    (ηi ηj ε δ : ℝ)
    (happrox : ApproxRecordedPairOn recs a b i j ηi ηj)
    (hlocal_i : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) i) (regions r))
    (hlocal_j : ∀ r, IsLocalTo
      (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : ∀ r r', r ≠ r' → Disjoint (regions r) (regions r'))
    (hinterference : ηi + ηj < 2 * δ)
    (r₀ : Fin R)
    (D : Circuit N d)
    (hOp : ApproximatesRecordPhaseFlipOp e D (recs r₀) j ε)
    (hreadout : 2 * δ + 2 * ηj + 2 * ε ≤ 2)
    (E : Circuit N d) (g : ℕ)
    (hbudget : Circuit.length D + 4 * Circuit.length E + g ≤ ceilHalf R) :
    HasProxyGapAtLeast e
      (Circuit.evalOnH E e a) (Circuit.evalOnH E e b) δ g :=
  approximate_records_gap_persists_under_circuit_evolution
    e regions recs a b r₀ i j ηi ηj (2 * ε) δ ha hb happrox hlocal_i hlocal_j
    hpairwise hinterference D
    (opApprox_implies_pointwise_phaseFlip e D (recs r₀) j a b ε hOp ha hb)
    hreadout E g hbudget

#print axioms approximate_records_opNorm_readout_give_proxy_gap
#print axioms approximate_records_opNorm_gap_persists_under_circuit

end

end QuantumFoundations.Complexity.OperatorNorm
