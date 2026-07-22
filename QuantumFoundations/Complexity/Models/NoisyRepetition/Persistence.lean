import QuantumFoundations.Complexity.Models.NoisyRepetition.Interference
import QuantumFoundations.Complexity.ApproxBranchGap
import QuantumFoundations.Complexity.ApproxRecordPersistence

/-!
# C10g — Robust proxy gap and conditional persistence

The noisy model's approximate records (C10c), one-gate readout (C10d), and
robust error thresholds (C10e) instantiate the generic C8 proxy-gap and
persistence theorems directly.  Persistence concerns the initial proxy gap
transported through a supplied finite circuit; the evolved states are not
claimed to retain the same approximate-record identities.
-/

namespace QuantumFoundations.Complexity.NoisyRepetitionModel

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.RepetitionModel

noncomputable section

private theorem interference_threshold (p : NoiseProfile) (hp : p.IsRobust) :
    2 * ‖p.leak‖ + 2 * ‖p.leak‖ < 2 * (1 / 2 : ℝ) := by
  unfold NoiseProfile.IsRobust at hp
  linarith

private theorem distinguishability_threshold (p : NoiseProfile) (hp : p.IsRobust) :
    2 * (1 / 2 : ℝ) + 2 * (2 * ‖p.leak‖) + 0 ≤ 2 := by
  unfold NoiseProfile.IsRobust at hp
  linarith

/-! ## C10g.1 — Static robust proxy gap -/

/-- The robust noisy repetition model certifies a subtraction-free proxy gap
`g` whenever the record budget covers the one-gate readout and the requested
gap. -/
theorem noisy_repetition_has_proxy_gap
    (p : NoiseProfile) (hp : p.IsRobust) (R : ℕ) [NeZero R]
    (g : ℕ) (hg : 1 + g ≤ ceilHalf R) :
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      (noisyZeroBranch p R) (noisyOneBranch p R) (1 / 2 : ℝ) g :=
  approximate_records_give_proxy_gap_certificate
    (sitesEquivR (R + 1)) (noisyRegions R) (noisyRecords R)
    (noisyZeroBranch p R) (noisyOneBranch p R) (0 : Fin R) 0 1
    (2 * ‖p.leak‖) (2 * ‖p.leak‖) 0 (1 / 2 : ℝ)
    (noisyZeroBranch_norm p R) (noisyOneBranch_norm p R)
    (noisy_repetition_approxRecordedPairOn p R)
    (fun r => noisyRecordProj_local_zero r) (fun r => noisyRecordProj_local_one r)
    noisyRegions_pairwise_disjoint
    (interference_threshold p hp)
    (noisyReadoutCircuit R) (noisyReadoutCircuit_approximatesRecordPhaseFlipOn p R)
    (distinguishability_threshold p hp)
    g (by rw [noisyReadoutCircuit_length]; exact hg)

/-- Minimum-level subtraction-free gap for the noisy model. -/
theorem noisy_repetition_complexity_gap
    (p : NoiseProfile) (hp : p.IsRobust) (R : ℕ) [NeZero R]
    (g : ℕ) (hg : 1 + g ≤ ceilHalf R) :
    distinguishabilityComplexity (sitesEquivR (R + 1))
        (noisyZeroBranch p R) (noisyOneBranch p R) (1 / 2 : ℝ) + (g : WithTop ℕ)
      ≤ interferenceComplexity (sitesEquivR (R + 1))
        (noisyZeroBranch p R) (noisyOneBranch p R) (1 / 2 : ℝ) :=
  approximate_records_complexity_gap
    (sitesEquivR (R + 1)) (noisyRegions R) (noisyRecords R)
    (noisyZeroBranch p R) (noisyOneBranch p R) (0 : Fin R) 0 1
    (2 * ‖p.leak‖) (2 * ‖p.leak‖) 0 (1 / 2 : ℝ)
    (noisyZeroBranch_norm p R) (noisyOneBranch_norm p R)
    (noisy_repetition_approxRecordedPairOn p R)
    (fun r => noisyRecordProj_local_zero r) (fun r => noisyRecordProj_local_one r)
    noisyRegions_pairwise_disjoint
    (interference_threshold p hp)
    (noisyReadoutCircuit R) (noisyReadoutCircuit_approximatesRecordPhaseFlipOn p R)
    (distinguishability_threshold p hp)
    g (by rw [noisyReadoutCircuit_length]; exact hg)

/-! ## C10g.2 — Conditional persistence under circuit evolution -/

/-- The robust noisy proxy gap persists through an arbitrary finite `2`-local
circuit evolution, as long as the record budget also covers four times the
evolution length (the reversible-conjugation overhead). The evolved states
are not claimed to retain the same approximate-record identities: only the
initial proxy-gap certificate is transported. -/
theorem noisy_repetition_gap_persists_under_circuit
    (p : NoiseProfile) (hp : p.IsRobust) (R : ℕ) [NeZero R]
    (E : Circuit (R + 1) 2) (g : ℕ)
    (hbudget : 1 + 4 * E.length + g ≤ ceilHalf R) :
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      (Circuit.evalOnH E (sitesEquivR (R + 1)) (noisyZeroBranch p R))
      (Circuit.evalOnH E (sitesEquivR (R + 1)) (noisyOneBranch p R))
      (1 / 2 : ℝ) g :=
  approximate_records_gap_persists_under_circuit_evolution
    (sitesEquivR (R + 1)) (noisyRegions R) (noisyRecords R)
    (noisyZeroBranch p R) (noisyOneBranch p R) (0 : Fin R) 0 1
    (2 * ‖p.leak‖) (2 * ‖p.leak‖) 0 (1 / 2 : ℝ)
    (noisyZeroBranch_norm p R) (noisyOneBranch_norm p R)
    (noisy_repetition_approxRecordedPairOn p R)
    (fun r => noisyRecordProj_local_zero r) (fun r => noisyRecordProj_local_one r)
    noisyRegions_pairwise_disjoint
    (interference_threshold p hp)
    (noisyReadoutCircuit R) (noisyReadoutCircuit_approximatesRecordPhaseFlipOn p R)
    (distinguishability_threshold p hp)
    E g (by rw [noisyReadoutCircuit_length]; exact hbudget)

/-- Three or more record qubits already give a nonzero robust proxy gap: the
same minimal record-count bound as the exact C9 model, since `ceilHalf` only
depends on the record count `R`. -/
theorem noisy_repetition_positive_gap
    (p : NoiseProfile) (hp : p.IsRobust) (R : ℕ) (hR : 3 ≤ R) :
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      (noisyZeroBranch p R) (noisyOneBranch p R) (1 / 2 : ℝ) 1 := by
  letI : NeZero R := ⟨by omega⟩
  apply noisy_repetition_has_proxy_gap p hp R 1
  unfold ceilHalf
  omega

#print axioms noisy_repetition_has_proxy_gap
#print axioms noisy_repetition_gap_persists_under_circuit

end

end QuantumFoundations.Complexity.NoisyRepetitionModel
