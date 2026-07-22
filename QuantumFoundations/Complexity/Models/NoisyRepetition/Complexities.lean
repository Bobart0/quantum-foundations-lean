import QuantumFoundations.Complexity.Models.NoisyRepetition.Readout
import QuantumFoundations.Complexity.ApproxRecordInterferenceBound
import QuantumFoundations.Complexity.Models.Repetition.Distinguishability

/-!
# C10e — Robust complexity separation at threshold `δ = 1/2`

At threshold `δ = 1 / 2`, the C8 interference-lower-bound threshold
`ηi + ηj < 2 * δ` becomes exactly `4 * ‖leak‖ < 1`, i.e. `NoiseProfile.IsRobust`.
The C8 distinguishability threshold `2 * δ + 2 * ηj + ξ ≤ 2` becomes
`1 + 4 * ‖leak‖ ≤ 2`, which the (strict) robust condition also implies.  Both
robust theorems are therefore direct instantiations of the C8 machinery.
-/

namespace QuantumFoundations.Complexity.NoisyRepetitionModel

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.RepetitionModel

noncomputable section

/-- Robust noise gives the strict C8 interference threshold at
`δ = 1 / 2`. -/
private theorem interference_threshold_of_isRobust {p : NoiseProfile}
    (hp : p.IsRobust) : 2 * ‖p.leak‖ + 2 * ‖p.leak‖ < 2 * (1 / 2 : ℝ) := by
  unfold NoiseProfile.IsRobust at hp
  linarith

/-- Robust noise gives the C8 distinguishability threshold at `δ = 1 / 2`
(readout error `ξ = 0`). -/
private theorem distinguishability_threshold_of_isRobust {p : NoiseProfile}
    (hp : p.IsRobust) :
    2 * (1 / 2 : ℝ) + 2 * (2 * ‖p.leak‖) + 0 ≤ 2 := by
  unfold NoiseProfile.IsRobust at hp
  linarith

/-- Interference lower bound: `R` disjoint approximate records force
`ceilHalf R ≤ C_I` whenever the noise is robust. -/
theorem noisy_repetition_interference_lower
    (p : NoiseProfile) (R : ℕ) [NeZero R] (hp : p.IsRobust) :
    (ceilHalf R : WithTop ℕ) ≤
      interferenceComplexity (sitesEquivR (R + 1))
        (noisyZeroBranch p R) (noisyOneBranch p R) (1 / 2 : ℝ) :=
  approximate_records_interferenceComplexity_lower_bound
    (sitesEquivR (R + 1)) (noisyRegions R) (noisyRecords R)
    (noisyZeroBranch p R) (noisyOneBranch p R) 0 1
    (2 * ‖p.leak‖) (2 * ‖p.leak‖) (1 / 2 : ℝ)
    (noisyZeroBranch_norm p R) (noisyOneBranch_norm p R)
    (noisy_repetition_approxRecordedPairOn p R)
    (fun r => noisyRecordProj_local_zero r) (fun r => noisyRecordProj_local_one r)
    noisyRegions_pairwise_disjoint
    (interference_threshold_of_isRobust hp)

/-- Distinguishability upper bound: the one-gate readout upper-bounds the
actual complexity by `1`, whenever the noise is robust. -/
theorem noisy_repetition_distinguishability_upper
    (p : NoiseProfile) (R : ℕ) [NeZero R] (hp : p.IsRobust) :
    distinguishabilityComplexity (sitesEquivR (R + 1))
        (noisyZeroBranch p R) (noisyOneBranch p R) (1 / 2 : ℝ)
      ≤ (1 : WithTop ℕ) := by
  have h := approx_record_phase_flip_complexity_upper_bound
    (sitesEquivR (R + 1)) (noisyReadoutCircuit R) (noisyRecords R 0) 1
    (noisyZeroBranch p R) (noisyOneBranch p R) (2 * ‖p.leak‖) 0 (1 / 2 : ℝ)
    (noisyZeroBranch_norm p R) (noisyOneBranch_norm p R)
    (noisy_repetition_approxRecordedPairOn p R 0).2
    (noisyReadoutCircuit_approximatesRecordPhaseFlipOn p R)
    (distinguishability_threshold_of_isRobust hp)
  rwa [noisyReadoutCircuit_length] at h

/-- The exact distinguishability complexity of the two noisy branches at
threshold `δ = 1 / 2` is exactly one gate, whenever the noise is robust. -/
theorem noisy_repetition_distinguishabilityComplexity
    (p : NoiseProfile) (R : ℕ) [NeZero R] (hp : p.IsRobust) :
    distinguishabilityComplexity (sitesEquivR (R + 1))
        (noisyZeroBranch p R) (noisyOneBranch p R) (1 / 2 : ℝ)
      = (1 : WithTop ℕ) :=
  le_antisymm (noisy_repetition_distinguishability_upper p R hp)
    (one_le_distinguishabilityComplexity_of_pos (sitesEquivR (R + 1))
      (noisyZeroBranch p R) (noisyOneBranch p R)
      (noisyZeroBranch_norm p R) (noisyOneBranch_norm p R) (1 / 2 : ℝ) (by norm_num))

end

end QuantumFoundations.Complexity.NoisyRepetitionModel
