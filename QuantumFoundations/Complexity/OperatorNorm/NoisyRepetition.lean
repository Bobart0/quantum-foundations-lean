import QuantumFoundations.Complexity.OperatorNorm.RecordGap
import QuantumFoundations.Complexity.Models.NoisyRepetition.Persistence

/-!
# C12f — Noisy repetition model corollaries with operator-norm readout

Instantiates C12e at the C10 noisy model: `a := noisyZeroBranch p R`,
`b := noisyOneBranch p R`, `ηi = ηj := 2 * ‖p.leak‖`, `δ := 1 / 2`. The
interference threshold remains `4 * ‖p.leak‖ < 1` (`p.IsRobust`); the
operator-norm readout threshold becomes
`2 * (1/2) + 2 * (2 * ‖p.leak‖) + 2 * ε ≤ 2`, i.e. `4 * ‖p.leak‖ + 2 * ε ≤ 1`.

**On the retained `hp : p.IsRobust` hypothesis.** `hreadout` alone
(`4 * ‖p.leak‖ + 2 * ε ≤ 1`) together with `ε ≥ 0` (itself only derivable
from `hOp` being inhabited, since operator-norm errors are nonnegative)
gives only the *non-strict* bound `4 * ‖p.leak‖ ≤ 1`. The interference
argument genuinely needs the *strict* inequality `4 * ‖p.leak‖ < 1`
(`p.IsRobust`): at the boundary `4 * ‖p.leak‖ = 1`, `ε = 0`, `hreadout`
holds with equality but `p.IsRobust` fails, and the underlying C4/C8
pigeonhole argument (`ηi + ηj < 2 * δ`, strict) does not go through at
equality. `hp` is therefore *not* redundant given `hreadout`, and is kept as
an explicit hypothesis of the primary theorem rather than derived.
-/

namespace QuantumFoundations.Complexity.OperatorNorm

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.RepetitionModel
open QuantumFoundations.Complexity.NoisyRepetitionModel

noncomputable section

/-- The robust noisy repetition model certifies a subtraction-free proxy gap
under an operator-norm-approximate readout circuit, whenever the combined
threshold `4 * ‖p.leak‖ + 2 * ε ≤ 1` holds. -/
theorem noisy_repetition_opNorm_readout_has_gap
    (p : NoiseProfile) (hp : p.IsRobust) (R : ℕ) [NeZero R]
    (D : Circuit (R + 1) 2) (ε : ℝ)
    (hOp : ApproximatesRecordPhaseFlipOp
      (sitesEquivR (R + 1)) D (noisyRecords R 0) 1 ε)
    (hreadout : 4 * ‖p.leak‖ + 2 * ε ≤ 1)
    (g : ℕ) (hgap : Circuit.length D + g ≤ ceilHalf R) :
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      (noisyZeroBranch p R) (noisyOneBranch p R) (1 / 2 : ℝ) g := by
  have hinterference : (2 * ‖p.leak‖) + (2 * ‖p.leak‖) < 2 * (1 / 2 : ℝ) := by
    have hrobust := hp
    unfold NoiseProfile.IsRobust at hrobust
    linarith
  have hthreshold :
      2 * (1 / 2 : ℝ) + 2 * (2 * ‖p.leak‖) + 2 * ε ≤ 2 := by linarith
  exact approximate_records_opNorm_readout_give_proxy_gap
    (sitesEquivR (R + 1)) (noisyRegions R) (noisyRecords R)
    (noisyZeroBranch p R) (noisyOneBranch p R)
    (noisyZeroBranch_norm p R) (noisyOneBranch_norm p R)
    (0 : Fin 2) 1
    (2 * ‖p.leak‖) (2 * ‖p.leak‖) ε (1 / 2 : ℝ)
    (noisy_repetition_approxRecordedPairOn p R)
    (fun r => noisyRecordProj_local_zero r) (fun r => noisyRecordProj_local_one r)
    noisyRegions_pairwise_disjoint hinterference
    (0 : Fin R) D hOp hthreshold g hgap

/-- The robust operator-norm-readout proxy gap persists through a further
finite `2`-local circuit, given the extra record budget `4 * E.length`. -/
theorem noisy_repetition_opNorm_gap_persists
    (p : NoiseProfile) (hp : p.IsRobust) (R : ℕ) [NeZero R]
    (D : Circuit (R + 1) 2) (ε : ℝ)
    (hOp : ApproximatesRecordPhaseFlipOp
      (sitesEquivR (R + 1)) D (noisyRecords R 0) 1 ε)
    (hreadout : 4 * ‖p.leak‖ + 2 * ε ≤ 1)
    (E : Circuit (R + 1) 2) (g : ℕ)
    (hbudget : Circuit.length D + 4 * Circuit.length E + g ≤ ceilHalf R) :
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      (Circuit.evalOnH E (sitesEquivR (R + 1)) (noisyZeroBranch p R))
      (Circuit.evalOnH E (sitesEquivR (R + 1)) (noisyOneBranch p R))
      (1 / 2 : ℝ) g := by
  have hinterference : (2 * ‖p.leak‖) + (2 * ‖p.leak‖) < 2 * (1 / 2 : ℝ) := by
    have hrobust := hp
    unfold NoiseProfile.IsRobust at hrobust
    linarith
  have hthreshold :
      2 * (1 / 2 : ℝ) + 2 * (2 * ‖p.leak‖) + 2 * ε ≤ 2 := by linarith
  exact approximate_records_opNorm_gap_persists_under_circuit
    (sitesEquivR (R + 1)) (noisyRegions R) (noisyRecords R)
    (noisyZeroBranch p R) (noisyOneBranch p R)
    (noisyZeroBranch_norm p R) (noisyOneBranch_norm p R)
    (0 : Fin 2) 1
    (2 * ‖p.leak‖) (2 * ‖p.leak‖) ε (1 / 2 : ℝ)
    (noisy_repetition_approxRecordedPairOn p R)
    (fun r => noisyRecordProj_local_zero r) (fun r => noisyRecordProj_local_one r)
    noisyRegions_pairwise_disjoint hinterference
    (0 : Fin R) D hOp hthreshold E g hbudget

/-- Regression: the exact one-gate readout circuit at operator-norm error
`ε = 0` recovers exactly the existing C10 theorem
`noisy_repetition_has_proxy_gap`. -/
theorem noisy_repetition_opNorm_readout_exact_regression
    (p : NoiseProfile) (hp : p.IsRobust) (R : ℕ) [NeZero R]
    (g : ℕ) (hgap : (noisyReadoutCircuit R).length + g ≤ ceilHalf R) :
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      (noisyZeroBranch p R) (noisyOneBranch p R) (1 / 2 : ℝ) g := by
  have hOp : ApproximatesRecordPhaseFlipOp
      (sitesEquivR (R + 1)) (noisyReadoutCircuit R) (noisyRecords R 0) 1 0 :=
    implementsRecordPhaseFlip_implies_opApprox_zero
      (sitesEquivR (R + 1)) (noisyReadoutCircuit R) (noisyRecords R 0) 1
      (noisyReadoutCircuit_implements R)
  have hreadout : 4 * ‖p.leak‖ + 2 * (0 : ℝ) ≤ 1 := by
    have hrobust := hp
    unfold NoiseProfile.IsRobust at hrobust
    linarith
  exact noisy_repetition_opNorm_readout_has_gap p hp R
    (noisyReadoutCircuit R) 0 hOp hreadout g hgap

#print axioms noisy_repetition_opNorm_readout_has_gap
#print axioms noisy_repetition_opNorm_gap_persists

end

end QuantumFoundations.Complexity.OperatorNorm
