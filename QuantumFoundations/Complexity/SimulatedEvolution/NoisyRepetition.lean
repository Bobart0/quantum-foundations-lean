import QuantumFoundations.Complexity.SimulatedEvolution.SimulationCertificate
import QuantumFoundations.Complexity.OperatorNorm.NoisyRepetition

/-!
# C13g — Noisy repetition model with a threshold margin

Instantiates the C13d margin certificate at the C10 noisy model (`a :=
noisyZeroBranch p R`, `b := noisyOneBranch p R`, `ηi = ηj := 2 * ‖p.leak‖`),
reusing C8's interference lower bound at `δ - μ` and C12's operator-norm
readout distinguishability upper bound at `δ + μ` independently — neither
amplitude estimate is reproved. The interference condition becomes
`4 * ‖p.leak‖ < 2 * (δ - μ)`; the readout condition becomes
`2 * (δ + μ) + 4 * ‖p.leak‖ + 2 * ρ ≤ 2`, where `ρ` is the operator-norm
error of the supplied readout circuit `D` (distinct from the evolution
simulation error `ε` used afterward).
-/

namespace QuantumFoundations.Complexity.SimulatedEvolution

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.RepetitionModel
open QuantumFoundations.Complexity.NoisyRepetitionModel
open QuantumFoundations.Complexity.OperatorNorm

noncomputable section

/-! ## C13g.1 — Static margin certificate -/

/-- The noisy repetition model certifies a threshold-margin proxy gap under
an operator-norm-approximate readout circuit. -/
theorem noisy_repetition_has_margin_gap
    (p : NoiseProfile) (R : ℕ) [NeZero R]
    (D : Circuit (R + 1) 2) (ρ δ μ : ℝ)
    (_hMuNonneg : 0 ≤ μ) (_hMuLe : μ ≤ δ)
    (hInterference : 4 * ‖p.leak‖ < 2 * (δ - μ))
    (hReadout : 2 * (δ + μ) + 4 * ‖p.leak‖ + 2 * ρ ≤ 2)
    (hOp : ApproximatesRecordPhaseFlipOp
      (sitesEquivR (R + 1)) D (noisyRecords R 0) 1 ρ)
    (g : ℕ) (hBudget : Circuit.length D + g ≤ ceilHalf R) :
    HasProxyGapMarginAtLeast (sitesEquivR (R + 1))
      (noisyZeroBranch p R) (noisyOneBranch p R) δ μ g := by
  refine ⟨ceilHalf R, Circuit.length D, ?_, ?_, hBudget⟩
  · exact approximate_records_give_interference_lower_bound
      (sitesEquivR (R + 1)) (noisyRegions R) (noisyRecords R)
      (noisyZeroBranch p R) (noisyOneBranch p R) 0 1
      (2 * ‖p.leak‖) (2 * ‖p.leak‖) (δ - μ)
      (noisyZeroBranch_norm p R) (noisyOneBranch_norm p R)
      (noisy_repetition_approxRecordedPairOn p R)
      (fun r => noisyRecordProj_local_zero r) (fun r => noisyRecordProj_local_one r)
      noisyRegions_pairwise_disjoint (by linarith)
  · exact opApprox_record_phase_flip_gives_upper_bound
      (sitesEquivR (R + 1)) D (noisyRecords R 0) 1
      (noisyZeroBranch p R) (noisyOneBranch p R) (2 * ‖p.leak‖) ρ (δ + μ)
      (noisyZeroBranch_norm p R) (noisyOneBranch_norm p R)
      (noisy_repetition_approxRecordedPairOn p R 0).2 hOp (by linarith)

/-! ## C13g.2 — Simulated-evolution specialization -/

/-- The principal model-level C13 result: the noisy model's margin gap
persists under a norm-preserving evolution `U` simulated at time `t` by a
finite circuit `E`, giving an ordinary central-threshold proxy gap for the
`U`-evolved noisy branches. -/
theorem noisy_repetition_gap_persists_under_simulated_evolution
    (p : NoiseProfile) (R : ℕ) [NeZero R]
    (D : Circuit (R + 1) 2) (ρ δ μ : ℝ)
    (hMuNonneg : 0 ≤ μ) (hMuLe : μ ≤ δ)
    (hInterference : 4 * ‖p.leak‖ < 2 * (δ - μ))
    (hReadout : 2 * (δ + μ) + 4 * ‖p.leak‖ + 2 * ρ ≤ 2)
    (hOp : ApproximatesRecordPhaseFlipOp
      (sitesEquivR (R + 1)) D (noisyRecords R 0) 1 ρ)
    (U : NormPreservingEvolution (H (2 ^ (R + 1))))
    (t : ℝ) (E : Circuit (R + 1) 2) (ε : ℝ)
    (hSim : CircuitSimulatesEvolutionAt U (sitesEquivR (R + 1)) t E ε)
    (hError : 2 * ε ≤ μ)
    (g : ℕ) (hBudget : Circuit.length D + 4 * Circuit.length E + g ≤ ceilHalf R) :
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      (U.evolve t (noisyZeroBranch p R)) (U.evolve t (noisyOneBranch p R)) δ g := by
  have hGap := noisy_repetition_has_margin_gap p R D ρ δ μ hMuNonneg hMuLe
    hInterference hReadout hOp (4 * Circuit.length E + g) (by omega)
  exact margin_gap_persists_under_simulated_evolution U (sitesEquivR (R + 1))
    (noisyZeroBranch p R) (noisyOneBranch p R)
    (noisyZeroBranch_norm p R) (noisyOneBranch_norm p R)
    δ μ ε g t E hGap hSim hError

#print axioms noisy_repetition_has_margin_gap
#print axioms noisy_repetition_gap_persists_under_simulated_evolution

end

end QuantumFoundations.Complexity.SimulatedEvolution
