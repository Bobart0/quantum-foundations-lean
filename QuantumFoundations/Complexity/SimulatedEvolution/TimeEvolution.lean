import QuantumFoundations.Complexity.SimulatedEvolution.NoisyRepetition

/-!
# C13j — Time-dependent simulation cost

`HasCircuitSimulationBound` packages a *supplied* cost function `cost : ℝ →
ℕ` and error function `error : ℝ → ℝ`, one simulation certificate per time
`t`. No asymptotic growth (`O(t)`, linear, or otherwise) is claimed or
assumed about `cost`/`error`: both are arbitrary functions, exactly as
supplied. `gap_persists_at_time_of_simulation_bound` is the direct
time-indexed specialization of C13f's cost-bounded persistence theorem; the
noisy-model specialization instantiates the generic margin certificate with
the explicit `ceilHalf R` record-budget bound used throughout C8–C13.
-/

namespace QuantumFoundations.Complexity.SimulatedEvolution

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.RepetitionModel
open QuantumFoundations.Complexity.NoisyRepetitionModel
open QuantumFoundations.Complexity.OperatorNorm

noncomputable section

/-! ## C13j.1 — The generic time-dependent cost interface -/

/-- A time-dependent simulation-cost/error bound: at every time `t`, some
circuit of length at most `cost t` simulates `U` at time `t` with error at
most `error t`. -/
def HasCircuitSimulationBound {N d : ℕ}
    (U : NormPreservingEvolution (H (d ^ N)))
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (cost : ℝ → ℕ) (error : ℝ → ℝ) : Prop :=
  ∀ t, HasCircuitSimulationAt U e t (cost t) (error t)

/-- Persistence expressed directly through the time-dependent simulation
cost and error at a single time `t`, given the available record redundancy
as a margin certificate at cost `4 * cost t + g`. -/
theorem gap_persists_at_time_of_simulation_bound {N d : ℕ}
    (U : NormPreservingEvolution (H (d ^ N)))
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (a b : H (d ^ N)) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (δ μ : ℝ) (g : ℕ) (cost : ℝ → ℕ) (error : ℝ → ℝ) (t : ℝ)
    (hSimulation : HasCircuitSimulationBound U e cost error)
    (hGap : HasProxyGapMarginAtLeast e a b δ μ (4 * cost t + g))
    (hError : 2 * error t ≤ μ) :
    HasProxyGapAtLeast e (U.evolve t a) (U.evolve t b) δ g :=
  margin_gap_persists_of_hasCircuitSimulationAt U e a b ha hb δ μ (error t) g
    (cost t) t (hSimulation t) hGap hError

/-! ## C13j.2 — Noisy-model specialization -/

/-- The noisy repetition model's proxy gap, expressed through a
time-dependent simulation-cost bound and the explicit `ceilHalf R`
record-budget inequality. -/
theorem noisy_repetition_gap_persists_at_time_of_simulation_bound
    (p : NoiseProfile) (R : ℕ) [NeZero R]
    (D : Circuit (R + 1) 2) (ρ δ μ : ℝ)
    (hMuNonneg : 0 ≤ μ) (hMuLe : μ ≤ δ)
    (hInterference : 4 * ‖p.leak‖ < 2 * (δ - μ))
    (hReadout : 2 * (δ + μ) + 4 * ‖p.leak‖ + 2 * ρ ≤ 2)
    (hOp : ApproximatesRecordPhaseFlipOp
      (sitesEquivR (R + 1)) D (noisyRecords R 0) 1 ρ)
    (U : NormPreservingEvolution (H (2 ^ (R + 1))))
    (cost : ℝ → ℕ) (error : ℝ → ℝ) (t : ℝ)
    (hSimulation : HasCircuitSimulationBound U (sitesEquivR (R + 1)) cost error)
    (hError : 2 * error t ≤ μ)
    (g : ℕ) (hBudget : Circuit.length D + 4 * cost t + g ≤ ceilHalf R) :
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      (U.evolve t (noisyZeroBranch p R)) (U.evolve t (noisyOneBranch p R)) δ g := by
  have hGap := noisy_repetition_has_margin_gap p R D ρ δ μ hMuNonneg hMuLe
    hInterference hReadout hOp (4 * cost t + g) (by omega)
  exact gap_persists_at_time_of_simulation_bound U (sitesEquivR (R + 1))
    (noisyZeroBranch p R) (noisyOneBranch p R)
    (noisyZeroBranch_norm p R) (noisyOneBranch_norm p R)
    δ μ g cost error t hSimulation hGap hError

#print axioms gap_persists_at_time_of_simulation_bound
#print axioms noisy_repetition_gap_persists_at_time_of_simulation_bound

end

end QuantumFoundations.Complexity.SimulatedEvolution
