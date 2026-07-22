import QuantumFoundations.Complexity.SimulatedEvolution.NoisyRepetition
import QuantumFoundations.Complexity.OperatorNorm.GeneratedBranches

/-!
# C13h — Dynamically generated branches under simulated evolution

Connects C11's unitary branch generation
(`noisyMeasurement_generates_branching`, unchanged) to the C13g simulated-
evolution persistence theorem. The proxy gap concerns the *normalized*
generated branch pair `noisyZeroBranch p R`/`noisyOneBranch p R` evolved
under `U`, not the `q`-scaled global superposition — no separate scaling
theorem for `HasProxyGapAtLeast` on scaled vectors has been proved, and none
is claimed here.
-/

namespace QuantumFoundations.Complexity.SimulatedEvolution

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.RepetitionModel
open QuantumFoundations.Complexity.NoisyRepetitionModel
open QuantumFoundations.Complexity.MeasurementGeneration
open QuantumFoundations.Complexity.OperatorNorm

noncomputable section

/-- End-to-end theorem: the exact C11 generation equality, nonzero
generated components (given nonzero source amplitudes), and the
central-threshold proxy gap for the simulated-evolution-evolved generated
branch pair. -/
theorem generated_branches_persist_under_simulated_evolution
    (p : NoiseProfile) (R : ℕ) [NeZero R]
    (D : Circuit (R + 1) 2) (ρ δ μ : ℝ)
    (hMuNonneg : 0 ≤ μ) (hMuLe : μ ≤ δ)
    (hInterference : 4 * ‖p.leak‖ < 2 * (δ - μ))
    (hReadout : 2 * (δ + μ) + 4 * ‖p.leak‖ + 2 * ρ ≤ 2)
    (hOp : ApproximatesRecordPhaseFlipOp
      (sitesEquivR (R + 1)) D (noisyRecords R 0) 1 ρ)
    (q : SourceAmplitudeProfile) (hq0 : q.amp0 ≠ 0) (hq1 : q.amp1 ≠ 0)
    (U : NormPreservingEvolution (H (2 ^ (R + 1))))
    (t : ℝ) (E : Circuit (R + 1) 2) (ε : ℝ)
    (hSim : CircuitSimulatesEvolutionAt U (sitesEquivR (R + 1)) t E ε)
    (hError : 2 * ε ≤ μ)
    (g : ℕ) (hBudget : Circuit.length D + 4 * Circuit.length E + g ≤ ceilHalf R) :
    Circuit.evalOnH (noisyMeasurementCircuit p R) (sitesEquivR (R + 1))
        (noisySourceInputState q R) =
      q.amp0 • noisyZeroBranch p R + q.amp1 • noisyOneBranch p R
    ∧
    rproj (sourceResolution R) 0 (noisySourceGeneratedState q p R) ≠ 0
    ∧
    rproj (sourceResolution R) 1 (noisySourceGeneratedState q p R) ≠ 0
    ∧
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      (U.evolve t (noisyZeroBranch p R)) (U.evolve t (noisyOneBranch p R)) δ g :=
  ⟨noisyMeasurement_generates_branching q.amp0 q.amp1 p R,
    noisy_source_zero_component_ne_zero q p R hq0,
    noisy_source_one_component_ne_zero q p R hq1,
    noisy_repetition_gap_persists_under_simulated_evolution p R D ρ δ μ
      hMuNonneg hMuLe hInterference hReadout hOp U t E ε hSim hError g hBudget⟩

/-- The evolved global generated state decomposes linearly into its two
evolved branch components. -/
theorem evolved_generated_state_decomposition
    (p : NoiseProfile) (R : ℕ) [NeZero R] (q : SourceAmplitudeProfile)
    (U : NormPreservingEvolution (H (2 ^ (R + 1)))) (t : ℝ) :
    U.evolve t (q.amp0 • noisyZeroBranch p R + q.amp1 • noisyOneBranch p R) =
      q.amp0 • U.evolve t (noisyZeroBranch p R) +
        q.amp1 • U.evolve t (noisyOneBranch p R) := by
  simp [map_add, map_smul]

#print axioms generated_branches_persist_under_simulated_evolution
#print axioms evolved_generated_state_decomposition

end

end QuantumFoundations.Complexity.SimulatedEvolution
