import QuantumFoundations.BornRule.RestrictedRecordSectors.StabilityOperatorNorm
import QuantumFoundations.Complexity.SimulatedEvolution.SimulationCertificate

/-!
# C17b — Stability under circuit-simulated evolution

A C13 simulation certificate controls the state-vector error in operator
norm.  The fixed-sector C17b bridge therefore controls the change of the
quadratic weight of every fixed sector.  No claim is made here that the
sector remains dynamically selected as a record sector.
-/

namespace QuantumFoundations.BornRule.RestrictedRecordSectors

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.OperatorNorm
open QuantumFoundations.Complexity.SimulatedEvolution
open scoped BigOperators InnerProductSpace

noncomputable section

/-- A C13 circuit simulation with operator-norm error `ε` changes the
quadratic weight of any fixed sector by at most `2 * ε` on a normalized
input. -/
theorem sector_weight_stability_under_circuit_simulation
    {N d : ℕ}
    (U : NormPreservingEvolution (H (d ^ N)))
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (t : ℝ)
    (C : Circuit N d)
    (ε : ℝ)
    (R : Submodule ℂ (H (d ^ N)))
    (ψ : H (d ^ N))
    (hψ : ‖ψ‖ = 1)
    (hSim : CircuitSimulatesEvolutionAt U e t C ε) :
    |‖R.starProjection (U.evolve t ψ)‖ ^ 2 -
        ‖R.starProjection (circuitCLMOnH C e ψ)‖ ^ 2|
      ≤ 2 * ε := by
  have hU : ‖U.evolve t ψ‖ = 1 := (U.norm_apply t ψ).trans hψ
  have hC : ‖circuitCLMOnH C e ψ‖ = 1 :=
    (circuitCLMOnH_isNormPreserving C e ψ).trans hψ
  calc
    |‖R.starProjection (U.evolve t ψ)‖ ^ 2 -
        ‖R.starProjection (circuitCLMOnH C e ψ)‖ ^ 2|
        ≤ 2 * ‖U.evolve t ψ - circuitCLMOnH C e ψ‖ :=
      projected_weight_stability_same_sector_of_normalized R _ _ hU hC
    _ ≤ 2 * ε :=
      mul_le_mul_of_nonneg_left
        (norm_apply_sub_le_of_unit hSim hψ) (by norm_num)

/-- Bounded-cost form of fixed-sector stability, using the circuit already
contained in a C13 `HasCircuitSimulationAt` certificate. -/
theorem sector_weight_stability_of_hasCircuitSimulationAt
    {N d : ℕ}
    (U : NormPreservingEvolution (H (d ^ N)))
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (t : ℝ)
    (L : ℕ)
    (ε : ℝ)
    (R : Submodule ℂ (H (d ^ N)))
    (ψ : H (d ^ N))
    (hψ : ‖ψ‖ = 1)
    (hSim : HasCircuitSimulationAt U e t L ε) :
    ∃ C : Circuit N d,
      Circuit.length C ≤ L ∧
      |‖R.starProjection (U.evolve t ψ)‖ ^ 2 -
          ‖R.starProjection (circuitCLMOnH C e ψ)‖ ^ 2|
        ≤ 2 * ε := by
  rcases hSim with ⟨C, hlength, hC⟩
  exact ⟨C, hlength,
    sector_weight_stability_under_circuit_simulation
      U e t C ε R ψ hψ hC⟩

/-- Finite-family version: the sum of fixed-sector weight discrepancies is
at most `2 * card * ε`.  The sectors are supplied explicitly and no
record-selection persistence is asserted. -/
theorem sector_weight_l1_stability_under_circuit_simulation
    {N d : ℕ}
    (U : NormPreservingEvolution (H (d ^ N)))
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (t : ℝ)
    (C : Circuit N d)
    (ε : ℝ)
    (sectors : Finset (Submodule ℂ (H (d ^ N))))
    (ψ : H (d ^ N))
    (hψ : ‖ψ‖ = 1)
    (hSim : CircuitSimulatesEvolutionAt U e t C ε) :
    ∑ R ∈ sectors,
        |‖R.starProjection (U.evolve t ψ)‖ ^ 2 -
          ‖R.starProjection (circuitCLMOnH C e ψ)‖ ^ 2|
      ≤ 2 * (sectors.card : ℝ) * ε := by
  calc
    ∑ R ∈ sectors,
        |‖R.starProjection (U.evolve t ψ)‖ ^ 2 -
          ‖R.starProjection (circuitCLMOnH C e ψ)‖ ^ 2|
        ≤ ∑ _R ∈ sectors, 2 * ε := by
          exact Finset.sum_le_sum fun R hR =>
            sector_weight_stability_under_circuit_simulation
              U e t C ε R ψ hψ hSim
    _ = 2 * (sectors.card : ℝ) * ε := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

end

end QuantumFoundations.BornRule.RestrictedRecordSectors
