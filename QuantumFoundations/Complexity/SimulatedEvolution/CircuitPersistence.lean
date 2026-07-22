import QuantumFoundations.Complexity.SimulatedEvolution.MarginCertificate
import QuantumFoundations.Complexity.CircuitInverse
import QuantumFoundations.Complexity.Persistence

/-!
# C13e — Exact circuit persistence of margin certificates

Reuses the existing C7 transport theorems
(`interference_lower_bound_under_evolution`,
`distinguishability_upper_bound_under_evolution`) separately at the two
margin thresholds `δ - μ` and `δ + μ`, through the canonical reversible
evolution `ReversibleCircuitEvolution.ofCircuit E` (overhead exactly
`2 * E.length`, `overhead_ofCircuit`). The combined budget therefore pays
`2 * (2 * E.length) = 4 * E.length`, matching the existing C7–C12 budget
convention `D.length + 4 * E.length + g ≤ ceilHalf R` exactly (not
`2 * E.length`).
-/

namespace QuantumFoundations.Complexity.SimulatedEvolution

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity

noncomputable section

/-- An exact finite circuit `E` transports a margin certificate: the margin
`μ` is unchanged, and the budget loses exactly `4 * E.length`. -/
theorem margin_gap_persists_under_circuit {N d : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (a b : H (d ^ N)) (δ μ : ℝ)
    (E : Circuit N d) (g : ℕ)
    (hGap : HasProxyGapMarginAtLeast e a b δ μ (4 * Circuit.length E + g)) :
    HasProxyGapMarginAtLeast e
      (Circuit.evalOnH E e a) (Circuit.evalOnH E e b) δ μ g := by
  obtain ⟨B, D, hI, hD, hbudget⟩ := hGap
  let Evo := ReversibleCircuitEvolution.ofCircuit E
  have hoverhead : Evo.overhead = 2 * Circuit.length E :=
    ReversibleCircuitEvolution.overhead_ofCircuit E
  refine ⟨D + Evo.overhead + g, D + Evo.overhead, ?_, ?_, ?_⟩
  · apply interference_lower_bound_under_evolution Evo e a b (δ - μ) B hI
      (D + Evo.overhead + g)
    omega
  · exact distinguishability_upper_bound_under_evolution Evo e a b (δ + μ) D hD
  · omega

#print axioms margin_gap_persists_under_circuit

end

end QuantumFoundations.Complexity.SimulatedEvolution
