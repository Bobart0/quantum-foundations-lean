import QuantumFoundations.Complexity.SimulatedEvolution.ConcreteModel
import QuantumFoundations.Complexity.SimulatedEvolution.TimeEvolution
import QuantumFoundations.Complexity.SimulatedEvolution.HamiltonianEvolution

/-!
# C13 — Non-vacuity of the simulated-evolution error-budget API

The identity evolution is norm preserving and is simulated *exactly* (error
`0`) by the empty circuit, so `CircuitSimulatesEvolutionAt`,
`HasCircuitSimulationAt`, and `HasCircuitSimulationBound` are all genuinely
inhabited — not merely vacuously true predicates. Monotonicity in the error
budget then carries this exact witness to the concrete `1/20`
evolution-simulation error used throughout C13i, giving a fully concrete,
non-vacuous instance of the principal C13 theorem. None of this constructs a
physically nontrivial (Hamiltonian-generated) evolution: the identity
evolution is not described as one.
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

/-! ## The identity evolution -/

/-- The identity evolution: `evolve t := id` for every `t`, trivially norm
preserving. -/
def identityEvolution (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    NormPreservingEvolution E where
  evolve _ := ContinuousLinearMap.id ℂ E
  norm_apply _ _ := rfl

/-- The identity evolution equals the empty circuit's transported
evaluation, at every time `t`. -/
theorem identityEvolution_evolve_eq_circuitCLMOnH_nil {N d : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (t : ℝ) :
    (identityEvolution (H (d ^ N))).evolve t = circuitCLMOnH ([] : Circuit N d) e := by
  apply ContinuousLinearMap.ext
  intro x
  show x = circuitCLMOnH ([] : Circuit N d) e x
  rw [circuitCLMOnH_apply]
  show x = Circuit.evalOnH [] e x
  simp [Circuit.evalOnH]

/-- The empty circuit simulates the identity evolution exactly (error `0`),
at every time `t`. -/
theorem identityEvolution_simulated_by_empty_circuit {N d : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (t : ℝ) :
    CircuitSimulatesEvolutionAt (identityEvolution (H (d ^ N))) e t [] 0 :=
  CircuitSimulatesEvolutionAt.exact (identityEvolution_evolve_eq_circuitCLMOnH_nil e t)

/-- `HasCircuitSimulationAt` is genuinely inhabited: cost `0`, error `0`. -/
theorem identityEvolution_hasCircuitSimulationAt {N d : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (t : ℝ) :
    HasCircuitSimulationAt (identityEvolution (H (d ^ N))) e t 0 0 :=
  ⟨[], le_refl 0, identityEvolution_simulated_by_empty_circuit e t⟩

/-- `HasCircuitSimulationBound` is genuinely inhabited: constant cost `0`,
constant error `0`. -/
theorem identityEvolution_hasCircuitSimulationBound {N d : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) :
    HasCircuitSimulationBound (identityEvolution (H (d ^ N))) e (fun _ => 0) (fun _ => 0) :=
  fun t => identityEvolution_hasCircuitSimulationAt e t

/-! ## Concrete non-vacuous instance -/

/-- The concrete `1/20`-error gap theorem is inhabited: the identity
evolution, exactly simulated by the empty circuit, satisfies the `1/20`
budget by monotonicity. -/
theorem concrete_gap_persists_nonvacuous (R : ℕ) [NeZero R] (g : ℕ)
    (hBudget : 1 + g ≤ ceilHalf R) :
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      ((identityEvolution (H (2 ^ (R + 1)))).evolve 0 (noisyZeroBranch rationalNoiseProfile R))
      ((identityEvolution (H (2 ^ (R + 1)))).evolve 0 (noisyOneBranch rationalNoiseProfile R))
      (1 / 2 : ℝ) g :=
  concrete_gap_persists_under_one_twentieth_simulation R (identityEvolution _) 0 []
    ((identityEvolution_simulated_by_empty_circuit (sitesEquivR (R + 1)) 0).mono_error
      (by norm_num))
    g (by simpa using hBudget)

/-- The concrete C11-generated-branch theorem is likewise inhabited, using
the concrete `(3/5, 4/5)` source profile. -/
theorem concrete_generated_branches_persist_nonvacuous (R : ℕ) [NeZero R] (g : ℕ)
    (hBudget : 1 + g ≤ ceilHalf R) :
    Circuit.evalOnH (noisyMeasurementCircuit rationalNoiseProfile R) (sitesEquivR (R + 1))
        (noisySourceInputState concreteSourceProfile R) =
      concreteSourceProfile.amp0 • noisyZeroBranch rationalNoiseProfile R
        + concreteSourceProfile.amp1 • noisyOneBranch rationalNoiseProfile R
    ∧
    rproj (sourceResolution R) 0
      (noisySourceGeneratedState concreteSourceProfile rationalNoiseProfile R) ≠ 0
    ∧
    rproj (sourceResolution R) 1
      (noisySourceGeneratedState concreteSourceProfile rationalNoiseProfile R) ≠ 0
    ∧
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      ((identityEvolution (H (2 ^ (R + 1)))).evolve 0 (noisyZeroBranch rationalNoiseProfile R))
      ((identityEvolution (H (2 ^ (R + 1)))).evolve 0 (noisyOneBranch rationalNoiseProfile R))
      (1 / 2 : ℝ) g :=
  concrete_generated_branches_persist_under_one_twentieth_simulation R (identityEvolution _) 0 []
    ((identityEvolution_simulated_by_empty_circuit (sitesEquivR (R + 1)) 0).mono_error
      (by norm_num))
    g (by simpa using hBudget)

end

end QuantumFoundations.Complexity.SimulatedEvolution
