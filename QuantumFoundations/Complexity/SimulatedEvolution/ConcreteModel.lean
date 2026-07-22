import QuantumFoundations.Complexity.SimulatedEvolution.GeneratedBranches

/-!
# C13i — Fully concrete rational instance

Uses `p := rationalNoiseProfile` (`(99/101, 20/101)`, C10h), the central
threshold `δ := 1/2`, margin `μ := 1/10`, readout circuit `D :=
noisyReadoutCircuit R` (exact, so `ρ := 0`), and evolution simulation error
`ε := 1/20`. All three required inequalities are checked by exact rational
arithmetic — no floating-point approximation, no unsafe evaluation tactic:

* interference margin: `4 * ‖leak‖ < 2 * (δ - μ)`, i.e. `80/101 < 4/5`
  (`80 * 5 = 400 < 404 = 4 * 101`);
* readout margin: `2 * (δ + μ) + 4 * ‖leak‖ ≤ 2`, i.e. `6/5 + 80/101 ≤ 2`
  (`1006/505 < 1010/505`);
* simulation-error margin: `2 * ε ≤ μ`, i.e. `1/10 ≤ 1/10` (equality).
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

/-- The concrete rational noisy model, at the exact readout circuit, has a
threshold-margin proxy gap at `δ = 1/2`, `μ = 1/10`. -/
theorem concrete_noisy_repetition_has_margin_gap
    (R : ℕ) [NeZero R] (g : ℕ) (hBudget : 1 + g ≤ ceilHalf R) :
    HasProxyGapMarginAtLeast (sitesEquivR (R + 1))
      (noisyZeroBranch rationalNoiseProfile R) (noisyOneBranch rationalNoiseProfile R)
      (1 / 2 : ℝ) (1 / 10 : ℝ) g :=
  noisy_repetition_has_margin_gap rationalNoiseProfile R (noisyReadoutCircuit R) 0
    (1 / 2 : ℝ) (1 / 10 : ℝ) (by norm_num) (by norm_num)
    (by rw [rationalNoiseProfile_leak, norm_div]; norm_num)
    (by rw [rationalNoiseProfile_leak, norm_div]; norm_num)
    (implementsRecordPhaseFlip_implies_opApprox_zero _ _ _ _
      (noisyReadoutCircuit_implements R))
    g (by rw [noisyReadoutCircuit_length]; exact hBudget)

/-- The principal concrete C13 theorem: the concrete rational noisy model's
proxy gap at `δ = 1/2` persists under any evolution simulated to operator-
norm error `1/20`. -/
theorem concrete_gap_persists_under_one_twentieth_simulation
    (R : ℕ) [NeZero R]
    (U : NormPreservingEvolution (H (2 ^ (R + 1))))
    (t : ℝ) (E : Circuit (R + 1) 2)
    (hSim : CircuitSimulatesEvolutionAt U (sitesEquivR (R + 1)) t E (1 / 20 : ℝ))
    (g : ℕ) (hBudget : 1 + 4 * Circuit.length E + g ≤ ceilHalf R) :
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      (U.evolve t (noisyZeroBranch rationalNoiseProfile R))
      (U.evolve t (noisyOneBranch rationalNoiseProfile R))
      (1 / 2 : ℝ) g :=
  noisy_repetition_gap_persists_under_simulated_evolution rationalNoiseProfile R
    (noisyReadoutCircuit R) 0 (1 / 2 : ℝ) (1 / 10 : ℝ) (by norm_num) (by norm_num)
    (by rw [rationalNoiseProfile_leak, norm_div]; norm_num)
    (by rw [rationalNoiseProfile_leak, norm_div]; norm_num)
    (implementsRecordPhaseFlip_implies_opApprox_zero _ _ _ _
      (noisyReadoutCircuit_implements R))
    U t E (1 / 20 : ℝ) hSim (by norm_num) g
    (by rw [noisyReadoutCircuit_length]; exact hBudget)

/-- The corresponding C11 generated-branch theorem, at the concrete
`(3/5, 4/5)` source profile. -/
theorem concrete_generated_branches_persist_under_one_twentieth_simulation
    (R : ℕ) [NeZero R]
    (U : NormPreservingEvolution (H (2 ^ (R + 1))))
    (t : ℝ) (E : Circuit (R + 1) 2)
    (hSim : CircuitSimulatesEvolutionAt U (sitesEquivR (R + 1)) t E (1 / 20 : ℝ))
    (g : ℕ) (hBudget : 1 + 4 * Circuit.length E + g ≤ ceilHalf R) :
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
      (U.evolve t (noisyZeroBranch rationalNoiseProfile R))
      (U.evolve t (noisyOneBranch rationalNoiseProfile R))
      (1 / 2 : ℝ) g :=
  generated_branches_persist_under_simulated_evolution rationalNoiseProfile R
    (noisyReadoutCircuit R) 0 (1 / 2 : ℝ) (1 / 10 : ℝ) (by norm_num) (by norm_num)
    (by rw [rationalNoiseProfile_leak, norm_div]; norm_num)
    (by rw [rationalNoiseProfile_leak, norm_div]; norm_num)
    (implementsRecordPhaseFlip_implies_opApprox_zero _ _ _ _
      (noisyReadoutCircuit_implements R))
    concreteSourceProfile concreteSourceProfile_amp0_ne_zero
    concreteSourceProfile_amp1_ne_zero
    U t E (1 / 20 : ℝ) hSim (by norm_num) g
    (by rw [noisyReadoutCircuit_length]; exact hBudget)

#print axioms concrete_noisy_repetition_has_margin_gap
#print axioms concrete_gap_persists_under_one_twentieth_simulation
#print axioms concrete_generated_branches_persist_under_one_twentieth_simulation

end

end QuantumFoundations.Complexity.SimulatedEvolution
