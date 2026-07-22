import QuantumFoundations.Complexity.Models.MeasurementGeneration.GeneratedComplexity
import QuantumFoundations.Complexity.Models.NoisyRepetition.ConcreteNoise

/-!
# C11j — A fully concrete unitary branch-generation witness

The Pythagorean triple `3² + 4² = 5²` gives an exact rational, genuinely
nonzero-amplitude source profile.  Paired with C10h's rational noise profile
`(99/101, 20/101)`, every C11 generation and persistence theorem applies
unconditionally: this is the principal nonvacuity witness of C11.
-/

namespace QuantumFoundations.Complexity.MeasurementGeneration

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.RepetitionModel
open QuantumFoundations.Complexity.NoisyRepetitionModel

noncomputable section

/-- The concrete rational source-amplitude profile `(amp0, amp1) = (3/5,
4/5)`, normalized exactly by the Pythagorean triple `3² + 4² = 5²`. -/
def concreteSourceProfile : SourceAmplitudeProfile where
  amp0 := (3 : ℂ) / 5
  amp1 := (4 : ℂ) / 5
  norm_sq := by
    rw [norm_div, norm_div]
    norm_num

@[simp] theorem concreteSourceProfile_amp0 : concreteSourceProfile.amp0 = (3 : ℂ) / 5 := rfl
@[simp] theorem concreteSourceProfile_amp1 : concreteSourceProfile.amp1 = (4 : ℂ) / 5 := rfl

theorem concreteSourceProfile_amp0_ne_zero : concreteSourceProfile.amp0 ≠ 0 := by
  rw [concreteSourceProfile_amp0]
  norm_num

theorem concreteSourceProfile_amp1_ne_zero : concreteSourceProfile.amp1 ≠ 0 := by
  rw [concreteSourceProfile_amp1]
  norm_num

/-! ## Fully concrete theorems, requiring no source- or noise-side
hypotheses -/

/-- The full generation circuit, instantiated at the concrete source and
noise profiles, turns the concrete blank-record input into the concrete
noisy generated state. -/
theorem concrete_unitary_generation_produces_noisy_branches (R : ℕ) [NeZero R] :
    Circuit.evalOnH (noisyMeasurementCircuit rationalNoiseProfile R) (sitesEquivR (R + 1))
        (noisySourceInputState concreteSourceProfile R) =
      noisySourceGeneratedState concreteSourceProfile rationalNoiseProfile R := by
  unfold noisySourceInputState noisySourceGeneratedState
  rw [map_add, map_smul, map_smul, noisyMeasurement_maps_basis00, noisyMeasurement_maps_basis10]

/-- The concretely generated branches carry a nonzero robust proxy gap. -/
theorem concrete_generated_branches_have_gap (R : ℕ) [NeZero R] (g : ℕ)
    (hg : 1 + g ≤ ceilHalf R) :
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      (Circuit.evalOnH (noisyMeasurementCircuit rationalNoiseProfile R) (sitesEquivR (R + 1))
        (basis00 R))
      (Circuit.evalOnH (noisyMeasurementCircuit rationalNoiseProfile R) (sitesEquivR (R + 1))
        (basis10 R))
      (1 / 2 : ℝ) g :=
  unitary_generation_produces_robust_branches rationalNoiseProfile rationalNoiseProfile_isRobust
    R g hg

/-- The concretely generated branches' proxy gap persists under any further
finite `2`-local circuit evolution, given enough record budget. -/
theorem concrete_generated_branches_persist (R : ℕ) [NeZero R] (E : Circuit (R + 1) 2) (g : ℕ)
    (hbudget : 1 + 4 * E.length + g ≤ ceilHalf R) :
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      (Circuit.evalOnH E (sitesEquivR (R + 1))
        (Circuit.evalOnH (noisyMeasurementCircuit rationalNoiseProfile R) (sitesEquivR (R + 1))
          (basis00 R)))
      (Circuit.evalOnH E (sitesEquivR (R + 1))
        (Circuit.evalOnH (noisyMeasurementCircuit rationalNoiseProfile R) (sitesEquivR (R + 1))
          (basis10 R)))
      (1 / 2 : ℝ) g :=
  generated_branches_persist_under_further_evolution rationalNoiseProfile
    rationalNoiseProfile_isRobust R E g hbudget

#print axioms concrete_unitary_generation_produces_noisy_branches
#print axioms concrete_generated_branches_have_gap
#print axioms concrete_generated_branches_persist

end

end QuantumFoundations.Complexity.MeasurementGeneration
