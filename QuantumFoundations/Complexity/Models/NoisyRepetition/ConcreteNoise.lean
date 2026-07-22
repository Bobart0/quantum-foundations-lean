import QuantumFoundations.Complexity.Models.NoisyRepetition.Persistence

/-!
# C10h — A fully concrete nonzero-noise profile

The Pythagorean triple `99² + 20² = 101²` gives an exact rational normalized
profile with genuinely nonzero leakage.  Since `4 * (20 / 101) = 80 / 101 < 1`,
this profile is robust, so every C10a–C10g theorem applies to it
unconditionally: this is the principal nonvacuity witness of C10.
-/

namespace QuantumFoundations.Complexity.NoisyRepetitionModel

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.RepetitionModel

noncomputable section

/-- The concrete rational noise profile `(keep, leak) = (99/101, 20/101)`,
normalized exactly by the Pythagorean triple `99² + 20² = 101²`. -/
def rationalNoiseProfile : NoiseProfile where
  keep := (99 : ℂ) / 101
  leak := (20 : ℂ) / 101
  norm_sq := by
    rw [norm_div, norm_div]
    norm_num

@[simp] theorem rationalNoiseProfile_keep :
    rationalNoiseProfile.keep = (99 : ℂ) / 101 := rfl

@[simp] theorem rationalNoiseProfile_leak :
    rationalNoiseProfile.leak = (20 : ℂ) / 101 := rfl

theorem rationalNoiseProfile_norm_sq :
    ‖rationalNoiseProfile.keep‖ ^ 2 + ‖rationalNoiseProfile.leak‖ ^ 2 = 1 :=
  rationalNoiseProfile.norm_sq

theorem rationalNoiseProfile_leak_ne_zero : rationalNoiseProfile.leak ≠ 0 := by
  rw [rationalNoiseProfile_leak]
  norm_num

theorem rationalNoiseProfile_isRobust : rationalNoiseProfile.IsRobust := by
  unfold NoiseProfile.IsRobust
  rw [rationalNoiseProfile_leak, norm_div]
  norm_num

/-! ## Fully concrete theorems, requiring no noise-side hypotheses -/

theorem concrete_noisy_repetition_has_proxy_gap
    (R : ℕ) [NeZero R] (g : ℕ) (hg : 1 + g ≤ ceilHalf R) :
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      (noisyZeroBranch rationalNoiseProfile R) (noisyOneBranch rationalNoiseProfile R)
      (1 / 2 : ℝ) g :=
  noisy_repetition_has_proxy_gap rationalNoiseProfile rationalNoiseProfile_isRobust R g hg

theorem concrete_noisy_repetition_gap_persists
    (R : ℕ) [NeZero R] (E : Circuit (R + 1) 2) (g : ℕ)
    (hbudget : 1 + 4 * E.length + g ≤ ceilHalf R) :
    HasProxyGapAtLeast (sitesEquivR (R + 1))
      (Circuit.evalOnH E (sitesEquivR (R + 1)) (noisyZeroBranch rationalNoiseProfile R))
      (Circuit.evalOnH E (sitesEquivR (R + 1)) (noisyOneBranch rationalNoiseProfile R))
      (1 / 2 : ℝ) g :=
  noisy_repetition_gap_persists_under_circuit
    rationalNoiseProfile rationalNoiseProfile_isRobust R E g hbudget

theorem concrete_noisy_distinguishabilityComplexity_eq_one
    (R : ℕ) [NeZero R] :
    distinguishabilityComplexity (sitesEquivR (R + 1))
        (noisyZeroBranch rationalNoiseProfile R) (noisyOneBranch rationalNoiseProfile R)
        (1 / 2 : ℝ)
      = (1 : WithTop ℕ) :=
  noisy_repetition_distinguishabilityComplexity
    rationalNoiseProfile R rationalNoiseProfile_isRobust

theorem concrete_noisy_interferenceComplexity_bounds
    (R : ℕ) [NeZero R] :
    (ceilHalf R : WithTop ℕ) ≤
        interferenceComplexity (sitesEquivR (R + 1))
          (noisyZeroBranch rationalNoiseProfile R) (noisyOneBranch rationalNoiseProfile R)
          (1 / 2 : ℝ) ∧
      interferenceComplexity (sitesEquivR (R + 1))
          (noisyZeroBranch rationalNoiseProfile R) (noisyOneBranch rationalNoiseProfile R)
          (1 / 2 : ℝ)
        ≤ ((R + 1 : ℕ) : WithTop ℕ) :=
  noisy_repetition_interference_bounds
    rationalNoiseProfile R rationalNoiseProfile_isRobust

#print axioms rationalNoiseProfile_isRobust
#print axioms concrete_noisy_repetition_has_proxy_gap

end

end QuantumFoundations.Complexity.NoisyRepetitionModel
