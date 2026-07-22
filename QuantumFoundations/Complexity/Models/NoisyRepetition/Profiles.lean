import QuantumFoundations.Complexity.Defs

/-!
# C10a — Noisy repetition-model noise profiles

A `NoiseProfile` packages a normalized pair of complex amplitudes `keep` and
`leak` describing how much of a record projector's target amplitude is
retained (`keep`) versus how much leaks into the wrong computational cell
(`leak`).  The small-noise condition needed by the robust complexity
theorems is a separate predicate `IsRobust`, not a field of the structure:
`NoiseProfile` itself only packages exact normalization.
-/

namespace QuantumFoundations.Complexity.NoisyRepetitionModel

noncomputable section

/-- A normalized pair of `keep`/`leak` complex amplitudes for one noisy
record label. -/
structure NoiseProfile where
  /-- The retained (correctly recorded) amplitude. -/
  keep : ℂ
  /-- The leaked (mis-recorded) amplitude. -/
  leak : ℂ
  /-- Exact normalization of the two amplitudes. -/
  norm_sq : ‖keep‖ ^ 2 + ‖leak‖ ^ 2 = 1

namespace NoiseProfile

variable (p : NoiseProfile)

theorem keep_norm_le_one : ‖p.keep‖ ≤ 1 := by
  nlinarith [p.norm_sq, norm_nonneg p.keep, norm_nonneg p.leak, sq_nonneg (‖p.leak‖)]

theorem leak_norm_le_one : ‖p.leak‖ ≤ 1 := by
  nlinarith [p.norm_sq, norm_nonneg p.keep, norm_nonneg p.leak, sq_nonneg (‖p.keep‖)]

theorem keep_leak_not_both_zero : p.keep ≠ 0 ∨ p.leak ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨hk, hl⟩ := h
  have hsq := p.norm_sq
  rw [hk, hl] at hsq
  norm_num at hsq

/-- The robust-noise condition: the two-sided interference error
`4 * ‖leak‖` stays below the unit budget available at threshold `δ = 1/2`.
This is deliberately excluded from the `NoiseProfile` structure itself; it is
a hypothesis used only by the robust complexity theorems. -/
def IsRobust (p : NoiseProfile) : Prop := 4 * ‖p.leak‖ < 1

theorem IsRobust.leak_norm_lt_quarter {p : NoiseProfile} (hp : p.IsRobust) :
    ‖p.leak‖ < 1 / 4 := by
  unfold IsRobust at hp
  linarith

end NoiseProfile

/-- The exact (zero-leak) profile: the C9 regression limit of the noisy
family. -/
def exactProfile : NoiseProfile where
  keep := 1
  leak := 0
  norm_sq := by norm_num

@[simp] theorem exactProfile_keep : exactProfile.keep = 1 := rfl

@[simp] theorem exactProfile_leak : exactProfile.leak = 0 := rfl

theorem exactProfile_isRobust : exactProfile.IsRobust := by
  unfold NoiseProfile.IsRobust
  simp

end

end QuantumFoundations.Complexity.NoisyRepetitionModel
