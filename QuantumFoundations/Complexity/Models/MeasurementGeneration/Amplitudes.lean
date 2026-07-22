import QuantumFoundations.Complexity.Models.MeasurementGeneration.IdealFanout

/-!
# C11c — Source amplitude profile and normalization

A `SourceAmplitudeProfile` packages the normalized pair of complex
amplitudes `amp0`/`amp1` of the source qubit before fanout, mirroring
`NoiseProfile`'s `keep`/`leak` pair.  No nonzero-amplitude hypothesis is
built into the structure: nontriviality is a separate hypothesis used only
where genuinely needed (e.g. the end-to-end C11i theorems).
-/

namespace QuantumFoundations.Complexity.MeasurementGeneration

open scoped InnerProductSpace

open Gleason
open QuantumFoundations.Complexity.RepetitionModel
open QuantumFoundations.Complexity.NoisyRepetitionModel

noncomputable section

/-- A normalized pair of source-qubit amplitudes `amp0`/`amp1`. -/
structure SourceAmplitudeProfile where
  /-- Amplitude of the source-`0` branch. -/
  amp0 : ℂ
  /-- Amplitude of the source-`1` branch. -/
  amp1 : ℂ
  /-- Exact normalization of the two amplitudes. -/
  norm_sq : ‖amp0‖ ^ 2 + ‖amp1‖ ^ 2 = 1

/-- Pre-fanout state: source superposition, all records blank
(all-zero). -/
def sourceInputState (q : SourceAmplitudeProfile) (R : ℕ) : H (2 ^ (R + 1)) :=
  q.amp0 • basis00 R + q.amp1 • basis10 R

/-- Post-fanout state: each source branch carries its own constant record
tail. -/
def idealGeneratedState (q : SourceAmplitudeProfile) (R : ℕ) : H (2 ^ (R + 1)) :=
  q.amp0 • basis00 R + q.amp1 • basis11 R

theorem sourceInputState_norm (q : SourceAmplitudeProfile) (R : ℕ) :
    ‖sourceInputState q R‖ = 1 := by
  apply norm_eq_one_of_mul_self_eq_one
  rw [sourceInputState, norm_mul_self_keep_leak_combo (basis00 R) (basis10 R) q.amp0 q.amp1
    (basis00_norm R) (basis10_norm R) (basis00_inner_basis10 R)]
  nlinarith [q.norm_sq]

theorem idealGeneratedState_norm (q : SourceAmplitudeProfile) (R : ℕ) :
    ‖idealGeneratedState q R‖ = 1 := by
  apply norm_eq_one_of_mul_self_eq_one
  rw [idealGeneratedState, norm_mul_self_keep_leak_combo (basis00 R) (basis11 R) q.amp0 q.amp1
    (basis00_norm R) (basis11_norm R) (basis00_inner_basis11 R)]
  nlinarith [q.norm_sq]

theorem sourceInputState_ne_zero (q : SourceAmplitudeProfile) (R : ℕ) :
    sourceInputState q R ≠ 0 :=
  ne_zero_of_norm_ne_zero (by rw [sourceInputState_norm]; norm_num)

theorem idealGeneratedState_ne_zero (q : SourceAmplitudeProfile) (R : ℕ) :
    idealGeneratedState q R ≠ 0 :=
  ne_zero_of_norm_ne_zero (by rw [idealGeneratedState_norm]; norm_num)

/-- The ideal fanout circuit turns a normalized source-amplitude input into
a normalized generated state (an immediate specialization of
`idealFanout_generates_branching`). -/
theorem idealFanout_generates_normalized_state (q : SourceAmplitudeProfile) (R : ℕ) :
    Circuit.evalOnH (idealFanoutCircuit R) (sitesEquivR (R + 1)) (sourceInputState q R) =
      idealGeneratedState q R :=
  idealFanout_generates_branching q.amp0 q.amp1 R

/-- A concrete nontrivial source profile with amplitudes of genuinely
*equal* norm, `1 / √2` each.  Uses the exact real identity
`Real.sqrt 2 ^ 2 = 2`, not a floating-point approximation. -/
def equalSourceProfile : SourceAmplitudeProfile where
  amp0 := ((1 / Real.sqrt 2 : ℝ) : ℂ)
  amp1 := ((1 / Real.sqrt 2 : ℝ) : ℂ)
  norm_sq := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.sqrt 2)]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hpos : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    linarith [h2]

#print axioms sourceInputState_norm

end

end QuantumFoundations.Complexity.MeasurementGeneration
