import QuantumFoundations.Complexity.Models.MeasurementGeneration.Amplitudes
import QuantumFoundations.Complexity.Models.Repetition.Records

/-!
# C11d — Source projectors and component-weight preservation

The source qubit's own binary resolution, `sourceResolution R`, exactly
extracts the two branch components from any generated state: applying its
label-`0`/`1` projector to `idealOutputState α β R` (resp. the noisy
generated state) returns exactly the `α`-weighted (resp. `β`-weighted)
component, unchanged.  These are amplitude-*preservation* facts — the
interaction neither amplifies nor damps `α`/`β` — not a re-derivation of the
Born rule.
-/

namespace QuantumFoundations.Complexity.MeasurementGeneration

open scoped InnerProductSpace

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.RepetitionModel
open QuantumFoundations.Complexity.NoisyRepetitionModel

noncomputable section

/-- The source qubit's own binary computational resolution. -/
def sourceResolution (R : ℕ) : LabeledResolution (2 ^ (R + 1)) 2 :=
  siteResolution (R + 1) (sourceSite R)

/-! ## C11d.1 — Exact projector actions on the four basis states -/

theorem sourceProj_zero_fixes_basis00 (R : ℕ) :
    rproj (sourceResolution R) 0 (basis00 R) = basis00 R := by
  have h := siteProj_apply_configuration (sourceSite R) 0 (config00 R)
  rwa [if_pos (config00_source R)] at h

theorem sourceProj_zero_fixes_basis01 (R : ℕ) :
    rproj (sourceResolution R) 0 (basis01 R) = basis01 R := by
  have h := siteProj_apply_configuration (sourceSite R) 0 (config01 R)
  rwa [if_pos (config01_source R)] at h

theorem sourceProj_zero_kills_basis10 (R : ℕ) :
    rproj (sourceResolution R) 0 (basis10 R) = 0 := by
  have h := siteProj_apply_configuration (sourceSite R) 0 (config10 R)
  rwa [if_neg (by simp [config10_source])] at h

theorem sourceProj_zero_kills_basis11 (R : ℕ) :
    rproj (sourceResolution R) 0 (basis11 R) = 0 := by
  have h := siteProj_apply_configuration (sourceSite R) 0 (config11 R)
  rwa [if_neg (by simp [config11_source])] at h

theorem sourceProj_one_kills_basis00 (R : ℕ) :
    rproj (sourceResolution R) 1 (basis00 R) = 0 := by
  have h := siteProj_apply_configuration (sourceSite R) 1 (config00 R)
  rwa [if_neg (by simp [config00_source])] at h

theorem sourceProj_one_kills_basis01 (R : ℕ) :
    rproj (sourceResolution R) 1 (basis01 R) = 0 := by
  have h := siteProj_apply_configuration (sourceSite R) 1 (config01 R)
  rwa [if_neg (by simp [config01_source])] at h

theorem sourceProj_one_fixes_basis10 (R : ℕ) :
    rproj (sourceResolution R) 1 (basis10 R) = basis10 R := by
  have h := siteProj_apply_configuration (sourceSite R) 1 (config10 R)
  rwa [if_pos (config10_source R)] at h

theorem sourceProj_one_fixes_basis11 (R : ℕ) :
    rproj (sourceResolution R) 1 (basis11 R) = basis11 R := by
  have h := siteProj_apply_configuration (sourceSite R) 1 (config11 R)
  rwa [if_pos (config11_source R)] at h

/-! ## C11d.2 — Exact projector actions on the noisy branches -/

theorem sourceProj_zero_fixes_noisyZeroBranch (p : NoiseProfile) (R : ℕ) :
    rproj (sourceResolution R) 0 (noisyZeroBranch p R) = noisyZeroBranch p R := by
  simp [noisyZeroBranch, map_add, map_smul,
    sourceProj_zero_fixes_basis00 R, sourceProj_zero_fixes_basis01 R]

theorem sourceProj_zero_kills_noisyOneBranch (p : NoiseProfile) (R : ℕ) :
    rproj (sourceResolution R) 0 (noisyOneBranch p R) = 0 := by
  simp [noisyOneBranch, map_add, map_smul,
    sourceProj_zero_kills_basis10 R, sourceProj_zero_kills_basis11 R]

theorem sourceProj_one_kills_noisyZeroBranch (p : NoiseProfile) (R : ℕ) :
    rproj (sourceResolution R) 1 (noisyZeroBranch p R) = 0 := by
  simp [noisyZeroBranch, map_add, map_smul,
    sourceProj_one_kills_basis00 R, sourceProj_one_kills_basis01 R]

theorem sourceProj_one_fixes_noisyOneBranch (p : NoiseProfile) (R : ℕ) :
    rproj (sourceResolution R) 1 (noisyOneBranch p R) = noisyOneBranch p R := by
  simp [noisyOneBranch, map_add, map_smul,
    sourceProj_one_fixes_basis10 R, sourceProj_one_fixes_basis11 R]

/-! ## C11d.3 — Component extraction from the ideal generated state -/

theorem sourceProj_zero_idealOutput (α β : ℂ) (R : ℕ) :
    rproj (sourceResolution R) 0 (idealOutputState α β R) = α • basis00 R := by
  simp [idealOutputState, map_add, map_smul,
    sourceProj_zero_fixes_basis00 R, sourceProj_zero_kills_basis11 R]

theorem sourceProj_one_idealOutput (α β : ℂ) (R : ℕ) :
    rproj (sourceResolution R) 1 (idealOutputState α β R) = β • basis11 R := by
  simp [idealOutputState, map_add, map_smul,
    sourceProj_one_kills_basis00 R, sourceProj_one_fixes_basis11 R]

theorem norm_sq_source_zero_component (α β : ℂ) (R : ℕ) :
    ‖rproj (sourceResolution R) 0 (idealOutputState α β R)‖ ^ 2 = ‖α‖ ^ 2 := by
  rw [sourceProj_zero_idealOutput, norm_smul, basis00_norm]
  ring

theorem norm_sq_source_one_component (α β : ℂ) (R : ℕ) :
    ‖rproj (sourceResolution R) 1 (idealOutputState α β R)‖ ^ 2 = ‖β‖ ^ 2 := by
  rw [sourceProj_one_idealOutput, norm_smul, basis11_norm]
  ring

/-- For a normalized `SourceAmplitudeProfile`, the two squared component
weights extracted from the generated state sum to one: an amplitude
*preservation* fact, not a new derivation of the Born rule. -/
theorem component_norm_squares_sum_one (q : SourceAmplitudeProfile) (R : ℕ) :
    ‖rproj (sourceResolution R) 0 (idealGeneratedState q R)‖ ^ 2 +
        ‖rproj (sourceResolution R) 1 (idealGeneratedState q R)‖ ^ 2 = 1 := by
  show ‖rproj (sourceResolution R) 0 (idealOutputState q.amp0 q.amp1 R)‖ ^ 2 +
      ‖rproj (sourceResolution R) 1 (idealOutputState q.amp0 q.amp1 R)‖ ^ 2 = 1
  rw [norm_sq_source_zero_component, norm_sq_source_one_component]
  exact q.norm_sq

#print axioms norm_sq_source_zero_component
#print axioms norm_sq_source_one_component

/-! ## C11h.1 — Normalized noisy source states -/

/-- Pre-generation state built from a normalized `SourceAmplitudeProfile`:
source superposition, all records blank. -/
def noisySourceInputState (q : SourceAmplitudeProfile) (R : ℕ) [NeZero R] : H (2 ^ (R + 1)) :=
  q.amp0 • basis00 R + q.amp1 • basis10 R

/-- Post-generation state: each source branch carries its own noisy
redundant-record tail, weighted by the normalized source amplitudes. -/
def noisySourceGeneratedState (q : SourceAmplitudeProfile) (p : NoiseProfile) (R : ℕ) [NeZero R] :
    H (2 ^ (R + 1)) :=
  q.amp0 • noisyZeroBranch p R + q.amp1 • noisyOneBranch p R

theorem noisySourceInputState_norm (q : SourceAmplitudeProfile) (R : ℕ) [NeZero R] :
    ‖noisySourceInputState q R‖ = 1 := by
  apply norm_eq_one_of_mul_self_eq_one
  rw [noisySourceInputState, norm_mul_self_keep_leak_combo (basis00 R) (basis10 R) q.amp0 q.amp1
    (basis00_norm R) (basis10_norm R) (basis00_inner_basis10 R)]
  nlinarith [q.norm_sq]

theorem noisySourceGeneratedState_norm (q : SourceAmplitudeProfile) (p : NoiseProfile) (R : ℕ)
    [NeZero R] :
    ‖noisySourceGeneratedState q p R‖ = 1 := by
  apply norm_eq_one_of_mul_self_eq_one
  rw [noisySourceGeneratedState, norm_mul_self_keep_leak_combo (noisyZeroBranch p R)
    (noisyOneBranch p R) q.amp0 q.amp1 (noisyZeroBranch_norm p R) (noisyOneBranch_norm p R)
    (noisyBranches_inner p R)]
  nlinarith [q.norm_sq]

theorem noisySourceInputState_ne_zero (q : SourceAmplitudeProfile) (R : ℕ) [NeZero R] :
    noisySourceInputState q R ≠ 0 :=
  ne_zero_of_norm_ne_zero (by rw [noisySourceInputState_norm]; norm_num)

theorem noisySourceGeneratedState_ne_zero (q : SourceAmplitudeProfile) (p : NoiseProfile) (R : ℕ)
    [NeZero R] :
    noisySourceGeneratedState q p R ≠ 0 :=
  ne_zero_of_norm_ne_zero (by rw [noisySourceGeneratedState_norm]; norm_num)

/-! ## C11h.2 — Component extraction from the noisy generated state -/

theorem sourceProj_zero_noisyGenerated (q : SourceAmplitudeProfile) (p : NoiseProfile) (R : ℕ)
    [NeZero R] :
    rproj (sourceResolution R) 0 (noisySourceGeneratedState q p R) =
      q.amp0 • noisyZeroBranch p R := by
  simp [noisySourceGeneratedState, map_add, map_smul,
    sourceProj_zero_fixes_noisyZeroBranch p R, sourceProj_zero_kills_noisyOneBranch p R]

theorem sourceProj_one_noisyGenerated (q : SourceAmplitudeProfile) (p : NoiseProfile) (R : ℕ)
    [NeZero R] :
    rproj (sourceResolution R) 1 (noisySourceGeneratedState q p R) =
      q.amp1 • noisyOneBranch p R := by
  simp [noisySourceGeneratedState, map_add, map_smul,
    sourceProj_one_kills_noisyZeroBranch p R, sourceProj_one_fixes_noisyOneBranch p R]

theorem norm_sq_noisy_source_zero_component (q : SourceAmplitudeProfile) (p : NoiseProfile) (R : ℕ)
    [NeZero R] :
    ‖rproj (sourceResolution R) 0 (noisySourceGeneratedState q p R)‖ ^ 2 = ‖q.amp0‖ ^ 2 := by
  rw [sourceProj_zero_noisyGenerated, norm_smul, noisyZeroBranch_norm]
  ring

theorem norm_sq_noisy_source_one_component (q : SourceAmplitudeProfile) (p : NoiseProfile) (R : ℕ)
    [NeZero R] :
    ‖rproj (sourceResolution R) 1 (noisySourceGeneratedState q p R)‖ ^ 2 = ‖q.amp1‖ ^ 2 := by
  rw [sourceProj_one_noisyGenerated, norm_smul, noisyOneBranch_norm]
  ring

/-- Amplitude preservation for the noisy generation: the two squared
component weights extracted from the noisy generated state sum to one,
regardless of the noise profile `p`. -/
theorem noisy_component_norm_squares_sum_one (q : SourceAmplitudeProfile) (p : NoiseProfile)
    (R : ℕ) [NeZero R] :
    ‖rproj (sourceResolution R) 0 (noisySourceGeneratedState q p R)‖ ^ 2 +
        ‖rproj (sourceResolution R) 1 (noisySourceGeneratedState q p R)‖ ^ 2 = 1 := by
  rw [norm_sq_noisy_source_zero_component, norm_sq_noisy_source_one_component]
  exact q.norm_sq

/-! ## C11h.3 — Nontriviality of the extracted components -/

/-- If the source-`0` amplitude is nonzero, so is its extracted noisy
component (the noisy zero branch itself is never zero). -/
theorem noisy_source_zero_component_ne_zero (q : SourceAmplitudeProfile) (p : NoiseProfile)
    (R : ℕ) [NeZero R] (h0 : q.amp0 ≠ 0) :
    rproj (sourceResolution R) 0 (noisySourceGeneratedState q p R) ≠ 0 := by
  rw [sourceProj_zero_noisyGenerated]
  exact smul_ne_zero h0 (noisyZeroBranch_ne_zero p R)

/-- If the source-`1` amplitude is nonzero, so is its extracted noisy
component (the noisy one branch itself is never zero). -/
theorem noisy_source_one_component_ne_zero (q : SourceAmplitudeProfile) (p : NoiseProfile)
    (R : ℕ) [NeZero R] (h1 : q.amp1 ≠ 0) :
    rproj (sourceResolution R) 1 (noisySourceGeneratedState q p R) ≠ 0 := by
  rw [sourceProj_one_noisyGenerated]
  exact smul_ne_zero h1 (noisyOneBranch_ne_zero p R)

#print axioms noisySourceGeneratedState_norm
#print axioms noisy_component_norm_squares_sum_one

end

end QuantumFoundations.Complexity.MeasurementGeneration
