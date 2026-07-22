import QuantumFoundations.Complexity.Models.NoisyRepetition.States
import QuantumFoundations.Complexity.Models.Repetition.Records
import QuantumFoundations.Complexity.ApproxRecordBasic

/-!
# C10c — Noisy record regions and exact error calculations

Each record qubit `r : Fin R` carries the same binary computational
resolution used by the exact C9 repetition model, `siteResolution (R + 1)
(recordSite r)`.  Because the noisy branches mix the two same-source-bit
configurations, every record projector has an *exact*, explicitly computed
error: fixing the target configuration exactly, and leaking exactly `leak`
amplitude into (or out of) the wrong one.  These exact errors instantiate the
C8 `ApproxRecordedPairOn` predicate with aggregate budget `2 * ‖leak‖` per
label — the noisy model's canonical, nonzero, C8 inhabitant.
-/

namespace QuantumFoundations.Complexity.NoisyRepetitionModel

open scoped InnerProductSpace Classical

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.RepetitionModel

noncomputable section

/-! ## C10c.1 — Record regions -/

/-- Every record qubit `r` carries the exact binary computational resolution
at its embedded site `recordSite r`. -/
def noisyRecords (R : ℕ) : Fin R → LabeledResolution (2 ^ (R + 1)) 2 :=
  fun r => siteResolution (R + 1) (recordSite r)

/-- The singleton region of record qubit `r`. -/
def noisyRegions (R : ℕ) : Fin R → Finset (Fin (R + 1)) :=
  fun r => {recordSite r}

theorem noisyRegions_pairwise_disjoint {R : ℕ} :
    ∀ r r' : Fin R, r ≠ r' → Disjoint (noisyRegions R r) (noisyRegions R r') := by
  intro r r' hrr'
  exact Finset.disjoint_singleton.mpr (recordSite_injective.ne hrr')

theorem noisyRecordProj_local_zero {R : ℕ} (r : Fin R) :
    IsLocalTo
      (transportedRecordProj (sitesEquivR (R + 1)) (noisyRecords R r) 0)
      (noisyRegions R r) :=
  siteRecordProj_local_zero (recordSite r)

theorem noisyRecordProj_local_one {R : ℕ} (r : Fin R) :
    IsLocalTo
      (transportedRecordProj (sitesEquivR (R + 1)) (noisyRecords R r) 1)
      (noisyRegions R r) :=
  siteRecordProj_local_one (recordSite r)

/-! ## C10c.2 — Exact projector actions on the four basis configurations -/

theorem siteProj_zero_basis00 (R : ℕ) (r : Fin R) :
    rproj (noisyRecords R r) 0 (basis00 R) = basis00 R := by
  have h := siteProj_apply_configuration (recordSite r) 0 (config00 R)
  rwa [if_pos (config00_record R r)] at h

theorem siteProj_one_basis00 (R : ℕ) (r : Fin R) :
    rproj (noisyRecords R r) 1 (basis00 R) = 0 := by
  have h := siteProj_apply_configuration (recordSite r) 1 (config00 R)
  rwa [if_neg (by simp [config00_record])] at h

theorem siteProj_zero_basis01 (R : ℕ) (r : Fin R) :
    rproj (noisyRecords R r) 0 (basis01 R) = 0 := by
  have h := siteProj_apply_configuration (recordSite r) 0 (config01 R)
  rwa [if_neg (by simp [config01_record])] at h

theorem siteProj_one_basis01 (R : ℕ) (r : Fin R) :
    rproj (noisyRecords R r) 1 (basis01 R) = basis01 R := by
  have h := siteProj_apply_configuration (recordSite r) 1 (config01 R)
  rwa [if_pos (config01_record R r)] at h

theorem siteProj_zero_basis10 (R : ℕ) (r : Fin R) :
    rproj (noisyRecords R r) 0 (basis10 R) = basis10 R := by
  have h := siteProj_apply_configuration (recordSite r) 0 (config10 R)
  rwa [if_pos (config10_record R r)] at h

theorem siteProj_one_basis10 (R : ℕ) (r : Fin R) :
    rproj (noisyRecords R r) 1 (basis10 R) = 0 := by
  have h := siteProj_apply_configuration (recordSite r) 1 (config10 R)
  rwa [if_neg (by simp [config10_record])] at h

theorem siteProj_zero_basis11 (R : ℕ) (r : Fin R) :
    rproj (noisyRecords R r) 0 (basis11 R) = 0 := by
  have h := siteProj_apply_configuration (recordSite r) 0 (config11 R)
  rwa [if_neg (by simp [config11_record])] at h

theorem siteProj_one_basis11 (R : ℕ) (r : Fin R) :
    rproj (noisyRecords R r) 1 (basis11 R) = basis11 R := by
  have h := siteProj_apply_configuration (recordSite r) 1 (config11 R)
  rwa [if_pos (config11_record R r)] at h

/-! ## C10c.3 — Exact projector actions on the noisy branches -/

theorem siteProj_zero_noisyZero (p : NoiseProfile) (R : ℕ) (r : Fin R) :
    rproj (noisyRecords R r) 0 (noisyZeroBranch p R) = p.keep • basis00 R := by
  simp [noisyZeroBranch, map_add, map_smul,
    siteProj_zero_basis00 R r, siteProj_zero_basis01 R r]

theorem siteProj_zero_noisyOne (p : NoiseProfile) (R : ℕ) (r : Fin R) :
    rproj (noisyRecords R r) 0 (noisyOneBranch p R) = p.leak • basis10 R := by
  simp [noisyOneBranch, map_add, map_smul,
    siteProj_zero_basis10 R r, siteProj_zero_basis11 R r]

theorem siteProj_one_noisyZero (p : NoiseProfile) (R : ℕ) (r : Fin R) :
    rproj (noisyRecords R r) 1 (noisyZeroBranch p R) = p.leak • basis01 R := by
  simp [noisyZeroBranch, map_add, map_smul,
    siteProj_one_basis00 R r, siteProj_one_basis01 R r]

theorem siteProj_one_noisyOne (p : NoiseProfile) (R : ℕ) (r : Fin R) :
    rproj (noisyRecords R r) 1 (noisyOneBranch p R) = p.keep • basis11 R := by
  simp [noisyOneBranch, map_add, map_smul,
    siteProj_one_basis10 R r, siteProj_one_basis11 R r]

/-! ## C10c.4 — Exact norms of the record errors -/

theorem norm_siteProj_zero_fix_error (p : NoiseProfile) (R : ℕ) (r : Fin R) :
    ‖rproj (noisyRecords R r) 0 (noisyZeroBranch p R) - noisyZeroBranch p R‖ =
      ‖p.leak‖ := by
  rw [siteProj_zero_noisyZero]
  rw [show p.keep • basis00 R - noisyZeroBranch p R = -(p.leak • basis01 R) by
    rw [noisyZeroBranch]; module]
  rw [norm_neg, norm_smul, basis01_norm]
  simp

theorem norm_siteProj_zero_leakage (p : NoiseProfile) (R : ℕ) (r : Fin R) :
    ‖rproj (noisyRecords R r) 0 (noisyOneBranch p R)‖ = ‖p.leak‖ := by
  rw [siteProj_zero_noisyOne, norm_smul, basis10_norm]
  simp

theorem norm_siteProj_one_fix_error (p : NoiseProfile) (R : ℕ) (r : Fin R) :
    ‖rproj (noisyRecords R r) 1 (noisyOneBranch p R) - noisyOneBranch p R‖ =
      ‖p.leak‖ := by
  rw [siteProj_one_noisyOne]
  rw [show p.keep • basis11 R - noisyOneBranch p R = -(p.leak • basis10 R) by
    rw [noisyOneBranch]; module]
  rw [norm_neg, norm_smul, basis10_norm]
  simp

theorem norm_siteProj_one_leakage (p : NoiseProfile) (R : ℕ) (r : Fin R) :
    ‖rproj (noisyRecords R r) 1 (noisyZeroBranch p R)‖ = ‖p.leak‖ := by
  rw [siteProj_one_noisyZero, norm_smul, basis01_norm]
  simp

/-! ## C10c.5 — The canonical C8 inhabitant -/

/-- The noisy repetition records instantiate the C8 approximate-record pair
predicate with aggregate error `2 * ‖leak‖` at every record site, in both
label orientations.  The exact `IsRecordedOn` predicate is not used: the two
component bounds are exact equalities, admitted in full. -/
theorem noisy_repetition_approxRecordedPairOn (p : NoiseProfile) (R : ℕ) [NeZero R] :
    ApproxRecordedPairOn (noisyRecords R)
      (noisyZeroBranch p R) (noisyOneBranch p R) 0 1
      (2 * ‖p.leak‖) (2 * ‖p.leak‖) := by
  intro r
  constructor
  · apply approxRecordFor_of_component_bounds
      (norm_siteProj_zero_fix_error p R r).le (norm_siteProj_zero_leakage p R r).le
    linarith
  · apply approxRecordFor_of_component_bounds
      (norm_siteProj_one_fix_error p R r).le (norm_siteProj_one_leakage p R r).le
    linarith

/-- Zero-leak regression: the exact profile recovers the exact-record
identities at error budget zero. -/
theorem exactProfile_approxRecordedPairOn_zero (R : ℕ) [NeZero R] :
    ApproxRecordedPairOn (noisyRecords R)
      (noisyZeroBranch exactProfile R) (noisyOneBranch exactProfile R) 0 1 0 0 := by
  have h := noisy_repetition_approxRecordedPairOn exactProfile R
  simpa using h

end

end QuantumFoundations.Complexity.NoisyRepetitionModel
