import QuantumFoundations.Complexity.Models.Repetition.Interference

/-!
# C9f — Explicit complexity bounds and proxy gap

The generic redundant-record theorems are instantiated with the singleton
regions, exact binary records, and the one-gate phase readout.  This yields
`ceilHalf R ≤ C_I ≤ R`, the exact value `C_D = 1`, and a subtraction-free
gap certificate.
-/

namespace QuantumFoundations.Complexity.RepetitionModel

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- The `R` independent exact records force the interference lower bound
`ceilHalf R`. -/
theorem repetition_interferenceComplexity_lower (R : ℕ) [NeZero R] :
    (ceilHalf R : WithTop ℕ) ≤ interferenceComplexity
      (sitesEquivR R) (zeroBranch R) (oneBranch R) 1 := by
  simpa [normalized_repetition_branch_zero, normalized_repetition_branch_one] using
    redundant_records_interferenceComplexity_lower_bound
      (sitesEquivR R) (repetitionRegions R) (repetitionRecords R)
      (repetitionState R) (repetitionState_isRecordedOn R) 0 1 (by decide)
      (by simpa [repetition_branch_zero] using zeroBranch_ne_zero R)
      (by simpa [repetition_branch_one] using oneBranch_ne_zero R)
      (fun r => siteRecordProj_local_zero r)
      (fun r => siteRecordProj_local_one r)
      repetitionRegions_pairwise_disjoint 1 (by norm_num)

/-- The explicit interference complexity is finite and lies between the
record-count lower bound and the constructed `R`-gate witness. -/
theorem repetition_interferenceComplexity_bounds (R : ℕ) [NeZero R] :
    (ceilHalf R : WithTop ℕ) ≤ interferenceComplexity
        (sitesEquivR R) (zeroBranch R) (oneBranch R) 1 ∧
      interferenceComplexity
        (sitesEquivR R) (zeroBranch R) (oneBranch R) 1 ≤ (R : WithTop ℕ) :=
  ⟨repetition_interferenceComplexity_lower R,
    repetition_interferenceComplexity_upper R⟩

/-- In particular, the explicit interference complexity is not `⊤`. -/
theorem repetition_interferenceComplexity_ne_top (R : ℕ) :
    interferenceComplexity
      (sitesEquivR R) (zeroBranch R) (oneBranch R) 1 ≠ ⊤ :=
  ne_top_of_le_ne_top WithTop.coe_ne_top
    (repetition_interferenceComplexity_upper R)

/-- Every `g` with `1 + g ≤ ceilHalf R` is certified as an exact proxy gap. -/
theorem repetition_has_proxy_gap (R : ℕ) [NeZero R]
    (g : ℕ) (hg : 1 + g ≤ ceilHalf R) :
    HasProxyGapAtLeast
      (sitesEquivR R) (zeroBranch R) (oneBranch R) 1 g := by
  simpa [normalized_repetition_branch_zero, normalized_repetition_branch_one] using
    redundant_records_give_proxy_gap_certificate
      (sitesEquivR R) (repetitionRegions R) (repetitionRecords R)
      (repetitionState R) (repetitionState_isRecordedOn R) (firstSite R)
      0 1 (by decide)
      (by simpa [repetition_branch_zero] using zeroBranch_ne_zero R)
      (by simpa [repetition_branch_one] using oneBranch_ne_zero R)
      (fun r => siteRecordProj_local_zero r)
      (fun r => siteRecordProj_local_one r)
      repetitionRegions_pairwise_disjoint 1 (by norm_num) (by norm_num)
      (recordReadoutCircuit R) (recordReadoutCircuit_implements_phase_flip R)
      g (by rw [recordReadoutCircuit_length]; exact hg)

/-- Minimum-level subtraction-free gap for the explicit model. -/
theorem repetition_complexity_gap (R : ℕ) [NeZero R]
    (g : ℕ) (hg : 1 + g ≤ ceilHalf R) :
    distinguishabilityComplexity
        (sitesEquivR R) (zeroBranch R) (oneBranch R) 1 + (g : WithTop ℕ)
      ≤ interferenceComplexity
        (sitesEquivR R) (zeroBranch R) (oneBranch R) 1 := by
  simpa [normalized_repetition_branch_zero, normalized_repetition_branch_one] using
    redundant_records_complexity_gap
      (sitesEquivR R) (repetitionRegions R) (repetitionRecords R)
      (repetitionState R) (repetitionState_isRecordedOn R) (firstSite R)
      0 1 (by decide)
      (by simpa [repetition_branch_zero] using zeroBranch_ne_zero R)
      (by simpa [repetition_branch_one] using oneBranch_ne_zero R)
      (fun r => siteRecordProj_local_zero r)
      (fun r => siteRecordProj_local_one r)
      repetitionRegions_pairwise_disjoint 1 (by norm_num) (by norm_num)
      (recordReadoutCircuit R) (recordReadoutCircuit_implements_phase_flip R)
      g (by rw [recordReadoutCircuit_length]; exact hg)

/-- Three or more record sites already give a nonzero proxy gap. -/
theorem repetition_has_positive_gap (R : ℕ) (hR : 3 ≤ R) :
    HasProxyGapAtLeast
      (sitesEquivR R) (zeroBranch R) (oneBranch R) 1 1 := by
  letI : NeZero R := ⟨by omega⟩
  apply repetition_has_proxy_gap R 1
  unfold ceilHalf
  omega

#print axioms repetition_interferenceComplexity_lower
#print axioms repetition_interferenceComplexity_upper
#print axioms repetition_has_proxy_gap

end


end QuantumFoundations.Complexity.RepetitionModel
