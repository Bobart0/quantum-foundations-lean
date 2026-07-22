import QuantumFoundations.Complexity.Models.Repetition.Complexities
import QuantumFoundations.Complexity.RecordPersistence

/-!
# C9g — Concrete finite-circuit persistence

The exact repetition-model gap is transported through an arbitrary finite
2-local circuit.  The sufficient budget loses four units per evolution gate,
exactly as in the generic C7 conjugation theorem.  This is conditional
finite-circuit persistence, not irreversible or continuous-time dynamics.
-/

namespace QuantumFoundations.Complexity.RepetitionModel

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- The repetition-model proxy gap survives a supplied finite circuit when
the redundant-record budget covers the readout, conjugation, and desired
remaining gap. -/
theorem repetition_gap_persists_under_circuit (R : ℕ) [NeZero R]
    (E : Circuit R 2) (g : ℕ)
    (hbudget : 1 + 4 * E.length + g ≤ ceilHalf R) :
    HasProxyGapAtLeast (sitesEquivR R)
      (Circuit.evalOnH E (sitesEquivR R) (zeroBranch R))
      (Circuit.evalOnH E (sitesEquivR R) (oneBranch R)) 1 g := by
  simpa [normalized_repetition_branch_zero, normalized_repetition_branch_one] using
    redundant_records_gap_persists_under_circuit_evolution
      (sitesEquivR R) (repetitionRegions R) (repetitionRecords R)
      (repetitionState R) (repetitionState_isRecordedOn R) (firstSite R)
      0 1 (by decide)
      (by simpa [repetition_branch_zero] using zeroBranch_ne_zero R)
      (by simpa [repetition_branch_one] using oneBranch_ne_zero R)
      (fun r => siteRecordProj_local_zero r)
      (fun r => siteRecordProj_local_one r)
      repetitionRegions_pairwise_disjoint 1 (by norm_num) (by norm_num)
      (recordReadoutCircuit R) (recordReadoutCircuit_implements_phase_flip R)
      E g (by rw [recordReadoutCircuit_length]; exact hbudget)

/-- A budget retaining one unit gives a positive proxy gap after the
finite circuit evolution. -/
theorem repetition_gap_one_persists_under_circuit (R : ℕ) [NeZero R]
    (E : Circuit R 2)
    (hbudget : 1 + 4 * E.length + 1 ≤ ceilHalf R) :
    HasProxyGapAtLeast (sitesEquivR R)
      (Circuit.evalOnH E (sitesEquivR R) (zeroBranch R))
      (Circuit.evalOnH E (sitesEquivR R) (oneBranch R)) 1 1 :=
  repetition_gap_persists_under_circuit R E 1 hbudget

#print axioms repetition_gap_persists_under_circuit

end


end QuantumFoundations.Complexity.RepetitionModel
