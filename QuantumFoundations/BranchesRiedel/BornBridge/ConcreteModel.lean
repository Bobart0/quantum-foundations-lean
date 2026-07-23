import QuantumFoundations.BranchesRiedel.BornBridge.Evolution
import QuantumFoundations.Complexity.Models.MeasurementGeneration.ConcreteGeneration

/-!
# C14l — Fully concrete instance

Instantiates `C14i`'s end-to-end theorem at the existing concrete source
profile `concreteSourceProfile` (`amp0 = 3/5`, `amp1 = 4/5`, from
`3² + 4² = 5²`), giving exact rational Born weights `9/25`/`16/25` — via
`norm_num` on exact rational arithmetic, no floating point and no unsafe
evaluation tactic.
-/

namespace QuantumFoundations.BranchesRiedel.BornBridge

open scoped InnerProductSpace Classical
open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.BornRule
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.MeasurementGeneration
open QuantumFoundations.Complexity.RepetitionModel

noncomputable section

theorem concrete_branch0_weight_eq (R : ℕ) [NeZero R]
    (Est : Perspective (2 ^ (R + 1)) → Submodule ℂ (H (2 ^ (R + 1))) → ℝ) (hn3 : 3 ≤ 2 ^ (R + 1))
    (hA : AxGrain Est) (hN : AxNorm Est) (hPos : AxPos Est)
    (hNul : AxNul Est (idealGeneratedState concreteSourceProfile R))
    (D : Perspective (2 ^ (R + 1)))
    (hDf : branchCell (jointBranch (idealRecords R) (idealGeneratedState concreteSourceProfile R))
      (idealGeneratedActive0 concreteSourceProfile_amp0_ne_zero) ∈ D.cells) :
    Est D (branchCell (jointBranch (idealRecords R) (idealGeneratedState concreteSourceProfile R))
      (idealGeneratedActive0 concreteSourceProfile_amp0_ne_zero)) = 9 / 25 := by
  rw [idealGenerated_branch0_weight concreteSourceProfile_amp0_ne_zero Est hn3 hA hN hPos hNul D hDf,
    concreteSourceProfile_amp0]
  norm_num

theorem concrete_branch1_weight_eq (R : ℕ) [NeZero R]
    (Est : Perspective (2 ^ (R + 1)) → Submodule ℂ (H (2 ^ (R + 1))) → ℝ) (hn3 : 3 ≤ 2 ^ (R + 1))
    (hA : AxGrain Est) (hN : AxNorm Est) (hPos : AxPos Est)
    (hNul : AxNul Est (idealGeneratedState concreteSourceProfile R))
    (D : Perspective (2 ^ (R + 1)))
    (hDf : branchCell (jointBranch (idealRecords R) (idealGeneratedState concreteSourceProfile R))
      (idealGeneratedActive1 concreteSourceProfile_amp1_ne_zero) ∈ D.cells) :
    Est D (branchCell (jointBranch (idealRecords R) (idealGeneratedState concreteSourceProfile R))
      (idealGeneratedActive1 concreteSourceProfile_amp1_ne_zero)) = 16 / 25 := by
  rw [idealGenerated_branch1_weight concreteSourceProfile_amp1_ne_zero Est hn3 hA hN hPos hNul D hDf,
    concreteSourceProfile_amp1]
  norm_num

/-- **The principal concrete C14 theorem.** At the concrete `(3/5, 4/5)`
source profile: exact circuit generation, exact record redundancy, a
record-induced Born decomposition (including arbitrary-record-choice
invariance, packaged in `RecordInducedBornConclusion`), and the two exact
rational branch weights `9/25`/`16/25`, summing to `1`. -/
theorem concrete_unitary_recorded_Born_decomposition (R : ℕ) [NeZero R]
    (Est : Perspective (2 ^ (R + 1)) → Submodule ℂ (H (2 ^ (R + 1))) → ℝ) (hn3 : 3 ≤ 2 ^ (R + 1))
    (hA : AxGrain Est) (hN : AxNorm Est) (hPos : AxPos Est)
    (hNul : AxNul Est (idealGeneratedState concreteSourceProfile R))
    (D : Perspective (2 ^ (R + 1)))
    (hDf0 : branchCell (jointBranch (idealRecords R) (idealGeneratedState concreteSourceProfile R))
      (idealGeneratedActive0 concreteSourceProfile_amp0_ne_zero) ∈ D.cells)
    (hDf1 : branchCell (jointBranch (idealRecords R) (idealGeneratedState concreteSourceProfile R))
      (idealGeneratedActive1 concreteSourceProfile_amp1_ne_zero) ∈ D.cells) :
    (Circuit.evalOnH (idealFanoutCircuit R) (sitesEquivR (R + 1))
        (sourceInputState concreteSourceProfile R) = idealGeneratedState concreteSourceProfile R)
      ∧ IsRecordedOn (idealGeneratedState concreteSourceProfile R) (idealRecords R 0)
      ∧ Nonempty (RecordInducedBornConclusion (idealRecords R)
          (idealGeneratedState concreteSourceProfile R) Est)
      ∧ Est D (branchCell (jointBranch (idealRecords R) (idealGeneratedState concreteSourceProfile R))
          (idealGeneratedActive0 concreteSourceProfile_amp0_ne_zero)) = 9 / 25
      ∧ Est D (branchCell (jointBranch (idealRecords R) (idealGeneratedState concreteSourceProfile R))
          (idealGeneratedActive1 concreteSourceProfile_amp1_ne_zero)) = 16 / 25
      ∧ (9 : ℝ) / 25 + 16 / 25 = 1 :=
  ⟨idealFanout_generates_normalized_state concreteSourceProfile R,
    idealGeneratedState_isRecordedOn concreteSourceProfile R,
    (unitary_generation_yields_record_induced_Born_decomposition concreteSourceProfile R Est hn3
      hA hN hPos hNul).2,
    concrete_branch0_weight_eq R Est hn3 hA hN hPos hNul D hDf0,
    concrete_branch1_weight_eq R Est hn3 hA hN hPos hNul D hDf1,
    by norm_num⟩

end

end QuantumFoundations.BranchesRiedel.BornBridge
