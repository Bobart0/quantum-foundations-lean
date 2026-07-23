import QuantumFoundations.BranchesRiedel.BornBridge.LocalRecords
import QuantumFoundations.Complexity.Models.MeasurementGeneration.BranchWeights
import QuantumFoundations.Complexity.Models.NoisyRepetition.Records

/-!
# C14i — Exact unitarily generated two-branch model

Connects C11's exact unitary generation (`idealFanoutCircuit`,
`idealFanout_generates_normalized_state`) to the abstract C14 machinery, at
the single binary "which-branch" observable. `idealRecords` reuses C10's
`noisyRecords` site-resolution family — which is itself *exact* (the
noise only enters through which *state* it is later applied to elsewhere in
the repository) — applied here to the exact `idealGeneratedState`, never to
the noisy branches; this is not the noisy C10 record family used with an
exact-branch theorem.

Since there is only *one* observable here (`Fin 1`), `CommuteWitness` holds
vacuously (no pair `a ≠ b` exists in `Fin 1`), and `jointBranch` reduces to
a single projector application — the ordinary single-observable `branch`
construction, not a genuinely multi-observable chain.
-/

namespace QuantumFoundations.BranchesRiedel.BornBridge

open scoped InnerProductSpace Classical
open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.BornRule
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.RepetitionModel
open QuantumFoundations.Complexity.NoisyRepetitionModel
open QuantumFoundations.Complexity.MeasurementGeneration

noncomputable section

/-! ## C14i.1 — The single-observable exact record family -/

/-- The single-observable exact record family: at every record site `r`,
the same binary site resolution as C10's `noisyRecords`, reused here for
the *exact* ideal generated state (not the noisy branches). -/
def idealRecords (R : ℕ) : Fin 1 → Fin R → LabeledResolution (2 ^ (R + 1)) 2 :=
  fun _ => noisyRecords R

/-- `CommuteWitness` holds vacuously for a single observable: there is no
pair `a ≠ b` in `Fin 1`. -/
theorem idealRecords_commuteWitness_vacuous (R : ℕ) : CommuteWitness (idealRecords R) :=
  fun a b hab => absurd (Subsingleton.elim a b) hab

/-- The ideal generated state is exactly redundantly recorded by every
record site: each site's projector acts identically on `basis00`/`basis11`,
independently of which site is chosen. -/
theorem idealGeneratedState_isRecordedOn (q : SourceAmplitudeProfile) (R : ℕ) :
    IsRecordedOn (idealGeneratedState q R) (idealRecords R 0) := by
  intro r r' b
  fin_cases b <;>
    simp [idealRecords, idealGeneratedState, map_add, map_smul,
      siteProj_zero_basis00, siteProj_zero_basis11, siteProj_one_basis00, siteProj_one_basis11]

/-! ## C14i.2 — The two joint branch vectors -/

theorem idealGenerated_branch0 (q : SourceAmplitudeProfile) (R : ℕ) [NeZero R] :
    jointBranch (idealRecords R) (idealGeneratedState q R) (fun _ => 0) = q.amp0 • basis00 R := by
  show rproj (idealRecords R 0 (0 : Fin R)) 0 (idealGeneratedState q R) = q.amp0 • basis00 R
  simp [idealRecords, idealGeneratedState, map_add, map_smul,
    siteProj_zero_basis00, siteProj_zero_basis11]

theorem idealGenerated_branch1 (q : SourceAmplitudeProfile) (R : ℕ) [NeZero R] :
    jointBranch (idealRecords R) (idealGeneratedState q R) (fun _ => 1) = q.amp1 • basis11 R := by
  show rproj (idealRecords R 0 (0 : Fin R)) 1 (idealGeneratedState q R) = q.amp1 • basis11 R
  simp [idealRecords, idealGeneratedState, map_add, map_smul,
    siteProj_one_basis00, siteProj_one_basis11]

/-! ## C14i.3 — General theorem, allowing zero amplitudes -/

/-- **The principal end-to-end C14 theorem.** The ideal fanout circuit
generates `idealGeneratedState q R` exactly from a source superposition,
and the generated state (whether or not either amplitude vanishes) admits a
record-induced Born decomposition: unique joint branches, arbitrary
redundant-record-choice invariance, the branch-cell perspective, and
squared-norm Born weights, all under (Pos), (Norm), (Grain), (Null). This
is not a derivation of rational expectation, and it does not claim that
records alone determine the weights. -/
theorem unitary_generation_yields_record_induced_Born_decomposition
    (q : SourceAmplitudeProfile) (R : ℕ) [NeZero R]
    (Est : Perspective (2 ^ (R + 1)) → Submodule ℂ (H (2 ^ (R + 1))) → ℝ) (hn3 : 3 ≤ 2 ^ (R + 1))
    (hA : AxGrain Est) (hN : AxNorm Est) (hPos : AxPos Est)
    (hNul : AxNul Est (idealGeneratedState q R)) :
    Circuit.evalOnH (idealFanoutCircuit R) (sitesEquivR (R + 1)) (sourceInputState q R)
        = idealGeneratedState q R
      ∧ Nonempty (RecordInducedBornConclusion (idealRecords R) (idealGeneratedState q R) Est) :=
  ⟨idealFanout_generates_normalized_state q R,
    record_induced_Born_decomposition (idealRecords R) (idealGeneratedState q R)
      (idealGeneratedState_norm q R) (fun _ => idealGeneratedState_isRecordedOn q R)
      (idealRecords_commuteWitness_vacuous R) Est hn3 hA hN hPos hNul⟩

/-! ## C14i.4 — Clean two-active-branch corollary -/

variable {q : SourceAmplitudeProfile} {R : ℕ} [NeZero R]

theorem idealGenerated_branch0_ne_zero (h0 : q.amp0 ≠ 0) :
    jointBranch (idealRecords R) (idealGeneratedState q R) (fun _ => 0) ≠ 0 := by
  rw [idealGenerated_branch0]; exact smul_ne_zero h0 (basis00_ne_zero R)

theorem idealGenerated_branch1_ne_zero (h1 : q.amp1 ≠ 0) :
    jointBranch (idealRecords R) (idealGeneratedState q R) (fun _ => 1) ≠ 0 := by
  rw [idealGenerated_branch1]; exact smul_ne_zero h1 (basis11_ne_zero R)

/-- The active index for the `0`-labeled branch, under a nonzero source
amplitude. -/
def idealGeneratedActive0 (h0 : q.amp0 ≠ 0) :
    ActiveBranchIndex (jointBranch (idealRecords R) (idealGeneratedState q R)) :=
  ⟨fun _ => 0, idealGenerated_branch0_ne_zero h0⟩

/-- The active index for the `1`-labeled branch, under a nonzero source
amplitude. -/
def idealGeneratedActive1 (h1 : q.amp1 ≠ 0) :
    ActiveBranchIndex (jointBranch (idealRecords R) (idealGeneratedState q R)) :=
  ⟨fun _ => 1, idealGenerated_branch1_ne_zero h1⟩

theorem idealGenerated_branch0_weight (h0 : q.amp0 ≠ 0)
    (Est : Perspective (2 ^ (R + 1)) → Submodule ℂ (H (2 ^ (R + 1))) → ℝ) (hn3 : 3 ≤ 2 ^ (R + 1))
    (hA : AxGrain Est) (hN : AxNorm Est) (hPos : AxPos Est)
    (hNul : AxNul Est (idealGeneratedState q R))
    (D : Perspective (2 ^ (R + 1)))
    (hDf : branchCell (jointBranch (idealRecords R) (idealGeneratedState q R))
      (idealGeneratedActive0 h0) ∈ D.cells) :
    Est D (branchCell (jointBranch (idealRecords R) (idealGeneratedState q R))
      (idealGeneratedActive0 h0)) = ‖q.amp0‖ ^ 2 := by
  rw [recordBranch_weight_eq_norm_sq (jointBranch (idealRecords R) (idealGeneratedState q R))
    (idealGeneratedState_norm q R) (jointBranch_sum (idealRecords R) (idealGeneratedState q R))
    (fun x y hxy => jointBranch_orthogonal (idealRecords R) (idealGeneratedState q R)
      (fun _ => idealGeneratedState_isRecordedOn q R) (idealRecords_commuteWitness_vacuous R) hxy)
    Est hn3 hA hN hPos hNul D (idealGeneratedActive0 h0) hDf]
  show ‖jointBranch (idealRecords R) (idealGeneratedState q R) (fun _ => 0)‖ ^ 2 = ‖q.amp0‖ ^ 2
  rw [idealGenerated_branch0, norm_smul, basis00_norm]
  simp

theorem idealGenerated_branch1_weight (h1 : q.amp1 ≠ 0)
    (Est : Perspective (2 ^ (R + 1)) → Submodule ℂ (H (2 ^ (R + 1))) → ℝ) (hn3 : 3 ≤ 2 ^ (R + 1))
    (hA : AxGrain Est) (hN : AxNorm Est) (hPos : AxPos Est)
    (hNul : AxNul Est (idealGeneratedState q R))
    (D : Perspective (2 ^ (R + 1)))
    (hDf : branchCell (jointBranch (idealRecords R) (idealGeneratedState q R))
      (idealGeneratedActive1 h1) ∈ D.cells) :
    Est D (branchCell (jointBranch (idealRecords R) (idealGeneratedState q R))
      (idealGeneratedActive1 h1)) = ‖q.amp1‖ ^ 2 := by
  rw [recordBranch_weight_eq_norm_sq (jointBranch (idealRecords R) (idealGeneratedState q R))
    (idealGeneratedState_norm q R) (jointBranch_sum (idealRecords R) (idealGeneratedState q R))
    (fun x y hxy => jointBranch_orthogonal (idealRecords R) (idealGeneratedState q R)
      (fun _ => idealGeneratedState_isRecordedOn q R) (idealRecords_commuteWitness_vacuous R) hxy)
    Est hn3 hA hN hPos hNul D (idealGeneratedActive1 h1) hDf]
  show ‖jointBranch (idealRecords R) (idealGeneratedState q R) (fun _ => 1)‖ ^ 2 = ‖q.amp1‖ ^ 2
  rw [idealGenerated_branch1, norm_smul, basis11_norm]
  simp

theorem idealGenerated_branch_weights_sum : ‖q.amp0‖ ^ 2 + ‖q.amp1‖ ^ 2 = 1 := q.norm_sq

end

end QuantumFoundations.BranchesRiedel.BornBridge
