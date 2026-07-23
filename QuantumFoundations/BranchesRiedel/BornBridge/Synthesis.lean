import QuantumFoundations.BranchesRiedel.BornBridge.BornWeights

/-!
# C14g — Abstract synthesis theorem

Assembles `C14a`–`C14f` into one principal theorem, connecting Riedel's
unique record-induced branch decomposition to the Born weight assigned by
an arbitrary estimation rule satisfying (Pos), (Norm), (Grain), (Null).
The conclusion is packaged as `RecordInducedBornConclusion` rather than a
deeply nested conjunction, per the task's own guidance.

**What this theorem does not claim** (see also the file-level scope notes
throughout `C14`): it does not claim that redundant records alone imply
the Born rule — the (Pos)/(Norm)/(Grain)/(Null) hypotheses are visibly
present and used; the theorem's name deliberately avoids "Born from records
alone" for this reason.
-/

namespace QuantumFoundations.BranchesRiedel.BornBridge

open scoped InnerProductSpace Classical
open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.BornRule

noncomputable section

variable {n K R A : ℕ}

/-- **The principal C14 conclusion package.** Bundles the record-induced
formal perspective together with: the Born weight of every active cell
(equal to the squared canonical branch norm), the residual weight (zero,
when the residual cell is present), normalization of the active weights,
and record-choice invariance of the weight. -/
structure RecordInducedBornConclusion (Obs : Fin A → Fin R → LabeledResolution n K) (ψ : H n)
    (Est : Perspective n → Submodule ℂ (H n) → ℝ) [NeZero R] [NeZero K] where
  /-- The record-induced formal perspective built from the canonical joint
  branch family. -/
  perspectivePackage : BranchPerspectivePackage (jointBranch Obs ψ)
  /-- Every active branch cell is assigned exactly its squared branch norm. -/
  active_weight_eq : ∀ f : ActiveBranchIndex (jointBranch Obs ψ),
    Est perspectivePackage.perspective (branchCell (jointBranch Obs ψ) f)
      = ‖jointBranch Obs ψ f.1‖ ^ 2
  /-- The residual cell, if present in the perspective, is assigned weight
  zero. -/
  residual_weight_eq_zero :
    residualCell (jointBranch Obs ψ) ∈ perspectivePackage.perspective.cells →
      Est perspectivePackage.perspective (residualCell (jointBranch Obs ψ)) = 0
  /-- The active branch weights sum to one. -/
  active_weights_sum_one :
    ∑ f : ActiveBranchIndex (jointBranch Obs ψ),
      Est perspectivePackage.perspective (branchCell (jointBranch Obs ψ) f) = 1
  /-- The weight assigned to any valid selected-record presentation's
  branch cell agrees with the squared canonical branch norm. -/
  record_choice_invariant : ∀ (choice : RecordChoice A R)
    (f : ActiveBranchIndex (jointBranchWithChoice Obs choice ψ)),
    branchCell (jointBranchWithChoice Obs choice ψ) f ∈ perspectivePackage.perspective.cells →
      Est perspectivePackage.perspective (branchCell (jointBranchWithChoice Obs choice ψ) f)
        = ‖jointBranch Obs ψ f.1‖ ^ 2

/-- **The principal C14 theorem.** Under redundancy, a commutation witness,
a normalized state, and an estimation rule satisfying (Pos), (Norm),
(Grain), (Null), a `RecordInducedBornConclusion` exists. This connects
Riedel's branch-decomposition theorem to the Grain Coherence Theorem: it
does not derive either from the other, and does not claim that records
alone determine Born weights. -/
theorem record_induced_Born_decomposition (Obs : Fin A → Fin R → LabeledResolution n K)
    (ψ : H n) [NeZero R] [NeZero K] (hψ : ‖ψ‖ = 1)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs)
    (Est : Perspective n → Submodule ℂ (H n) → ℝ) (hn3 : 3 ≤ n)
    (hA : AxGrain Est) (hN : AxNorm Est) (hPos : AxPos Est) (hNul : AxNul Est ψ) :
    Nonempty (RecordInducedBornConclusion Obs ψ Est) := by
  set B := jointBranch Obs ψ with hB_def
  have hsum : ∑ g : Fin A → Fin K, B g = ψ := jointBranch_sum Obs ψ
  have hortho : Pairwise (fun x y : Fin A → Fin K => ⟪B x, B y⟫_ℂ = 0) :=
    fun x y hxy => jointBranch_orthogonal Obs ψ hrec hcw hxy
  obtain ⟨P, -⟩ := exists_branchPerspectivePackage B hortho
  refine ⟨⟨P, ?_, ?_, ?_, ?_⟩⟩
  · intro f
    exact recordBranch_weight_eq_norm_sq B hψ hsum hortho Est hn3 hA hN hPos hNul
      P.perspective f (P.activeCell_mem f)
  · intro hDres
    exact residualCell_weight_eq_zero B hψ hsum Est hn3 hA hN hPos hNul P.perspective hDres
  · exact sum_activeBranch_weights_eq_one B hψ hsum hortho Est hn3 hA hN hPos hNul
      P.perspective P.activeCell_mem
  · intro choice f hDf
    exact recordChoice_weight_invariant Obs hrec hcw choice hψ Est hn3 hA hN hPos hNul
      P.perspective f hDf

end

end QuantumFoundations.BranchesRiedel.BornBridge
