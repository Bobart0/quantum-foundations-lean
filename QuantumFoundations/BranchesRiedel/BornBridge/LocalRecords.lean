import QuantumFoundations.BranchesRiedel.BornBridge.Synthesis

/-!
# C14h — Local multisite corollary

Instantiates `record_induced_Born_decomposition` (C14g) at the existing
finite local record model: `CommuteWitness` is discharged via
`commuteWitness_of_not_pairCovers` (locality plus pairwise non-pair-covering
of the observable supports, exactly as in `riedel_local`), rather than
assumed directly. No local hypothesis is weakened relative to
`riedel_local`'s own.
-/

namespace QuantumFoundations.BranchesRiedel.BornBridge

open scoped InnerProductSpace Classical
open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.BornRule

noncomputable section

/-- **The local corollary.** Under the same hypotheses as `riedel_local`
(spatial locality of every record projector and pairwise non-pair-covering
of the observable supports), together with a normalized state and an
estimation rule satisfying (Pos), (Norm), (Grain), (Null), a
`RecordInducedBornConclusion` exists: unique joint branches,
arbitrary-record-choice invariance, the branch-cell perspective, squared-norm
Born weights, and normalization all hold in the finite local record
model. -/
theorem local_record_induced_Born_decomposition {N d A R K : ℕ}
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d)
    (Obs : Fin A → Fin R → LabeledResolution (d ^ N) K)
    (supp : Fin A → Fin R → Finset (Fin N)) [NeZero R] [NeZero K] (hR2 : 2 ≤ R)
    (ψ : H (d ^ N)) (hψ : ‖ψ‖ = 1)
    (hrec : ∀ a, IsRecordedOn ψ (Obs a))
    (hlocal : ∀ a r i, IsLocalTo
      (e.toLinearIsometry.toLinearMap ∘ₗ rproj (Obs a r) i ∘ₗ e.symm.toLinearIsometry.toLinearMap)
      (supp a r))
    (hnpc : ∀ a b : Fin A, a ≠ b → ¬ PairCovers (supp a) (supp b))
    (Est : Perspective (d ^ N) → Submodule ℂ (H (d ^ N)) → ℝ) (hn3 : 3 ≤ d ^ N)
    (hA : AxGrain Est) (hN : AxNorm Est) (hPos : AxPos Est) (hNul : AxNul Est ψ) :
    Nonempty (RecordInducedBornConclusion Obs ψ Est) :=
  record_induced_Born_decomposition Obs ψ hψ hrec
    (commuteWitness_of_not_pairCovers e Obs supp hR2 hlocal hnpc) Est hn3 hA hN hPos hNul

end

end QuantumFoundations.BranchesRiedel.BornBridge
