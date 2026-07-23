import QuantumFoundations.BranchesRiedel.BornBridge.BranchPerspective
import QuantumFoundations.BornRule.Assembly

/-!
# C14f — Born weights of record-induced branches

This file connects `C14c`'s projection identity to the existing
`BornRule.grainCoherenceTheorem_projector`, without reproving Gleason's
theorem or non-contextuality (`BornRule.lemma4_noncontextual`). The
estimation-rule API used here is exactly the one already exported by
`BornRule.Assembly`/`BornRule.Perspective`: `Est : Perspective n →
Submodule ℂ (H n) → ℝ`, together with the `AxGrain`/`AxNorm`/`AxPos`/`AxNul`
hypotheses (there is no separate `EstimationRule` structure in the
repository — `Est` is a bare function, as elsewhere in `BornRule`).

Throughout, `v := ψ` (the fixed unit vector of `AxNul`/`grainCoherenceTheorem`
*is* the state whose branch decomposition we are studying).
-/

namespace QuantumFoundations.BranchesRiedel.BornBridge

open scoped InnerProductSpace Classical
open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.BornRule

noncomputable section

variable {n : ℕ} {F : Type*} [Fintype F]

/-- `Gleason.projL` and `Submodule.starProjection` coincide, definitionally;
this bridges `grainCoherenceTheorem_projector`'s `‖projL c v‖ ^ 2` form to
`C14c`'s `starProjection`-based projection identities. -/
theorem projL_eq_starProjection (c : Submodule ℂ (H n)) (x : H n) :
    projL c x = c.starProjection x := rfl

/-! ## C14f.1 — Active branch weight -/

/-- **The central Born-weight identity.** For any perspective `D` containing
the branch cell `branchCell B f`, an estimation rule satisfying (Grain),
(Norm), (Pos), (Null) at the unit vector `ψ` assigns it exactly the squared
branch norm. Proved by chaining `grainCoherenceTheorem_projector` (Born
weight = squared projector norm) with `bornQuantity_branchCell` (squared
projector norm = squared branch norm) — never assumed as a rewrite target. -/
theorem recordBranch_weight_eq_norm_sq (B : F → H n) {ψ : H n} (hψ : ‖ψ‖ = 1)
    (hsum : ∑ g : F, B g = ψ) (hortho : Pairwise (fun x y : F => ⟪B x, B y⟫_ℂ = 0))
    (Est : Perspective n → Submodule ℂ (H n) → ℝ) (hn3 : 3 ≤ n)
    (hA : AxGrain Est) (hN : AxNorm Est) (hPos : AxPos Est) (hNul : AxNul Est ψ)
    (D : Perspective n) (f : ActiveBranchIndex B) (hDf : branchCell B f ∈ D.cells) :
    Est D (branchCell B f) = ‖activeBranchVector B f‖ ^ 2 := by
  rw [grainCoherenceTheorem_projector Est hn3 hA hN hPos hψ hNul D hDf, projL_eq_starProjection]
  exact bornQuantity_branchCell B hsum hortho f

/-! ## C14f.2 — Residual weight -/

/-- **Residual weight, via the Born projector formula.** The residual cell,
if it belongs to a perspective, is assigned weight zero, because its
projection of `ψ` is zero (`C14d`'s `starProjection_residualCell_apply_state`). -/
theorem residualCell_weight_eq_zero (B : F → H n) {ψ : H n} (hψ : ‖ψ‖ = 1)
    (hsum : ∑ g : F, B g = ψ) (Est : Perspective n → Submodule ℂ (H n) → ℝ) (hn3 : 3 ≤ n)
    (hA : AxGrain Est) (hN : AxNorm Est) (hPos : AxPos Est) (hNul : AxNul Est ψ)
    (D : Perspective n) (hDres : residualCell B ∈ D.cells) :
    Est D (residualCell B) = 0 := by
  rw [grainCoherenceTheorem_projector Est hn3 hA hN hPos hψ hNul D hDres, projL_eq_starProjection,
    starProjection_residualCell_apply_state B hsum, norm_zero]
  ring

/-- **Residual weight, via (Null) directly.** The same conclusion, derived
instead from `AxNul` applied to the fact that `ψ` is orthogonal to the
residual cell (`residualCell_orthogonal_state`) — an independent proof
route, as short as the projector-formula one. -/
theorem residualCell_weight_eq_zero_of_null (B : F → H n) {ψ : H n}
    (hsum : ∑ g : F, B g = ψ) (Est : Perspective n → Submodule ℂ (H n) → ℝ) (hNul : AxNul Est ψ)
    (D : Perspective n) (hDres : residualCell B ∈ D.cells) :
    Est D (residualCell B) = 0 :=
  hNul D (residualCell B) hDres
    ((Submodule.mem_orthogonal (residualCell B) ψ).mpr (residualCell_orthogonal_state B hsum))

/-! ## C14f.3 — Normalization over active branches -/

/-- The squared norms of the active branch vectors sum to one, for a
normalized `ψ`. A direct corollary of pairwise orthogonality and
reconstruction (`Pythagoras`), independent of any estimation-rule
hypothesis. -/
theorem sum_activeBranch_norm_sq_eq_one (B : F → H n) {ψ : H n} (hψ : ‖ψ‖ = 1)
    (hsum : ∑ g : F, B g = ψ) (hortho : Pairwise (fun x y : F => ⟪B x, B y⟫_ℂ = 0)) :
    ∑ f : ActiveBranchIndex B, ‖activeBranchVector B f‖ ^ 2 = 1 := by
  have hrecon : ∑ f : ActiveBranchIndex B, activeBranchVector B f = ψ :=
    sum_over_F_eq_sum_active B hsum
  have hpyth := norm_sq_sum_of_pairwise_orthogonal (Finset.univ : Finset (ActiveBranchIndex B))
    (activeBranchVector B) (fun i _ j _ hij => hortho (fun h => hij (Subtype.ext h)))
  rw [hrecon, hψ] at hpyth
  simpa using hpyth.symm

/-- The active branch *weights* (not merely the branch norms) also sum to
one, for any perspective containing all the active branch cells (e.g. a
`BranchPerspectivePackage`'s `perspective`). -/
theorem sum_activeBranch_weights_eq_one (B : F → H n) {ψ : H n} (hψ : ‖ψ‖ = 1)
    (hsum : ∑ g : F, B g = ψ) (hortho : Pairwise (fun x y : F => ⟪B x, B y⟫_ℂ = 0))
    (Est : Perspective n → Submodule ℂ (H n) → ℝ) (hn3 : 3 ≤ n)
    (hA : AxGrain Est) (hN : AxNorm Est) (hPos : AxPos Est) (hNul : AxNul Est ψ)
    (D : Perspective n) (hDmem : ∀ f : ActiveBranchIndex B, branchCell B f ∈ D.cells) :
    ∑ f : ActiveBranchIndex B, Est D (branchCell B f) = 1 := by
  have heach : ∀ f : ActiveBranchIndex B, Est D (branchCell B f) = ‖activeBranchVector B f‖ ^ 2 :=
    fun f => recordBranch_weight_eq_norm_sq B hψ hsum hortho Est hn3 hA hN hPos hNul D f (hDmem f)
  simp_rw [heach]
  exact sum_activeBranch_norm_sq_eq_one B hψ hsum hortho

/-! ## C14f.4 — Uniqueness of the branch weighting -/

/-- Two estimation rules satisfying (Pos), (Norm), (Grain), (Null) at the
same unit vector `ψ` assign the same weight to every active branch cell: a
direct corollary of both equalling the squared branch norm. -/
theorem recordBranch_weights_unique (B : F → H n) {ψ : H n} (hψ : ‖ψ‖ = 1)
    (hsum : ∑ g : F, B g = ψ) (hortho : Pairwise (fun x y : F => ⟪B x, B y⟫_ℂ = 0))
    (E₁ E₂ : Perspective n → Submodule ℂ (H n) → ℝ) (hn3 : 3 ≤ n)
    (hA₁ : AxGrain E₁) (hN₁ : AxNorm E₁) (hPos₁ : AxPos E₁) (hNul₁ : AxNul E₁ ψ)
    (hA₂ : AxGrain E₂) (hN₂ : AxNorm E₂) (hPos₂ : AxPos E₂) (hNul₂ : AxNul E₂ ψ)
    (D : Perspective n) (f : ActiveBranchIndex B) (hDf : branchCell B f ∈ D.cells) :
    E₁ D (branchCell B f) = E₂ D (branchCell B f) := by
  rw [recordBranch_weight_eq_norm_sq B hψ hsum hortho E₁ hn3 hA₁ hN₁ hPos₁ hNul₁ D f hDf,
    recordBranch_weight_eq_norm_sq B hψ hsum hortho E₂ hn3 hA₂ hN₂ hPos₂ hNul₂ D f hDf]

/-! ## C14f.5 — Record-choice invariance of the weights -/

/-- **Record-choice invariance of the Born weight.** For every valid
selected-record presentation, the weight assigned to its branch cell equals
the squared norm of the *canonical* joint branch — because `C14a` already
identifies the underlying branch *vectors* (`jointBranchWithChoice_eq_jointBranch`),
not merely their norms, the branch cell itself is unaffected by the choice
of records, and the Born weight is computed for that (unchanged) cell. -/
theorem recordChoice_weight_invariant {K R A : ℕ}
    (Obs : Fin A → Fin R → LabeledResolution n K) {ψ : H n}
    (hrec : ∀ a, IsRecordedOn ψ (Obs a)) (hcw : CommuteWitness Obs) [NeZero R] [NeZero K]
    (choice : RecordChoice A R) (hψ : ‖ψ‖ = 1)
    (Est : Perspective n → Submodule ℂ (H n) → ℝ) (hn3 : 3 ≤ n)
    (hA : AxGrain Est) (hN : AxNorm Est) (hPos : AxPos Est) (hNul : AxNul Est ψ)
    (D : Perspective n) (f : ActiveBranchIndex (jointBranchWithChoice Obs choice ψ))
    (hDf : branchCell (jointBranchWithChoice Obs choice ψ) f ∈ D.cells) :
    Est D (branchCell (jointBranchWithChoice Obs choice ψ) f) = ‖jointBranch Obs ψ f.1‖ ^ 2 := by
  have hveq : jointBranchWithChoice Obs choice ψ f.1 = jointBranch Obs ψ f.1 :=
    jointBranchWithChoice_eq_jointBranch Obs ψ hrec hcw choice f.1
  rw [← hveq]
  exact recordBranch_weight_eq_norm_sq (jointBranchWithChoice Obs choice ψ) hψ
    (jointBranchWithChoice_sum Obs ψ hrec hcw choice)
    (fun x y hxy => jointBranchWithChoice_orthogonal Obs ψ hrec hcw choice hxy)
    Est hn3 hA hN hPos hNul D f hDf

end

end QuantumFoundations.BranchesRiedel.BornBridge
