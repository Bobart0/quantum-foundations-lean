import QuantumFoundations.BranchesRiedel.BornBridge.BornWeights
import QuantumFoundations.BornRule.RestrictedRecordSectors.Stability

/-!
# C17b — Stability bridge for C14 branch weights

The C14 Born-weight identity rewrites each explicitly selected active-branch
weight as the squared norm of its active branch vector.  The generic C17
estimate then compares two branches whose correspondence is supplied by the
caller.  No matching or approximate branch-uniqueness result is asserted.
-/

namespace QuantumFoundations.BranchesRiedel.BornBridge

open scoped InnerProductSpace Classical
open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.BornRule
open QuantumFoundations.BornRule.RestrictedRecordSectors

noncomputable section

variable {n : ℕ} {F₁ F₂ : Type*} [Fintype F₁] [Fintype F₂]

/-- C14 weights of two explicitly matched active branches inherit the generic
C17 branch-vector stability estimate. -/
theorem recordBranch_weight_pointwise_stability
    (B₁ : F₁ → H n) (B₂ : F₂ → H n)
    {ψ₁ ψ₂ : H n}
    (hψ₁ : ‖ψ₁‖ = 1) (hψ₂ : ‖ψ₂‖ = 1)
    (hsum₁ : ∑ g : F₁, B₁ g = ψ₁)
    (hsum₂ : ∑ g : F₂, B₂ g = ψ₂)
    (hortho₁ : Pairwise (fun x y : F₁ => ⟪B₁ x, B₁ y⟫_ℂ = 0))
    (hortho₂ : Pairwise (fun x y : F₂ => ⟪B₂ x, B₂ y⟫_ℂ = 0))
    (E₁ E₂ : Perspective n → Submodule ℂ (H n) → ℝ)
    (hn3 : 3 ≤ n)
    (hA₁ : AxGrain E₁) (hN₁ : AxNorm E₁)
    (hPos₁ : AxPos E₁) (hNul₁ : AxNul E₁ ψ₁)
    (hA₂ : AxGrain E₂) (hN₂ : AxNorm E₂)
    (hPos₂ : AxPos E₂) (hNul₂ : AxNul E₂ ψ₂)
    (D₁ D₂ : Perspective n)
    (f₁ : ActiveBranchIndex B₁) (f₂ : ActiveBranchIndex B₂)
    (hDf₁ : branchCell B₁ f₁ ∈ D₁.cells)
    (hDf₂ : branchCell B₂ f₂ ∈ D₂.cells) :
    |E₁ D₁ (branchCell B₁ f₁) - E₂ D₂ (branchCell B₂ f₂)|
      ≤
    (‖activeBranchVector B₁ f₁‖ + ‖activeBranchVector B₂ f₂‖) *
      ‖activeBranchVector B₁ f₁ - activeBranchVector B₂ f₂‖ := by
  rw [recordBranch_weight_eq_norm_sq B₁ hψ₁ hsum₁ hortho₁
      E₁ hn3 hA₁ hN₁ hPos₁ hNul₁ D₁ f₁ hDf₁,
    recordBranch_weight_eq_norm_sq B₂ hψ₂ hsum₂ hortho₂
      E₂ hn3 hA₂ hN₂ hPos₂ hNul₂ D₂ f₂ hDf₂]
  exact abs_norm_sq_sub_norm_sq_le _ _

/-- Unit-ball form of the C14 branch-vector stability estimate.  The caller
supplies the correspondence between `f₁` and `f₂` and the two norm bounds. -/
theorem recordBranch_weight_pointwise_stability_of_unit_bound
    (B₁ : F₁ → H n) (B₂ : F₂ → H n)
    {ψ₁ ψ₂ : H n}
    (hψ₁ : ‖ψ₁‖ = 1) (hψ₂ : ‖ψ₂‖ = 1)
    (hsum₁ : ∑ g : F₁, B₁ g = ψ₁)
    (hsum₂ : ∑ g : F₂, B₂ g = ψ₂)
    (hortho₁ : Pairwise (fun x y : F₁ => ⟪B₁ x, B₁ y⟫_ℂ = 0))
    (hortho₂ : Pairwise (fun x y : F₂ => ⟪B₂ x, B₂ y⟫_ℂ = 0))
    (E₁ E₂ : Perspective n → Submodule ℂ (H n) → ℝ)
    (hn3 : 3 ≤ n)
    (hA₁ : AxGrain E₁) (hN₁ : AxNorm E₁)
    (hPos₁ : AxPos E₁) (hNul₁ : AxNul E₁ ψ₁)
    (hA₂ : AxGrain E₂) (hN₂ : AxNorm E₂)
    (hPos₂ : AxPos E₂) (hNul₂ : AxNul E₂ ψ₂)
    (D₁ D₂ : Perspective n)
    (f₁ : ActiveBranchIndex B₁) (f₂ : ActiveBranchIndex B₂)
    (hDf₁ : branchCell B₁ f₁ ∈ D₁.cells)
    (hDf₂ : branchCell B₂ f₂ ∈ D₂.cells)
    (hf₁ : ‖activeBranchVector B₁ f₁‖ ≤ 1)
    (hf₂ : ‖activeBranchVector B₂ f₂‖ ≤ 1) :
    |E₁ D₁ (branchCell B₁ f₁) - E₂ D₂ (branchCell B₂ f₂)|
      ≤ 2 * ‖activeBranchVector B₁ f₁ - activeBranchVector B₂ f₂‖ := by
  rw [recordBranch_weight_eq_norm_sq B₁ hψ₁ hsum₁ hortho₁
      E₁ hn3 hA₁ hN₁ hPos₁ hNul₁ D₁ f₁ hDf₁,
    recordBranch_weight_eq_norm_sq B₂ hψ₂ hsum₂ hortho₂
      E₂ hn3 hA₂ hN₂ hPos₂ hNul₂ D₂ f₂ hDf₂]
  exact abs_norm_sq_sub_norm_sq_le_two_mul _ _ hf₁ hf₂

end

end QuantumFoundations.BranchesRiedel.BornBridge
