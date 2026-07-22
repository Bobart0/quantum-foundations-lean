import QuantumFoundations.BranchesRiedel.Basic

/-!
# C3 — Normalized recorded branches

Riedel's `branch` is intentionally unnormalized.  This file supplies only
the normalization needed by the exact circuit proxy statements.  All useful
properties explicitly assume that the raw branch is nonzero.
-/

namespace QuantumFoundations.Complexity

open scoped InnerProductSpace

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

/-- Normalize a Riedel branch by its norm.  If the raw branch is zero this
definition evaluates to zero; theorems asserting unit norm require a
nonzero-branch hypothesis. -/
noncomputable def normalizedBranch {n K R : ℕ} [NeZero R]
    (recs : Fin R → LabeledResolution n K) (ψ : H n) (i : Fin K) : H n :=
  ((‖branch recs ψ i‖ : ℂ)⁻¹) • branch recs ψ i

/-- The defining scalar-multiple form of a normalized branch. -/
theorem normalizedBranch_eq_smul_branch {n K R : ℕ} [NeZero R]
    (recs : Fin R → LabeledResolution n K) (ψ : H n) (i : Fin K) :
    normalizedBranch recs ψ i =
      ((‖branch recs ψ i‖ : ℂ)⁻¹) • branch recs ψ i := rfl

/-- A normalized nonzero branch has norm one. -/
theorem normalizedBranch_norm {n K R : ℕ} [NeZero R]
    (recs : Fin R → LabeledResolution n K) (ψ : H n) (i : Fin K)
    (hi : branch recs ψ i ≠ 0) :
    ‖normalizedBranch recs ψ i‖ = 1 := by
  rw [normalizedBranch_eq_smul_branch, norm_smul, norm_inv,
    Complex.norm_real, norm_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hi)

/-- Normalizing a nonzero branch does not annihilate it. -/
theorem normalizedBranch_ne_zero {n K R : ℕ} [NeZero R]
    (recs : Fin R → LabeledResolution n K) (ψ : H n) (i : Fin K)
    (hi : branch recs ψ i ≠ 0) :
    normalizedBranch recs ψ i ≠ 0 := by
  rw [normalizedBranch_eq_smul_branch]
  exact smul_ne_zero
    (inv_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hi))) hi

/-- A record projector for label `j` fixes the normalized `j` branch. -/
theorem recordProj_normalizedBranch_same {n K R : ℕ} [NeZero R]
    (recs : Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : IsRecordedOn ψ recs) (r : Fin R) (j : Fin K) :
    rproj (recs r) j (normalizedBranch recs ψ j) =
      normalizedBranch recs ψ j := by
  rw [normalizedBranch_eq_smul_branch, map_smul,
    branch_wellDefined ψ recs hrec r j,
    rproj_contract_apply, if_pos rfl, one_smul]

/-- A record projector for label `j` annihilates a normalized branch with a
different label `i`. -/
theorem recordProj_normalizedBranch_other {n K R : ℕ} [NeZero R]
    (recs : Fin R → LabeledResolution n K) (ψ : H n)
    (hrec : IsRecordedOn ψ recs) (r : Fin R) (i j : Fin K) (hij : i ≠ j) :
    rproj (recs r) j (normalizedBranch recs ψ i) = 0 := by
  rw [normalizedBranch_eq_smul_branch, map_smul,
    branch_wellDefined ψ recs hrec r i,
    rproj_contract_apply, if_neg (Ne.symm hij), zero_smul, smul_zero]

/-- Distinct normalized Riedel branches are orthogonal.  The underlying raw
orthogonality follows from the labeled resolution itself. -/
theorem normalizedBranches_inner_eq_zero {n K R : ℕ} [NeZero R]
    (recs : Fin R → LabeledResolution n K) (ψ : H n)
    (i j : Fin K) (hij : i ≠ j) :
    ⟪normalizedBranch recs ψ i, normalizedBranch recs ψ j⟫_ℂ = 0 := by
  rw [normalizedBranch_eq_smul_branch, normalizedBranch_eq_smul_branch,
    inner_smul_left, inner_smul_right, branch_orthogonal ψ recs hij]
  simp

end

end QuantumFoundations.Complexity
