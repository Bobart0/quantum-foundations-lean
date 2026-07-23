import QuantumFoundations.BranchesRiedel.BornBridge.ActiveBranches

/-!
# C14b.2 — Branch cells, and C14c — projection onto a branch cell

A branch *cell* is the one-dimensional span of an active branch vector —
defined only for active indices, since a zero vector's span is `⊥`, which no
`Perspective` cell may equal. `branchCell_injective` needs pairwise
orthogonality of the branch family: two distinct nonzero vectors do not, in
general, span distinct lines (a nonzero scalar multiple spans the same
line), so genuine orthogonality between distinct branch vectors is what
rules this out.

The central projection identity, `starProjection_branchCell_apply_state`,
is a linear-algebra fact independent of Born weighting: splitting
`ψ = B f + ∑_{g ≠ f} B g` exhibits `ψ` as a sum of a vector in
`branchCell B f` and a vector orthogonal to it, so `Submodule.
eq_starProjection_of_mem_orthogonal'` identifies the projection directly,
without invoking Gleason or the coherence axioms at all.
-/

namespace QuantumFoundations.BranchesRiedel.BornBridge

open scoped InnerProductSpace Classical
open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

variable {n : ℕ} {F : Type*} [Fintype F]

/-- The active branch *cell*: the one-dimensional span of the active branch
vector. Defined only for active indices — this is precisely why zero
branches are excluded from `ActiveBranchIndex`. -/
def branchCell (B : F → H n) (f : ActiveBranchIndex B) : Submodule ℂ (H n) :=
  Submodule.span ℂ {activeBranchVector B f}

theorem branchCell_eq_span_singleton (B : F → H n) (f : ActiveBranchIndex B) :
    branchCell B f = Submodule.span ℂ {activeBranchVector B f} := rfl

theorem activeBranchVector_mem_branchCell (B : F → H n) (f : ActiveBranchIndex B) :
    activeBranchVector B f ∈ branchCell B f :=
  Submodule.mem_span_singleton_self _

theorem branchCell_ne_bot (B : F → H n) (f : ActiveBranchIndex B) : branchCell B f ≠ ⊥ := by
  rw [branchCell, Submodule.ne_bot_iff]
  exact ⟨activeBranchVector B f, Submodule.mem_span_singleton_self _,
    activeBranchVector_ne_zero B f⟩

/-! ## C14b.3 — Orthogonality and injectivity -/

/-- Pairwise orthogonality of the cells, in the exact form needed by
`Perspective.ortho`: `f ≠ g → branchCell B f ≤ (branchCell B g)ᗮ`. -/
theorem branchCells_pairwise_orthogonal (B : F → H n)
    (hortho : Pairwise (fun x y : F => ⟪B x, B y⟫_ℂ = 0)) :
    ∀ f g : ActiveBranchIndex B, f ≠ g → branchCell B f ≤ (branchCell B g)ᗮ := by
  intro f g hfg
  have hfg1 : f.1 ≠ g.1 := fun h => hfg (Subtype.ext h)
  rw [branchCell, branchCell, Submodule.span_singleton_le_iff_mem,
    Submodule.mem_orthogonal_singleton_iff_inner_left]
  exact hortho hfg1

/-- **Section C14b.** Two active indices with the same branch cell must
coincide: if `branchCell B f = branchCell B g`, then `activeBranchVector B f`
lies in `branchCell B g`, so it is a scalar multiple of `activeBranchVector
B g`; if `f ≠ g`, orthogonality forces that scalar to be zero, contradicting
`activeBranchVector B f ≠ 0`. This genuinely uses orthogonality: distinct
nonzero vectors need not have distinct spans without it. -/
theorem branchCell_injective (B : F → H n)
    (hortho : Pairwise (fun x y : F => ⟪B x, B y⟫_ℂ = 0)) :
    Function.Injective (branchCell B) := by
  intro f g heq
  by_contra hfg
  have hfg1 : f.1 ≠ g.1 := fun h => hfg (Subtype.ext h)
  have hmem : activeBranchVector B f ∈ branchCell B g := heq ▸ activeBranchVector_mem_branchCell B f
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hinner0 : (⟪activeBranchVector B g, activeBranchVector B f⟫_ℂ : ℂ) = 0 :=
    hortho (Ne.symm hfg1)
  rw [← hc, inner_smul_right] at hinner0
  have hgg_ne : (⟪activeBranchVector B g, activeBranchVector B g⟫_ℂ : ℂ) ≠ 0 :=
    inner_self_ne_zero.mpr (activeBranchVector_ne_zero B g)
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp hinner0 with h | h
    · exact h
    · exact absurd h hgg_ne
  rw [hc0, zero_smul] at hc
  exact activeBranchVector_ne_zero B f hc.symm

/-! ## C14c — Projection of the state onto a branch cell -/

/-- **The central projection identity.** Given reconstruction of `ψ` from
the *full* branch family (`∑ g : F, B g = ψ`) and pairwise orthogonality,
the state's orthogonal projection onto any active branch cell is exactly
the active branch vector itself. A pure linear-algebra fact, established
independently of any Born-weight/estimation-rule hypothesis. -/
theorem starProjection_branchCell_apply_state (B : F → H n) {ψ : H n}
    (hsum : ∑ g : F, B g = ψ) (hortho : Pairwise (fun x y : F => ⟪B x, B y⟫_ℂ = 0))
    (f : ActiveBranchIndex B) :
    (branchCell B f).starProjection ψ = activeBranchVector B f := by
  set z : H n := ∑ g ∈ Finset.univ.erase f.1, B g with hz_def
  have hu : ψ = activeBranchVector B f + z := by
    rw [← hsum, hz_def, activeBranchVector]
    exact (Finset.add_sum_erase Finset.univ B (Finset.mem_univ f.1)).symm
  have hzmem : z ∈ (branchCell B f)ᗮ := by
    rw [branchCell, Submodule.mem_orthogonal_singleton_iff_inner_right, hz_def, inner_sum]
    apply Finset.sum_eq_zero
    intro g hg
    have hgf : g ≠ f.1 := Finset.ne_of_mem_erase hg
    exact hortho hgf.symm
  exact Submodule.eq_starProjection_of_mem_orthogonal' (activeBranchVector_mem_branchCell B f)
    hzmem hu

theorem norm_starProjection_branchCell_state (B : F → H n) {ψ : H n}
    (hsum : ∑ g : F, B g = ψ) (hortho : Pairwise (fun x y : F => ⟪B x, B y⟫_ℂ = 0))
    (f : ActiveBranchIndex B) :
    ‖(branchCell B f).starProjection ψ‖ = ‖activeBranchVector B f‖ := by
  rw [starProjection_branchCell_apply_state B hsum hortho f]

theorem bornQuantity_branchCell (B : F → H n) {ψ : H n}
    (hsum : ∑ g : F, B g = ψ) (hortho : Pairwise (fun x y : F => ⟪B x, B y⟫_ℂ = 0))
    (f : ActiveBranchIndex B) :
    ‖(branchCell B f).starProjection ψ‖ ^ 2 = ‖activeBranchVector B f‖ ^ 2 := by
  rw [norm_starProjection_branchCell_state B hsum hortho f]

/-- **Zero-branch analogue.** If `B f = 0` for some (not necessarily active)
index `f`, its contribution to the squared-norm accounting is zero — stated
directly on `B`, not on `ActiveBranchIndex`, since no formal cell exists for
such an `f`. -/
theorem zero_branch_norm_sq (B : F → H n) {f : F} (hf : B f = 0) : ‖B f‖ ^ 2 = 0 := by
  rw [hf, norm_zero]; ring

end

end QuantumFoundations.BranchesRiedel.BornBridge
