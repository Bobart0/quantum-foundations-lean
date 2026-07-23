import QuantumFoundations.BranchesRiedel.BornBridge.BranchCells

/-!
# C14d — Branch support and residual cell, C14e — the formal branch perspective

`branchSupport B` is the supremum of the active branch cells: it need not be
the whole space `H n`, because a redundant record family generally lives on
a proper subspace of some ambient system (or, more simply, because some
branch labels may carry zero amplitude). `residualCell B` is its orthogonal
complement, which may be `⊥`.

Because a `Perspective` (`BornRule.Perspective`) forbids `⊥` cells, the
residual cell can only be *inserted* into a perspective when it is nonzero.
`branchPerspective` therefore case-splits on `branchSupport B = ⊤` (no
residual cell needed) versus `branchSupport B ≠ ⊤` (the residual cell is
added, and is itself nonzero and disjoint from every active cell).
-/

namespace QuantumFoundations.BranchesRiedel.BornBridge

open scoped InnerProductSpace Classical
open Gleason
open QuantumFoundations.BornRule

noncomputable section

variable {n : ℕ} {F : Type*} [Fintype F]

/-! ## C14d — Branch support and residual cell -/

/-- The support of the active branch family: the supremum of its cells.
Spans the state `ψ` (`ψ_mem_branchSupport`), but not necessarily the whole
space `H n`. -/
def branchSupport (B : F → H n) : Submodule ℂ (H n) :=
  ⨆ f : ActiveBranchIndex B, branchCell B f

theorem activeBranchVector_mem_branchSupport (B : F → H n) (f : ActiveBranchIndex B) :
    activeBranchVector B f ∈ branchSupport B :=
  (le_iSup (fun f => branchCell B f) f) (activeBranchVector_mem_branchCell B f)

theorem ψ_mem_branchSupport (B : F → H n) {ψ : H n} (hsum : ∑ g : F, B g = ψ) :
    ψ ∈ branchSupport B := by
  rw [← sum_over_F_eq_sum_active B hsum]
  exact Submodule.sum_mem _ (fun f _ => activeBranchVector_mem_branchSupport B f)

/-- The residual orthogonal cell: everything not spanned by the active
branches. May be `⊥`. -/
def residualCell (B : F → H n) : Submodule ℂ (H n) := (branchSupport B)ᗮ

theorem residualCell_orthogonal_active (B : F → H n) (f : ActiveBranchIndex B) :
    branchCell B f ≤ (residualCell B)ᗮ :=
  le_trans (le_iSup (fun f => branchCell B f) f) (Submodule.le_orthogonal_orthogonal _)

/-- The symmetric form: the residual cell is orthogonal to every active
branch cell. -/
theorem residualCell_orthogonal_active' (B : F → H n) (f : ActiveBranchIndex B) :
    residualCell B ≤ (branchCell B f)ᗮ :=
  (Submodule.isOrtho_iff_le.mpr (residualCell_orthogonal_active B f)).ge

theorem starProjection_residualCell_apply_state (B : F → H n) {ψ : H n}
    (hsum : ∑ g : F, B g = ψ) : (residualCell B).starProjection ψ = 0 := by
  rw [residualCell, Submodule.starProjection_apply_eq_zero_iff]
  exact Submodule.le_orthogonal_orthogonal (branchSupport B) (ψ_mem_branchSupport B hsum)

theorem residualCell_orthogonal_state (B : F → H n) {ψ : H n}
    (hsum : ∑ g : F, B g = ψ) : ∀ x ∈ residualCell B, ⟪x, ψ⟫_ℂ = 0 := by
  intro x hx
  have h := (Submodule.mem_orthogonal (branchSupport B) x).mp hx ψ (ψ_mem_branchSupport B hsum)
  rw [← inner_conj_symm x ψ, h]
  simp

theorem branchSupport_sup_residualCell (B : F → H n) : branchSupport B ⊔ residualCell B = ⊤ :=
  Submodule.sup_orthogonal_of_hasOrthogonalProjection

theorem branchSupport_disjoint_residualCell (B : F → H n) :
    Disjoint (branchSupport B) (residualCell B) :=
  Submodule.orthogonal_disjoint (branchSupport B)

/-! ## C14e — The record-induced formal perspective -/

/-- The `Finset` of active branch cells, as a subset of `Submodule ℂ (H n)`.
Injective by `branchCell_injective`, so it has exactly `Fintype.card
(ActiveBranchIndex B)` elements. -/
def activeCellsFinset (B : F → H n) : Finset (Submodule ℂ (H n)) :=
  Finset.univ.image (branchCell B)

theorem mem_activeCellsFinset_iff (B : F → H n) (c : Submodule ℂ (H n)) :
    c ∈ activeCellsFinset B ↔ ∃ f : ActiveBranchIndex B, branchCell B f = c := by
  simp [activeCellsFinset]

/-- **Full-support case.** When `branchSupport B = ⊤`, the active branch
cells alone already form a `Perspective`. -/
def branchPerspectiveOfFullSupport (B : F → H n) (hortho : Pairwise (fun x y : F => ⟪B x, B y⟫_ℂ = 0))
    (hfull : branchSupport B = ⊤) : Perspective n where
  cells := activeCellsFinset B
  nz := by
    intro c hc
    obtain ⟨f, rfl⟩ := (mem_activeCellsFinset_iff B c).mp hc
    exact branchCell_ne_bot B f
  ortho := by
    intro c hc c' hc' hne
    obtain ⟨f, rfl⟩ := (mem_activeCellsFinset_iff B c).mp hc
    obtain ⟨g, rfl⟩ := (mem_activeCellsFinset_iff B c').mp hc'
    exact branchCells_pairwise_orthogonal B hortho f g
      (fun h => hne (by rw [h]))
  span := by
    rw [activeCellsFinset, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rw [← hfull, branchSupport]
    apply le_antisymm
    · exact sSup_le (fun c ⟨f, hf⟩ => hf ▸ le_iSup (fun f => branchCell B f) f)
    · exact iSup_le (fun f => le_sSup ⟨f, rfl⟩)

/-- **Non-full-support case.** When `branchSupport B ≠ ⊤`, the residual
cell is nonzero and is adjoined to the active branch cells. -/
def branchPerspectiveOfResidual (B : F → H n)
    (hortho : Pairwise (fun x y : F => ⟪B x, B y⟫_ℂ = 0))
    (hres : residualCell B ≠ ⊥) : Perspective n where
  cells := insert (residualCell B) (activeCellsFinset B)
  nz := by
    intro c hc
    rw [Finset.mem_insert] at hc
    rcases hc with rfl | hc
    · exact hres
    · obtain ⟨f, rfl⟩ := (mem_activeCellsFinset_iff B c).mp hc
      exact branchCell_ne_bot B f
  ortho := by
    intro c hc c' hc' hne
    rw [Finset.mem_insert] at hc hc'
    rcases hc with rfl | hc
    · rcases hc' with rfl | hc'
      · exact absurd rfl hne
      · obtain ⟨g, rfl⟩ := (mem_activeCellsFinset_iff B c').mp hc'
        exact residualCell_orthogonal_active' B g
    · obtain ⟨f, rfl⟩ := (mem_activeCellsFinset_iff B c).mp hc
      rcases hc' with rfl | hc'
      · exact residualCell_orthogonal_active B f
      · obtain ⟨g, rfl⟩ := (mem_activeCellsFinset_iff B c').mp hc'
        exact branchCells_pairwise_orthogonal B hortho f g (fun h => hne (by rw [h]))
  span := by
    show sSup ((insert (residualCell B) (activeCellsFinset B) :
      Finset (Submodule ℂ (H n))) : Set (Submodule ℂ (H n))) = ⊤
    rw [Finset.coe_insert]
    rw [sSup_insert]
    rw [activeCellsFinset, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    have hactive : sSup (Set.range (branchCell B)) = branchSupport B := by
      rw [branchSupport]; exact (sSup_range).symm
    rw [hactive, sup_comm]
    exact branchSupport_sup_residualCell B

/-! ## C14e — Unified package -/

/-- **The unified public API.** A `Perspective n` built from the active
branch cells, together with the data connecting it back to the branch
family: every active cell genuinely belongs to the perspective, the
residual cell either belongs to it too or is `⊥` (the full-support case),
and every cell of the perspective is either an active branch cell or the
residual cell. Adapted from the task's suggested structure to the
repository's actual `Perspective` API, where cells are literally
`Submodule ℂ (H n)` values (a `Finset`), not an abstract indexed `Cell`
type. -/
structure BranchPerspectivePackage (B : F → H n) where
  /-- The underlying formal perspective. -/
  perspective : Perspective n
  /-- Every active branch cell belongs to the perspective. -/
  activeCell_mem : ∀ f : ActiveBranchIndex B, branchCell B f ∈ perspective.cells
  /-- The residual cell belongs to the perspective, or is trivial (`⊥`). -/
  residual_mem_or_bot : residualCell B ∈ perspective.cells ∨ residualCell B = ⊥
  /-- Every cell of the perspective is an active branch cell or the
  residual cell. -/
  cells_exhaust : ∀ c ∈ perspective.cells,
    (∃ f : ActiveBranchIndex B, branchCell B f = c) ∨ c = residualCell B

/-- **The public existence theorem.** Both perspective constructions
(full-support and residual) package into a `BranchPerspectivePackage`. -/
theorem exists_branchPerspectivePackage (B : F → H n)
    (hortho : Pairwise (fun x y : F => ⟪B x, B y⟫_ℂ = 0)) :
    ∃ _ : BranchPerspectivePackage B, True := by
  by_cases hfull : branchSupport B = ⊤
  · have hresbot : residualCell B = ⊥ := by rw [residualCell, hfull, Submodule.top_orthogonal_eq_bot]
    exact ⟨{ perspective := branchPerspectiveOfFullSupport B hortho hfull
             activeCell_mem := fun f => (mem_activeCellsFinset_iff B _).mpr ⟨f, rfl⟩
             residual_mem_or_bot := Or.inr hresbot
             cells_exhaust := fun c hc => Or.inl ((mem_activeCellsFinset_iff B c).mp hc) }, trivial⟩
  · have hres : residualCell B ≠ ⊥ := by
      intro hbot
      apply hfull
      have := branchSupport_sup_residualCell B
      rw [hbot, sup_bot_eq] at this
      exact this
    refine ⟨{ perspective := branchPerspectiveOfResidual B hortho hres
              activeCell_mem := fun f => Finset.mem_insert_of_mem
                ((mem_activeCellsFinset_iff B _).mpr ⟨f, rfl⟩)
              residual_mem_or_bot := Or.inl (Finset.mem_insert_self _ _)
              cells_exhaust := fun c hc => ?_ }, trivial⟩
    rw [branchPerspectiveOfResidual, Finset.mem_insert] at hc
    rcases hc with rfl | hc
    · exact Or.inr rfl
    · exact Or.inl ((mem_activeCellsFinset_iff B c).mp hc)

/-- **Section C14e, the residual cell is distinct from every active cell.**
When the residual cell is nonzero, it cannot equal any active branch cell
(an active cell is contained in `branchSupport B`, while the residual cell
is disjoint from it and nonzero). -/
theorem residualCell_ne_branchCell (B : F → H n) (hres : residualCell B ≠ ⊥)
    (f : ActiveBranchIndex B) : residualCell B ≠ branchCell B f := by
  intro heq
  apply hres
  have hle : branchCell B f ≤ branchSupport B := le_iSup (fun f => branchCell B f) f
  have hle' : residualCell B ≤ branchSupport B := heq ▸ hle
  have hdisj : branchSupport B ⊓ residualCell B = ⊥ :=
    (branchSupport_disjoint_residualCell B).eq_bot
  have hmem : residualCell B ≤ branchSupport B ⊓ residualCell B := le_inf hle' (le_refl _)
  rw [hdisj] at hmem
  exact le_bot_iff.mp hmem

end

end QuantumFoundations.BranchesRiedel.BornBridge
