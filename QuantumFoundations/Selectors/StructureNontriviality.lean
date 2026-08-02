import QuantumFoundations.Selectors.PerspectiveClassification

/-!
**FR.** # Selectors — Module B, non-trivialité (hiérarchie stricte)

L'analogue, au niveau des perspectives, du fait (déjà établi au niveau
d'une seule base dans `BasisStabilizer.lean`) que fixer chaque cellule
SETWISE est une contrainte STRICTEMENT plus forte que permettre des
permutations de cellules : pour une perspective de base en dimension
`≥ 2`, `PerspectiveCellwiseStabilizer < PerspectiveSetwiseStabilizer`
(inclusion stricte de sous-groupes). Le témoin est `swapIso b i0 i1` : il
échange les deux cellules `ℂ ∙ b i0` et `ℂ ∙ b i1` (donc appartient au
stabilisateur setwise) sans fixer `ℂ ∙ b i0` (donc n'appartient PAS au
stabilisateur cellwise, puisque `ℂ ∙ b i0 ≠ ℂ ∙ b i1` par injectivité des
droites, `line_injective`).

Moins de symétrie imposée (`PerspectiveCellwiseStabilizer`, contrainte
stricte "fixe chaque cellule") admet donc STRICTEMENT plus d'opérateurs
invariants que plus de symétrie imposée
(`PerspectiveSetwiseStabilizer`, contrainte plus lâche "permute les
cellules") -- thème de l'objectif 12 de la mission.

**EN.** # Selectors — Module B, nontriviality (strict hierarchy)

The perspective-level analogue of the fact (already established at the
single-basis level in `BasisStabilizer.lean`) that fixing every cell
SETWISE is a STRICTLY stronger constraint than merely permitting cell
permutations: for a basis perspective in dimension `≥ 2`,
`PerspectiveCellwiseStabilizer < PerspectiveSetwiseStabilizer` (strict
subgroup inclusion). The witness is `swapIso b i0 i1`: it swaps the two
cells `ℂ ∙ b i0` and `ℂ ∙ b i1` (so it lies in the setwise stabilizer)
without fixing `ℂ ∙ b i0` (so it does NOT lie in the cellwise stabilizer,
since `ℂ ∙ b i0 ≠ ℂ ∙ b i1` by injectivity of the lines, `line_injective`).

Less imposed symmetry (`PerspectiveCellwiseStabilizer`, the strict "fix
every cell" constraint) therefore admits STRICTLY more invariant operators
than more imposed symmetry (`PerspectiveSetwiseStabilizer`, the looser
"permute the cells" constraint) -- the theme of mission objective 12.
-/

namespace QuantumFoundations.Selector

open scoped InnerProductSpace
open Gleason
open QuantumFoundations.BornRule
open scoped Classical

noncomputable section

variable {n : ℕ}

/-- Strict hierarchy: for a basis perspective in dimension `≥ 2`, the
cellwise stabilizer is a STRICT subgroup of the setwise stabilizer --
`swapIso` witnesses a symmetry that permutes two cells without fixing
either one setwise, so it lies in the setwise but not the cellwise
stabilizer. This is the perspective analogue of
`BasisPhaseStabilizer < BasisMonomialStabilizer`. -/
theorem PerspectiveCellwiseStabilizer_lt_PerspectiveSetwiseStabilizer_of_basisPerspective
    (hn2 : 2 ≤ n) (b : OrthonormalBasis (Fin n) ℂ (H n)) :
    PerspectiveCellwiseStabilizer (basisPerspective b) < PerspectiveSetwiseStabilizer (basisPerspective b) := by
  apply lt_of_le_of_ne (PerspectiveCellwiseStabilizer_le_PerspectiveSetwiseStabilizer _)
  intro heq
  set i0 : Fin n := ⟨0, by omega⟩ with hi0_def
  set i1 : Fin n := ⟨1, by omega⟩ with hi1_def
  have hij : i0 ≠ i1 := by simp [hi0_def, hi1_def, Fin.ext_iff]
  set U := swapIso b i0 i1 with hU_def
  have hmem_cells : ∀ k : Fin n, (ℂ ∙ (b k : H n)) ∈ (basisPerspective b).cells := by
    intro k
    show (ℂ ∙ (b k : H n)) ∈ Finset.univ.image (fun i => ℂ ∙ (b i : H n))
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
  have hUmap : ∀ k : Fin n, (ℂ ∙ (b k : H n)).map U.toLinearMap = ℂ ∙ (b (Equiv.swap i0 i1 k) : H n) := by
    intro k
    rw [Submodule.map_span, Set.image_singleton]
    have hveq : U.toLinearMap (b k) = b (Equiv.swap i0 i1 k) := by
      rw [hU_def]; exact swapIso_apply b i0 i1 k
    rw [hveq]
  have hUsetwise : U ∈ PerspectiveSetwiseStabilizer (basisPerspective b) := by
    intro c hc
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨ℂ ∙ (b (Equiv.swap i0 i1 k) : H n), hmem_cells _, hUmap k⟩
  rw [← heq] at hUsetwise
  have hUcellwise : (ℂ ∙ (b i0 : H n)).map U.toLinearMap = ℂ ∙ (b i0 : H n) :=
    hUsetwise (ℂ ∙ (b i0 : H n)) (hmem_cells i0)
  rw [hUmap i0, Equiv.swap_apply_left] at hUcellwise
  exact hij (line_injective b (Finset.mem_coe.mpr (Finset.mem_univ i0))
    (Finset.mem_coe.mpr (Finset.mem_univ i1)) hUcellwise.symm)

end

end QuantumFoundations.Selector
