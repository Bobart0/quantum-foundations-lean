import QuantumFoundations.Histories.Defs

/-!
# K0 — Nonvacuity : une famille à un étage est toujours cohérente

Habitant concret de `IsConsistent` (règle absolue 3 du projet, dans le même
commit que `Defs.lean`) : la famille à un seul étage donnée par une
`Perspective` quelconque `D` est cohérente, pour n'importe quel vecteur `ψ`
(aucune hypothèse de normalisation nécessaire — la cohérence ne dépend que de
l'orthogonalité des cellules, pas de la norme de `ψ`).

Preuve : pour `L = 1`, `chainOp h ψ` se réduit à `projL (h 0) ψ`
(`Fin.foldl_succ_last` + `Fin.foldl_zero`). Deux histoires distinctes `h ≠ k`
de la famille diffèrent nécessairement à l'étage `0` (seul étage), donc
`h 0 ≠ k 0` sont deux cellules distinctes de `D`, orthogonales par `D.ortho` ;
`projL (h 0) ψ` et `projL (k 0) ψ` tombent dans ces cellules orthogonales,
d'où `decFunctional ψ h k = 0`.
-/

namespace QuantumFoundations.Histories

open scoped InnerProductSpace
open Gleason QuantumFoundations.BornRule

noncomputable section

variable {n : ℕ}

private theorem chainOp_single_stage (h : History n 1) (ψ : H n) :
    chainOp h ψ = projL (h 0) ψ := by
  show (Fin.foldl 1 (fun acc t => projL (h t) ∘ₗ acc) LinearMap.id) ψ = projL (h 0) ψ
  rw [Fin.foldl_succ_last, Fin.foldl_zero]
  simp

/-- **Témoin de Nonvacuity K0** : toute `Perspective` `D`, vue comme famille à
un seul étage, est cohérente pour tout `ψ`. -/
theorem isConsistent_single_stage (D : Perspective n) (ψ : H n) :
    IsConsistent ψ (fun _ : Fin 1 => D) := by
  intro h k hh hk hne
  have hh0 : h 0 ∈ D.cells := hh 0
  have hk0 : k 0 ∈ D.cells := hk 0
  have hne0 : h 0 ≠ k 0 := fun heq => hne (funext (fun i => by fin_cases i; exact heq))
  have hortho : h 0 ≤ (k 0)ᗮ := D.ortho (h 0) hh0 (k 0) hk0 hne0
  show ⟪chainOp k ψ, chainOp h ψ⟫_ℂ = 0
  rw [chainOp_single_stage k ψ, chainOp_single_stage h ψ]
  have hmem_h : projL (h 0) ψ ∈ h 0 := Submodule.starProjection_apply_mem (h 0) ψ
  have hmem_k : projL (k 0) ψ ∈ k 0 := Submodule.starProjection_apply_mem (k 0) ψ
  have hperp : projL (h 0) ψ ∈ (k 0)ᗮ := hortho hmem_h
  exact (Submodule.mem_orthogonal (k 0) (projL (h 0) ψ)).mp hperp (projL (k 0) ψ) hmem_k

/-- Instance concrète (dimension 3, `basisPerspective` de la base canonique
`EuclideanSpace.basisFun`) — confirme que `isConsistent_single_stage` n'est
pas vacuement vrai faute d'habitant de `Perspective`. -/
example : ∃ (D : Perspective 3) (ψ : H 3), IsConsistent ψ (fun _ : Fin 1 => D) :=
  ⟨basisPerspective (EuclideanSpace.basisFun (Fin 3) ℂ), 0, isConsistent_single_stage _ 0⟩

end
end QuantumFoundations.Histories
