import QuantumFoundations.HistoriesKent.Defs

/-!
**FR.** # K0 — Nonvacuity : une famille à un étage est toujours cohérente

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

**EN.** # K0 — Nonvacuity: every one-stage family is consistent

A concrete inhabitant of IsConsistent (absolute project rule 3, in the same
commit as Defs.lean): the one-stage family defined by an arbitrary
Perspective D is consistent for every vector ψ. No normalization
hypothesis is required, since consistency depends only on orthogonality of
the cells, not on the norm of ψ.

Proof: for L = 1, chainOp h ψ reduces to projL (h 0) ψ
(Fin.foldl_succ_last + Fin.foldl_zero). Two distinct histories h ≠ k
in the family must differ at stage 0, the only stage, so h 0 ≠ k 0 are
distinct cells of D and are orthogonal by D.ortho. The vectors
projL (h 0) ψ and projL (k 0) ψ lie in these orthogonal cells, hence
decFunctional ψ h k = 0.
-/

namespace QuantumFoundations.HistoriesKent

open scoped InnerProductSpace
open Gleason QuantumFoundations.BornRule

noncomputable section

variable {n : ℕ}

private theorem chainOp_single_stage (h : History n 1) (ψ : H n) :
    chainOp h ψ = projL (h 0) ψ := by
  show (Fin.foldl 1 (fun acc t => projL (h t) ∘ₗ acc) LinearMap.id) ψ = projL (h 0) ψ
  rw [Fin.foldl_succ_last, Fin.foldl_zero]
  simp

/--
**FR.** **Témoin de Nonvacuity K0** : toute `Perspective` `D`, vue comme famille à
un seul étage, est cohérente pour tout `ψ`.

**EN.** K0 nonvacuity witness: every Perspective D, viewed as a
one-stage family, is consistent for every ψ.
-/
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

/--
**FR.** Instance concrète (dimension 3, `basisPerspective` de la base canonique
`EuclideanSpace.basisFun`) — confirme que `isConsistent_single_stage` n'est
pas vacuement vrai faute d'habitant de `Perspective`.

**EN.** Concrete instance in dimension 3 using basisPerspective for the
canonical basis EuclideanSpace.basisFun; this confirms that
isConsistent_single_stage is not vacuously true for lack of an inhabitant
of Perspective.
-/
example : ∃ (D : Perspective 3) (ψ : H 3), IsConsistent ψ (fun _ : Fin 1 => D) :=
  ⟨basisPerspective (EuclideanSpace.basisFun (Fin 3) ℂ), 0, isConsistent_single_stage _ 0⟩

end
end QuantumFoundations.HistoriesKent
