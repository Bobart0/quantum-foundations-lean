import QuantumFoundations.Branches.Nonvacuity

/-!
# R1 — Lemmes généraux courts sur `LabeledResolution`

Jalon de dé-risquage minimal, avant `TwoObs.lean`/`Induction.lean`.
-/

namespace QuantumFoundations.Branches

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n K R : ℕ}

/-- **Résolution de l'identité.** Somme des projections d'un record sur `x` :
`x` lui-même (`projL_sup_of_pairwise_isOrtho` + `covers`, gère les cellules
`⊥` sans difficulté — aucun champ `nz` requis). -/
theorem resolution_apply (Λ : LabeledResolution n K) (x : H n) :
    ∑ i, rproj Λ i x = x := by
  have hortho' : ∀ i ∈ (Finset.univ : Finset (Fin K)), ∀ j ∈ (Finset.univ : Finset (Fin K)),
      i ≠ j → Λ.cells i ⟂ Λ.cells j := by
    intro i _ j _ hij
    exact Submodule.isOrtho_iff_le.mpr (Λ.ortho i j hij)
  have hsum : projL (Finset.univ.sup Λ.cells) = ∑ i, projL (Λ.cells i) :=
    projL_sup_of_pairwise_isOrtho Finset.univ Λ.cells hortho'
  rw [Finset.sup_univ_eq_iSup, Λ.covers] at hsum
  have hid : projL (⊤ : Submodule ℂ (H n)) = LinearMap.id := by
    unfold projL
    rw [Submodule.starProjection_top]
    rfl
  rw [hid] at hsum
  have := congrArg (fun f => f x) hsum
  simpa using this.symm

/-- **Contraction opératorielle.** Le produit de deux projections du MÊME
record : idempotence si les étiquettes coïncident, `0` sinon (orthogonalité).
Énoncé AU NIVEAU OPÉRATEURS (pas seulement pointwise) — le lemme de diagonale
`E` (`Induction.diagonal`) en a besoin ainsi, au contact du dernier maillon de
la chaîne. -/
theorem rproj_contract (Λ : LabeledResolution n K) (i i' : Fin K) :
    rproj Λ i ∘ₗ rproj Λ i' = if i = i' then rproj Λ i else 0 := by
  split_ifs with h
  · subst h
    apply LinearMap.ext; intro x
    show (Λ.cells i).starProjection ((Λ.cells i).starProjection x) = (Λ.cells i).starProjection x
    exact congrFun (congrArg DFunLike.coe (Λ.cells i).isIdempotentElem_starProjection.eq) x
  · apply LinearMap.ext; intro x
    show (Λ.cells i).starProjection ((Λ.cells i').starProjection x) = 0
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact (Λ.ortho i' i (Ne.symm h)) (Submodule.starProjection_apply_mem (Λ.cells i') x)

/-- **`branch` est indépendant du record choisi**, sous redondance
(`IsRecordedOn`) — justifie a posteriori le choix arbitraire du record `0`
dans la définition de `branch`. -/
theorem branch_wellDefined [NeZero R] (ψ : H n) (recs : Fin R → LabeledResolution n K)
    (hrec : IsRecordedOn ψ recs) (r : Fin R) (i : Fin K) :
    branch recs ψ i = rproj (recs r) i ψ := by
  show rproj (recs 0) i ψ = rproj (recs r) i ψ
  exact hrec 0 r i

/-- **Les branches d'un même record sont deux à deux orthogonales.** -/
theorem branch_orthogonal [NeZero R] (ψ : H n) (recs : Fin R → LabeledResolution n K)
    {i i' : Fin K} (hii : i ≠ i') :
    ⟪branch recs ψ i, branch recs ψ i'⟫_ℂ = 0 := by
  show ⟪rproj (recs 0) i ψ, rproj (recs 0) i' ψ⟫_ℂ = 0
  have hmem : rproj (recs 0) i ψ ∈ (recs 0).cells i := Submodule.starProjection_apply_mem _ _
  have hmem' : rproj (recs 0) i' ψ ∈ (recs 0).cells i' := Submodule.starProjection_apply_mem _ _
  have hortho' : (recs 0).cells i' ≤ ((recs 0).cells i)ᗮ := (recs 0).ortho i' i hii.symm
  exact (Submodule.mem_orthogonal ((recs 0).cells i) _).mp (hortho' hmem') _ hmem

end
end QuantumFoundations.Branches
