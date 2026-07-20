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
  sorry

/-- **Contraction opératorielle.** Le produit de deux projections du MÊME
record : idempotence si les étiquettes coïncident, `0` sinon (orthogonalité).
Énoncé AU NIVEAU OPÉRATEURS (pas seulement pointwise) — le lemme de diagonale
`E` (`Induction.diagonal`) en a besoin ainsi, au contact du dernier maillon de
la chaîne. -/
theorem rproj_contract (Λ : LabeledResolution n K) (i i' : Fin K) :
    rproj Λ i ∘ₗ rproj Λ i' = if i = i' then rproj Λ i else 0 := by
  sorry

/-- **`branch` est indépendant du record choisi**, sous redondance
(`IsRecordedOn`) — justifie a posteriori le choix arbitraire du record `0`
dans la définition de `branch`. -/
theorem branch_wellDefined [NeZero R] (ψ : H n) (recs : Fin R → LabeledResolution n K)
    (hrec : IsRecordedOn ψ recs) (r : Fin R) (i : Fin K) :
    branch recs ψ i = rproj (recs r) i ψ := by
  sorry

/-- **Les branches d'un même record sont deux à deux orthogonales.** -/
theorem branch_orthogonal [NeZero R] (ψ : H n) (recs : Fin R → LabeledResolution n K)
    {i i' : Fin K} (hii : i ≠ i') :
    ⟪branch recs ψ i, branch recs ψ i'⟫_ℂ = 0 := by
  sorry

end
end QuantumFoundations.Branches
