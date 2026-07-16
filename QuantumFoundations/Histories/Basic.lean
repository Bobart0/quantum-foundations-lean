import QuantumFoundations.Histories.Nonvacuity

/-!
# K1 — Lemmes généraux courts

## Écart vs la feuille de route (à noter, pas à re-discuter) : (c) supprimé

La feuille de route prévoyait un but ouvert `projL_self_adjoint`/idempotence
« seulement si absent de la reconnaissance ». Reconnaissance A.2 : les deux
faits sont dérivables en une ligne depuis `gleason`/Mathlib, sans laisser de
but supplémentaire ouvert :
* `LinearMap.IsSymmetric (projL A)` via `Submodule.starProjection_isSymmetric`.
* `projL A (projL A x) = projL A x` via `Submodule.isIdempotentElem_starProjection`.
Aucun des deux n'est actuellement invoqué ailleurs dans ce bloc (K1(a)/K1(b) ne
s'en servent pas) ; ils seront cités inline le jour où K2/K3 en ont besoin,
plutôt que factorisés ici sans utilisateur. K1 ne compte donc que 2 buts
ouverts ((a) et (b)), pas 3.
-/

namespace QuantumFoundations.Histories

open scoped InnerProductSpace
open Gleason QuantumFoundations.BornRule

noncomputable section

variable {n L : ℕ}

/-- **K1(a).** Si deux histoires d'une même famille `Ps : Fin (L+1) →
Perspective n` diffèrent au DERNIER étage, leur fonctionnelle de décohérence
s'annule automatiquement — sans qu'il soit besoin d'examiner les étages
antérieurs. C'est le lemme qui réduit la charge de K2 : pour `L = 1` (deux
étages, indices `0` et `1`), il ne reste à vérifier que les paires
d'histoires différant SEULEMENT à l'étage `0`. -/
theorem decFunctional_last_stage_orthogonal (Ps : Fin (L + 1) → Perspective n) (ψ : H n)
    (h k : History n (L + 1)) (hh : IsHistoryOf Ps h) (hk : IsHistoryOf Ps k)
    (hlast : h (Fin.last L) ≠ k (Fin.last L)) :
    decFunctional ψ h k = 0 := by
  sorry

/-- **K1(b).** Version minimale de l'additivité des probabilités d'histoires
(écho d'`AxGrain`), suffisante pour K3 : sur une perspective `D1` quelconque
de l'étage final, la somme des probabilités de prolongement d'une histoire
partielle `c0` égale la probabilité de `c0` seule (théorème de Pythagore fini
sur `D1`, via `sum_sq_projL_of_pairwise_isOrtho` désormais public dans
`BornRule/Perspective.lean`). -/
theorem histProb_additivity_two_stage (D1 : Perspective n) (ψ : H n)
    (c0 : Submodule ℂ (H n)) :
    ∑ c ∈ D1.cells, ‖projL c (projL c0 ψ)‖ ^ 2 = ‖projL c0 ψ‖ ^ 2 := by
  sorry

end
end QuantumFoundations.Histories
