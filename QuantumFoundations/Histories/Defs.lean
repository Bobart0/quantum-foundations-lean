import QuantumFoundations.BornRule.Perspective

/-!
# K0 — Défs : histoires cohérentes, fonctionnelle de décohérence

Cadre des histoires cohérentes (Griffiths / Gell-Mann–Hartle) en dimension finie,
formalisé en vue du théorème des **inférences contraires** de Kent (PRL 78, 2874
(1997), arXiv:gr-qc/9604012) : deux ensembles cohérents partageant la même
préparation et la même post-sélection peuvent impliquer avec certitude des
propositions mutuellement orthogonales. Le théorème de profusion générique de
Dowker–Kent (J. Stat. Phys. 82, 1575 (1996)) est explicitement hors scope de ce
bloc.

Un étage temporel d'un ensemble d'histoires **est** une `Perspective` au sens de
`QuantumFoundations.BornRule.Perspective` — aucune redéfinition, réutilisation
directe (confirmée en reconnaissance : cellules = `Submodule ℂ (H n)` dans un
`Finset`, `projL` s'applique tel quel).

## Conventions fixées ici (point de non-retour du bloc)

* **Ordre de `chainOp`** : la classe d'opérateurs d'une histoire `h : Fin L →
  Submodule ℂ (H n)` est `C_h = P_{h(L-1)} ∘ ⋯ ∘ P_{h(0)}`, LE DERNIER ÉTAGE
  APPLIQUÉ EN DERNIER (convention physique standard). Implémenté par
  `Fin.foldl L (fun acc t => projL (h t) ∘ₗ acc) LinearMap.id`, qui déroule
  exactement dans cet ordre (vérifié : pour `L = 2`, se réduit à
  `projL (h 1) ∘ₗ projL (h 0)` via `Fin.foldl_succ_last`/`Fin.foldl_zero`).
* **Orientation de `decFunctional`** : `D(h,k) := ⟪C_k ψ, C_h ψ⟫_ℂ` porte `k`
  CONJUGUÉ (produit scalaire du projet conj-linéaire à GAUCHE, confirmé en
  reconnaissance via `LinearMap.adjoint_inner_left`).
* **Cohérence forte (medium)**, celle du papier de Kent : `D(h,k) = 0` pour
  `h ≠ k` dans la famille. La cohérence faible (`Re D(h,k) = 0` seulement) est
  hors scope.

Ces deux points sont LES deux endroits où une erreur de convention coûterait
tout le reste du bloc — validés par un check-in utilisateur après K0.
-/

namespace QuantumFoundations.Histories

open scoped InnerProductSpace
open Gleason QuantumFoundations.BornRule

noncomputable section

variable {n L : ℕ}

/-- Une histoire à `L` étages sur `H n` : un choix de cellule par étage.
Définition TOTALE (pattern du projet) : rien n'impose ici que `h t` appartienne
à une perspective donnée — c'est le rôle de `IsHistoryOf`, une condition côté
`Prop`, pas un sous-type. -/
abbrev History (n L : ℕ) := Fin L → Submodule ℂ (H n)

/-- `h` est une histoire effective de la famille de perspectives `Ps` : chaque
cellule choisie à l'étage `t` appartient bien à la perspective `Ps t`. -/
def IsHistoryOf (Ps : Fin L → Perspective n) (h : History n L) : Prop :=
  ∀ t, h t ∈ (Ps t).cells

/-- **Classe d'opérateurs** d'une histoire : produit ordonné des projections
`projL (h t)`, le DERNIER étage appliqué EN DERNIER — `C_h = P_{h(L-1)} ∘ ⋯ ∘
P_{h(0)}`. Voir note d'en-tête pour la vérification de l'ordre (`Fin.foldl`
déroule de l'étage `0` vers l'étage `L-1`, chaque nouvelle projection composée
À GAUCHE de l'accumulateur). -/
def chainOp (h : History n L) : H n →ₗ[ℂ] H n :=
  Fin.foldl L (fun acc t => projL (h t) ∘ₗ acc) LinearMap.id

/-- **Fonctionnelle de décohérence** : `D(ψ; h, k) := ⟪C_k ψ, C_h ψ⟫_ℂ`. Porte
`k` conjugué (produit scalaire conj-linéaire à gauche) — voir note d'en-tête. -/
def decFunctional (ψ : H n) (h k : History n L) : ℂ :=
  ⟪chainOp k ψ, chainOp h ψ⟫_ℂ

/-- **Cohérence (medium/forte)** d'une famille d'histoires pour l'état `ψ` :
la fonctionnelle de décohérence s'annule sur toute paire d'histoires distinctes
de la famille. C'est la notion utilisée par Kent (PRL 78, 2874) ; la cohérence
faible (partie réelle seulement) est hors scope de ce bloc. -/
def IsConsistent (ψ : H n) (Ps : Fin L → Perspective n) : Prop :=
  ∀ h k : History n L, IsHistoryOf Ps h → IsHistoryOf Ps k → h ≠ k → decFunctional ψ h k = 0

/-- **Probabilité d'une histoire** (règle de Born généralisée aux histoires) :
`p(h) := ‖C_h ψ‖²`. -/
def histProb (ψ : H n) (h : History n L) : ℝ :=
  ‖chainOp h ψ‖ ^ 2

end
end QuantumFoundations.Histories
