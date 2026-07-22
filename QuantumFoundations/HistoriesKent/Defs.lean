import QuantumFoundations.BornRule.Perspective

/-!
**FR.** # K0 — Défs : histoires cohérentes, fonctionnelle de décohérence

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

**EN.** # K0 — Definitions: consistent histories and the decoherence functional

Finite-dimensional consistent-histories framework
(Griffiths / Gell-Mann–Hartle), formalized in preparation for Kent's
contrary-inferences theorem (PRL 78, 2874 (1997),
arXiv:gr-qc/9604012): two consistent sets sharing the same preparation and
postselection can imply mutually orthogonal propositions with certainty.
The generic profusion theorem of Dowker–Kent
(J. Stat. Phys. 82, 1575 (1996)) is explicitly outside the scope of this
block.

A temporal stage of a history set is a Perspective in the sense of
QuantumFoundations.BornRule.Perspective; there is no redefinition, only
direct reuse (confirmed during reconnaissance: cells = Submodule ℂ (H n) elements in a Finset, and projL applies unchanged).

## Conventions fixed here (point of no return for the block)

* Ordering of chainOp: the class operator of a history
 h : Fin L →
 Submodule ℂ (H n) is
 C_h = P_{h(L-1)} ∘ ⋯ ∘ P_{h(0)}, with THE FINAL STAGE APPLIED LAST, as in
 the standard physical convention. It is implemented by
 Fin.foldl L (fun acc t => projL (h t) ∘ₗ acc) LinearMap.id, which unfolds
 in exactly this order (verified: for L = 2, it reduces to
 projL (h 1) ∘ₗ projL (h 0) via
 Fin.foldl_succ_last/Fin.foldl_zero).
* Orientation of decFunctional:
 D(h,k) := ⟪C_k ψ, C_h ψ⟫_ℂ has k CONJUGATED (the project's inner
 product is conjugate-linear in its LEFT argument, as confirmed during
 reconnaissance via LinearMap.adjoint_inner_left).
* Strong (medium) consistency, as used in Kent's paper:
 D(h,k) = 0 for h ≠ k in the family. Weak consistency, requiring only
 Re D(h,k) = 0, is outside the scope of this block.

These are THE two points at which a convention error would invalidate the
remainder of the block; both were validated through a user check-in after K0.
-/

namespace QuantumFoundations.HistoriesKent

open scoped InnerProductSpace
open Gleason QuantumFoundations.BornRule

noncomputable section

variable {n L : ℕ}

/--
**FR.** Une histoire à `L` étages sur `H n` : un choix de cellule par étage.
Définition TOTALE (pattern du projet) : rien n'impose ici que `h t` appartienne
à une perspective donnée — c'est le rôle de `IsHistoryOf`, une condition côté
`Prop`, pas un sous-type.

**EN.** A history with L stages on H n: a choice of one cell at each stage.
This is a TOTAL definition, following the project pattern: nothing here
requires h t to belong to a specified perspective. That role is played by
IsHistoryOf, a Prop-valued condition rather than a subtype.
-/
abbrev History (n L : ℕ) := Fin L → Submodule ℂ (H n)

/--
**FR.** `h` est une histoire effective de la famille de perspectives `Ps` : chaque
cellule choisie à l'étage `t` appartient bien à la perspective `Ps t`.

**EN.** h is an actual history of the perspective family Ps: every cell
selected at stage t belongs to the perspective Ps t.
-/
def IsHistoryOf (Ps : Fin L → Perspective n) (h : History n L) : Prop :=
  ∀ t, h t ∈ (Ps t).cells

/--
**FR.** **Classe d'opérateurs** d'une histoire : produit ordonné des projections
`projL (h t)`, le DERNIER étage appliqué EN DERNIER — `C_h = P_{h(L-1)} ∘ ⋯ ∘
P_{h(0)}`. Voir note d'en-tête pour la vérification de l'ordre (`Fin.foldl`
déroule de l'étage `0` vers l'étage `L-1`, chaque nouvelle projection composée
À GAUCHE de l'accumulateur).

**EN.** Class operator of a history: the ordered product of the projections
projL (h t), with the FINAL stage applied LAST:
C_h = P_{h(L-1)} ∘ ⋯ ∘
P_{h(0)}. See the header note for verification of
the ordering (Fin.foldl unfolds from stage 0 to stage L-1, composing
each new projection on the LEFT of the accumulator).
-/
def chainOp (h : History n L) : H n →ₗ[ℂ] H n :=
  Fin.foldl L (fun acc t => projL (h t) ∘ₗ acc) LinearMap.id

/--
**FR.** **Fonctionnelle de décohérence** : `D(ψ; h, k) := ⟪C_k ψ, C_h ψ⟫_ℂ`. Porte
`k` conjugué (produit scalaire conj-linéaire à gauche) — voir note d'en-tête.

**EN.** Decoherence functional:
D(ψ; h, k) := ⟪C_k ψ, C_h ψ⟫_ℂ. The k argument is conjugated because
the inner product is conjugate-linear in its left argument; see the header
note.
-/
def decFunctional (ψ : H n) (h k : History n L) : ℂ :=
  ⟪chainOp k ψ, chainOp h ψ⟫_ℂ

/--
**FR.** **Cohérence (medium/forte)** d'une famille d'histoires pour l'état `ψ` :
la fonctionnelle de décohérence s'annule sur toute paire d'histoires distinctes
de la famille. C'est la notion utilisée par Kent (PRL 78, 2874) ; la cohérence
faible (partie réelle seulement) est hors scope de ce bloc.

**EN.** Strong (medium) consistency of a family of histories for the state
ψ: the decoherence functional vanishes for every pair of distinct
histories in the family. This is the notion used by Kent
(PRL 78, 2874); weak consistency, involving only the real part, is outside
the scope of this block.
-/
def IsConsistent (ψ : H n) (Ps : Fin L → Perspective n) : Prop :=
  ∀ h k : History n L, IsHistoryOf Ps h → IsHistoryOf Ps k → h ≠ k → decFunctional ψ h k = 0

/--
**FR.** **Probabilité d'une histoire** (règle de Born généralisée aux histoires) :
`p(h) := ‖C_h ψ‖²`.

**EN.** Probability of a history (the Born rule generalized to histories):
p(h) := ‖C_h ψ‖².
-/
def histProb (ψ : H n) (h : History n L) : ℝ :=
  ‖chainOp h ψ‖ ^ 2

end
end QuantumFoundations.HistoriesKent
