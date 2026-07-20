import QuantumFoundations.BornRule.Perspective

/-!
# R0 — Défs : décompositions en branches, records redondants (Riedel)

Formalisation du théorème de Riedel (PRL 118, 120402 (2017), arXiv:1608.05377) :
un ensemble d'observables redondamment enregistrées dont aucune ne « pair-couvre »
une autre induit une décomposition en branches jointe, unique, orthogonale, en
états propres simultanés de tous les records. Contrepoint POSITIF de
`Histories.contrary_inferences` : la cohérence seule autorise les inférences
contraires (Kent), les records redondants forcent l'unicité (Riedel).

## Architecture à deux couches (décision ferme)

* **Couche 1 (ce fichier, `Basic`/`TwoObs`/`Induction`)** : tout sur `H n`. Les
  records sont des résolutions orthogonales étiquetées de `Submodule ℂ (H n)` ;
  la commutation issue de la disjonction spatiale (couche 2) apparaît ici comme
  une pure HYPOTHÈSE (`CommuteWitness`). Zéro produit tensoriel, zéro géométrie.
* **Couche 2 (`Local.lean`)** : modèle multi-sites plat
  `Sites N d := EuclideanSpace ℂ ((Fin N) → Fin d)` — jamais le `TensorProduct`
  abstrait de Mathlib.

## Décisions de conception (écarts signalés)

(A) Les records sont des résolutions étiquetées + `projL` (réutilise l'appareil
`Gleason.projL` existant, comme `BornRule.Perspective`).
(B) Étiquettes uniformes `Fin K` ; cellules `⊥` AUTORISÉES (padding plat, index
    des branches jointes = `Fin A → Fin K`). Divergence délibérée avec
    `Perspective` : PAS de champ `nz` (`LabeledResolution` n'est donc PAS un
    remplacement de `Perspective`, seuls ses lemmes publics de niveau vecteurs
    sont réutilisés si utiles — ici aucun ne l'a été, `projL_sup_of_pairwise_isOrtho`
    de `Gleason.Operator` suffit directement).
(C) Nombre de records uniforme `Fin R`, padding par répétition (préserve
    trivialement les identités de record `IsRecordedOn`). `[NeZero R]` est
    filé partout où un record canonique `(0 : Fin R)` est nécessaire
    (`branch`, `jointBranch`) — absent du pseudocode de conception initial,
    ajout de plomberie minimal : `(0 : Fin R)` n'existe pas pour `R` générique
    sans cette instance (confirmé en reconnaissance).
(D) `ψ` SANS hypothèse de norme, nulle part dans ce fichier.
(E) `CommuteWitness` : `∃ ĝ` AVANT les indices de valeurs propres `i j` (le
    `Ĝ(F,F′)` de l'éq. (12) de Riedel, uniforme en `i,j`) — POINT CRITIQUE,
    un `∃` mal placé rendrait le lemme de tunneling (`Induction.tunneling`)
    impossible à établir.

## Convention d'ordre de `chainProj`

Analogue à `Histories.chainOp` (`Fin.foldl`, dernier étage appliqué en
dernier) : `chainProj Obs L ρ f` replie `L : List (Fin A)` via `List.foldl`,
chaque nouvelle observable de `L` composée par la GAUCHE de l'accumulateur —
la DERNIÈRE observable de `L` est donc appliquée EN DERNIER (extérieure).
Cette convention est PROVISOIRE par nature : l'invariance par rapport à
l'ordre de `L` sera un corollaire du mécanisme d'action diagonale (`E`,
`Induction.lean`), pas un invariant imposé ici — voir la note dans
`Induction.lean`.
-/

namespace QuantumFoundations.Branches

open scoped InnerProductSpace
open Gleason QuantumFoundations.BornRule

noncomputable section

variable {n K R A : ℕ}

/-- Un record : résolution ORTHOGONALE ÉTIQUETÉE de `H n`, cellules indexées
par `Fin K` (padding plat autorisé — pas de champ `nz`, divergence délibérée
avec `Perspective`, voir décision (B)). -/
structure LabeledResolution (n K : ℕ) where
  /-- Les cellules, une par étiquette `i : Fin K`. -/
  cells : Fin K → Submodule ℂ (H n)
  /-- Orthogonalité deux à deux. -/
  ortho : ∀ i j, i ≠ j → cells i ≤ (cells j)ᗮ
  /-- Résolution complète de l'identité. -/
  covers : (⨆ i, cells i) = ⊤

/-- La projection orthogonale associée à l'étiquette `i` du record `Λ`. -/
abbrev rproj (Λ : LabeledResolution n K) (i : Fin K) : H n →ₗ[ℂ] H n := projL (Λ.cells i)

/-- **Redondance** (éq. (11) de Riedel) : tous les records de la famille
`recs` donnent la MÊME image de `ψ` par leur projection à l'étiquette `i`,
quel que soit le record choisi. -/
def IsRecordedOn (ψ : H n) (recs : Fin R → LabeledResolution n K) : Prop :=
  ∀ r r' : Fin R, ∀ i : Fin K, rproj (recs r) i ψ = rproj (recs r') i ψ

/-- La branche `i` de `ψ` vue à travers la famille de records `recs` :
grâce à `IsRecordedOn`, le choix du record `0` est sans conséquence (voir
`Basic.branch_wellDefined`). -/
def branch [NeZero R] (recs : Fin R → LabeledResolution n K) (ψ : H n) (i : Fin K) : H n :=
  rproj (recs 0) i ψ

/-- **Témoin de commutation** (éq. (12) de Riedel, `Ĝ(F,F′)`) : pour deux
observables distinctes `a ≠ b` et toute paire de records `r, r'` de `a`, il
existe un UNIQUE record `ĝ` de `b` (décision (E) : le `∃ ĝ` précède les
indices `i j`, uniforme en eux) tel que TOUTES les projections de `a` aux
records `r` ET `r'` commutent avec TOUTES les projections de `b` au record
`ĝ`. C'est l'hypothèse abstraite qui, en couche 2, provient de la disjonction
spatiale des supports (`Local.commute_of_disjoint`). -/
def CommuteWitness (Obs : Fin A → Fin R → LabeledResolution n K) : Prop :=
  ∀ a b : Fin A, a ≠ b → ∀ r r' : Fin R, ∃ ĝ : Fin R, ∀ i j : Fin K,
    Commute (rproj (Obs a r) i) (rproj (Obs b ĝ) j) ∧
    Commute (rproj (Obs a r') i) (rproj (Obs b ĝ) j)

/-- Classe d'opérateurs repliée sur la liste d'observables `L`, choix de
records `ρ` et d'étiquettes cibles `f`. Convention d'ordre : voir la note
d'en-tête (dernière observable de `L` appliquée en dernier). Type `H n → H n`
(fonction directe sur les vecteurs, PAS de `LinearMap` bundlé — les lemmes de
tunneling/diagonale (`Induction.lean`) portent sur des égalités de vecteurs,
pas d'opérateurs). -/
def chainProj (Obs : Fin A → Fin R → LabeledResolution n K) (L : List (Fin A))
    (ρ : Fin A → Fin R) (f : Fin A → Fin K) : H n → H n :=
  fun ψ => L.foldl (fun acc a => rproj (Obs a (ρ a)) (f a) acc) ψ

/-- La branche jointe `f : Fin A → Fin K` de `ψ` : replie TOUTES les
observables (`List.finRange A`, ordre `0, 1, …, A-1`), au record canonique
`0` de chacune (sans conséquence par `IsRecordedOn`, décision (C)). -/
def jointBranch [NeZero R] (Obs : Fin A → Fin R → LabeledResolution n K) (ψ : H n)
    (f : Fin A → Fin K) : H n :=
  chainProj Obs (List.finRange A) 0 f ψ

end
end QuantumFoundations.Branches
