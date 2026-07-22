import QuantumFoundations.BornRule.Perspective

/-!
**FR.** # R0 — Défs : décompositions en branches, records redondants (Riedel)

Formalisation du théorème de Riedel (PRL 118, 120402 (2017), arXiv:1608.05377) :
un ensemble d'observables redondamment enregistrées dont aucune ne « pair-couvre »
une autre induit une décomposition en branches jointe, unique, orthogonale, en
états propres simultanés de tous les records. Contrepoint POSITIF de
`HistoriesKent.contrary_inferences` : la cohérence seule autorise les inférences
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

Analogue à `HistoriesKent.chainOp` (`Fin.foldl`, dernier étage appliqué en
dernier) : `chainProj Obs L ρ f` replie `L : List (Fin A)` via `List.foldl`,
chaque nouvelle observable de `L` composée par la GAUCHE de l'accumulateur —
la DERNIÈRE observable de `L` est donc appliquée EN DERNIER (extérieure).
Cette convention est PROVISOIRE par nature : l'invariance par rapport à
l'ordre de `L` sera un corollaire du mécanisme d'action diagonale (`E`,
`Induction.lean`), pas un invariant imposé ici — voir la note dans
`Induction.lean`.

**EN.** # R0 — Definitions: branch decompositions and redundant records (Riedel)

Formalization of Riedel's theorem (PRL 118, 120402 (2017), arXiv:1608.05377):
a set of redundantly recorded observables, none of which pair-covers another,
induces a unique orthogonal joint-branch decomposition into simultaneous
eigenstates of all records. This is the POSITIVE counterpart of
HistoriesKent.contrary_inferences: consistency alone permits contrary
inferences (Kent), whereas redundant records enforce uniqueness (Riedel).

## Two-layer architecture (fixed decision)

* Layer 1 (this file, Basic/TwoObs/Induction): everything is defined
 on H n. Records are labeled orthogonal resolutions of
 Submodule ℂ (H n); commutation arising from spatial disjointness (layer 2)
 appears here as a pure HYPOTHESIS (CommuteWitness). No tensor products and
 no geometry.
* Layer 2 (Local.lean): the flat multisite model
 Sites N d := EuclideanSpace ℂ ((Fin N) → Fin d)—never Mathlib's abstract
 TensorProduct.

## Design decisions (documented deviations)

(A) Records are labeled resolutions + projL (reusing the existing
Gleason.projL infrastructure, as in BornRule.Perspective).
(B) Uniform labels Fin K; cells equal to ⊥ are ALLOWED (flat padding, joint-branch index
 = Fin A → Fin K). This deliberately differs
 from Perspective: there is NO nz field (LabeledResolution is
 therefore NOT a replacement for Perspective; only its public
 vector-level lemmas are reused when useful—none were needed here, since
 projL_sup_of_pairwise_isOrtho from Gleason.Operator suffices directly).
(C) A uniform number of records Fin R, with padding by repetition (which
 trivially preserves the record identities in IsRecordedOn). [NeZero R]
 is threaded wherever a canonical record (0 : Fin R) is needed
 (branch, jointBranch)—it was absent from the initial design
 pseudocode and is the minimal plumbing addition: (0 : Fin R) does not
 exist for generic R without this instance (confirmed during
 reconnaissance).
(D) There is NO norm hypothesis on ψ anywhere in this file.
(E) CommuteWitness: ∃ ĝ appears BEFORE the eigenvalue indices i j (the
 Ĝ(F,F′) of Riedel's Eq. (12), uniform in i,j)—a CRITICAL POINT, since
 placing the ∃ incorrectly would make the tunneling lemma
 (Induction.tunneling) impossible to prove.

## Ordering convention for chainProj

As in HistoriesKent.chainOp (Fin.foldl, with the final stage applied last),
chainProj Obs L ρ f folds L : List (Fin A) using List.foldl, composing
each new observable from L on the LEFT of the accumulator. Consequently,
the LAST observable in L is applied LAST, as the outermost operator. This
convention is provisional by construction: invariance under the ordering of
L will be a corollary of the diagonal-action mechanism (E,
Induction.lean), not an invariant imposed here; see the note in
Induction.lean.
-/

namespace QuantumFoundations.BranchesRiedel

open scoped InnerProductSpace
open Gleason QuantumFoundations.BornRule

noncomputable section

variable {n K R A : ℕ}

/--
**FR.** Un record : résolution ORTHOGONALE ÉTIQUETÉE de `H n`, cellules indexées
par `Fin K` (padding plat autorisé — pas de champ `nz`, divergence délibérée
avec `Perspective`, voir décision (B)).

**EN.** A record: a LABELED ORTHOGONAL resolution of H n, with cells indexed
by Fin K (flat padding allowed—no nz field, deliberately differing from
Perspective; see decision (B)).
-/
structure LabeledResolution (n K : ℕ) where
  /--
**FR.** Les cellules, une par étiquette `i : Fin K`.

**EN.** The cells, one for each label i : Fin K.
-/
  cells : Fin K → Submodule ℂ (H n)
  /--
**FR.** Orthogonalité deux à deux.

**EN.** Pairwise orthogonality.
-/
  ortho : ∀ i j, i ≠ j → cells i ≤ (cells j)ᗮ
  /--
**FR.** Résolution complète de l'identité.

**EN.** Complete resolution of the identity.
-/
  covers : (⨆ i, cells i) = ⊤

/--
**FR.** La projection orthogonale associée à l'étiquette `i` du record `Λ`.

**EN.** The orthogonal projection associated with label i of record Λ.
-/
abbrev rproj (Λ : LabeledResolution n K) (i : Fin K) : H n →ₗ[ℂ] H n := projL (Λ.cells i)

/--
**FR.** **Redondance** (éq. (11) de Riedel) : tous les records de la famille
`recs` donnent la MÊME image de `ψ` par leur projection à l'étiquette `i`,
quel que soit le record choisi.

**EN.** Redundancy (Riedel's Eq. (11)): every record in the family recs
produces the SAME image of ψ under its projection at label i, independently
of the chosen record.
-/
def IsRecordedOn (ψ : H n) (recs : Fin R → LabeledResolution n K) : Prop :=
  ∀ r r' : Fin R, ∀ i : Fin K, rproj (recs r) i ψ = rproj (recs r') i ψ

/--
**FR.** La branche `i` de `ψ` vue à travers la famille de records `recs` :
grâce à `IsRecordedOn`, le choix du record `0` est sans conséquence (voir
`Basic.branch_wellDefined`).

**EN.** The branch i of ψ as seen through the record family recs: by
IsRecordedOn, the choice of record 0 is immaterial (see
Basic.branch_wellDefined).
-/
def branch [NeZero R] (recs : Fin R → LabeledResolution n K) (ψ : H n) (i : Fin K) : H n :=
  rproj (recs 0) i ψ

/--
**FR.** **Témoin de commutation** (éq. (12) de Riedel, `Ĝ(F,F′)`) : pour deux
observables distinctes `a ≠ b` et toute paire de records `r, r'` de `a`, il
existe un UNIQUE record `ĝ` de `b` (décision (E) : le `∃ ĝ` précède les
indices `i j`, uniforme en eux) tel que TOUTES les projections de `a` aux
records `r` ET `r'` commutent avec TOUTES les projections de `b` au record
`ĝ`. C'est l'hypothèse abstraite qui, en couche 2, provient de la disjonction
spatiale des supports (`Local.commute_of_disjoint`).

**EN.** Commutation witness (Riedel's Eq. (12), Ĝ(F,F′)): for two distinct
observables a ≠ b and every pair of records r, r' of a, there exists a
SINGLE record ĝ of b (decision (E): ∃ ĝ precedes the indices i j and
is uniform in them) such that ALL projections of a in records r AND r'
commute with ALL projections of b in record ĝ. This is the abstract
hypothesis that, in layer 2, follows from spatial disjointness of the supports
(Local.commute_of_disjoint).
-/
def CommuteWitness (Obs : Fin A → Fin R → LabeledResolution n K) : Prop :=
  ∀ a b : Fin A, a ≠ b → ∀ r r' : Fin R, ∃ ĝ : Fin R, ∀ i j : Fin K,
    Commute (rproj (Obs a r) i) (rproj (Obs b ĝ) j) ∧
    Commute (rproj (Obs a r') i) (rproj (Obs b ĝ) j)

/--
**FR.** Classe d'opérateurs repliée sur la liste d'observables `L`, choix de
records `ρ` et d'étiquettes cibles `f`. Convention d'ordre : voir la note
d'en-tête (dernière observable de `L` appliquée en dernier). Type `H n → H n`
(fonction directe sur les vecteurs, PAS de `LinearMap` bundlé — les lemmes de
tunneling/diagonale (`Induction.lean`) portent sur des égalités de vecteurs,
pas d'opérateurs).

**EN.** Operator class folded over the list of observables L, with choices of
records ρ and target labels f. Ordering convention: see the header note
(the last observable in L is applied last). Type H n → H n (a direct
function on vectors, NOT a bundled LinearMap—the tunneling/diagonal lemmas
in Induction.lean concern vector equalities, not operator equalities).
-/
def chainProj (Obs : Fin A → Fin R → LabeledResolution n K) (L : List (Fin A))
    (ρ : Fin A → Fin R) (f : Fin A → Fin K) : H n → H n :=
  fun ψ => L.foldl (fun acc a => rproj (Obs a (ρ a)) (f a) acc) ψ

/--
**FR.** La branche jointe `f : Fin A → Fin K` de `ψ` : replie TOUTES les
observables (`List.finRange A`, ordre `0, 1, …, A-1`), au record canonique
`0` de chacune (sans conséquence par `IsRecordedOn`, décision (C)).

**EN.** The joint branch f : Fin A → Fin K of ψ: folds over ALL observables
(List.finRange A, in the order 0, 1, …, A-1), using the canonical record
0 for each (which is immaterial by IsRecordedOn; decision (C)).
-/
def jointBranch [NeZero R] (Obs : Fin A → Fin R → LabeledResolution n K) (ψ : H n)
    (f : Fin A → Fin K) : H n :=
  chainProj Obs (List.finRange A) 0 f ψ

end
end QuantumFoundations.BranchesRiedel
