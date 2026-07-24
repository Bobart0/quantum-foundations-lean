# quantum-foundations-lean — Formalisations Lean 4 : Naimark, Wigner, Uhlhorn, BornRule, HistoriesKent, BranchesRiedel et Complexity

**Statut : Naimark v2 COMPLET (`v2.0-naimark`, 2026-07-11), Wigner COMPLET avec
unicité/exclusivité optionnelles (`v2.0-wigner`, 2026-07-13), Uhlhorn COMPLET
(`v1.0-uhlhorn`, 2026-07-14), BornRule COMPLET avec Nonvacuity
(`v2.0-bornrule`, 2026-07-15) ET HistoriesKent COMPLET (`v1.0-histories`,
2026-07-16), avec les blocs BranchesRiedel et Complexity C0–C13, et désormais
le pont **C14 records → poids de Born** ainsi que **C15, unicité quadratique
sur les secteurs de records restreints**, désormais complété par **C17,
première stabilité quantitative des poids restreints**.** Sept blocs
mécanisés, **sans axiome**
(au sens des règles du projet — hors les trois axiomes standards du noyau Lean,
voir plus bas), en dimension finie sur ℂ.

**En chiffres (recalculés le 2026-07-23, fichiers du projet hors scratch) :
119 fichiers `.lean`, 19598 lignes, 663 déclarations publiques (`theorem`), 0
`sorry`, 0 axiome propre au projet. Le bloc Complexity compte 70 fichiers et
9490 lignes, dont 12 fichiers et 1224 lignes pour le jalon C13 de
persistance sous évolution simulée. Le bloc BranchesRiedel compte 17 fichiers
et 3250 lignes, dont 11 fichiers et 1438 lignes pour le nouveau
sous-répertoire `BornBridge/` (jalon C14, pont entre la décomposition en
branches de Riedel et le poids de Born). Les
théorèmes principaux des blocs Complexity et BornBridge ont été vérifiés par
`#print axioms` et dépendent exactement de
`[propext, Classical.choice, Quot.sound]`, le trio standard Lean/Mathlib.**

**Noms de modules actuels :** le bloc Riedel est
`QuantumFoundations.BranchesRiedel` et le bloc des inférences contraires de
Kent est `QuantumFoundations.HistoriesKent`. Les anciens chemins/namespaces
`QuantumFoundations.Branches` et `QuantumFoundations.Histories` ne sont plus
exposés.

Le **théorème de dilation de Naimark** pour les POVM finies (Watrous, *The Theory
of Quantum Information*, Theorem 2.42) : toute POVM `E : Fin m → (H n →ₗ[ℂ] H n)` se
réalise comme mesure projective (`dilProj`) sous l'action d'une isométrie `dilV`,
avec formule de Born préservée.

Le **théorème de Wigner** (Bargmann 1964, *Note on Wigner's Theorem on Symmetry
Operations*) : toute transformation sur les états purs qui préserve les probabilités
de transition `|⟨φ|ψ⟩|²` est induite par un opérateur unitaire ou antiunitaire —
formulation (A), **sans hypothèse de bijectivité** sur la transformation de départ
(strictement plus fort que Simon–Mukunda–Chaturvedi–Srinivasan 2008, eq. 2.8, qui
la suppose). Complété (W6, optionnel) par l'**exclusivité** unitaire/antiunitaire
et l'**unicité à phase globale près** (version restreinte), Bargmann §1.5 et §6.

Le **Corollaire 1.2 de Šemrl** (Šemrl 2021, *Wigner symmetries and Gleason's
theorem*, arXiv:2106.06182) : en dimension finie `n ≥ 3`, toute application sur
les projections de rang 1 qui préserve l'orthogonalité **dans un seul sens**
(ni injectivité ni surjectivité supposées) est automatiquement une symétrie de
Wigner. Contrairement à Naimark et Wigner, ce n'est PAS un résultat autonome :
il **compose** le théorème de Gleason (`gleason-theorem-lean`, dépendance
externe épinglée) et le théorème de Wigner (bloc interne ci-dessus) — voir la
section dédiée plus bas pour le détail de cette double dépendance et sa
vérification d'axiomes.

Le **Théorème de Cohérence de Grain** (Gleason 1957, *Measures on the closed
subspaces of a Hilbert space*, comme théorème sous-jacent) : pour une
« perspective » (partition orthogonale de `H n` en cellules) et une règle
d'estimation satisfaisant quatre axiomes purement combinatoires (Grain, Norm,
Pos, Null), la valeur de la règle sur toute cellule est EXACTEMENT la règle de
Born (`∑ᵢ ‖⟨v,fᵢ⟩‖²` sur une base orthonormée de la cellule) — sans jamais
supposer a priori que la règle est de la forme d'une trace. Comme Uhlhorn,
c'est un résultat qui **compose** un bloc interne (l'infrastructure Uhlhorn,
U2 et U3a) et une dépendance externe (`Gleason.gleason`, importé comme vrai
théorème plutôt que comme axiome) — voir la section dédiée plus bas.

Le **théorème des inférences contraires** (Kent 1997, *Quasiclassical Dynamics
in a Closed Quantum System*, PRL 78, 2874, arXiv:gr-qc/9604012), dans le cadre
des histoires cohérentes en dimension finie : deux ensembles cohérents
d'histoires peuvent partager la même préparation et la même post-sélection,
tout en impliquant chacun avec CERTITUDE une proposition différente, ces deux
propositions étant mutuellement orthogonales. Un étage temporel d'un ensemble
d'histoires **réutilise directement** `BornRule.Perspective`, sans
redéfinition — comme Uhlhorn et BornRule le font déjà pour d'autres briques,
`HistoriesKent` **compose** l'infrastructure interne du dépôt (`BornRule` →
`Uhlhorn`/`Gleason`) plutôt que de repartir de zéro. Le théorème de profusion
générique de Dowker–Kent (1996) — qui montrerait que la contrariété du témoin
n'est pas un cas isolé — est explicitement hors scope de ce bloc.

Ce dépôt s'appuie sur [`gleason-theorem-lean`](https://github.com/Bobart0/gleason-theorem-lean)
(tag `v1.0-gleason`). Naimark n'y réutilise que `IsPositiveOp`
(`Gleason.Busch.Effects`) ; Uhlhorn et BornRule, en revanche, invoquent
`Gleason.gleason` lui-même ainsi qu'une partie de sa machinerie interne ;
HistoriesKent n'invoque pas `Gleason.gleason` directement mais en hérite par
transitivité via `BornRule.Perspective`/`projL` — voir la section
« Dépendances » plus bas pour le détail et la vérification de non-fuite
d'axiome.

## Énoncé

```lean
structure POVM (n m : ℕ) where
  E : Fin m → (H n →ₗ[ℂ] H n)
  pos : ∀ i, IsPositiveOp (E i)
  sum_eq_one : ∑ i, E i = 1

theorem naimark (P : POVM n m) :
    ∃ V : H n →ₗ[ℂ] DilSpace n m, LinearMap.adjoint V ∘ₗ V = LinearMap.id ∧
      ∀ i, LinearMap.adjoint V ∘ₗ dilProj n m i ∘ₗ V = P.E i

theorem naimark_born (P : POVM n m) (i : Fin m) (x : H n) :
    ⟪x, P.E i x⟫_ℂ = ⟪dilV P x, dilProj n m i (dilV P x)⟫_ℂ
```

`DilSpace n m := EuclideanSpace ℂ (Fin m × Fin n)` et `dilProj i` est la projection
orthogonale sur le `i`-ème bloc.

**N5 (optionnel, clos)** : `dilV` s'étend en un vrai unitaire de `DilSpace n m` (pas
seulement une isométrie), pour tout indice ancilla `i₀` fixé (Watrous Cor. 2.43 /
Paris §3.2 Thm 4) :

```lean
theorem exists_unitary_extension (P : POVM n m) (i₀ : Fin m) :
    ∃ U : DilSpace n m ≃ₗᵢ[ℂ] DilSpace n m, U.toLinearMap ∘ₗ singleL n m i₀ = dilV P

theorem naimark_projective_form (P : POVM n m) (i₀ : Fin m) :
    ∃ U : DilSpace n m ≃ₗᵢ[ℂ] DilSpace n m, ∀ (i : Fin m) (x : H n),
      ⟪x, P.E i x⟫_ℂ = ⟪U (singleL n m i₀ x), dilProj n m i (U (singleL n m i₀ x))⟫_ℂ
```

## Écart documenté vs Watrous

Watrous dilate dans un produit tensoriel `X ⊗ ℂ^Σ`. Nous dilatons dans la **somme
directe hilbertienne** `K := ⊕_{i<m} H n`, canoniquement isomorphe (l'API Mathlib
pour `PiLp`/`EuclideanSpace` est plus mûre que celle du produit tensoriel hilbertien
à cette date). Correspondance : `1_X ⊗ E_{a,a}` devient `dilProj a` ; `√μ(a) ⊗ e_a`
devient `singleL a ∘ₗ sqrtOp (E a)`. Le contenu mathématique (isométrie + formule de
Born) est identique ; seule la réalisation concrète de l'espace de dilatation diffère.

`DilSpace n m := EuclideanSpace ℂ (Fin m × Fin n)` a été choisi (étape 0, jalon N0)
sur `PiLp 2 (fun _ : Fin m => H n)` à friction de preuve égale, pour son index plat
unique — voir `MILESTONES.md` pour le détail des deux routes testées.

## Théorème de Wigner

```lean
def IsWignerMap (T : H n → H n) : Prop :=
  ∀ x y : H n, ‖x‖ = 1 → ‖y‖ = 1 → ‖⟪T x, T y⟫_ℂ‖ = ‖⟪x, y⟫_ℂ‖

theorem wigner (n : ℕ) (T : H n → H n) (hT : IsWignerMap T) :
    (∃ U' : H n ≃ₗᵢ[ℂ] H n, ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U' x)
  ∨ (∃ U' : H n ≃ₛₗᵢ[starRingEnd ℂ] H n, ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U' x)
```

Aucune hypothèse de bijectivité sur `T` : en dimension finie, l'isométrie construite
`U'` est automatiquement bijective (`U_bijective`), et l'injectivité au niveau des
rayons découle de `hT` seul. Blueprint mathématique : Bargmann 1964, §1–§5 (repris
quasi tel quel) ; Simon–Mukunda–Chaturvedi–Srinivasan 2008 utilisé uniquement en
contre-vérification (rejeté comme blueprint principal — approche
trigonométrique/`Real.Angle`).

Construction (Bargmann §3–§5) : `V` (colinéarité définitionnelle sur `𝒫 := e⊥`, W3)
puis `χ` (dichotomie `id`/`conj` établie sur CHAQUE direction indépendamment, puis
globalisée sans hypothèse de repère orthogonal, W4) puis `U := χ⟨e,·⟩•e' + V(· − ⟨e,·⟩•e)`
étendant `V`/`χ` à tout l'espace (W5). Aucune coordonnée, aucune extension de base
orthonormée, aucun `Submodule` pour `𝒫` (une simple `Prop`, `InPerp`).

**Écarts documentés vs le plan initial** (voir `MILESTONES.md`, sections W3–W5, pour le
détail complet) :
- W3 (`V_colinear`) : le squelette initial affirmait `‖δ‖ = 1` pour le coefficient de
  colinéarité — FAUX en général (réfuté par le contre-exemple `T = id`) ; corrigé en
  `‖δ‖ = ‖z‖`.
- W4 (`chi_eq_chidir`) : l'argument de Bargmann §4.3–4.5 (`w = f₁+f₂`, orthogonal
  uniquement) est insuffisant dès que `n ≥ 3` et que le second vecteur n'est ni
  colinéaire ni orthogonal à `refVec`. Résolu par réduction à un seul point de
  comparaison (`i`, où `id` et `conj` se distinguent) plutôt que l'identité
  fonctionnelle complète.
- W5 (`U_bijective`) : la bijectivité semilinéaire (branche antiunitaire) ne dispose
  d'aucun lemme Mathlib direct ; résolue par restriction aux scalaires réels
  (`starRingEnd ℂ` est ℝ-linéaire), sur laquelle `LinearMap.injective_iff_surjective`
  s'applique tel quel.

Voir `ARCHITECTURE_NOTES.md` pour la liste consolidée de tous les écarts
signalés (N0–N5 et W0–W6), compilée en un seul endroit.

## W6 (optionnel) — Exclusivité et unicité (Bargmann §1.5, §6 restreint)

```lean
def Delta (a b c : H n) : ℂ := ⟪a, b⟫_ℂ * ⟪b, c⟫_ℂ * ⟪c, a⟫_ℂ

theorem exclusivity (hT : IsWignerMap T) (hn : 2 ≤ n) :
    ¬ ((∃ U : H n ≃ₗᵢ[ℂ] H n, ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U x)
     ∧ (∃ U' : H n ≃ₛₗᵢ[starRingEnd ℂ] H n, ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U' x))

theorem U_alt_eq_smul (T : H n → H n) (lam : ℂ) (hlam : ‖lam‖ = 1) (a : H n) :
    Up T (lam • eImg T) a = lam • U T a
```

**(A) Exclusivité** (Bargmann §1.5) : un même `T` ne peut jamais être compatible
à la fois avec une équivalence unitaire et une équivalence antiunitaire, pour
`n ≥ 2`. Preuve par témoin explicite : le triplet `e, e₂ := (e−refVec)/√2,
e₃ := (e+refVec(1−i))/√3` donne `Delta(e,e₂,e₃) = i/6 ∉ ℝ`
(`bargmann_delta_witness`, confirmé par Lean au chiffre près) ; or `Delta` est
invariant sous une branche unitaire et conjugué sous une branche antiunitaire
(`delta_transform_lin`/`delta_transform_conj`), ce qui forcerait `i/6 = -i/6`.

**(B) Unicité à phase globale près — version RESTREINTE** : si l'on reconstruit
`U` en remplaçant, dans les formules mêmes de `Defs.lean`, le représentant
unitaire `eImg T := T(e n)` par un autre représentant unitaire `λ • eImg T` de
la même classe (`‖λ‖ = 1`), le nouveau `U` vaut exactement `λ • U`
(`U_alt_eq_smul`). Version strictement plus faible que le Théorème 2 complet
de Bargmann §6 (qui couvrirait un `U'` complètement arbitraire, pas seulement
la liberté de représentant de `eImg`) — suffisante pour le cas d'usage réel du
dépôt. `Defs.lean` n'est pas modifié : la reconstruction paramétrée (`Vp`,
`chidirp`, `chip`, `Up`) est locale à `Uniqueness.lean`, reliée à `V`/`chi`/`U`
par des lemmes-pont prouvés `rfl`.

## Corollaire 1.2 de Šemrl (Uhlhorn)

```lean
def PreservesOrthogonality (φ : Proj1 n → Proj1 n) : Prop :=
  ∀ P Q : Proj1 n, (P : Submodule ℂ (H n)) ⟂ (Q : Submodule ℂ (H n)) →
    (φ P : Submodule ℂ (H n)) ⟂ (φ Q : Submodule ℂ (H n))

theorem uhlhorn_finite_dim (hn : 3 ≤ n) (φ : Proj1 n → Proj1 n)
    (hφ : PreservesOrthogonality φ) : IsWignerSymmetryProj φ
```

`Proj1 n := {A : Submodule ℂ (H n) // Module.finrank ℂ A = 1}` (une projection
de rang 1, pas de wrapper `rankOne` dédié — convention identique à celle de
`gleason-theorem-lean`). Toute application sur les projections de rang 1 qui
préserve l'orthogonalité **dans un seul sens** (`PQ = 0 ⟹ φ(P)φ(Q) = 0`, ni
injectivité ni surjectivité supposées) est, en dimension finie `n ≥ 3`, une
symétrie de Wigner — Šemrl 2021, *Wigner symmetries and Gleason's theorem*
(arXiv:2106.06182), Corollaire 1.2.

**Ce résultat COMPOSE deux théorèmes plutôt que d'introduire un contenu
mathématique autonome** : le cœur de la preuve applique `Gleason.gleason`
(dépendance externe) DEUX FOIS — une fois pour construire, à partir d'une
densité-test `D` et de l'hypothèse de préservation, une seconde densité `E` ;
une seconde fois implicitement en spécialisant `D := projL(φQ)` pour identifier
`E = projL Q` via le lemme spectral élémentaire (U2) — puis conclut avec
`wigner` (bloc interne ci-dessus) via le corollaire (B) de Wigner en langage de
projections (U1, jamais construit avant ce jalon). Découpage complet en six
sous-jalons (U1 : corollaire de Wigner en projections ; U2 : lemme spectral ;
U3a : extension d'une fonction-cadre sur les droites en `ProjMeasure` complet,
absente de `gleason-theorem-lean` et donc dérivée dans ce dépôt ; U3b :
« Gleason appliqué deux fois » ; U4 : assemblage ; U5 : réduction
fini-dimensionnelle par comptage de cardinalité) — détail complet dans
`MILESTONES.md`.

## Théorème de Cohérence de Grain (BornRule)

```lean
structure Perspective (n : ℕ) where
  cells : Finset (Submodule ℂ (H n))
  nz    : ∀ c ∈ cells, c ≠ ⊥
  ortho : ∀ c ∈ cells, ∀ c' ∈ cells, c ≠ c' → c ≤ c'ᗮ
  span  : sSup (cells : Set (Submodule ℂ (H n))) = ⊤

theorem grainCoherenceTheorem (hn3 : 3 ≤ n) (hA : AxGrain Est) (hN : AxNorm Est)
    (hPos : AxPos Est) {v : H n} (hv : ‖v‖ = 1) (hNul : AxNul Est v)
    (D : Perspective n) {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
    Est D c = ∑ i : Fin (Module.finrank ℂ c),
      ‖⟪v, ((stdOrthonormalBasis ℂ c i : c) : H n)⟫_ℂ‖ ^ 2

theorem grainCoherenceTheorem_projector (hn3 : 3 ≤ n) (hA : AxGrain Est)
    (hN : AxNorm Est) (hPos : AxPos Est) {v : H n} (hv : ‖v‖ = 1)
    (hNul : AxNul Est v) (D : Perspective n) {c : Submodule ℂ (H n)}
    (hc : c ∈ D.cells) :
    Est D c = ‖projL c v‖ ^ 2
```

Pour une perspective `D` (partition orthogonale de `H n` en cellules non
nulles) et une cellule `c` de `D`, toute règle d'estimation `Est` satisfaisant
(Grain), (Norm), (Pos) et, pour un vecteur unitaire `v` fixé, (Null), vérifie
`Est D c = ∑ᵢ ‖⟨v,fᵢ⟩‖²` sur toute base orthonormée `(fᵢ)` de `c` — la règle de
Born en toute généralité, dérivée des quatre axiomes de cohérence seuls, sans
supposer `Est` a priori de la forme d'une trace. Couvre la route descriptive
(via le théorème de Gleason) ; une seconde route de dérivation indépendante
(via un axiome de stabilité dynamique plutôt que de cohérence de grain),
l'existence/consistance des quatre axiomes eux-mêmes, et la convergence
intersubjective entre observateurs comme corollaire sont des extensions
futures possibles, non attaquées ici.

**Ce résultat COMPOSE Gleason et l'infrastructure Uhlhorn plutôt que
d'introduire un contenu mathématique autonome** : B2 construit une fonction-
cadre sur les droites directement depuis la règle d'estimation (via
`Perspective.binary`) et invoque U3a + `Gleason.gleason` (réel, pas un axiome)
pour obtenir une densité `ρ` ; B3 réutilise U2 pour montrer qu'un opérateur
densité qui s'annule sur l'orthogonal d'un vecteur unitaire `v` est exactement
`projL (ℂ∙v)` ; B4 relie (Null) à cette hypothèse d'annulation et assemble le
tout via `refinePerspective`/`refine_filter_eq_cellLines` (déjà prouvés en B1).
Découpage complet en quatre jalons (B1 : scaffolding — perspectives, axiomes,
non-contextualité ; B2 : pont vers Gleason ; B3 : pinning ; B4 : assemblage
final) — détail complet et écarts favorables dans `MILESTONES.md`.

`#print axioms grainCoherenceTheorem` ne dépend que de `[propext,
Classical.choice, Quot.sound]` : le théorème de Gleason est importé comme un
vrai théorème (`Gleason.gleason`), jamais postulé.

`grainCoherenceTheorem_projector` est uniquement la version en notation
projecteur du théorème précédent : l'identité de Parseval identifie sa somme
sur la base orthonormée à `‖projL c v‖²`. Ce n'est pas un nouveau résultat
mathématique indépendant.

## Théorème des inférences contraires de Kent (HistoriesKent)

```lean
abbrev History (n L : ℕ) := Fin L → Submodule ℂ (H n)

def IsConsistent (ψ : H n) (Ps : Fin L → Perspective n) : Prop :=
  ∀ h k : History n L, IsHistoryOf Ps h → IsHistoryOf Ps k → h ≠ k →
    decFunctional ψ h k = 0

def histProb (ψ : H n) (h : History n L) : ℝ := ‖chainOp h ψ‖ ^ 2

theorem contrary_inferences :
    ∃ (Ps Ps' : Fin 2 → Perspective 3) (ψ : H 3),
      P 0 ⟂ P 1 ∧
      IsConsistent ψ Ps ∧ IsConsistent ψ Ps' ∧
      (histProb ψ (![(P 0)ᗮ, F] : History 3 2) = 0 ∧ histProb ψ (![P 0, F] : History 3 2) ≠ 0) ∧
      (histProb ψ (![(P 1)ᗮ, F] : History 3 2) = 0 ∧ histProb ψ (![P 1, F] : History 3 2) ≠ 0)
```

En français : il existe deux familles cohérentes d'histoires à deux étages sur
`H 3`, partageant la même préparation `ψ` et le même étage final de
post-sélection `F`, telles que la première implique avec certitude la
proposition `P 0`, la seconde implique avec certitude `P 1`, et `P 0` est
orthogonale à `P 1` — Kent 1997, PRL 78, 2874, arXiv:gr-qc/9604012. Un étage
temporel d'un ensemble d'histoires **est** une `BornRule.Perspective`,
réutilisée telle quelle. La cohérence utilisée est la version « medium/forte »
de Kent (`decFunctional ψ h k = 0` pour toute paire d'histoires distinctes de
la famille, pas seulement sa partie réelle). Témoin explicite construit en
dimension 3 : `ψ₀ := e₀+e₁+e₂`, `φ₀ := e₀+e₁−e₂` (non normalisés), `P i :=
ℂ∙(e i)`, `F := ℂ∙φ₀` — l'annulation clé du témoin est `⟪φ₀, e i⟫ = 1` pour
`i ∈ {0,1}` (`= -1` pour `i = 2`, hors témoin).

**Note de neutralité.** Le contenu mathématique ci-dessus — deux ensembles
cohérents impliquant chacun avec certitude une proposition, ces deux
propositions étant orthogonales — est un fait incontesté. Son interprétation
comme objection à la prédictibilité des histoires cohérentes est débattue :
la réponse usuelle (Griffiths) invoque la « single-framework rule » — les
deux inférences ne sont valides que chacune dans son propre cadre, jamais
combinées dans un même raisonnement. Ce dépôt fixe l'énoncé mathématique,
sans trancher le débat interprétatif.

Le théorème de profusion générique de Dowker–Kent (J. Stat. Phys. 82, 1575
(1996), comptage de paramètres/dimensions de variétés montrant que la
contrariété n'est pas un cas isolé) est explicitement hors scope de ce bloc —
extension future possible, voir `MILESTONES.md`.

## Borne de circuit d’interférence par records redondants (Complexity)

Le bloc `QuantumFoundations.Complexity` relie les records spatiaux exacts ou
approximatifs de
Riedel aux circuits quantiques 2-locaux. Les circuits sont des listes finies
de portes unitaires, chacune locale à un `Finset (Fin N)` de cardinal au plus
deux. Pour `[G₁, G₂, G₃]`, la convention est
`eval C x = G₃ (G₂ (G₁ x))`.

Le théorème principal a le type exact suivant :

```lean
theorem regions_card_le_two_mul_circuit_length_of_cross_amplitude_ne_zero
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (C : Circuit N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K) (ψ : H (d ^ N))
    (hrec : IsRecordedOn ψ recs) (i j : Fin K) (hij : i ≠ j)
    (hlocal : ∀ r, IsLocalTo (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : ∀ r r', r ≠ r' → Disjoint (regions r) (regions r'))
    (hcross : ⟪branch recs ψ j, Circuit.evalOnH C e (branch recs ψ i)⟫_ℂ ≠ 0) :
    R ≤ 2 * Circuit.length C
```

Ainsi, toute amplitude croisée exacte non nulle entre deux branches
distinctes force le circuit à toucher chaque région-record ; les régions
étant deux-à-deux disjointes et chaque porte touchant au plus deux sites, on
obtient la borne explicite `R ≤ 2 * C.length`.

Les jalons C3–C6 ajoutent les proxies exacts, sans division :

```lean
DistinguishesAt e a b δ C :=
  2 * δ ≤ ‖⟪a, C.evalOnH e a⟫_ℂ - ⟪b, C.evalOnH e b⟫_ℂ‖

InterferesAt e a b δ C :=
  2 * δ ≤ ‖⟪a, C.evalOnH e b⟫_ℂ‖ + ‖⟪b, C.evalOnH e a⟫_ℂ‖
```

Pour deux branches enregistrées distinctes et non nulles, normalisées par
`normalizedBranch`, avec `0 < δ ≤ 1`, des régions-records deux-à-deux
disjointes et la localité des projecteurs cibles pour **les deux** étiquettes,
`redundant_records_give_interference_lower_bound` prouve que tout circuit
interférant a longueur au moins `ceilHalf R := (R + 1) / 2`. Si un circuit
explicite `D` implémente exactement `2 P_j - I`, alors
`record_phase_flip_gives_distinguishability_upper_bound` donne un témoin de
distinguabilité de longueur `D.length`. Finalement,
`redundant_records_give_proxy_gap_certificate` prouve le certificat sans
soustraction `D.length + g ≤ ceilHalf R`, et
`redundant_records_complexity_gap` en donne la version minimale dans
`WithTop ℕ` :

```lean
distinguishabilityComplexity e a b δ + (g : WithTop ℕ)
  ≤ interferenceComplexity e a b δ
```

Le jalon C7 ajoute une persistance conditionnelle sous évolution réversible
par circuits finis. Une `ReversibleCircuitEvolution` contient deux circuits
explicites `forward` et `backward`, dont les évaluations sont inverses, et le
surcoût `forward.length + backward.length`. Comme
`eval (C ++ D) = eval D ∘ₗ eval C`, `backward ++ C ++ forward` implémente
`forward ∘ₗ C ∘ₗ backward`, tandis que `forward ++ C ++ backward` implémente
le pullback opposé. Les proxies sont exactement invariants sous ces
conjugaisons. Une borne supérieure de distinguabilité augmente d'au plus un
surcoût, une borne inférieure d'interférence diminue d'au plus un surcoût, et
le gap certifié diminue donc d'au plus deux surcoûts.

L'inverse canonique a également été construit : chaque porte inverse garde le
même support local, et le circuit inverse renverse la liste en inversant ses
portes. Ainsi `ofCircuit E` a un surcoût `2 * E.length`, d'où la condition
exacte sur les records
`D.length + 4 * E.length + g ≤ ceilHalf R`. Les versions minimales dans
`WithTop ℕ` sont prouvées directement sous l'infimum, y compris dans le cas
`⊤`, sans supposer qu'un minimum est atteint et sans soustraction.

Le jalon C8 remplace les identités de record exactes par le budget agrégé
`ApproxRecordFor P target other η :=
‖P target - target‖ + ‖P other‖ ≤ η`. Cette agrégation correspond exactement
aux deux termes produits par la décomposition projecteur/défaut : une région
non touchée donne la constante nette `‖cross amplitude‖ ≤ η`. Pour les deux
orientations du proxy, le budget devient `ηi + ηj`; la condition stricte
`ηi + ηj < 2 * δ` force donc encore chaque région à être touchée.

Le circuit de lecture explicite peut lui-même être approché sur les deux
vecteurs, avec erreur agrégée `ξ`. La séparation diagonale idéale `2` se
dégrade d'au plus `2 * ηj + ξ`, d'où le seuil suffisant
`2 * δ + 2 * ηj + ξ ≤ 2`. Ces certificats donnent le gap robuste et sa version
minimale. Le transport C7 étant une conjugaison unitaire exacte, il n'ajoute
aucune erreur analytique : seul subsiste le coût combinatoire
`2 * Evo.overhead`, ou `4 * E.length`. À `ηi = ηj = ξ = 0`, les résultats
exacts C4–C7 sont retrouvés.

Les trois prédicats robustes publics sont exactement :

```lean
ApproxRecordFor P target other η :=
  ‖P target - target‖ + ‖P other‖ ≤ η

ApproxRecordedPairOn recs a b i j ηi ηj := ∀ r,
  ApproxRecordFor (rproj (recs r) i) a b ηi ∧
  ApproxRecordFor (rproj (recs r) j) b a ηj

ApproximatesRecordPhaseFlipOn e D Λ j a b ξ :=
  ‖Circuit.evalOnH D e a - recordPhaseFlip Λ j a‖ +
  ‖Circuit.evalOnH D e b - recordPhaseFlip Λ j b‖ ≤ ξ
```

Le jalon C9 instancie cette architecture dans le modèle binaire explicite de
répétition. `zeroBranch R` et `oneBranch R` sont les vecteurs de base des
configurations constantes zéro et un, transportés par `sitesEquivR`; leur somme
`repetitionState R` n'est volontairement pas normalisée. Chaque singleton
`{r}` porte la résolution computationnelle locale et constitue un record
indépendant du même label binaire. La réflexion `2 P₁ - I` au premier site est
une porte de lecture unique, tandis que le circuit ordonné de `R` portes
Pauli-X échange exactement les deux branches. On obtient donc

```lean
distinguishabilityComplexity (sitesEquivR R) (zeroBranch R) (oneBranch R) 1 = 1
ceilHalf R ≤ interferenceComplexity (sitesEquivR R) (zeroBranch R) (oneBranch R) 1
interferenceComplexity (sitesEquivR R) (zeroBranch R) (oneBranch R) 1 ≤ R
```

ainsi que le gap pour `1 + g ≤ ceilHalf R` et sa persistance conditionnelle
sous le budget exact `1 + 4 * E.length + g ≤ ceilHalf R`. Le majorant fini
prouve en particulier que l'interference complexity n'est pas `⊤`.
L'option de sharpness par flips appariés n'est pas revendiquée : les bornes
fermées sont `ceilHalf R ≤ C_I ≤ R`.

Le jalon C10 instancie enfin la théorie robuste C8 sur une famille à bruit
**non nul** explicite, sur `R + 1` sites : un qubit source (site `0`) plus
`R` qubits de mémoire (`recordSite r := Fin.succ r`). Un `NoiseProfile`
normalisé `(keep, leak)` (`‖keep‖² + ‖leak‖² = 1`) mélange deux
configurations de même bit source, `noisyZeroBranch := keep • basis00 + leak
• basis01` et `noisyOneBranch := leak • basis10 + keep • basis11`, qui restent
**exactement orthogonales pour tout `leak`** puisque le qubit source diffère
entre elles. Chaque record a une erreur exacte calculée : il fixe
exactement la configuration alignée et fuit exactement `‖leak‖` vers
l'autre, d'où l'erreur agrégée exacte `2 * ‖leak‖` par étiquette — un
habitant non trivial de `ApproxRecordedPairOn`, sans jamais invoquer
`IsRecordedOn`. Au seuil `δ = 1/2`, la condition robuste est exactement

```lean
def NoiseProfile.IsRobust (p : NoiseProfile) : Prop := 4 * ‖p.leak‖ < 1
```

sous laquelle on obtient exactement les mêmes bornes que C9 :

```lean
distinguishabilityComplexity (sitesEquivR (R+1)) (noisyZeroBranch p R) (noisyOneBranch p R) (1/2) = 1
ceilHalf R ≤ interferenceComplexity (sitesEquivR (R+1)) (noisyZeroBranch p R) (noisyOneBranch p R) (1/2)
interferenceComplexity (sitesEquivR (R+1)) (noisyZeroBranch p R) (noisyOneBranch p R) (1/2) ≤ R + 1
```

ainsi que le gap robuste et sa persistance conditionnelle sous le même budget
`1 + 4 * E.length + g ≤ ceilHalf R`. Le triplet pythagoricien
`99² + 20² = 101²` fournit un témoin rationnel concret
`(keep, leak) = (99/101, 20/101)` avec `4 * (20/101) = 80/101 < 1`, auquel
tous les théorèmes C10a–C10g s'appliquent sans hypothèse supplémentaire.
Trois généralisations additives de C9 (jamais nécessaires à C9 lui-même) ont
servi de brique : une branche de base à configuration arbitraire
(`configurationBranch`), une lecture par réflexion à site arbitraire
(`recordReadoutGateAt`/`recordReadoutCircuitAt`), et l'action du circuit
« flip tous les bits » sur une configuration arbitraire
(`allBitFlipCircuit_maps_configurationBranch`) — dans chaque cas la
déclaration C9 existante est reprouvée comme cas particulier, sans changer
son type public.

Le jalon C11 comble précisément l'écart signalé à la fin de C10 : un circuit
fini explicite de portes `1`- et `2`-locales génère **unitairement** les
branches source-record à partir d'un qubit source non corrélé
`α|0⟩ + β|1⟩` et de `R` qubits de mémoire vierges, au lieu de les supposer
déjà formées. `controlledBitFlipGate` (C11a) est une porte de permutation
`2`-locale; `idealFanoutCircuit R` (C11b) copie l'étiquette classique du
qubit source vers chaque record — un fanout d'étiquette en base de calcul,
jamais un clonage d'un état quantique arbitraire (le no-cloning n'est pas
violé : seule l'étiquette classique `0`/`1` est propagée, jamais les
amplitudes propres du qubit source). La construction la plus délicate
(C11e) est une véritable rotation unitaire de mélange d'amplitude sur un
qubit, élevée à tous les `N` sites via la représentation plate `Sites N d`
(aucune infrastructure de facteur tensoriel n'existait dans le dépôt pour
cela) : `prepLinearMap p t := keep • P₀ + leak • (F ∘ P₀) - conj(leak) •
(F ∘ P₁) + conj(keep) • P₁`, prouvée unitaire par expansion directe du
produit scalaire à 16 termes. Cette construction réussit **sans condition**
pour chaque `NoiseProfile` — aucune porte supplémentaire n'a dû être
supposée. `noisyMeasurementCircuit p R` (C11f–g, longueur `2R`) transforme
`α • basis00 + β • basis10` en exactement
`α • noisyZeroBranch p R + β • noisyOneBranch p R` : ce sont les *mêmes*
états que ceux de C10, si bien que le gap robuste et sa persistance
conditionnelle sous un circuit ultérieur arbitraire s'y transportent
immédiatement (C11i), sans nouvel argument de distinguabilité. Le triplet
pythagoricien `3² + 4² = 5²` fournit un témoin rationnel concret
`(amp0, amp1) = (3/5, 4/5)` (C11j), auquel s'applique — combiné au profil de
bruit rationnel `(99/101, 20/101)` de C10h — toute la chaîne C11 sans
hypothèse supplémentaire.

Le jalon C12 comble le pont optionnel en norme d'opérateur laissé de côté
depuis C8 : `toContinuousLinearMapFD` (C12a) est la vue canonique en
application linéaire continue d'une application linéaire issue d'un espace
normé complexe de dimension finie (`LinearMap.toContinuousLinearMap` de
Mathlib) — `Circuit.evalOnH`, `recordPhaseFlip` et toute l'API `LinearMap`
existante restent inchangées; c'est une vue supplémentaire, pas un
remplacement. `ApproximatesOperator A B ε := ‖A - B‖ ≤ ε` (C12b) est une
erreur de norme d'opérateur générique, sans référence aux records ou
circuits; l'estimation centrale `‖A x - B x‖ ≤ ε‖x‖` donne, sur deux états
unitaires `a, b`, l'accumulation `‖A a - B a‖ + ‖A b - B b‖ ≤ 2ε` — le
facteur `2` dérivé par arithmétique simple, jamais postulé.
`ApproximatesRecordPhaseFlipOp` (C12c) spécialise ce pont à
`recordPhaseFlip` : un budget d'erreur en norme d'opérateur `ε` implique le
budget ponctuel C8 `ξ = 2ε`, ce qui restitue directement (C12d) le seuil de
lecture `2δ + 2ηj + 2ε ≤ 2` et (C12e) le gap proxy robuste ainsi que sa
persistance conditionnelle, en réutilisant tel quel l'estimation analytique
de C8 — aucune nouvelle estimation n'est introduite. Au modèle bruité C10
(C12f), ce seuil devient exactement `4‖leak‖ + 2ε ≤ 1`; l'hypothèse
`p.IsRobust` (`4‖leak‖ < 1`, stricte) reste néanmoins nécessaire en plus de
ce seuil — non redondante, car `hreadout` seul (avec `ε ≥ 0`) ne donne que
l'inégalité large `4‖leak‖ ≤ 1`, insuffisante pour l'argument
d'interférence strict. Aux branches dynamiquement engendrées par C11
(C12g), le même seuil s'applique directement au couple de branches généré.
Le témoin rationnel concret `ε = 1/20` vérifie exactement
`80/101 + 2·(1/20) ≤ 1` par arithmétique rationnelle exacte. Des lois de
composition génériques (C12h, facultatives) préparent l'accumulation
d'erreur de simulation de C13.

Le jalon C13 établit la persistance robuste du gap sous une véritable
évolution `U` préservant la norme (pas nécessairement un circuit), tant
qu'un circuit exact `E` l'approche en norme d'opérateur à erreur `ε`. Le
point mathématique central est qu'une persistance au **même** seuil `δ` sans
marge n'est en général **pas** justifiée : perturber deux états unitaires de
`ε` chacun déplace la différence diagonale d'au plus `4ε` et la somme
croisée d'au plus `4ε` (C13b), ce qui déplace le seuil de proxy de `2ε`
(puisque les définitions utilisent `2·seuil`). C13 introduit donc une marge
`μ` : un certificat à seuils écartés `δ-μ` (interférence) et `δ+μ`
(distinguabilité) — `HasProxyGapMarginAtLeast` (C13d) — persiste sous circuit
exact (C13e) puis se transporte vers le seuil central `δ` pour les états
évolués par `U`, dès que `2ε ≤ μ` (C13f, le théorème principal). Le
certificat de simulation `CircuitSimulatesEvolutionAt`/`HasCircuitSimulationAt`
(C13f) et son extension dépendante du temps `HasCircuitSimulationBound`
(C13j) rendent ce résultat directement réutilisable. Instancié au modèle
bruité C10 (C13g) puis aux branches engendrées par C11 (C13h), avec le
témoin rationnel concret `δ=1/2, μ=1/10, ε=1/20` (C13i,
`80/101 < 4/5`, `6/5+80/101 ≤ 2`, `2·(1/20) ≤ 1/10`). Une interface
optionnelle (C13k) construit une évolution *effectivement* engendrée par un
générateur auto-adjoint `H` — `evolve t := exp(-itH)`, via l'exponentielle
opératorielle existante de Mathlib pour les C⋆-algèbres bornées, sans aucune
hypothèse supplémentaire — dont seule la loi de groupe additive reste non
prouvée (obstruction de résolution d'instances Mathlib précisément
documentée dans le fichier, non une lacune mathématique).

Le jalon **C14** relie deux théorèmes déjà établis plutôt que d'en dériver un
depuis l'autre : la décomposition en branches jointes, uniques et
orthogonales de `Induction.riedel` (BranchesRiedel), et le poids de Born
`grainCoherenceTheorem_projector` (BornRule), qui assigne `‖projL c v‖²` à
toute cellule `c` d'une perspective, sous (Pos), (Norm), (Grain), (Null).
`BranchesRiedel/BornBridge/` distingue quatre objets : un vecteur de branche
`B f`, sa cellule active `span ℂ {B f}` (définie seulement si `B f ≠ 0` —
un vecteur nul n'a pas de cellule formelle), le support `branchSupport`
(la borne supérieure des cellules actives, pas nécessairement tout
l'espace) et la cellule résiduelle orthogonale `residualCell` (qui peut
être `⊥`). L'identité de projection centrale,
`starProjection_branchCell_apply_state : (branchCell B f).starProjection ψ
= activeBranchVector B f` (C14c), est un fait d'algèbre linéaire pur — via
`Submodule.eq_starProjection_of_mem_orthogonal'` — indépendant de toute
pondération. `BranchPerspectivePackage` (C14e) construit une véritable
`Perspective` à partir des cellules actives, en ajoutant la cellule
résiduelle seulement si elle est non nulle (`Perspective` interdit les
cellules `⊥`). `recordBranch_weight_eq_norm_sq` (C14f) chaîne alors
`grainCoherenceTheorem_projector` et l'identité de projection : le poids de
Born de chaque cellule active vaut exactement `‖B f‖²`, le poids résiduel
est nul, et les poids actifs somment à `1`. L'invariance de choix de
record (C14a) — `chainProj_choice_invariant`, prouvée par remplacement
d'observable un par un via `Induction.tunneling`, sans jamais composer deux
records différents de la même observable — donne l'invariance du poids par
rapport au record choisi (C14f.5), au niveau des vecteurs, pas seulement
des normes. `record_induced_Born_decomposition` (C14g) assemble le tout en
un théorème abstrait unique, spécialisé au modèle multi-sites local (C14h)
puis à la génération unitaire exacte de C11 (C14i) — deux branches
`q.amp0 • basis00 R`/`q.amp1 • basis11 R`, poids `‖amp0‖²`/`‖amp1‖²` —,
concrètement à `(3/5, 4/5)` donnant les poids rationnels exacts `9/25` et
`16/25` (C14l). Le modèle bruité C10 ne satisfait que la redondance
approximative (`ApproxRecordedPairOn`), pas l'exacte `IsRecordedOn` :
l'unicité exacte de branche n'est donc pas conclue pour lui, seule
l'extraction exacte des composantes de source (C14j) demeure. Enfin, les
poids de Born des branches évoluées sous une évolution norm-préservante
(C13) conservent leur norme au carré — via l'identité de polarisation en
termes de normes, `inner_eq_sum_norm_sq_div_four` — sans que la branche
évoluée soit encore sélectionnée par les projecteurs de record d'origine
(C14k).

Le résultat porte uniquement
sur un nombre fini de sites, une dimension locale finie, des records exacts
ou des records approximatifs fournis,
des régions deux-à-deux disjointes, des portes exactement 2-locales et une
amplitude/proxy au-dessus du seuil explicite. Il ne traite pas
la formation générique de records approximatifs par décohérence (distincte de
la construction unitaire explicite de C11), la synthèse
efficace de projecteurs locaux arbitraires, la complétion en norme
d'opérateur de toute l'API du dépôt (C12 ne couvre que le pont de lecture de
record), le
critère physique complet de Taylor–McCulloch, une borne de simulation de
Trotter/formule produit ou de Lieb–Robinson, une croissance linéaire ou
polynomiale du coût de simulation en temps (C13 ne formalise aucune notation
`O(t)`), la croissance générique de complexité, la croissance
de Brown–Susskind, l'irréversibilité macroscopique, l'équivalence avec
Weingarten, ni une interprétation de la mécanique quantique. C14 relie
records redondants et poids de Born pour un modèle donné, sous (Pos),
(Norm), (Grain), (Null) — il ne prétend pas que les records seuls
impliquent la règle de Born, ni que (Grain) n'a besoin de valoir que sur
les perspectives physiquement réalisées, ni une unicité de décomposition
en branches approximative ou générique en système à N corps.

**C15** est la formalisation Lean et l’intégration au dépôt du Théorème 3 et
du Corollaire 2 de Marko Lela, « The Born Rule as the Unique
Refinement-Stable Induced Weight on Robust Record Sectors »
(arXiv:2603.24619v1). Son objet est un poids induit sur des situations de
record admissibles, pas une mesure sur le treillis complet des projecteurs.
L’équivalence interne est d’abord l’égalité des profils de raffinement
binaire; la saturation binaire exacte prouve ensuite que ces profils sont
classifiés par la norme projetée. L’équation fonctionnelle qui en résulte
force `W = c ‖P_R Ψ‖²`, et une normalisation finie fixe `c = 1`.
L’additivité peut être héritée d’une valuation extensive sur des faisceaux de
continuations disjoints. Aucun théorème de Gleason, Busch,
décision-théorique ou d’envariance n’est utilisé. La saturation binaire est
supposée, non dérivée de la dynamique C14; saturation dense plus continuité,
le pont physique C14/C15 et C16 sont explicitement différés.

**C17** est le premier théorème de stabilité quantitative de ce
développement. Il suppose que les deux poids satisfont déjà la loi
quadratique exacte fournie par C15 et mesure la perturbation par la distance
entre composantes projetées `u = P_(R₁)x Ψ₁x` et `v = P_(R₂)x Ψ₂x`. Il prouve
`|W₁-W₂| ≤ (‖u‖+‖v‖)‖u-v‖`, puis `|W₁-W₂| ≤ 2‖u-v‖` sur la boule unité, ainsi
que les bornes finies `L¹`, `2·card(s)·ε` et demi-`L¹`. Il ne traite ni des
hypothèses C15 approximatives, ni de l’unicité approximative des branches, ni
de la production dynamique de la proximité des composantes. Aucune
revendication de priorité historique n’est faite.

**C17b** est un jalon d’intégration, pas un renforcement du cœur C17 déjà
clos. Sur la boule unité, un secteur fixé vérifie
`|w_R(ψ)-w_R(φ)| ≤ 2‖ψ-φ‖`; deux projecteurs à distance au plus `ε` en norme
d’opérateur vérifient `|w_R(ψ)-w_S(ψ)| ≤ 2ε`. Un certificat de simulation C13
donne donc, pour chaque secteur fixé,
`|w_R(U(t)ψ)-w_R(Cψ)| ≤ 2ε`. Les poids de branches C14 héritent aussi de la
borne générique sur les vecteurs de branches lorsqu’une correspondance entre
branches est fournie explicitement. Ces ponts ne prouvent ni unicité ou
appariement approximatif des branches, ni saturation approximative, ni
persistance physique de la sélection des records.

## Assistance IA

Ce développement (squelette, preuves, choix d'architecture) a été réalisé avec
l'assistance de Claude (Anthropic), sous supervision humaine à chaque étape : chaque
API Mathlib incertaine a été vérifiée en `stdin` avant usage (`lake env lean --stdin`),
chaque jalon a démarré par un squelette en `sorry` validé avant remplissage, et
`lake build` + `./scripts/guard.sh` ont tourné après chaque preuve fermée. Voir
`AGENTS.md` pour les règles exactes suivies et l'historique des commits pour le détail
jalon par jalon.

## Démarrage

```bash
./setup.sh          # toolchain + mathlib + cache + build (~10 min avec cache)
./scripts/guard.sh  # audit : 0 axiome, 0 native_decide, compte des sorry
```

## Vérifier les preuves

```bash
lake build                    # doit terminer vert
./scripts/guard.sh            # 0 axiome, 0 native_decide, 0 sorry (sept blocs)
```

`#print axioms` sur les théorèmes-têtes de chapitre (liste exhaustive des 155
déclarations publiques porteuses de contenu dans `ARCHITECTURE_NOTES.md`/le
rapport de clôture — toutes dépendent du même trio) :

```
'QuantumFoundations.naimark' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.naimark_born' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.exists_unitary_extension' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.naimark_projective_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Wigner.wigner' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Wigner.exclusivity' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Wigner.bargmann_delta_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Wigner.U_alt_eq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Uhlhorn.uhlhorn_finite_dim' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Uhlhorn.wignerSymmetryProj_of_sendsONBToONB' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Uhlhorn.traceProd_preserved_of_sendsONBToONB' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Uhlhorn.exists_projMeasure_of_frameFunctionOnLines' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.grainCoherenceTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.grainCoherenceTheorem_projector' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.full_rho_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.hker_derivation' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.exists_rho' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.eq_projL_of_vanishes_on_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.E₀_satisfies_axioms' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.refine_filter_sup_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.HistoriesKent.contrary_inferences' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.HistoriesKent.inference' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.HistoriesKent.S_consistent' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.HistoriesKent.isConsistent_single_stage' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Ce sont les trois axiomes standards acceptés par Lean/Mathlib lui-même (extensionnalité
propositionnelle, axiome du choix, solidité des quotients) — aucun `sorryAx`, aucun
`axiom` spécifique au projet. **Points vérifiés spécifiquement** : `uhlhorn_finite_dim`
est le premier théorème du dépôt à dépendre à la fois de `Gleason.gleason`
(dépendance externe) ET de `QuantumFoundations.Wigner.wigner` (bloc interne) ;
`grainCoherenceTheorem` dépend à la fois de `Gleason.gleason` ET de
l'infrastructure Uhlhorn interne (U2, U3a) — dans les deux cas, cette double
chaîne de dépendances ne fait fuiter aucun axiome supplémentaire, confirmé
ci-dessus. `contrary_inferences` dépend transitivement d'une chaîne à TROIS
niveaux (`HistoriesKent` → `BornRule.Perspective` → `Uhlhorn`/`Gleason` externe) —
même trio, confirmé lors de la clôture de `HistoriesKent` (2026-07-16), ainsi que
la non-régression des axiomes de `BornRule` suite à la relocalisation de
`norm_sq_sum_of_pairwise_orthogonal`/`sum_sq_projL_of_pairwise_isOrtho`
(`private` dans `Nonvacuity.lean`, migrés public vers `Perspective.lean`) :
les 34 déclarations PUBLIQUES de `BornRule` (32 précédentes + les 2 lemmes
relocalisés, désormais publics) re-vérifiées individuellement, aucune
affectée.

## Carte du dépôt

| Fichier                                     | Contenu                                                                            | Lignes |
|---|---|---:|
| `QuantumFoundations/Naimark/Defs.lean`      | `POVM n m` (réutilise `Gleason.IsPositiveOp`)                                      | 46 |
| `QuantumFoundations/Naimark/SqrtOp.lean`    | Racine carrée positive (construction spectrale)                                    | 191 |
| `QuantumFoundations/Naimark/DilSpace.lean`  | Espace de dilatation `K`, `singleL`/`coordL`/`dilProj`                             | 194 |
| `QuantumFoundations/Naimark/Main.lean`      | `dilV`, isométrie, théorème de Naimark, corollaire de Born                         | 157 |
| `QuantumFoundations/Naimark/Unitary.lean`   | N5 (optionnel) : extension unitaire, forme ancilla                                 | 210 |
| `QuantumFoundations/Wigner/Defs.lean`       | `e`, `eImg`, `InPerp`, `V`, `refVec`, `chidir`, `chi`, `U`, `IsWignerMap`          | 119 |
| `QuantumFoundations/Wigner/Scalar.lean`     | Kit scalaire ℂ (rigidité, dichotomie `id`/`conj`)                                  | 117 |
| `QuantumFoundations/Wigner/Bessel.lean`     | Identité de Bessel (égalité) ; images orthonormées                                 | 126 |
| `QuantumFoundations/Wigner/VConstruction.lean` | Construction B de Bargmann : `V`, colinéarité, (11)-(12a)                       | 449 |
| `QuantumFoundations/Wigner/Core.lean`       | Cœur : dichotomie de `chi`, additivité/homogénéité de `V`                          | 833 |
| `QuantumFoundations/Wigner/Main.lean`       | `U`, bijectivité, compatibilité avec `T`, théorème `wigner`                        | 399 |
| `QuantumFoundations/Wigner/Uniqueness.lean` | W6 (optionnel) : exclusivité (A), unicité restreinte (B)                           | 439 |
| `QuantumFoundations/Wigner/Nonvacuity.lean` | Témoins Wigner : `id` (branche unitaire), `conjCoords` (branche antiunitaire)      | 112 |
| `QuantumFoundations/Uhlhorn/Defs.lean` | `Proj1`, `TraceProd`, `PreservesOrthogonality`, `IsWignerSymmetryProj`, `IsFrameFunctionOnLines`, `SendsONBToONB` | 278 |
| `QuantumFoundations/Uhlhorn/WignerProjectionForm.lean` | U1 : corollaire (B) de Wigner en langage de projections                 | 117 |
| `QuantumFoundations/Uhlhorn/Spectral.lean`  | U2 : lemme spectral élémentaire                                                     | 131 |
| `QuantumFoundations/Uhlhorn/GleasonExtend.lean` | U3a : extension d'une fonction-cadre sur les droites en `ProjMeasure` complet  | 268 |
| `QuantumFoundations/Uhlhorn/GleasonTwice.lean` | U3b : « Gleason appliqué deux fois »                                            | 175 |
| `QuantumFoundations/Uhlhorn/Assembly.lean`  | U4 (assemblage) + U5 (réduction fini-dimensionnelle), théorème `uhlhorn_finite_dim` | 111 |
| `QuantumFoundations/Uhlhorn/Nonvacuity.lean` | Témoin Uhlhorn : `φ := id`                                                        | 53 |
| `QuantumFoundations/BornRule/Perspective.lean` | B1 : `Perspective`, `Refines`, `AxGrain`/`AxNorm`/`AxPos`/`AxNul`, `lemma4_noncontextual`, `basisPerspective`, `cellLines`, `refinePerspective` | 555 |
| `QuantumFoundations/BornRule/GleasonBridge.lean` | B2 : `g`, `g_isFrameFunctionOnLines`, `exists_rho` (remplace `axiom gleason`) | 115 |
| `QuantumFoundations/BornRule/Pinning.lean`   | B3 : `eq_projL_of_vanishes_on_orthogonal` (identification de `ρ` via U2)          | 83 |
| `QuantumFoundations/BornRule/Assembly.lean`  | B4 (assemblage), théorème final `grainCoherenceTheorem`                          | 215 |
| `QuantumFoundations/BornRule/Nonvacuity.lean` | Témoin BornRule : `E₀ v` (règle de Born) satisfait Grain+Norm+Pos+Null simultanément | 177 |
| `QuantumFoundations/Nonvacuity.lean`         | Témoin Naimark : POVM uniforme `n=2, m=2`                                         | 65 |
| `QuantumFoundations/HistoriesKent/Defs.lean`     | `History`, `IsHistoryOf`, `chainOp`, `decFunctional`, `IsConsistent`, `histProb`   | 162 |
| `QuantumFoundations/HistoriesKent/Nonvacuity.lean` | Témoin HistoriesKent : toute `Perspective`, famille à un étage, est cohérente        | 85 |
| `QuantumFoundations/HistoriesKent/Basic.lean`    | K1 : `decFunctional_last_stage_orthogonal`, `histProb_additivity_two_stage`       | 121 |
| `QuantumFoundations/HistoriesKent/Witness.lean`  | K2 : témoin explicite de Kent en `H 3`, `S_consistent`                            | 490 |
| `QuantumFoundations/HistoriesKent/ContraryInferences.lean` | K3 : `inference`, théorème final `contrary_inferences`                  | 162 |
| `QuantumFoundations/BranchesRiedel/Defs.lean` | R0 : résolutions étiquetées, branches et records redondants | 234 |
| `QuantumFoundations/BranchesRiedel/Nonvacuity.lean` | R0 : témoin GHZ à trois records | 210 |
| `QuantumFoundations/BranchesRiedel/Basic.lean` | R1 : identités générales des projecteurs de records | 133 |
| `QuantumFoundations/BranchesRiedel/TwoObs.lean` | R2 : deux observables enregistrés | 207 |
| `QuantumFoundations/BranchesRiedel/Induction.lean` | R3 : induction multi-observables | 559 |
| `QuantumFoundations/BranchesRiedel/Local.lean` | R4 : localité spatiale et comptage `PairCovers` | 469 |
| `QuantumFoundations/BranchesRiedel/BornBridge/RecordChoice.lean` | C14a : invariance de choix de record redondant | 203 |
| `QuantumFoundations/BranchesRiedel/BornBridge/ActiveBranches.lean` | C14b : indice de branche active | 76 |
| `QuantumFoundations/BranchesRiedel/BornBridge/BranchCells.lean` | C14b/c : cellules de branche, identité de projection | 134 |
| `QuantumFoundations/BranchesRiedel/BornBridge/BranchPerspective.lean` | C14d/e : support, cellule résiduelle, perspective formelle | 218 |
| `QuantumFoundations/BranchesRiedel/BornBridge/BornWeights.lean` | C14f : poids de Born des branches induites par records | 151 |
| `QuantumFoundations/BranchesRiedel/BornBridge/Synthesis.lean` | C14g : théorème de synthèse abstrait | 92 |
| `QuantumFoundations/BranchesRiedel/BornBridge/LocalRecords.lean` | C14h : corollaire local multi-sites | 49 |
| `QuantumFoundations/BranchesRiedel/BornBridge/GeneratedBranches.lean` | C14i/j : modèle unitaire exact C11, frontière du modèle bruité | 199 |
| `QuantumFoundations/BranchesRiedel/BornBridge/Evolution.lean` | C14k : préservation des poids sous évolution norm-préservante | 129 |
| `QuantumFoundations/BranchesRiedel/BornBridge/ConcreteModel.lean` | C14l : instance concrète (poids 9/25, 16/25) | 86 |
| `QuantumFoundations/BranchesRiedel/BornBridge/Nonvacuity.lean` | C14 : témoins de non-vacuité | 101 |
| `QuantumFoundations/Complexity/Defs.lean` | C0 : portes et circuits 2-locaux, évaluation et support | 129 |
| `QuantumFoundations/Complexity/Nonvacuity.lean` | C0/C6/C7/C8/C9/C10/C11/C12/C13 : témoins élémentaires et modèles concrets | 389 |
| `QuantumFoundations/Complexity/CircuitLocality.lean` | C1 : commutation d'un circuit avec une région disjointe | 45 |
| `QuantumFoundations/Complexity/RecordInterference.lean` | C1 : records non touchés et amplitude croisée nulle | 122 |
| `QuantumFoundations/Complexity/Counting.lean` | C2 : comptage générique des régions disjointes touchées | 35 |
| `QuantumFoundations/Complexity/Main.lean` | C2 : borne principale `R ≤ 2 * C.length` | 63 |
| `QuantumFoundations/Complexity/ProxyDefs.lean` | C3 : proxies exacts de distinguabilité et d’interférence | 82 |
| `QuantumFoundations/Complexity/NormalizedBranches.lean` | C3 : normalisation des branches enregistrées non nulles | 83 |
| `QuantumFoundations/Complexity/ProxyCertificates.lean` | C3 : certificats relationnels et `ceilHalf` | 96 |
| `QuantumFoundations/Complexity/RecordInterferenceBound.lean` | C4 : borne d’interférence à deux orientations | 96 |
| `QuantumFoundations/Complexity/RecordDistinguishability.lean` | C5 : lecture par phase flip exact | 114 |
| `QuantumFoundations/Complexity/BranchGap.lean` | C6 : certificat de gap sans soustraction | 50 |
| `QuantumFoundations/Complexity/MinComplexity.lean` | C6 : minima `WithTop ℕ` et gap effectif | 180 |
| `QuantumFoundations/Complexity/CircuitConjugation.lean` | C7a : évolution réversible et circuits sandwich | 157 |
| `QuantumFoundations/Complexity/CircuitInverse.lean` | C7a : inverses locaux de portes et circuits | 207 |
| `QuantumFoundations/Complexity/ProxyTransport.lean` | C7b : transport exact des éléments de matrice et proxies | 180 |
| `QuantumFoundations/Complexity/Persistence.lean` | C7c : transport des certificats relationnels | 111 |
| `QuantumFoundations/Complexity/RecordPersistence.lean` | C7d : bornes de persistance par records | 104 |
| `QuantumFoundations/Complexity/PersistenceMinima.lean` | C7e : transport `WithTop ℕ` sans atteinte du minimum | 117 |
| `QuantumFoundations/Complexity/ApproxRecordDefs.lean` | C8a : record approximatif à erreur agrégée | 78 |
| `QuantumFoundations/Complexity/ApproxRecordBasic.lean` | C8a : paire enregistrée et pont exact | 64 |
| `QuantumFoundations/Complexity/ApproxRecordInterference.lean` | C8b : borne nette d’amplitude croisée hors support | 132 |
| `QuantumFoundations/Complexity/ApproxRecordInterferenceBound.lean` | C8c : borne d’interférence robuste et minima | 123 |
| `QuantumFoundations/Complexity/ApproxRecordDistinguishability.lean` | C8d : lecture de phase approximative | 203 |
| `QuantumFoundations/Complexity/ApproxBranchGap.lean` | C8e : gap proxy robuste et régression exacte | 152 |
| `QuantumFoundations/Complexity/ApproxRecordPersistence.lean` | C8f : persistance conditionnelle du gap robuste | 160 |
| `QuantumFoundations/Complexity/Models/Repetition/States.lean` | C9a : branches computationnelles zéro/un et état cohérent | 106 |
| `QuantumFoundations/Complexity/Models/Repetition/Records.lean` | C9b : résolutions mono-site et records exacts | 278 |
| `QuantumFoundations/Complexity/Models/Repetition/Readout.lean` | C9c : réflexion de lecture en une porte | 161 |
| `QuantumFoundations/Complexity/Models/Repetition/Distinguishability.lean` | C9d : complexité de distinguabilité exactement un | 82 |
| `QuantumFoundations/Complexity/Models/Repetition/Interference.lean` | C9e : circuit fini de flips de tous les bits | 205 |
| `QuantumFoundations/Complexity/Models/Repetition/Complexities.lean` | C9f : bornes linéaires et gap concret | 105 |
| `QuantumFoundations/Complexity/Models/Repetition/Persistence.lean` | C9g : budget concret de persistance par circuit | 57 |
| `QuantumFoundations/Complexity/Models/NoisyRepetition/Profiles.lean` | C10a : profils de bruit `keep`/`leak` normalisés | 76 |
| `QuantumFoundations/Complexity/Models/NoisyRepetition/States.lean` | C10b : quatre configurations et branches bruitées | 215 |
| `QuantumFoundations/Complexity/Models/NoisyRepetition/Records.lean` | C10c : erreurs de record exactes et paire approximative | 182 |
| `QuantumFoundations/Complexity/Models/NoisyRepetition/Readout.lean` | C10d : lecture exacte à site de record arbitraire | 59 |
| `QuantumFoundations/Complexity/Models/NoisyRepetition/Complexities.lean` | C10e : séparation de complexité robuste à `δ = 1/2` | 89 |
| `QuantumFoundations/Complexity/Models/NoisyRepetition/Interference.lean` | C10f : témoin fini d'interférence bruitée | 151 |
| `QuantumFoundations/Complexity/Models/NoisyRepetition/Persistence.lean` | C10g : gap robuste et persistance conditionnelle | 123 |
| `QuantumFoundations/Complexity/Models/NoisyRepetition/ConcreteNoise.lean` | C10h : profil rationnel concret `(99/101, 20/101)` | 95 |
| `QuantumFoundations/Complexity/Gates/ControlledBitFlip.lean` | C11a : portes de bit-flip contrôlé, 2-locales | 229 |
| `QuantumFoundations/Complexity/Gates/AmplitudeRotation.lean` | C11e : rotation unitaire de mélange d'amplitude sur `N` sites | 415 |
| `QuantumFoundations/Complexity/Models/MeasurementGeneration/IdealFanout.lean` | C11b : fanout unitaire d'étiquette en base de calcul | 219 |
| `QuantumFoundations/Complexity/Models/MeasurementGeneration/Amplitudes.lean` | C11c : profil d'amplitude source normalisé | 89 |
| `QuantumFoundations/Complexity/Models/MeasurementGeneration/BranchWeights.lean` | C11d/h : projecteurs source et préservation des poids de branche | 231 |
| `QuantumFoundations/Complexity/Models/MeasurementGeneration/ProfilePreparation.lean` | C11e : porte de préparation canonique par profil | 95 |
| `QuantumFoundations/Complexity/Models/MeasurementGeneration/NoisyGeneration.lean` | C11f/g : préparation corrélée des records et génération bruitée complète | 493 |
| `QuantumFoundations/Complexity/Models/MeasurementGeneration/GeneratedComplexity.lean` | C11i : connexion génération unitaire / persistance du gap | 70 |
| `QuantumFoundations/Complexity/Models/MeasurementGeneration/ConcreteGeneration.lean` | C11j : témoin concret de génération unitaire | 89 |
| `QuantumFoundations/Complexity/OperatorNorm/FiniteDimensional.lean` | C12a : vue en application linéaire continue, dimension finie | 115 |
| `QuantumFoundations/Complexity/OperatorNorm/Approximation.lean` | C12b : approximation générique en norme d'opérateur | 106 |
| `QuantumFoundations/Complexity/OperatorNorm/RecordReadout.lean` | C12c : pont erreur d'opérateur / erreur ponctuelle de lecture | 113 |
| `QuantumFoundations/Complexity/OperatorNorm/RecordGap.lean` | C12d/e : distinguabilité et gap proxy en norme d'opérateur | 207 |
| `QuantumFoundations/Complexity/OperatorNorm/NoisyRepetition.lean` | C12f : instanciation bruitée concrète, budget `1/20` | 165 |
| `QuantumFoundations/Complexity/OperatorNorm/GeneratedBranches.lean` | C12g : connexion à la génération unitaire C11 | 87 |
| `QuantumFoundations/Complexity/OperatorNorm/Composition.lean` | C12h : lois de composition (facultatif, pour C13) | 84 |
| `QuantumFoundations/Complexity/OperatorNorm/Nonvacuity.lean` | C12 : non-vacuité de l'API budget d'erreur | 83 |
| `QuantumFoundations/Complexity/SimulatedEvolution/NormPreserving.lean` | C13a : opérateurs préservant la norme | 92 |
| `QuantumFoundations/Complexity/SimulatedEvolution/MatrixElementStability.lean` | C13b : bornes de perturbation d'élément de matrice | 132 |
| `QuantumFoundations/Complexity/SimulatedEvolution/ThresholdTransport.lean` | C13c : transport de seuil sous erreur d'opérateur | 127 |
| `QuantumFoundations/Complexity/SimulatedEvolution/MarginCertificate.lean` | C13d : certificat de gap à marge de seuil | 88 |
| `QuantumFoundations/Complexity/SimulatedEvolution/CircuitPersistence.lean` | C13e : persistance de la marge sous circuit exact | 50 |
| `QuantumFoundations/Complexity/SimulatedEvolution/SimulationCertificate.lean` | C13f : persistance sous évolution simulée | 142 |
| `QuantumFoundations/Complexity/SimulatedEvolution/NoisyRepetition.lean` | C13g : instanciation à marge pour le modèle bruité | 92 |
| `QuantumFoundations/Complexity/SimulatedEvolution/GeneratedBranches.lean` | C13h : connexion aux branches engendrées C11 | 77 |
| `QuantumFoundations/Complexity/SimulatedEvolution/ConcreteModel.lean` | C13i : instance rationnelle concrète `δ=1/2, μ=1/10, ε=1/20` | 108 |
| `QuantumFoundations/Complexity/SimulatedEvolution/TimeEvolution.lean` | C13j : coût de simulation dépendant du temps | 85 |
| `QuantumFoundations/Complexity/SimulatedEvolution/HamiltonianEvolution.lean` | C13k : évolution certifiée par générateur auto-adjoint | 117 |
| `QuantumFoundations/Complexity/SimulatedEvolution/Nonvacuity.lean` | C13 : non-vacuité de l'API d'évolution simulée | 114 |
| `QuantumFoundations.lean`                    | Agrégateur d'imports racine                                                       | 69 |
| **Total recalculé**                          | **119 fichiers**                                                                  | **19598** |

Documentation : `AGENTS.md` (règles pour l'agent IA, à lire au démarrage),
`MILESTONES.md` (suivi détaillé jalon par jalon), `ARCHITECTURE_NOTES.md` (mémoire
consolidée de tous les écarts vs les plans initiaux).

## Jalons — Naimark

| Jalon | Contenu                                                    | État |
|-------|------------------------------------------------------------|------|
| N0    | Squelette (POVM, DilSpace, Nonvacuity)                     | ✅ |
| N1    | `sqrtOp` (racine carrée positive spectrale)                | ✅ |
| N2    | Briques de l'espace dilaté (`singleL`/`coordL`/`dilProj`)  | ✅ |
| N3    | Dilation (`dilV`, `naimark`, `naimark_born`)               | ✅ |
| N4    | Clôture (README, `#print axioms`, tag)                     | ✅ |
| N5    | *Optionnel* : version unitaire/ancilla (tag `v2.0-naimark`)| ✅ |

## Jalons — Wigner

| Jalon | Contenu                                                                    | État |
|-------|----------------------------------------------------------------------------|------|
| W0    | Squelette (Defs, Nonvacuity, 24 sorry)                                     | ✅ |
| W1    | Kit scalaire (`Scalar.lean` : rigidité, `scalar_dichotomy`)                | ✅ |
| W2    | Identité de Bessel (égalité), images orthonormées                          | ✅ |
| W3    | Construction `V` (colinéarité, eqs 11–12a)                                 | ✅ |
| W4    | Cœur : dichotomie de `chi`, additivité/homogénéité de `V`                  | ✅ |
| W5    | Assemblage (`U`, bijectivité, compatibilité, `wigner`)                     | ✅ |
| W6    | *Optionnel* : exclusivité (A) + unicité restreinte (B) (tag `v2.0-wigner`) | ✅ |

## Jalons — Uhlhorn

| Jalon | Contenu                                                                        | État |
|-------|--------------------------------------------------------------------------------|------|
| U0    | Reconnaissance + squelette (`Defs.lean`, 6 sorry)                              | ✅ |
| U1    | Corollaire (B) de Wigner en langage de projections (`wigner_projection_form`)  | ✅ |
| U2    | Lemme spectral élémentaire (`eq_projL_of_positive_le_one_trace_one_inner_one`) | ✅ |
| U3a   | Extension d'une fonction-cadre sur les droites en `ProjMeasure` complet        | ✅ |
| U3b   | « Gleason appliqué deux fois » (`traceProd_preserved_of_sendsONBToONB`)        | ✅ |
| U4    | Assemblage direct de U1 et U3b                                                 | ✅ |
| U5    | Réduction fini-dimensionnelle, théorème final (tag `v1.0-uhlhorn`)             | ✅ |

## Jalons — BornRule

| Jalon | Contenu                                                                        | État |
|-------|----------------------------------------------------------------------------------|------|
| B1    | Scaffolding : `Perspective`, axiomes, `lemma4_noncontextual`, `refinePerspective` | ✅ |
| B2    | Pont vers Gleason : `g`, `IsFrameFunctionOnLines`, `exists_rho`                | ✅ |
| B3    | Pinning : `eq_projL_of_vanishes_on_orthogonal` (identification de `ρ` via U2)  | ✅ |
| B4    | Assemblage final, théorème `grainCoherenceTheorem`                             | ✅ |
| Nonvacuity | `E₀ v` (règle de Born) habite simultanément Grain+Norm+Pos+Null            | ✅ |

## Jalons — BornRule/EffectPerspectives (extension qubit/Busch)

Voir aussi `QuantumFoundations/BornRule/EffectPerspectives/README.md` pour le
détail complet (portée, dérivations, non-revendications interprétatives).

| Jalon | Contenu | État |
|-------|---------|------|
| QB1 | `Effect` (sous-type de `Gleason.IsEffect`), `zeroEffect`/`oneEffect`/`complementEffect`/`projectionEffect` | ✅ |
| QB2 | `EffectPerspective` (POVM finie étiquetée), `binaryPerspective`/`splitPerspective`/`duplicateZeroPerspective` | ✅ |
| QB3 | `Refines` (raffinement par `parent` + reconstruction par fibre) ; `Refines.trans` différé (documenté, non bloquant) | ✅ |
| QB4 | `EstimationRule` (poids/positivité/normalisation/`grain`), hypothèse strictement plus large que `AxGrain` projectif | ✅ |
| QB5 | Indépendance contextuelle, poids nul/unité et additivité binaire **dérivés** de `grain` seul (jamais des axiomes) | ✅ |
| QB6 | Construction de `Gleason.EffectMeasure` ; application directe de `Gleason.busch`/`Gleason.busch_born_rule` | ✅ |
| QB7 | `ContextualNullSupport` (état-relatif) ; pinning de repli `density_bornValue_eq_pure_of_null` | ✅ |
| QB8 | `projectionEffect_weight_eq_born` : poids de Born pour les effets de projection, en dimension quelconque | ✅ |
| QB9 | Corollaire explicite en dimension deux (qubit), sans passer par `Gleason.gleason` | ✅ |
| QB10 | Non-vacuité : `pureStateEstimationRule` (preuve directe, sans Busch), témoins qubit exacts | ✅ |
| QB11 | Pont vers Naimark : `EffectPerspective.toPOVM`, réalisation projective dilatée (`naimark`/`naimark_born`/`naimark_projective_form`), simple couche d'intégration | ✅ |

## Jalons — HistoriesKent

| Jalon | Contenu                                                                        | État |
|-------|---------------------------------------------------------------------------------|------|
| K0    | Squelette (`History`, `chainOp`, `decFunctional`, `IsConsistent`, `Nonvacuity`)  | ✅ |
| K1    | Lemmes généraux : `decFunctional_last_stage_orthogonal`, `histProb_additivity_two_stage` | ✅ |
| K2    | Témoin explicite de Kent en `H 3` (`Witness.lean`), `S_consistent`               | ✅ |
| K3    | `inference`, théorème final `contrary_inferences` (tag `v1.0-histories`)         | ✅ |

## Jalons — Complexity

| Jalon | Contenu | État |
|---|---|---|
| C0 | Circuits finis de portes unitaires supportées sur au plus deux sites | ✅ |
| C1 | Commutation hors support et annulation de l’amplitude croisée | ✅ |
| C2 | Comptage indépendant et borne exacte `R ≤ 2 * C.length` | ✅ |
| C3 | Proxies exacts, branches normalisées et certificats relationnels | ✅ |
| C4 | Borne d’interférence `ceilHalf R` issue des records redondants | ✅ |
| C5 | Borne de distinguabilité issue d’un phase flip de record explicite | ✅ |
| C6 | Gap sans soustraction et minima dans `WithTop ℕ` | ✅ |
| C7 | Transport exact et persistance conditionnelle sous circuit réversible fini | ✅ |
| C8 | Records approximatifs, bornes quantitatives et persistance conditionnelle | ✅ |
| C9 | Modèle explicite de répétition, circuits concrets et gap linéaire | ✅ |
| C10 | Modèle explicite de répétition **bruitée** (`leak ≠ 0`), séparation robuste | ✅ |
| C11 | Génération **unitaire** des branches source-record par circuit local explicite | ✅ |
| C12 | Pont fini-dimensionnel en **norme d'opérateur** vers les hypothèses de lecture ponctuelles C8–C11 | ✅ |
| C13 | Persistance robuste du gap sous **évolution simulée** norm-preservante, avec marge de seuil | ✅ |
| C14 | Pont **records redondants → poids de Born** : décomposition en branches de Riedel + Théorème de Cohérence de Grain | ✅ |
| C15 | Unicité `W = c ‖P_R Ψ‖²` sur les situations de record admissibles sous stabilité, équivalence interne et saturation binaire | ✅ |
| C17 | Première stabilité quantitative des poids C15 sous perturbation des composantes projetées, avec bornes ponctuelle, `L¹` et uniforme | ✅ |
| C17b | Ponts de stabilité vers les secteurs fixes, la norme d’opérateur C12, la simulation C13 et les poids de branches C14 explicitement appariées | ✅ |

## Théorèmes principaux — table de référence

| Théorème | Énoncé informel | Référence | Fichier (lignes) | Statut | Tag |
|---|---|---|---:|---|---|
| `naimark` | Toute POVM finie se dilate en une mesure projective sous une isométrie | Watrous Thm 2.42 | `Naimark/Main.lean` (157) | 0 sorry, 0 axiome | `v2.0-naimark` |
| `naimark_born` | La formule de Born est préservée par cette dilation | Watrous Thm 2.42 | `Naimark/Main.lean` (157) | 0 sorry, 0 axiome | `v2.0-naimark` |
| `exists_unitary_extension` / `naimark_projective_form` | L'isométrie de dilatation s'étend en un unitaire global (forme ancilla) | Paris §3.2 Thm 4 / Watrous Cor. 2.43 | `Naimark/Unitary.lean` (210) | 0 sorry, 0 axiome | `v2.0-naimark` |
| `wigner` | Toute transformation préservant `\|⟨φ\|ψ⟩\|²` est induite par un unitaire ou un antiunitaire, sans hypothèse de bijectivité | Bargmann 1964 §1–§5 | `Wigner/Main.lean` (399) | 0 sorry, 0 axiome | `v1.0-wigner` |
| `exclusivity` | Un même `T` ne peut être compatible à la fois avec une équivalence unitaire et une antiunitaire (`n ≥ 2`) | Bargmann 1964 §1.5 | `Wigner/Uniqueness.lean` (439) | 0 sorry, 0 axiome | `v2.0-wigner` |
| `U_alt_eq_smul` | `U` est unique à phase globale près relativement au choix du représentant de `eImg` (version restreinte) | Bargmann 1964 §6 (restreint) | `Wigner/Uniqueness.lean` (439) | 0 sorry, 0 axiome | `v2.0-wigner` |
| `uhlhorn_finite_dim` | En dimension `n ≥ 3`, préserver l'orthogonalité dans un seul sens (ni injectivité ni surjectivité) suffit à être une symétrie de Wigner | Šemrl 2021, arXiv:2106.06182, Cor. 1.2 | `Uhlhorn/Assembly.lean` (111) | 0 sorry, 0 axiome | `v1.0-uhlhorn` |
| `grainCoherenceTheorem` | Sous (Grain)+(Norm)+(Pos)+(Null), la valeur d'une règle d'estimation sur une cellule est la règle de Born (`∑ᵢ‖⟨v,fᵢ⟩‖²`) | Gleason 1957 (théorème sous-jacent) | `BornRule/Assembly.lean` (215) | 0 sorry, 0 axiome | `v2.0-bornrule` |
| `grainCoherenceTheorem_projector` | Version en notation projecteur du théorème précédent (`Est D c = ‖projL c v‖²`), sans contenu mathématique indépendant supplémentaire | Corollaire de `grainCoherenceTheorem` | `BornRule/Assembly.lean` | 0 sorry, 0 axiome | — |
| `EffectPerspectives.projectionEffect_weight_eq_born` | Sous non-vacuité d'effets et support nul état-relatif, le poids d'un effet de projection égale le poids de Born `‖A.starProjection ψ‖²`, en dimension quelconque `n ≥ 1` | Busch 2003, PRL 91, 120403 | `BornRule/EffectPerspectives/Main.lean` | 0 sorry, 0 axiome | — |
| `EffectPerspectives.qubit_projectionEffect_weight_eq_born` | Corollaire explicite en dimension deux (qubit) du théorème précédent, sans invoquer `Gleason.gleason` | Busch 2003 (spécialisé `n = 2`) | `BornRule/EffectPerspectives/Qubit.lean` | 0 sorry, 0 axiome | — |
| `contrary_inferences` | Deux ensembles cohérents d'histoires partageant préparation et post-sélection peuvent impliquer avec certitude deux propositions orthogonales | Kent 1997, PRL 78, 2874, arXiv:gr-qc/9604012 | `HistoriesKent/ContraryInferences.lean` (162) | 0 sorry, 0 axiome | `v1.0-histories` |
| `regions_card_le_two_mul_circuit_length_of_cross_amplitude_ne_zero` | `R` records exacts disjoints et une amplitude croisée non nulle imposent `R ≤ 2 * C.length` | Comptage fini + records de Riedel | `Complexity/Main.lean` (63) | 0 sorry, 0 axiome | — |
| `redundant_records_give_interference_lower_bound` | Tout circuit satisfaisant le proxy exact a longueur au moins `ceilHalf R` | Proxy exact + C2 dans les deux orientations | `Complexity/RecordInterferenceBound.lean` (96) | 0 sorry, 0 axiome | — |
| `record_phase_flip_gives_distinguishability_upper_bound` | Un circuit implémentant `2 P_j - I` distingue les branches normalisées à seuil `δ ≤ 1` | Lecture exacte d’un record | `Complexity/RecordDistinguishability.lean` (114) | 0 sorry, 0 axiome | — |
| `redundant_records_give_proxy_gap_certificate` | `D.length + g ≤ ceilHalf R` certifie un gap proxy d’au moins `g` | Composition des certificats C4/C5 | `Complexity/BranchGap.lean` (50) | 0 sorry, 0 axiome | — |
| `redundant_records_complexity_gap` | Le même gap vaut pour les minima exacts dans `WithTop ℕ` | Infimum des longueurs de circuits | `Complexity/MinComplexity.lean` (180) | 0 sorry, 0 axiome | — |
| `redundant_records_gap_persists_under_reversible_evolution` | Le gap de records persiste sous `D.length + 2 * overhead + g ≤ ceilHalf R` | Transport exact par paire de circuits inverses | `Complexity/RecordPersistence.lean` (104) | 0 sorry, 0 axiome | — |
| `redundant_records_gap_persists_under_circuit_evolution` | Pour l'inverse canonique, le budget devient `D.length + 4 * E.length + g ≤ ceilHalf R` | Inverse local canonique + théorème précédent | `Complexity/RecordPersistence.lean` (104) | 0 sorry, 0 axiome | — |
| `norm_cross_amplitude_le_of_untouched_approx_record` | Une région approximativement enregistrée et non touchée borne l’amplitude croisée par `η` | Décomposition projecteur/défaut + Cauchy–Schwarz | `Complexity/ApproxRecordInterference.lean` (132) | 0 sorry, 0 axiome | — |
| `approximate_records_give_interference_lower_bound` | `ηi + ηj < 2δ` impose une longueur au moins `ceilHalf R` | Borne robuste + comptage C2 | `Complexity/ApproxRecordInterferenceBound.lean` (123) | 0 sorry, 0 axiome | — |
| `approx_record_phase_flip_gives_upper_bound` | `2δ + 2ηj + ξ ≤ 2` fournit le témoin de distinguabilité | Lecture de phase approximative explicite | `Complexity/ApproxRecordDistinguishability.lean` (203) | 0 sorry, 0 axiome | — |
| `approximate_records_give_proxy_gap_certificate` | Les deux seuils robustes et `D.length + g ≤ ceilHalf R` certifient le gap | Composition C8c/C8d | `Complexity/ApproxBranchGap.lean` (152) | 0 sorry, 0 axiome | — |
| `approximate_records_gap_persists_under_circuit_evolution` | Le gap robuste persiste sous `D.length + 4 * E.length + g ≤ ceilHalf R` | Transport exact C7 du certificat C8 | `Complexity/ApproxRecordPersistence.lean` (160) | 0 sorry, 0 axiome | — |
| `repetition_distinguishabilityComplexity` | Le modèle explicite a `C_D = 1` | Réflexion mono-site + exclusion du circuit vide | `Models/Repetition/Distinguishability.lean` (82) | 0 sorry, 0 axiome | — |
| `repetition_interferenceComplexity_bounds` | `ceilHalf R ≤ C_I ≤ R` et donc `C_I ≠ ⊤` | Records singletons + circuit de `R` flips | `Models/Repetition/Complexities.lean` (105) | 0 sorry, 0 axiome | — |
| `repetition_has_proxy_gap` | `1 + g ≤ ceilHalf R` certifie le gap explicite | Instanciation directe de C4–C6 | `Models/Repetition/Complexities.lean` (105) | 0 sorry, 0 axiome | — |
| `repetition_gap_persists_under_circuit` | `1 + 4 * E.length + g ≤ ceilHalf R` conserve le gap | Instanciation directe de C7 | `Models/Repetition/Persistence.lean` (57) | 0 sorry, 0 axiome | — |
| `noisy_repetition_approxRecordedPairOn` | Les records bruités habitent `ApproxRecordedPairOn` avec erreur agrégée exacte `2 * ‖leak‖` | Actions exactes des projecteurs sur les quatre configurations | `Models/NoisyRepetition/Records.lean` (182) | 0 sorry, 0 axiome | — |
| `noisy_repetition_distinguishabilityComplexity` | Sous bruit robuste (`4‖leak‖ < 1`), `C_D = 1` à `δ = 1/2` | Lecture exacte à un site + seuil C8d | `Models/NoisyRepetition/Complexities.lean` (89) | 0 sorry, 0 axiome | — |
| `noisy_repetition_interference_bounds` | Sous bruit robuste, `ceilHalf R ≤ C_I ≤ R + 1` à `δ = 1/2` | Records approximatifs C8c + témoin flip-tous-les-bits | `Models/NoisyRepetition/Interference.lean` (151) | 0 sorry, 0 axiome | — |
| `noisy_repetition_has_proxy_gap` | `1 + g ≤ ceilHalf R` certifie le gap robuste | Instanciation directe de C8e | `Models/NoisyRepetition/Persistence.lean` (123) | 0 sorry, 0 axiome | — |
| `noisy_repetition_gap_persists_under_circuit` | `1 + 4 * E.length + g ≤ ceilHalf R` conserve le gap robuste | Instanciation directe de C8f | `Models/NoisyRepetition/Persistence.lean` (123) | 0 sorry, 0 axiome | — |
| `rationalNoiseProfile_isRobust` | Le profil rationnel `(99/101, 20/101)` est robuste (`80/101 < 1`) | Triplet pythagoricien `99² + 20² = 101²` | `Models/NoisyRepetition/ConcreteNoise.lean` (95) | 0 sorry, 0 axiome | — |

Statut « 0 axiome » signifie : dépend uniquement de
`[propext, Classical.choice, Quot.sound]` (vérifié par `#print axioms` sur
chacun des théorèmes principaux, voir section précédente et les sorties
`#print axioms` conservées dans les fichiers d’assemblage).

## Dépendances

Ce dépôt épingle deux dépendances Lake sur des révisions fixes et résolvables
(`lakefile.toml`/`lake-manifest.json`), jamais sur une branche flottante :

- [`gleason-theorem-lean`](https://github.com/Bobart0/gleason-theorem-lean),
  `rev = "v1.0-gleason"` (résolu en `876aa7390b5d831cd81415d55493a1c0c3bae31e`,
  révision fixe inchangée depuis Naimark). **Usage étendu depuis Uhlhorn, repris
  par BornRule** (contrairement à Naimark, qui ne réutilise que
  `Gleason.IsPositiveOp`, un simple `Prop`) : Uhlhorn ET BornRule invoquent
  `Gleason.gleason` lui-même — le théorème de Gleason complet, pas seulement
  une définition — ainsi qu'une partie de sa machinerie interne
  (`Gleason.positive_inner_self_eq_zero`, `Gleason.cframe_sum_invariant`,
  `Gleason.ProjMeasure`/`bornValue`/`projL`,
  `Gleason.exists_orthonormalBasis_extension_complex`,
  `Submodule.starProjection_isSymmetric`/`re_inner_starProjection_nonneg`).
  C'est délibéré et attendu : Uhlhorn (Corollaire 1.2 de Šemrl) et BornRule
  (`grainCoherenceTheorem`) **composent** Gleason (et, pour Uhlhorn, Wigner)
  par construction — ce ne sont pas des résultats autonomes, voir les sections
  dédiées plus haut. Malgré cette dépendance substantiellement plus large,
  **aucune fuite d'axiome par transitivité** : confirmé directement par
  `#print axioms` sur chaque théorème du présent dépôt, y compris
  `uhlhorn_finite_dim` (dépend à la fois de `Gleason.gleason` externe et de
  `QuantumFoundations.Wigner.wigner` interne) et `grainCoherenceTheorem`
  (dépend à la fois de `Gleason.gleason` externe et de l'infrastructure
  Uhlhorn interne U2/U3a) — dans les deux cas sans faire apparaître un axiome
  supplémentaire. BornRule réutilise en outre directement, depuis Uhlhorn,
  `eq_projL_of_positive_le_one_trace_one_inner_one` (U2),
  `exists_projMeasure_of_frameFunctionOnLines` (U3a) et
  `isEffect_of_isDensityOperator` (relocalisé de U3b vers `Uhlhorn/Defs.lean`
  lors de B3) — aucun contenu Gleason/Uhlhorn n'est reprouvé. **HistoriesKent**
  n'invoque `Gleason.gleason` ni `Gleason.projL`/`Submodule.starProjection`
  directement, mais en hérite par transitivité via `BornRule.Perspective`
  (chaîne à trois niveaux HistoriesKent → BornRule → Uhlhorn/Gleason externe) —
  même absence de fuite d'axiome, confirmée sur `contrary_inferences` et les
  35 autres déclarations publiques du bloc. **`BornRule/EffectPerspectives`**
  (extension qubit/Busch) réutilise, dans la même révision épinglée déjà en
  place, `Gleason.Busch.Effects`/`Gleason.Busch.Main` : `Gleason.IsEffect`,
  `Gleason.EffectMeasure`, et surtout `Gleason.busch`/`Gleason.busch_born_rule`
  (le théorème de Busch complet, appliqué directement en un seul point,
  `EffectMeasure.lean`, jamais reprouvé). Contrairement à `Gleason.gleason`
  (dimension `≥ 3`), Busch s'applique dès la dimension `1`, ce qui permet
  d'atteindre le qubit (`n = 2`) sans emprunter la voie projective. Aucune
  déclaration de dépendance n'a été ajoutée ou modifiée : toutes ces
  déclarations existaient déjà dans la révision épinglée.
- `mathlib`, `rev = "8bba4200986270d3b30be2bb2f8840af47a7854f"`.

`./setup.sh` (`lake exe cache get` puis `lake build`) reproduit l'état exact
du dépôt sur un clone frais, sans intervention manuelle — testé lors de
chaque passe de clôture (`lake clean` + `lake exe cache get` + `lake build`),
la plus récente incluant `HistoriesKent` (2026-07-16).

## Règles

Aucun `axiom`, aucun `native_decide` (CI bloquante, `scripts/guard.sh`). Toute nouvelle
structure d'hypothèses reçoit un habitant concret dans `Nonvacuity.lean`, dans le même
commit. Un `sorry` honnête plutôt qu'un énoncé affaibli en silence — voir `AGENTS.md`
pour l'ensemble des règles.

## Licence

[Apache License 2.0](LICENSE).

---

## English translation

# quantum-foundations-lean — Lean 4 formalizations: Naimark, Wigner, Uhlhorn, BornRule, HistoriesKent, BranchesRiedel, and Complexity

Status: Naimark v2 COMPLETE (v2.0-naimark, 2026-07-11), Wigner COMPLETE
with optional uniqueness/exclusivity (v2.0-wigner, 2026-07-13), Uhlhorn
COMPLETE (v1.0-uhlhorn, 2026-07-14), BornRule COMPLETE with Nonvacuity
(v2.0-bornrule, 2026-07-15), AND HistoriesKent COMPLETE
(v1.0-histories, 2026-07-16), plus the BranchesRiedel and Complexity C0–C13
blocks, and now the **C14 records-to-Born-weight bridge**. Seven mechanized
blocks,
without axioms in the sense of the project rules, apart from the three
standard Lean kernel axioms described below, in finite dimension over ℂ.

By the numbers (recomputed on 2026-07-23, project files excluding scratch):
119 `.lean` files, 19,598 lines, 663 public declarations (`theorem`), 0
`sorry`, and 0 project-specific axioms. The Complexity block contains 70
files and 9,490 lines, of which 12 files and 1,224 lines are the C13
simulated-evolution persistence milestone. The BranchesRiedel block
contains 17 files and 3,250 lines, of which 11 files and 1,438 lines are
the new `BornBridge/` subdirectory (the C14 milestone, bridging Riedel's
branch decomposition to the Born weight). The
main theorems of the Complexity and BornBridge blocks were checked with
`#print axioms` and depend on exactly `[propext, Classical.choice,
Quot.sound]`, the standard Lean/Mathlib trio.

**Current module names:** the Riedel block is
`QuantumFoundations.BranchesRiedel`, and Kent's contrary-inferences block is
`QuantumFoundations.HistoriesKent`. The former
`QuantumFoundations.Branches` and `QuantumFoundations.Histories` module paths
and namespaces are no longer exposed.

The Naimark dilation theorem for finite POVMs
(Watrous, The Theory of Quantum Information, Theorem 2.42): every POVM
E : Fin m → (H n →ₗ[ℂ] H n) is realized as a projection-valued measure
(dilProj) under an isometry dilV, with preservation of the Born formula.

Wigner's theorem (Bargmann 1964, Note on Wigner's Theorem on Symmetry
Operations): every transformation on pure states preserving transition
probabilities |⟨φ|ψ⟩|² is induced by a unitary or antiunitary operator—
formulation (A), without a bijectivity hypothesis on the initial
transformation (strictly stronger than Simon–Mukunda–Chaturvedi–Srinivasan
2008, Eq. 2.8, which assumes it). It is supplemented in optional W6 by
unitary/antiunitary exclusivity and uniqueness up to a global phase
in a restricted form, following Bargmann §1.5 and §6.

Šemrl's Corollary 1.2 (Šemrl 2021, Wigner symmetries and Gleason's
theorem, arXiv:2106.06182): in finite dimension n ≥ 3, every map on
rank-one projections that preserves orthogonality in one direction only
(with neither injectivity nor surjectivity assumed) is automatically a Wigner
symmetry. Unlike Naimark and Wigner, this is NOT a self-contained result: it
composes Gleason's theorem (gleason-theorem-lean, pinned external
dependency) with Wigner's theorem (the internal block above). See the
dedicated section below for details of this dual dependency and its axiom
audit.

The Grain Coherence Theorem (with Gleason 1957, Measures on the closed
subspaces of a Hilbert space, as the underlying theorem): for a
“perspective,” an orthogonal partition of H n into cells, and an estimation
rule satisfying four purely combinatorial axioms (Grain, Norm, Pos, Null),
the rule's value on every cell is EXACTLY the Born rule
(∑ᵢ ‖⟨v,fᵢ⟩‖² over an orthonormal basis of the cell), without ever assuming
a priori that the rule has trace form. Like Uhlhorn, this result composes
an internal block (Uhlhorn infrastructure U2 and U3a) with an external
dependency (Gleason.gleason, imported as an actual theorem rather than as
an axiom). See the dedicated section below.

The contrary-inferences theorem (Kent 1997, Quasiclassical Dynamics in a
Closed Quantum System, PRL 78, 2874, arXiv:gr-qc/9604012), in the
finite-dimensional consistent-histories framework: two consistent sets of
histories can share the same preparation and postselection while each
implying with CERTAINTY a different proposition, the two propositions being
mutually orthogonal. A temporal stage of a history set directly reuses
BornRule.Perspective, with no redefinition. As Uhlhorn and BornRule already
do for other components, HistoriesKent composes the repository's internal
infrastructure (BornRule → Uhlhorn/Gleason) rather than starting over.
The generic profusion theorem of Dowker–Kent (1996), which would show that the
witness is not an isolated contrary-inference example, is explicitly outside
the scope of this block.

This repository relies on
gleason-theorem-lean
(tag v1.0-gleason). Naimark reuses only IsPositiveOp
(Gleason.Busch.Effects); Uhlhorn and BornRule, by contrast, invoke
Gleason.gleason itself as well as part of its internal machinery. HistoriesKent
does not invoke Gleason.gleason directly but inherits it transitively
through BornRule.Perspective/projL. See “Dependencies” below for details
and verification that no additional axioms leak through the dependency
chain.

## Statements

lean
structure POVM (n m : ℕ) where
 E : Fin m → (H n →ₗ[ℂ] H n)
 pos : ∀ i, IsPositiveOp (E i)
 sum_eq_one : ∑ i, E i = 1

theorem naimark (P : POVM n m) :
 ∃ V : H n →ₗ[ℂ] DilSpace n m, LinearMap.adjoint V ∘ₗ V = LinearMap.id ∧
 ∀ i, LinearMap.adjoint V ∘ₗ dilProj n m i ∘ₗ V = P.E i

theorem naimark_born (P : POVM n m) (i : Fin m) (x : H n) :
 ⟪x, P.E i x⟫_ℂ = ⟪dilV P x, dilProj n m i (dilV P x)⟫_ℂ


DilSpace n m := EuclideanSpace ℂ (Fin m × Fin n), and dilProj i is the
orthogonal projection onto the ith block.

N5 (optional, closed): dilV extends to a genuine unitary on
DilSpace n m, not merely an isometry, for every fixed ancilla index i₀
(Watrous Cor. 2.43 / Paris §3.2 Thm 4):

lean
theorem exists_unitary_extension (P : POVM n m) (i₀ : Fin m) :
 ∃ U : DilSpace n m ≃ₗᵢ[ℂ] DilSpace n m, U.toLinearMap ∘ₗ singleL n m i₀ = dilV P

theorem naimark_projective_form (P : POVM n m) (i₀ : Fin m) :
 ∃ U : DilSpace n m ≃ₗᵢ[ℂ] DilSpace n m, ∀ (i : Fin m) (x : H n),
 ⟪x, P.E i x⟫_ℂ = ⟪U (singleL n m i₀ x), dilProj n m i (U (singleL n m i₀ x))⟫_ℂ


## Documented deviation from Watrous

Watrous dilates in a tensor product X ⊗ ℂ^Σ. We dilate in the
Hilbert direct sum K := ⊕_{i<m} H n, which is canonically isomorphic
(the Mathlib API for PiLp/EuclideanSpace was more mature at the time than
the Hilbert tensor-product API). Correspondence:
1_X ⊗ E_{a,a} becomes dilProj a; √μ(a) ⊗ e_a becomes
singleL a ∘ₗ sqrtOp (E a). The mathematical content (isometry + Born formula) is identical; only the concrete realization of the dilation
space differs.

DilSpace n m := EuclideanSpace ℂ (Fin m × Fin n) was selected in step 0,
milestone N0, over PiLp 2 (fun _ : Fin m => H n) at equal proof-engineering
cost, because of its single flat index. See MILESTONES.md for details of the
two tested routes.

## Wigner's theorem

lean
def IsWignerMap (T : H n → H n) : Prop :=
 ∀ x y : H n, ‖x‖ = 1 → ‖y‖ = 1 → ‖⟪T x, T y⟫_ℂ‖ = ‖⟪x, y⟫_ℂ‖

theorem wigner (n : ℕ) (T : H n → H n) (hT : IsWignerMap T) :
 (∃ U' : H n ≃ₗᵢ[ℂ] H n, ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U' x)
 ∨ (∃ U' : H n ≃ₛₗᵢ[starRingEnd ℂ] H n, ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U' x)


There is no bijectivity hypothesis on T: in finite dimension, the
constructed isometry U' is automatically bijective (U_bijective), and
injectivity at the ray level follows from hT alone. Mathematical blueprint:
Bargmann 1964, §1–§5, followed almost verbatim; Simon–Mukunda–Chaturvedi–
Srinivasan 2008 is used only as a cross-check and rejected as the primary
blueprint because of its trigonometric/Real.Angle approach.

Construction (Bargmann §3–§5): first V—definitional collinearity on
𝒫 := e⊥, W3—then χ—the id/conj dichotomy established independently
on EACH direction and then globalized without an orthogonal-frame
hypothesis, W4—and finally
U := χ⟨e,·⟩•e' + V(· − ⟨e,·⟩•e), extending V/χ to the whole space,
W5. No coordinates, no extension of an orthonormal basis, and no Submodule
for 𝒫, which is represented by the simple Prop InPerp.

Documented deviations from the initial plan (see MILESTONES.md, sections
W3–W5, for full details):
- W3 (V_colinear): the initial skeleton asserted ‖δ‖ = 1 for the
 collinearity coefficient—FALSE in general, as refuted by T = id; corrected
 to ‖δ‖ = ‖z‖.
- W4 (chi_eq_chidir): Bargmann's argument in §4.3–§4.5
 (w = f₁+f₂, orthogonal case only) is insufficient when n ≥ 3 and the
 second vector is neither collinear nor orthogonal to refVec. This was
 resolved by reduction to a single comparison point (i, where id and
 conj differ) rather than by proving the full functional identity.
- W5 (U_bijective): there is no direct Mathlib lemma for semilinear
 bijectivity in the antiunitary branch. The result was obtained by
 restriction to the real scalars (starRingEnd ℂ is ℝ-linear), where
 LinearMap.injective_iff_surjective applies unchanged.

See ARCHITECTURE_NOTES.md for the consolidated list of all documented
deviations from N0–N5 and W0–W6.

## W6 (optional) — Exclusivity and uniqueness (Bargmann §1.5, restricted §6)

lean
def Delta (a b c : H n) : ℂ := ⟪a, b⟫_ℂ * ⟪b, c⟫_ℂ * ⟪c, a⟫_ℂ

theorem exclusivity (hT : IsWignerMap T) (hn : 2 ≤ n) :
 ¬ ((∃ U : H n ≃ₗᵢ[ℂ] H n, ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U x)
 ∧ (∃ U' : H n ≃ₛₗᵢ[starRingEnd ℂ] H n, ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U' x))

theorem U_alt_eq_smul (T : H n → H n) (lam : ℂ) (hlam : ‖lam‖ = 1) (a : H n) :
 Up T (lam • eImg T) a = lam • U T a


**(A) Exclusivity** (Bargmann §1.5): the same T can never be compatible with
both a unitary and an antiunitary equivalence when n ≥ 2. The proof uses an
explicit witness: the triple
e, e₂ := (e−refVec)/√2,
e₃ := (e+refVec(1−i))/√3 gives
Delta(e,e₂,e₃) = i/6 ∉ ℝ
(bargmann_delta_witness, confirmed exactly by Lean). But Delta is
invariant in the unitary branch and conjugated in the antiunitary branch
(delta_transform_lin/delta_transform_conj), which would force
i/6 = -i/6.

**(B) Uniqueness up to a global phase—RESTRICTED version**: reconstructing
U after replacing, in the formulas of Defs.lean, the unit representative
eImg T := T(e n) with another unit representative λ • eImg T of the same
class (‖λ‖ = 1) produces a new U exactly equal to λ • U (U_alt_eq_smul). This is
strictly weaker than the full Bargmann §6 Theorem 2, which would cover a
completely arbitrary U', not merely freedom in the representative of
eImg, but it is sufficient for the repository's actual use case.
Defs.lean is unchanged: the parameterized reconstruction
(Vp, chidirp, chip, Up) is local to Uniqueness.lean and is connected
to V/chi/U by bridge lemmas proved by rfl.

## Šemrl's Corollary 1.2 (Uhlhorn)

lean
def PreservesOrthogonality (φ : Proj1 n → Proj1 n) : Prop :=
 ∀ P Q : Proj1 n, (P : Submodule ℂ (H n)) ⟂ (Q : Submodule ℂ (H n)) →
 (φ P : Submodule ℂ (H n)) ⟂ (φ Q : Submodule ℂ (H n))

theorem uhlhorn_finite_dim (hn : 3 ≤ n) (φ : Proj1 n → Proj1 n)
 (hφ : PreservesOrthogonality φ) : IsWignerSymmetryProj φ


Proj1 n := {A : Submodule ℂ (H n) // Module.finrank ℂ A = 1} represents a
rank-one projection, with no dedicated rankOne wrapper, in accordance with
gleason-theorem-lean. Every map on rank-one projections that preserves
orthogonality in one direction only
(PQ = 0 ⟹ φ(P)φ(Q) = 0, with neither injectivity nor surjectivity assumed)
is, in finite dimension n ≥ 3, a Wigner symmetry—Šemrl 2021,
Wigner symmetries and Gleason's theorem (arXiv:2106.06182),
Corollary 1.2.

This result COMPOSES two theorems rather than introducing self-contained
mathematical content: the core proof applies Gleason.gleason, an external
dependency, TWICE—first to construct, from a test density D and the
preservation hypothesis, a second density E; and a second time implicitly
by specializing D := projL(φQ) to identify E = projL Q through the
elementary spectral lemma U2. It then concludes with wigner, the internal
block above, through Wigner's Corollary (B) in projection language (U1), which
had never been constructed before this milestone. The full decomposition
has six submilestones: U1, Wigner's corollary in projection language; U2,
the spectral lemma; U3a, extension of a frame function on lines to a full
ProjMeasure, absent from gleason-theorem-lean and therefore derived in
this repository; U3b, “Gleason applied twice”; U4, assembly; and U5, the
finite-dimensional cardinality-counting reduction. Full details are in
MILESTONES.md.

## Grain Coherence Theorem (BornRule)

lean
structure Perspective (n : ℕ) where
 cells : Finset (Submodule ℂ (H n))
 nz : ∀ c ∈ cells, c ≠ ⊥
 ortho : ∀ c ∈ cells, ∀ c' ∈ cells, c ≠ c' → c ≤ c'ᗮ
 span : sSup (cells : Set (Submodule ℂ (H n))) = ⊤

theorem grainCoherenceTheorem (hn3 : 3 ≤ n) (hA : AxGrain Est) (hN : AxNorm Est)
 (hPos : AxPos Est) {v : H n} (hv : ‖v‖ = 1) (hNul : AxNul Est v)
 (D : Perspective n) {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
 Est D c = ∑ i : Fin (Module.finrank ℂ c),
 ‖⟪v, ((stdOrthonormalBasis ℂ c i : c) : H n)⟫_ℂ‖ ^ 2

theorem grainCoherenceTheorem_projector (hn3 : 3 ≤ n) (hA : AxGrain Est)
 (hN : AxNorm Est) (hPos : AxPos Est) {v : H n} (hv : ‖v‖ = 1)
 (hNul : AxNul Est v) (D : Perspective n) {c : Submodule ℂ (H n)}
 (hc : c ∈ D.cells) :
 Est D c = ‖projL c v‖ ^ 2


For a perspective D, an orthogonal partition of H n into nonzero cells,
and a cell c of D, every estimation rule Est satisfying (Grain), (Norm),
(Pos), and, for a fixed unit vector v, (Null), satisfies
Est D c = ∑ᵢ ‖⟨v,fᵢ⟩‖² over every orthonormal basis (fᵢ) of c: the Born
rule in full generality, derived from the four coherence axioms alone, without
assuming a priori that Est has trace form. This covers the descriptive
route through Gleason's theorem. A second independent derivation route, using
a dynamic-stability axiom rather than grain coherence, the
existence/consistency of the four axioms themselves, and intersubjective
convergence between observers as a corollary are possible future extensions
and are not attempted here.

This result COMPOSES Gleason with the Uhlhorn infrastructure rather than
introducing self-contained mathematical content: B2 constructs a frame
function on lines directly from the estimation rule through
Perspective.binary, then invokes U3a + Gleason.gleason, an actual theorem
rather than an axiom, to obtain a density ρ; B3 reuses U2 to show that a
density operator vanishing on the orthogonal complement of a unit vector v
is exactly projL (ℂ∙v); and B4 connects (Null) to this vanishing hypothesis
and assembles the result through
refinePerspective/refine_filter_eq_cellLines, already proved in B1. The
full decomposition has four milestones: B1, scaffolding—perspectives, axioms,
non-contextuality; B2, bridge to Gleason; B3, pinning; and B4, final assembly.
Full details and favorable deviations are in MILESTONES.md.

#print axioms grainCoherenceTheorem depends only on
[propext,
Classical.choice, Quot.sound]: Gleason's theorem is imported as an
actual theorem (Gleason.gleason), never postulated.

grainCoherenceTheorem_projector is only the projector-notation version of
the preceding theorem: Parseval's identity identifies its orthonormal-basis
sum with ‖projL c v‖². It is not a new independent mathematical result.

## Kent's contrary-inferences theorem (HistoriesKent)

lean
abbrev History (n L : ℕ) := Fin L → Submodule ℂ (H n)

def IsConsistent (ψ : H n) (Ps : Fin L → Perspective n) : Prop :=
 ∀ h k : History n L, IsHistoryOf Ps h → IsHistoryOf Ps k → h ≠ k →
 decFunctional ψ h k = 0

def histProb (ψ : H n) (h : History n L) : ℝ := ‖chainOp h ψ‖ ^ 2

theorem contrary_inferences :
 ∃ (Ps Ps' : Fin 2 → Perspective 3) (ψ : H 3),
 P 0 ⟂ P 1 ∧
 IsConsistent ψ Ps ∧ IsConsistent ψ Ps' ∧
 (histProb ψ (![(P 0)ᗮ, F] : History 3 2) = 0 ∧ histProb ψ (![P 0, F] : History 3 2) ≠ 0) ∧
 (histProb ψ (![(P 1)ᗮ, F] : History 3 2) = 0 ∧ histProb ψ (![P 1, F] : History 3 2) ≠ 0)


In words: there exist two consistent families of two-stage histories on
H 3, sharing the same preparation ψ and the same final postselection
stage F, such that the first implies proposition P 0 with certainty, the
second implies P 1 with certainty, and P 0 is orthogonal to P 1—Kent
1997, PRL 78, 2874, arXiv:gr-qc/9604012. A temporal stage of a history set
is a BornRule.Perspective, reused unchanged. The consistency notion is
Kent's “medium/strong” version (decFunctional ψ h k = 0 for every pair of
distinct histories in the family, not merely vanishing of its real part).
The explicit witness is constructed in dimension 3:
ψ₀ := e₀+e₁+e₂, φ₀ := e₀+e₁−e₂ (not normalized),
P i :=
ℂ∙(e i), and F := ℂ∙φ₀. The key cancellation is
⟪φ₀, e i⟫ = 1 for i ∈ {0,1} (= -1 for i = 2, outside the witness).

Neutrality note. The mathematical content above—two consistent sets each
implying with certainty a proposition, with the two propositions
orthogonal—is undisputed. Its interpretation as an objection to the
predictability of consistent histories is debated: the standard response
(Griffiths) invokes the “single-framework rule,” under which the two
inferences are valid only within their respective frameworks and may never
be combined in one argument. This repository fixes the mathematical
statement without adjudicating the interpretive debate.

The generic profusion theorem of Dowker–Kent
(J. Stat. Phys. 82, 1575 (1996), using parameter/dimension counting on
manifolds to show that contrary inferences are not isolated) is explicitly
outside the scope of this block. It remains a possible future extension; see
MILESTONES.md.

## Redundant-record interference-circuit bound (Complexity)

`QuantumFoundations.Complexity` connects Riedel's exact or approximate spatial records to
exact 2-local quantum circuits. A circuit is a finite list of unitary gates,
each local to a `Finset (Fin N)` of cardinality at most two. The evaluation
convention is chronological: for `[G₁, G₂, G₃]`,
`eval C x = G₃ (G₂ (G₁ x))`.

Its main theorem has the exact type:

```lean
theorem regions_card_le_two_mul_circuit_length_of_cross_amplitude_ne_zero
    {N d K R : ℕ} [NeZero R]
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (C : Circuit N d)
    (regions : Fin R → Finset (Fin N))
    (recs : Fin R → LabeledResolution (d ^ N) K) (ψ : H (d ^ N))
    (hrec : IsRecordedOn ψ recs) (i j : Fin K) (hij : i ≠ j)
    (hlocal : ∀ r, IsLocalTo (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : ∀ r r', r ≠ r' → Disjoint (regions r) (regions r'))
    (hcross : ⟪branch recs ψ j, Circuit.evalOnH C e (branch recs ψ i)⟫_ℂ ≠ 0) :
    R ≤ 2 * Circuit.length C
```

Thus an exact nonzero cross amplitude between distinct recorded branches
forces the circuit to touch every record region. Pairwise disjointness and
the two-site support bound then give `R ≤ 2 * C.length`.

C3–C6 add the exact division-free `DistinguishesAt` and `InterferesAt`
predicates displayed in the French section above. For distinct nonzero
normalized recorded branches and `0 < δ ≤ 1`, redundant pairwise-disjoint
records imply the per-circuit interference bound `ceilHalf R ≤ C.length`.
An explicitly supplied circuit implementing `2 P_j - I` provides the
distinguishability upper bound. These combine first as a relational,
subtraction-free proxy-gap certificate and then as
`distinguishabilityComplexity + g ≤ interferenceComplexity` in `WithTop ℕ`.
Both target-label locality hypotheses are required because either orientation
of the two-term interference proxy may be nonzero.

C7 proves conditional persistence under an explicit finite reversible
circuit evolution. A `ReversibleCircuitEvolution` stores forward and backward
circuits whose evaluations are mutual inverses, with overhead
`forward.length + backward.length`. The append convention implies that
`backward ++ C ++ forward` implements `forward ∘ C ∘ backward`, while
`forward ++ C ++ backward` implements the pullback. Exact matrix elements and
both proxies are invariant under these conjugations. Distinguishability can
gain one overhead, interference can lose one, and the certified gap can
therefore lose at most twice the overhead.

A canonical inverse circuit was constructed by reversing the gate list and
inverting every gate while preserving its local support. Consequently
`ofCircuit E` has overhead `2 * E.length`, and the record theorem derives the
budget `D.length + 4 * E.length + g ≤ ceilHalf R`. The `WithTop ℕ` transport
theorems work directly under the infimum, including `⊤`, without attainment
or subtraction.

C8 replaces the exact record identities by the aggregated predicate
`‖P target - target‖ + ‖P other‖ ≤ η`. The projector/defect decomposition
gives the sharp untouched cross-amplitude bound `η`; the two proxy
orientations therefore require `ηi + ηj < 2 * δ`. A supplied readout circuit
may have aggregate pointwise error `ξ`; its diagonal separation loses exactly
`2 * ηj + ξ`, giving the sufficient threshold
`2 * δ + 2 * ηj + ξ ≤ 2`. The robust certificates and `WithTop ℕ` bounds then
reuse C6. Exact C7 conjugation adds no analytic error, only the existing
twice-overhead circuit budget. Setting all errors to zero recovers C4–C7.

C9 instantiates this architecture in the explicit binary repetition model.
`zeroBranch R` and `oneBranch R` are the transported constant-zero and
constant-one computational basis vectors; their coherent sum
`repetitionState R` is deliberately unnormalized. Every singleton site is an
independent exact binary record. Reflection in the bit-one cell at the first
site gives an exact one-gate readout, while an ordered list of `R` Pauli-X
gates exchanges the two branches. Consequently
`C_D = 1`, `ceilHalf R ≤ C_I ≤ R`, the interference minimum is finite,
every `1 + g ≤ ceilHalf R` gives a proxy gap, and the concrete persistence
budget is `1 + 4 * E.length + g ≤ ceilHalf R`. Paired-flip sharpness is not
claimed; the closed interference result is the stated pair of linear bounds.

C10 finally shows this robust C8 theory is inhabited by a genuinely
**nonzero-noise** explicit family, on `R + 1` sites: one source qubit (site
`0`) plus `R` record qubits (`recordSite r := Fin.succ r`). A normalized
`NoiseProfile` (`keep`, `leak`, with `‖keep‖² + ‖leak‖² = 1`) mixes two
same-source-bit configurations,
`noisyZeroBranch := keep • basis00 + leak • basis01` and
`noisyOneBranch := leak • basis10 + keep • basis11`, which stay **exactly
orthogonal for every `leak`** because their source qubits differ. Every
record projector has an exact computed error — it fixes the aligned
configuration exactly and leaks exactly `‖leak‖` into the other one — giving
the exact aggregate `ApproxRecordedPairOn` budget `2 * ‖leak‖` per label, a
genuine (not merely zero-error) inhabitant of the C8 approximate-record
predicate. At threshold `δ = 1/2` the robust condition
`NoiseProfile.IsRobust p := 4 * ‖p.leak‖ < 1` gives exactly the same
qualitative bounds as C9:

```lean
distinguishabilityComplexity (sitesEquivR (R+1)) (noisyZeroBranch p R) (noisyOneBranch p R) (1/2) = 1
ceilHalf R ≤ interferenceComplexity (sitesEquivR (R+1)) (noisyZeroBranch p R) (noisyOneBranch p R) (1/2)
interferenceComplexity (sitesEquivR (R+1)) (noisyZeroBranch p R) (noisyOneBranch p R) (1/2) ≤ R + 1
```

together with the robust proxy gap and its conditional persistence under the
same budget `1 + 4 * E.length + g ≤ ceilHalf R`. The Pythagorean triple
`99² + 20² = 101²` gives a fully concrete rational witness
`(keep, leak) = (99/101, 20/101)` with `4 * (20/101) = 80/101 < 1`, to which
every C10a–C10g theorem applies unconditionally. Three generalizations were
added additively to C9 (at a generality C9 itself never needed, and without
changing any existing public type): a basis vector at an arbitrary
configuration (`configurationBranch`), a reflection readout at an arbitrary
site (`recordReadoutGateAt`/`recordReadoutCircuitAt`), and the all-bit-flip
action on an arbitrary configuration
(`allBitFlipCircuit_maps_configurationBranch`).

C11 closes precisely the gap noted at the end of C10: an explicit finite
circuit of 1- and 2-local unitary gates **dynamically generates** the
source-record branching from an uncorrelated source qubit `α|0⟩ + β|1⟩` and
`R` blank record qubits, rather than assuming the branched state as given.
`controlledBitFlipGate` (C11a) is a genuine 2-local permutation gate;
`idealFanoutCircuit R` (C11b) copies the source qubit's classical label onto
every record — computational-basis label fanout, never cloning of an
arbitrary quantum state (no-cloning is not violated: only the classical
`0`/`1` label is fanned out, never the source qubit's own amplitudes). The
hardest construction (C11e) is a genuine single-qubit amplitude-mixing
unitary lifted to all `N` sites through the flat `Sites N d` representation
(no tensor-factor infrastructure existed in the repository for this):
`prepLinearMap p t := keep • P₀ + leak • (F ∘ P₀) - conj(leak) • (F ∘ P₁) +
conj(keep) • P₁`, proved unitary by a direct 16-term inner-product
expansion. This construction succeeds **unconditionally** for every
`NoiseProfile` — no supplied-gate fallback was needed. `noisyMeasurementCircuit
p R` (C11f–g, length `2R`) turns `α • basis00 + β • basis10` into exactly
`α • noisyZeroBranch p R + β • noisyOneBranch p R` — the *same* states as
C10's, so C10's robust proxy gap and its conditional persistence under any
further circuit transport immediately (C11i), with no new distinguishability
argument. The Pythagorean triple `3² + 4² = 5²` gives a fully concrete
rational source-amplitude witness `(amp0, amp1) = (3/5, 4/5)` (C11j), to
which — paired with C10h's rational noise profile `(99/101, 20/101)` — the
full C11 chain applies unconditionally.

C12 closes the optional operator-norm bridge left open since C8:
`toContinuousLinearMapFD` (C12a) is the canonical continuous-linear-map view
of a linear map out of a finite-dimensional complex normed space
(Mathlib's `LinearMap.toContinuousLinearMap`) — `Circuit.evalOnH`,
`recordPhaseFlip`, and every existing `LinearMap` API are left entirely
unchanged; this is an additional view, not a replacement.
`ApproximatesOperator A B ε := ‖A - B‖ ≤ ε` (C12b) is a generic operator-norm
error budget mentioning no records or circuits; the central estimate
`‖A x - B x‖ ≤ ε‖x‖` gives, on two unit states `a, b`, the accumulation
`‖A a - B a‖ + ‖A b - B b‖ ≤ 2ε` — the factor `2` derived by plain
arithmetic, never postulated. `ApproximatesRecordPhaseFlipOp` (C12c)
specializes this bridge to `recordPhaseFlip`: an operator-norm error budget
`ε` implies the C8 pointwise budget `ξ = 2ε`, which directly recovers
(C12d) the readout threshold `2δ + 2ηj + 2ε ≤ 2` and (C12e) the robust
proxy gap and its conditional persistence, reusing C8's own analytic
estimate unchanged — no new estimate is introduced. At C10's noisy model
(C12f) this threshold becomes exactly `4‖leak‖ + 2ε ≤ 1`; the hypothesis
`p.IsRobust` (`4‖leak‖ < 1`, strict) is still required alongside it — not
redundant, since `hreadout` alone (with `ε ≥ 0`) gives only the non-strict
`4‖leak‖ ≤ 1`, insufficient for the strict interference argument. At C11's
dynamically generated branches (C12g), the same threshold applies directly
to the generated branch pair. The concrete rational witness `ε = 1/20`
checks exactly `80/101 + 2·(1/20) ≤ 1` by exact rational arithmetic.
Generic composition laws (C12h, optional) prepare C13's simulation-error
accumulation.

C13 establishes robust gap persistence under an actual norm-preserving
evolution `U` (not necessarily a circuit), as long as an exact circuit `E`
approximates it in operator norm to error `ε`. The central mathematical
point is that same-threshold persistence at `δ` with **no** margin is
generally **not** justified: perturbing two unit states by `ε` each moves
the diagonal difference by at most `4ε` and the cross sum by at most `4ε`
(C13b), shifting the proxy threshold by `2ε` (since the definitions use
`2 · threshold`). C13 therefore introduces a margin `μ`: a certificate at
the widened thresholds `δ - μ` (interference) and `δ + μ`
(distinguishability) — `HasProxyGapMarginAtLeast` (C13d) — persists under an
exact circuit (C13e) and then transports to the central threshold `δ` for
the `U`-evolved states, whenever `2ε ≤ μ` (C13f, the main theorem). The
simulation certificates `CircuitSimulatesEvolutionAt`/`HasCircuitSimulationAt`
(C13f) and their time-dependent extension `HasCircuitSimulationBound` (C13j)
make this directly reusable. Instantiated at C10's noisy model (C13g) and
then at C11's generated branches (C13h), with the concrete rational witness
`δ=1/2, μ=1/10, ε=1/20` (C13i, `80/101 < 4/5`, `6/5+80/101 ≤ 2`,
`2·(1/20) ≤ 1/10`). An optional layer (C13k) constructs an evolution
*genuinely* generated by a self-adjoint generator `H` — `evolve t :=
exp(-itH)`, via Mathlib's existing operator exponential for bounded C⋆-
algebras, with no extra assumption — leaving only the additive group law
unproved (a precisely documented Mathlib instance-resolution obstruction,
not a mathematical gap).

**C14** connects two already-established theorems rather than deriving one
from the other: Riedel's unique orthogonal joint-branch decomposition
(`Induction.riedel`, BranchesRiedel) and the Born weight
`grainCoherenceTheorem_projector` (BornRule), which assigns `‖projL c v‖²`
to any cell `c` of a perspective under (Pos), (Norm), (Grain), (Null).
`BranchesRiedel/BornBridge/` distinguishes four objects: a branch vector
`B f`, its active cell `span ℂ {B f}` (defined only when `B f ≠ 0` — a
zero vector has no formal cell), the support `branchSupport` (the supremum
of the active cells, not necessarily the whole space), and the residual
orthogonal cell `residualCell` (which may be `⊥`). The central projection
identity, `starProjection_branchCell_apply_state : (branchCell B
f).starProjection ψ = activeBranchVector B f` (C14c), is a pure
linear-algebra fact — via `Submodule.eq_starProjection_of_mem_orthogonal'`
— independent of any weighting. `BranchPerspectivePackage` (C14e) builds a
genuine `Perspective` from the active cells, adding the residual cell only
when it is nonzero (`Perspective` forbids `⊥` cells).
`recordBranch_weight_eq_norm_sq` (C14f) then chains
`grainCoherenceTheorem_projector` with the projection identity: the Born
weight of each active cell is exactly `‖B f‖²`, the residual weight is
zero, and the active weights sum to `1`. Record-choice invariance (C14a) —
`chainProj_choice_invariant`, proved by replacing one observable's record
at a time via `Induction.tunneling`, never composing two different records
of the same observable — gives weight invariance under the chosen record
(C14f.5) at the vector level, not merely the norm level.
`record_induced_Born_decomposition` (C14g) assembles all of this into one
abstract theorem, specialized to the local multisite model (C14h) and then
to C11's exact unitary generation (C14i) — two branches `q.amp0 • basis00
R`/`q.amp1 • basis11 R`, weights `‖amp0‖²`/`‖amp1‖²` — concretely at
`(3/5, 4/5)` giving the exact rational weights `9/25` and `16/25` (C14l).
C10's noisy model satisfies only approximate redundancy
(`ApproxRecordedPairOn`), not exact `IsRecordedOn`: exact branch uniqueness
is therefore not concluded for it, only exact source-component extraction
(C14j). Finally, the Born weights of evolved branches under a
norm-preserving evolution (C13) retain their squared norm — via the
norm-based polarization identity `inner_eq_sum_norm_sq_div_four` — without
the evolved branch still being selected by the original record projectors
(C14k).

The result is
limited to finitely many sites, finite local dimension, supplied exact or
approximate records,
pairwise disjoint regions, exact 2-local gates, and an exact nonzero cross
amplitude/proxy above the explicit threshold. It does not
address generic formation of approximate records from decoherence (distinct
from C11's explicit unitary construction), establish efficient synthesis of
arbitrary local record projectors, complete the operator-norm view of every
repository API (C12 covers only the record-readout bridge), the full
physical Taylor–McCulloch
criterion, a Trotter/product-formula or Lieb–Robinson simulation bound,
linear or polynomial simulation-cost growth in time (C13 formalizes no
`O(t)` notation), generic or
Brown–Susskind complexity growth, macroscopic irreversibility, equivalence
with Weingarten, or any interpretive claim about quantum mechanics. C14
connects redundant records to Born weights for a given model, under (Pos),
(Norm), (Grain), (Null) — it does not claim that records alone imply the
Born rule, that (Grain) need only hold on physically realized
perspectives, or approximate/generic many-body branch-decomposition
uniqueness.

**C15** is the Lean formalization and repository integration of Theorem 3
and Corollary 2 of Marko Lela, “The Born Rule as the Unique
Refinement-Stable Induced Weight on Robust Record Sectors”
(arXiv:2603.24619v1). It concerns induced weights on admissible record
situations, not a measure on the full projector lattice. Internal
equivalence initially means equality of binary refinement profiles; exact
binary saturation then proves that projected magnitude classifies those
profiles. The resulting functional equation forces
`W = c ‖P_R Ψ‖²`, and finite normalization fixes `c = 1`. Additivity may be
inherited from an extensive valuation on disjoint continuation bundles. No
Gleason, Busch, decision-theoretic, or envariance theorem is used. Binary
saturation is assumed rather than derived from C14 dynamics; dense
saturation plus continuity, the physical C14/C15 bridge, and C16 are
explicitly deferred.

**C17** is the first quantitative stability theorem within this
development. It assumes that both weights already obey the exact quadratic
law supplied by C15 and measures perturbations by the distance between
projected components `u = P_(R₁)x Ψ₁x` and `v = P_(R₂)x Ψ₂x`. It proves
`|W₁-W₂| ≤ (‖u‖+‖v‖)‖u-v‖`, the unit-ball estimate
`|W₁-W₂| ≤ 2‖u-v‖`, and explicit finite-`L¹`, `2·card(s)·ε`, and half-`L¹`
bounds. It does not address approximate C15 hypotheses, approximate branch
uniqueness, or a dynamical derivation of component proximity. No historical
priority claim is made.

**C17b** is an integration milestone, not a strengthening of the already
completed reduced C17 core. On the unit ball, a fixed sector satisfies
`|w_R(ψ)-w_R(φ)| ≤ 2‖ψ-φ‖`; projectors within operator-norm error `ε` satisfy
`|w_R(ψ)-w_S(ψ)| ≤ 2ε`. A C13 simulation certificate therefore gives
`|w_R(U(t)ψ)-w_R(Cψ)| ≤ 2ε` for every fixed sector. C14 branch weights also
inherit the generic branch-vector bound when the caller supplies an explicit
branch correspondence. These bridges do not establish approximate branch
matching or uniqueness, approximate saturation, or physical persistence of
record selection.

## AI assistance

This development—skeleton, proofs, and architectural choices—was carried out
with assistance from Claude (Anthropic), under human supervision at every
stage: every uncertain Mathlib API was checked through stdin before use
(lake env lean --stdin), every milestone began with a validated skeleton
containing sorry before being filled, and lake build +
./scripts/guard.sh were run after every closed proof. See AGENTS.md for
the exact rules followed and the commit history for milestone-by-milestone
details.

## Getting started

bash
./setup.sh # toolchain + mathlib + cache + build (~10 min avec cache)
./scripts/guard.sh # audit : 0 axiome, 0 native_decide, compte des sorry


## Verifying the proofs

bash
lake build # doit terminer vert
./scripts/guard.sh # 0 axiome, 0 native_decide, 0 sorry (seven blocks)


#print axioms for the chapter-level theorems (the exhaustive list of 155
content-bearing public declarations is in ARCHITECTURE_NOTES.md/the closing
report; all depend on the same trio):


'QuantumFoundations.naimark' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.naimark_born' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.exists_unitary_extension' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.naimark_projective_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Wigner.wigner' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Wigner.exclusivity' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Wigner.bargmann_delta_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Wigner.U_alt_eq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Uhlhorn.uhlhorn_finite_dim' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Uhlhorn.wignerSymmetryProj_of_sendsONBToONB' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Uhlhorn.traceProd_preserved_of_sendsONBToONB' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Uhlhorn.exists_projMeasure_of_frameFunctionOnLines' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.grainCoherenceTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.grainCoherenceTheorem_projector' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.full_rho_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.hker_derivation' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.exists_rho' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.eq_projL_of_vanishes_on_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.E₀_satisfies_axioms' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.refine_filter_sup_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.HistoriesKent.contrary_inferences' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.HistoriesKent.inference' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.HistoriesKent.S_consistent' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.HistoriesKent.isConsistent_single_stage' depends on axioms: [propext, Classical.choice, Quot.sound]


These are the three standard axioms accepted by Lean/Mathlib itself:
propositional extensionality, choice, and quotient soundness. There is no
sorryAx and no project-specific axiom. Points checked specifically:
uhlhorn_finite_dim is the first theorem in the repository to depend both on
Gleason.gleason, an external dependency, AND on
QuantumFoundations.Wigner.wigner, an internal block;
grainCoherenceTheorem depends both on Gleason.gleason AND on the internal
Uhlhorn infrastructure U2/U3a. In both cases, the dual dependency chain leaks
no additional axioms, as confirmed above. contrary_inferences depends
transitively on a THREE-level chain
(HistoriesKent → BornRule.Perspective → external Uhlhorn/Gleason); the
same trio was confirmed when HistoriesKent was closed on 2026-07-16, as was the
absence of any BornRule axiom regression following the relocation of
norm_sq_sum_of_pairwise_orthogonal/sum_sq_projL_of_pairwise_isOrtho
(from private in Nonvacuity.lean to public declarations in
Perspective.lean). The 34 PUBLIC BornRule declarations—the previous 32 +
the two relocated, now public lemmas—were rechecked individually; none
was affected.

## Repository map

| File | Content | Lines |
|---|---|---:|
| QuantumFoundations/Naimark/Defs.lean | POVM n m (reuses Gleason.IsPositiveOp) | 46 |
| QuantumFoundations/Naimark/SqrtOp.lean | Positive square root (spectral construction) | 191 |
| QuantumFoundations/Naimark/DilSpace.lean | Dilation space K, singleL/coordL/dilProj | 194 |
| QuantumFoundations/Naimark/Main.lean | dilV, isometry, Naimark theorem, Born corollary | 157 |
| QuantumFoundations/Naimark/Unitary.lean | N5 (optional): unitary extension, ancilla form | 210 |
| QuantumFoundations/Wigner/Defs.lean | e, eImg, InPerp, V, refVec, chidir, chi, U, IsWignerMap | 119 |
| QuantumFoundations/Wigner/Scalar.lean | Scalar toolkit over ℂ (rigidity, id/conj dichotomy) | 117 |
| QuantumFoundations/Wigner/Bessel.lean | Bessel identity (equality); orthonormal images | 126 |
| QuantumFoundations/Wigner/VConstruction.lean | Bargmann's Construction B: V, collinearity, (11)–(12a) | 449 |
| QuantumFoundations/Wigner/Core.lean | Core: dichotomy of chi, additivity/homogeneity of V | 833 |
| QuantumFoundations/Wigner/Main.lean | U, bijectivity, compatibility with T, theorem wigner | 399 |
| QuantumFoundations/Wigner/Uniqueness.lean | W6 (optional): exclusivity (A), restricted uniqueness (B) | 439 |
| QuantumFoundations/Wigner/Nonvacuity.lean | Wigner witnesses: id (unitary branch), conjCoords (antiunitary branch) | 112 |
| QuantumFoundations/Uhlhorn/Defs.lean | Proj1, TraceProd, PreservesOrthogonality, IsWignerSymmetryProj, IsFrameFunctionOnLines, SendsONBToONB | 278 |
| QuantumFoundations/Uhlhorn/WignerProjectionForm.lean | U1: Wigner's Corollary (B) in projection language | 117 |
| QuantumFoundations/Uhlhorn/Spectral.lean | U2: elementary spectral lemma | 131 |
| QuantumFoundations/Uhlhorn/GleasonExtend.lean | U3a: extension of a frame function on lines to a full ProjMeasure | 268 |
| QuantumFoundations/Uhlhorn/GleasonTwice.lean | U3b: “Gleason applied twice” | 175 |
| QuantumFoundations/Uhlhorn/Assembly.lean | U4 (assembly) + U5 (finite-dimensional reduction), theorem uhlhorn_finite_dim | 111 |
| QuantumFoundations/Uhlhorn/Nonvacuity.lean | Uhlhorn witness: φ := id | 53 |
| QuantumFoundations/BornRule/Perspective.lean | B1: Perspective, Refines, AxGrain/AxNorm/AxPos/AxNul, lemma4_noncontextual, basisPerspective, cellLines, refinePerspective | 555 |
| QuantumFoundations/BornRule/GleasonBridge.lean | B2: g, g_isFrameFunctionOnLines, exists_rho (replaces axiom gleason) | 115 |
| QuantumFoundations/BornRule/Pinning.lean | B3: eq_projL_of_vanishes_on_orthogonal (identification of ρ via U2) | 83 |
| QuantumFoundations/BornRule/Assembly.lean | B4 (assembly), final theorem grainCoherenceTheorem | 215 |
| QuantumFoundations/BornRule/Nonvacuity.lean | BornRule witness: E₀ v (Born rule) satisfies Grain+Norm+Pos+Null simultaneously | 177 |
| QuantumFoundations/Nonvacuity.lean | Naimark witness: uniform POVM with n=2, m=2 | 65 |
| QuantumFoundations/HistoriesKent/Defs.lean | History, IsHistoryOf, chainOp, decFunctional, IsConsistent, histProb | 162 |
| QuantumFoundations/HistoriesKent/Nonvacuity.lean | HistoriesKent witness: every one-stage Perspective is consistent | 85 |
| QuantumFoundations/HistoriesKent/Basic.lean | K1: decFunctional_last_stage_orthogonal, histProb_additivity_two_stage | 121 |
| QuantumFoundations/HistoriesKent/Witness.lean | K2: explicit Kent witness in H 3, S_consistent | 490 |
| QuantumFoundations/HistoriesKent/ContraryInferences.lean | K3: inference, final theorem contrary_inferences | 162 |
| QuantumFoundations/BranchesRiedel/Defs.lean | R0: labeled resolutions, branches, and redundant records | 234 |
| QuantumFoundations/BranchesRiedel/Nonvacuity.lean | R0: three-record GHZ witness | 210 |
| QuantumFoundations/BranchesRiedel/Basic.lean | R1: general record-projector identities | 133 |
| QuantumFoundations/BranchesRiedel/TwoObs.lean | R2: two recorded observables | 207 |
| QuantumFoundations/BranchesRiedel/Induction.lean | R3: multi-observable induction | 559 |
| QuantumFoundations/BranchesRiedel/Local.lean | R4: spatial locality and `PairCovers` counting | 469 |
| QuantumFoundations/BranchesRiedel/BornBridge/RecordChoice.lean | C14a: redundant record-choice invariance | 203 |
| QuantumFoundations/BranchesRiedel/BornBridge/ActiveBranches.lean | C14b: active branch index | 76 |
| QuantumFoundations/BranchesRiedel/BornBridge/BranchCells.lean | C14b/c: branch cells, projection identity | 134 |
| QuantumFoundations/BranchesRiedel/BornBridge/BranchPerspective.lean | C14d/e: support, residual cell, formal perspective | 218 |
| QuantumFoundations/BranchesRiedel/BornBridge/BornWeights.lean | C14f: Born weights of record-induced branches | 151 |
| QuantumFoundations/BranchesRiedel/BornBridge/Synthesis.lean | C14g: abstract synthesis theorem | 92 |
| QuantumFoundations/BranchesRiedel/BornBridge/LocalRecords.lean | C14h: local multisite corollary | 49 |
| QuantumFoundations/BranchesRiedel/BornBridge/GeneratedBranches.lean | C14i/j: C11 exact unitary model, noisy-model boundary | 199 |
| QuantumFoundations/BranchesRiedel/BornBridge/Evolution.lean | C14k: weight preservation under norm-preserving evolution | 129 |
| QuantumFoundations/BranchesRiedel/BornBridge/ConcreteModel.lean | C14l: concrete instance (weights 9/25, 16/25) | 86 |
| QuantumFoundations/BranchesRiedel/BornBridge/Nonvacuity.lean | C14: non-vacuity witnesses | 101 |
| QuantumFoundations/Complexity/Defs.lean | C0: exact 2-local gates and circuits, evaluation and support | 129 |
| QuantumFoundations/Complexity/Nonvacuity.lean | C0/C6/C7/C8/C9/C10/C11/C12/C13: elementary witnesses and concrete models | 389 |
| QuantumFoundations/Complexity/CircuitLocality.lean | C1: circuit commutation away from its support | 45 |
| QuantumFoundations/Complexity/RecordInterference.lean | C1: untouched records force zero cross amplitude | 122 |
| QuantumFoundations/Complexity/Counting.lean | C2: generic counting of touched disjoint regions | 35 |
| QuantumFoundations/Complexity/Main.lean | C2: main bound `R ≤ 2 * C.length` | 63 |
| QuantumFoundations/Complexity/ProxyDefs.lean | C3: exact distinguishability and interference proxies | 82 |
| QuantumFoundations/Complexity/NormalizedBranches.lean | C3: normalization of nonzero recorded branches | 83 |
| QuantumFoundations/Complexity/ProxyCertificates.lean | C3: relational certificates and `ceilHalf` | 96 |
| QuantumFoundations/Complexity/RecordInterferenceBound.lean | C4: two-orientation interference bound | 96 |
| QuantumFoundations/Complexity/RecordDistinguishability.lean | C5: exact phase-flip readout | 114 |
| QuantumFoundations/Complexity/BranchGap.lean | C6: subtraction-free gap certificate | 50 |
| QuantumFoundations/Complexity/MinComplexity.lean | C6: `WithTop ℕ` minima and actual gap | 180 |
| QuantumFoundations/Complexity/CircuitConjugation.lean | C7a: reversible evolution certificates and sandwich circuits | 157 |
| QuantumFoundations/Complexity/CircuitInverse.lean | C7a: local gate inverses and canonical inverse circuits | 207 |
| QuantumFoundations/Complexity/ProxyTransport.lean | C7b: exact matrix-element and proxy transport | 180 |
| QuantumFoundations/Complexity/Persistence.lean | C7c: relational certificate transport | 111 |
| QuantumFoundations/Complexity/RecordPersistence.lean | C7d: redundant-record persistence bounds | 104 |
| QuantumFoundations/Complexity/PersistenceMinima.lean | C7e: `WithTop ℕ` transport without attainment | 117 |
| QuantumFoundations/Complexity/ApproxRecordDefs.lean | C8a: aggregated approximate-record predicate | 78 |
| QuantumFoundations/Complexity/ApproxRecordBasic.lean | C8a: recorded pairs and exact bridge | 64 |
| QuantumFoundations/Complexity/ApproxRecordInterference.lean | C8b: sharp untouched cross-amplitude bound | 132 |
| QuantumFoundations/Complexity/ApproxRecordInterferenceBound.lean | C8c: robust interference bound and minima | 123 |
| QuantumFoundations/Complexity/ApproxRecordDistinguishability.lean | C8d: approximate phase readout | 203 |
| QuantumFoundations/Complexity/ApproxBranchGap.lean | C8e: robust proxy gap and exact regression | 152 |
| QuantumFoundations/Complexity/ApproxRecordPersistence.lean | C8f: conditional robust-gap persistence | 160 |
| QuantumFoundations/Complexity/Models/Repetition/States.lean | C9a: zero/one computational branches and coherent state | 106 |
| QuantumFoundations/Complexity/Models/Repetition/Records.lean | C9b: single-site resolutions and exact records | 278 |
| QuantumFoundations/Complexity/Models/Repetition/Readout.lean | C9c: one-gate reflection readout | 161 |
| QuantumFoundations/Complexity/Models/Repetition/Distinguishability.lean | C9d: distinguishability complexity exactly one | 82 |
| QuantumFoundations/Complexity/Models/Repetition/Interference.lean | C9e: finite all-bit-flip circuit | 205 |
| QuantumFoundations/Complexity/Models/Repetition/Complexities.lean | C9f: linear bounds and concrete gap | 105 |
| QuantumFoundations/Complexity/Models/Repetition/Persistence.lean | C9g: concrete circuit-persistence budget | 57 |
| QuantumFoundations/Complexity/Models/NoisyRepetition/Profiles.lean | C10a: normalized `keep`/`leak` noise profiles | 76 |
| QuantumFoundations/Complexity/Models/NoisyRepetition/States.lean | C10b: four configurations and noisy branches | 215 |
| QuantumFoundations/Complexity/Models/NoisyRepetition/Records.lean | C10c: exact record errors and approximate pair | 182 |
| QuantumFoundations/Complexity/Models/NoisyRepetition/Readout.lean | C10d: exact readout at an arbitrary record site | 59 |
| QuantumFoundations/Complexity/Models/NoisyRepetition/Complexities.lean | C10e: robust complexity separation at `δ = 1/2` | 89 |
| QuantumFoundations/Complexity/Models/NoisyRepetition/Interference.lean | C10f: finite noisy interference witness | 151 |
| QuantumFoundations/Complexity/Models/NoisyRepetition/Persistence.lean | C10g: robust gap and conditional persistence | 123 |
| QuantumFoundations/Complexity/Models/NoisyRepetition/ConcreteNoise.lean | C10h: concrete rational profile `(99/101, 20/101)` | 95 |
| QuantumFoundations/Complexity/Gates/ControlledBitFlip.lean | C11a: 2-local controlled-bit-flip gates | 229 |
| QuantumFoundations/Complexity/Gates/AmplitudeRotation.lean | C11e: amplitude-mixing unitary lifted to `N` sites | 415 |
| QuantumFoundations/Complexity/Models/MeasurementGeneration/IdealFanout.lean | C11b: unitary computational-basis label fanout | 219 |
| QuantumFoundations/Complexity/Models/MeasurementGeneration/Amplitudes.lean | C11c: normalized source-amplitude profile | 89 |
| QuantumFoundations/Complexity/Models/MeasurementGeneration/BranchWeights.lean | C11d/h: source projectors and branch-weight preservation | 231 |
| QuantumFoundations/Complexity/Models/MeasurementGeneration/ProfilePreparation.lean | C11e: canonical profile-preparation gate | 95 |
| QuantumFoundations/Complexity/Models/MeasurementGeneration/NoisyGeneration.lean | C11f/g: correlated record preparation and full noisy generation | 493 |
| QuantumFoundations/Complexity/Models/MeasurementGeneration/GeneratedComplexity.lean | C11i: unitary generation meets branch persistence | 70 |
| QuantumFoundations/Complexity/Models/MeasurementGeneration/ConcreteGeneration.lean | C11j: concrete unitary generation witness | 89 |
| QuantumFoundations/Complexity/OperatorNorm/FiniteDimensional.lean | C12a: finite-dimensional continuous-linear-map view | 115 |
| QuantumFoundations/Complexity/OperatorNorm/Approximation.lean | C12b: generic operator-norm approximation | 106 |
| QuantumFoundations/Complexity/OperatorNorm/RecordReadout.lean | C12c: operator-norm/pointwise readout-error bridge | 113 |
| QuantumFoundations/Complexity/OperatorNorm/RecordGap.lean | C12d/e: distinguishability and proxy gap from operator norm | 207 |
| QuantumFoundations/Complexity/OperatorNorm/NoisyRepetition.lean | C12f: concrete noisy instantiation, `1/20` budget | 165 |
| QuantumFoundations/Complexity/OperatorNorm/GeneratedBranches.lean | C12g: connection to C11 unitary generation | 87 |
| QuantumFoundations/Complexity/OperatorNorm/Composition.lean | C12h: composition laws (optional, for C13) | 84 |
| QuantumFoundations/Complexity/OperatorNorm/Nonvacuity.lean | C12: non-vacuity of the error-budget API | 83 |
| QuantumFoundations/Complexity/SimulatedEvolution/NormPreserving.lean | C13a: norm-preserving operators | 92 |
| QuantumFoundations/Complexity/SimulatedEvolution/MatrixElementStability.lean | C13b: matrix-element perturbation bounds | 132 |
| QuantumFoundations/Complexity/SimulatedEvolution/ThresholdTransport.lean | C13c: threshold transport under operator error | 127 |
| QuantumFoundations/Complexity/SimulatedEvolution/MarginCertificate.lean | C13d: threshold-margin gap certificate | 88 |
| QuantumFoundations/Complexity/SimulatedEvolution/CircuitPersistence.lean | C13e: margin persistence under an exact circuit | 50 |
| QuantumFoundations/Complexity/SimulatedEvolution/SimulationCertificate.lean | C13f: persistence under simulated evolution | 142 |
| QuantumFoundations/Complexity/SimulatedEvolution/NoisyRepetition.lean | C13g: margin instantiation for the noisy model | 92 |
| QuantumFoundations/Complexity/SimulatedEvolution/GeneratedBranches.lean | C13h: connection to C11 generated branches | 77 |
| QuantumFoundations/Complexity/SimulatedEvolution/ConcreteModel.lean | C13i: concrete rational instance `δ=1/2, μ=1/10, ε=1/20` | 108 |
| QuantumFoundations/Complexity/SimulatedEvolution/TimeEvolution.lean | C13j: time-dependent simulation cost | 85 |
| QuantumFoundations/Complexity/SimulatedEvolution/HamiltonianEvolution.lean | C13k: certified self-adjoint-generated evolution | 117 |
| QuantumFoundations/Complexity/SimulatedEvolution/Nonvacuity.lean | C13: non-vacuity of the simulated-evolution API | 114 |
| QuantumFoundations.lean | Root import aggregator | 69 |
| Recomputed total | 119 files | 19598 |

Documentation: AGENTS.md (rules for the AI agent, to be read at startup),
MILESTONES.md (detailed milestone-by-milestone tracking), and
ARCHITECTURE_NOTES.md (consolidated record of all deviations from the
initial plans).

## Milestones — Naimark

| Milestone | Content | Status |
|-----------|------------------------------------------------------------|--------|
| N0 | Skeleton (POVM, DilSpace, Nonvacuity) | ✅ |
| N1 | sqrtOp (spectral positive square root) | ✅ |
| N2 | Dilation-space components (singleL/coordL/dilProj) | ✅ |
| N3 | Dilation (dilV, naimark, naimark_born) | ✅ |
| N4 | Closure (README, #print axioms, tag) | ✅ |
| N5 | Optional: unitary/ancilla version (tag v2.0-naimark) | ✅ |

## Milestones — Wigner

| Milestone | Content | Status |
|-----------|----------------------------------------------------------------------------|--------|
| W0 | Skeleton (Defs, Nonvacuity, 24 sorry) | ✅ |
| W1 | Scalar toolkit (Scalar.lean: rigidity, scalar_dichotomy) | ✅ |
| W2 | Bessel identity (equality), orthonormal images | ✅ |
| W3 | Construction of V (collinearity, Eqs. 11–12a) | ✅ |
| W4 | Core: dichotomy of chi, additivity/homogeneity of V | ✅ |
| W5 | Assembly (U, bijectivity, compatibility, wigner) | ✅ |
| W6 | Optional: exclusivity (A) + restricted uniqueness (B) (tag v2.0-wigner) | ✅ |

## Milestones — Uhlhorn

| Milestone | Content | Status |
|-----------|--------------------------------------------------------------------------------|--------|
| U0 | Reconnaissance + skeleton (Defs.lean, 6 sorry) | ✅ |
| U1 | Wigner's Corollary (B) in projection language (wigner_projection_form) | ✅ |
| U2 | Elementary spectral lemma (eq_projL_of_positive_le_one_trace_one_inner_one) | ✅ |
| U3a | Extension of a frame function on lines to a full ProjMeasure | ✅ |
| U3b | “Gleason applied twice” (traceProd_preserved_of_sendsONBToONB) | ✅ |
| U4 | Direct assembly of U1 and U3b | ✅ |
| U5 | Finite-dimensional reduction, final theorem (tag v1.0-uhlhorn) | ✅ |

## Milestones — BornRule

| Milestone | Content | Status |
|-----------|----------------------------------------------------------------------------------|--------|
| B1 | Scaffolding: Perspective, axioms, lemma4_noncontextual, refinePerspective | ✅ |
| B2 | Bridge to Gleason: g, IsFrameFunctionOnLines, exists_rho | ✅ |
| B3 | Pinning: eq_projL_of_vanishes_on_orthogonal (identification of ρ via U2) | ✅ |
| B4 | Final assembly, theorem grainCoherenceTheorem | ✅ |
| Nonvacuity | E₀ v (Born rule) simultaneously inhabits Grain+Norm+Pos+Null | ✅ |

## Milestones — BornRule/EffectPerspectives (qubit/Busch extension)

See also `QuantumFoundations/BornRule/EffectPerspectives/README.md` for the
full detail (scope, derivations, interpretive non-claims).

| Milestone | Content | Status |
|-----------|---------|--------|
| QB1 | `Effect` (subtype of `Gleason.IsEffect`), `zeroEffect`/`oneEffect`/`complementEffect`/`projectionEffect` | ✅ |
| QB2 | `EffectPerspective` (finite labelled POVM-like family), `binaryPerspective`/`splitPerspective`/`duplicateZeroPerspective` | ✅ |
| QB3 | `Refines` (refinement via `parent` + fiber-sum reconstruction); `Refines.trans` deferred (documented, non-blocking) | ✅ |
| QB4 | `EstimationRule` (weight/non-negativity/normalization/`grain`), a strictly larger hypothesis domain than the projective `AxGrain` | ✅ |
| QB5 | Context independence, zero/unit-effect weight, and binary additivity **derived** from `grain` alone (never axioms) | ✅ |
| QB6 | Construction of `Gleason.EffectMeasure`; direct application of `Gleason.busch`/`Gleason.busch_born_rule` | ✅ |
| QB7 | `ContextualNullSupport` (state-relative); fallback pinning theorem `density_bornValue_eq_pure_of_null` | ✅ |
| QB8 | `projectionEffect_weight_eq_born`: Born weight for projection effects, in arbitrary finite dimension | ✅ |
| QB9 | Explicit dimension-two (qubit) corollary, without invoking `Gleason.gleason` | ✅ |
| QB10 | Nonvacuity: `pureStateEstimationRule` (proved directly, without Busch), exact qubit witnesses | ✅ |
| QB11 | Bridge to Naimark: `EffectPerspective.toPOVM`, dilated projective realization (`naimark`/`naimark_born`/`naimark_projective_form`), a pure integration layer | ✅ |

## Milestones — HistoriesKent

| Milestone | Content | Status |
|-----------|--------------------------------------------------------------------------------------------------|--------|
| K0 | Skeleton (History, chainOp, decFunctional, IsConsistent, Nonvacuity) | ✅ |
| K1 | General lemmas: decFunctional_last_stage_orthogonal, histProb_additivity_two_stage | ✅ |
| K2 | Explicit Kent witness in H 3 (Witness.lean), S_consistent | ✅ |
| K3 | inference, final theorem contrary_inferences (tag v1.0-histories) | ✅ |

## Milestones — Complexity

| Milestone | Content | Status |
|---|---|---|
| C0 | Finite circuits of unitary gates supported on at most two sites | ✅ |
| C1 | Commutation away from the support and zero cross amplitude | ✅ |
| C2 | Independent counting and exact bound `R ≤ 2 * C.length` | ✅ |
| C3 | Exact proxy predicates, normalized branches, and relational certificates | ✅ |
| C4 | Interference lower bound `ceilHalf R` from redundant records | ✅ |
| C5 | Distinguishability upper bound from a supplied exact record phase flip | ✅ |
| C6 | Subtraction-free proxy gap and `WithTop ℕ` minima | ✅ |
| C7 | Exact transport and conditional persistence under finite reversible circuits | ✅ |
| C8 | Approximate records, quantitative bounds, and conditional persistence | ✅ |
| C9 | Explicit repetition model, concrete circuits, and linear proxy gap | ✅ |
| C10 | Explicit **noisy** repetition model (`leak ≠ 0`), robust separation | ✅ |
| C11 | **Unitary** local-circuit generation of source-record branches | ✅ |
| C12 | Finite-dimensional **operator-norm** bridge to the C8–C11 pointwise readout hypotheses | ✅ |
| C13 | Robust gap persistence under **simulated evolution**, with a mandatory threshold margin | ✅ |
| C14 | **Record-induced Born bridge**: Riedel's branch decomposition + the Grain Coherence Theorem | ✅ |
| C15 | Uniqueness `W = c ‖P_R Ψ‖²` on admissible record situations under stability, internal equivalence, and binary saturation | ✅ |
| C17 | First quantitative stability theorem for C15 weights under projected-component perturbations, with pointwise, `L¹`, and uniform bounds | ✅ |
| C17b | Stability bridges to fixed sectors, C12 operator norm, C13 simulation, and explicitly matched C14 branch weights | ✅ |

## Main theorems — reference table

| Theorem | Informal statement | Reference | File (lines) | Status | Tag |
|---|---|---|---:|---|---|
| naimark | Every finite POVM dilates to a projection-valued measure under an isometry | Watrous Thm 2.42 | Naimark/Main.lean (157) | 0 sorry, 0 axioms | v2.0-naimark |
| naimark_born | The Born formula is preserved by this dilation | Watrous Thm 2.42 | Naimark/Main.lean (157) | 0 sorry, 0 axioms | v2.0-naimark |
| exists_unitary_extension / naimark_projective_form | The dilation isometry extends to a global unitary (ancilla form) | Paris §3.2 Thm 4 / Watrous Cor. 2.43 | Naimark/Unitary.lean (210) | 0 sorry, 0 axioms | v2.0-naimark |
| wigner | Every transformation preserving \|⟨φ\|ψ⟩\|² is induced by a unitary or antiunitary, without a bijectivity hypothesis | Bargmann 1964 §1–§5 | Wigner/Main.lean (399) | 0 sorry, 0 axioms | v1.0-wigner |
| exclusivity | The same T cannot be compatible with both a unitary and an antiunitary equivalence (n ≥ 2) | Bargmann 1964 §1.5 | Wigner/Uniqueness.lean (439) | 0 sorry, 0 axioms | v2.0-wigner |
| U_alt_eq_smul | U is unique up to a global phase relative to the choice of representative of eImg (restricted version) | Bargmann 1964 §6 (restricted) | Wigner/Uniqueness.lean (439) | 0 sorry, 0 axioms | v2.0-wigner |
| uhlhorn_finite_dim | In dimension n ≥ 3, preserving orthogonality in one direction only (neither injectivity nor surjectivity) suffices to be a Wigner symmetry | Šemrl 2021, arXiv:2106.06182, Cor. 1.2 | Uhlhorn/Assembly.lean (111) | 0 sorry, 0 axioms | v1.0-uhlhorn |
| grainCoherenceTheorem | Under (Grain)+(Norm)+(Pos)+(Null), the value of an estimation rule on a cell is the Born rule (∑ᵢ‖⟨v,fᵢ⟩‖²) | Gleason 1957 (underlying theorem) | BornRule/Assembly.lean (215) | 0 sorry, 0 axioms | v2.0-bornrule |
| grainCoherenceTheorem_projector | Projector-notation version of the preceding theorem (Est D c = ‖projL c v‖²), with no additional independent mathematical content | Corollary of grainCoherenceTheorem | BornRule/Assembly.lean | 0 sorry, 0 axioms | — |
| EffectPerspectives.projectionEffect_weight_eq_born | Under effect nonvacuity and state-relative null support, the weight of a projection effect equals the Born weight ‖A.starProjection ψ‖², in arbitrary finite dimension n ≥ 1 | Busch 2003, PRL 91, 120403 | BornRule/EffectPerspectives/Main.lean | 0 sorry, 0 axioms | — |
| EffectPerspectives.qubit_projectionEffect_weight_eq_born | Explicit dimension-two (qubit) corollary of the preceding theorem, without invoking Gleason.gleason | Busch 2003 (specialized n = 2) | BornRule/EffectPerspectives/Qubit.lean | 0 sorry, 0 axioms | — |
| contrary_inferences | Two consistent history sets sharing preparation and postselection can imply two orthogonal propositions with certainty | Kent 1997, PRL 78, 2874, arXiv:gr-qc/9604012 | HistoriesKent/ContraryInferences.lean (162) | 0 sorry, 0 axioms | v1.0-histories |
| regions_card_le_two_mul_circuit_length_of_cross_amplitude_ne_zero | `R` exact disjoint records and a nonzero cross amplitude imply `R ≤ 2 * C.length` | Finite counting + Riedel records | Complexity/Main.lean (63) | 0 sorry, 0 axioms | — |
| redundant_records_give_interference_lower_bound | Every circuit satisfying the exact proxy has length at least `ceilHalf R` | Exact proxy + C2 in both orientations | Complexity/RecordInterferenceBound.lean (96) | 0 sorry, 0 axioms | — |
| record_phase_flip_gives_distinguishability_upper_bound | A circuit implementing `2 P_j - I` distinguishes normalized branches at threshold `δ ≤ 1` | Exact record readout | Complexity/RecordDistinguishability.lean (114) | 0 sorry, 0 axioms | — |
| redundant_records_give_proxy_gap_certificate | `D.length + g ≤ ceilHalf R` certifies a proxy gap of at least `g` | Composition of C4/C5 certificates | Complexity/BranchGap.lean (50) | 0 sorry, 0 axioms | — |
| redundant_records_complexity_gap | The same gap holds for exact `WithTop ℕ` minima | Infimum of circuit lengths | Complexity/MinComplexity.lean (180) | 0 sorry, 0 axioms | — |
| redundant_records_gap_persists_under_reversible_evolution | The record gap persists under `D.length + 2 * overhead + g ≤ ceilHalf R` | Exact transport by an inverse circuit pair | Complexity/RecordPersistence.lean (104) | 0 sorry, 0 axioms | — |
| redundant_records_gap_persists_under_circuit_evolution | The canonical inverse specializes the budget to `D.length + 4 * E.length + g ≤ ceilHalf R` | Canonical local inverse + preceding theorem | Complexity/RecordPersistence.lean (104) | 0 sorry, 0 axioms | — |
| norm_cross_amplitude_le_of_untouched_approx_record | An untouched approximate record bounds its cross amplitude by `η` | Projector/defect split + Cauchy–Schwarz | Complexity/ApproxRecordInterference.lean (132) | 0 sorry, 0 axioms | — |
| approximate_records_give_interference_lower_bound | `ηi + ηj < 2δ` forces length at least `ceilHalf R` | Robust bound + C2 counting | Complexity/ApproxRecordInterferenceBound.lean (123) | 0 sorry, 0 axioms | — |
| approx_record_phase_flip_gives_upper_bound | `2δ + 2ηj + ξ ≤ 2` supplies a distinguishability witness | Explicit approximate phase readout | Complexity/ApproxRecordDistinguishability.lean (203) | 0 sorry, 0 axioms | — |
| approximate_records_give_proxy_gap_certificate | The robust thresholds and `D.length + g ≤ ceilHalf R` certify the proxy gap | C8c/C8d composition | Complexity/ApproxBranchGap.lean (152) | 0 sorry, 0 axioms | — |
| approximate_records_gap_persists_under_circuit_evolution | The robust gap persists under `D.length + 4 * E.length + g ≤ ceilHalf R` | Exact C7 transport of the C8 certificate | Complexity/ApproxRecordPersistence.lean (160) | 0 sorry, 0 axioms | — |
| repetition_distinguishabilityComplexity | The explicit model has `C_D = 1` | One-site reflection + exclusion of the empty circuit | Models/Repetition/Distinguishability.lean (82) | 0 sorry, 0 axioms | — |
| repetition_interferenceComplexity_bounds | `ceilHalf R ≤ C_I ≤ R`, hence `C_I ≠ ⊤` | Singleton records + explicit `R`-flip circuit | Models/Repetition/Complexities.lean (105) | 0 sorry, 0 axioms | — |
| repetition_has_proxy_gap | `1 + g ≤ ceilHalf R` certifies the explicit gap | Direct C4–C6 instantiation | Models/Repetition/Complexities.lean (105) | 0 sorry, 0 axioms | — |
| repetition_gap_persists_under_circuit | `1 + 4 * E.length + g ≤ ceilHalf R` preserves the gap | Direct C7 instantiation | Models/Repetition/Persistence.lean (57) | 0 sorry, 0 axioms | — |
| noisy_repetition_approxRecordedPairOn | Noisy records inhabit `ApproxRecordedPairOn` with exact aggregate error `2 * ‖leak‖` | Exact projector actions on the four configurations | Models/NoisyRepetition/Records.lean (182) | 0 sorry, 0 axioms | — |
| noisy_repetition_distinguishabilityComplexity | Under robust noise (`4‖leak‖ < 1`), `C_D = 1` at `δ = 1/2` | One-site exact readout + C8d threshold | Models/NoisyRepetition/Complexities.lean (89) | 0 sorry, 0 axioms | — |
| noisy_repetition_interference_bounds | Under robust noise, `ceilHalf R ≤ C_I ≤ R + 1` at `δ = 1/2` | C8c approximate records + all-bit-flip witness | Models/NoisyRepetition/Interference.lean (151) | 0 sorry, 0 axioms | — |
| noisy_repetition_has_proxy_gap | `1 + g ≤ ceilHalf R` certifies the robust gap | Direct C8e instantiation | Models/NoisyRepetition/Persistence.lean (123) | 0 sorry, 0 axioms | — |
| noisy_repetition_gap_persists_under_circuit | `1 + 4 * E.length + g ≤ ceilHalf R` preserves the robust gap | Direct C8f instantiation | Models/NoisyRepetition/Persistence.lean (123) | 0 sorry, 0 axioms | — |
| rationalNoiseProfile_isRobust | The rational profile `(99/101, 20/101)` is robust (`80/101 < 1`) | Pythagorean triple `99² + 20² = 101²` | Models/NoisyRepetition/ConcreteNoise.lean (95) | 0 sorry, 0 axioms | — |

“0 axioms” means dependence only on
[propext, Classical.choice, Quot.sound], verified by #print axioms for
each main theorem; see the preceding section and the `#print axioms` output
kept in the assembly files.

## Dependencies

This repository pins two Lake dependencies to fixed, resolvable revisions
(lakefile.toml/lake-manifest.json), never to a floating branch:

- gleason-theorem-lean,
 rev = "v1.0-gleason" (resolved to
 876aa7390b5d831cd81415d55493a1c0c3bae31e, a fixed revision unchanged
 since Naimark). Usage expanded from Uhlhorn and reused by BornRule
 (unlike Naimark, which reuses only Gleason.IsPositiveOp, a simple Prop):
 Uhlhorn AND BornRule invoke Gleason.gleason itself—the full Gleason
 theorem, not merely a definition—as well as part of its internal machinery
 (Gleason.positive_inner_self_eq_zero, Gleason.cframe_sum_invariant,
 Gleason.ProjMeasure/bornValue/projL,
 Gleason.exists_orthonormalBasis_extension_complex,
 Submodule.starProjection_isSymmetric/re_inner_starProjection_nonneg).
 This is deliberate and expected: Uhlhorn (Šemrl's Corollary 1.2) and
 BornRule (grainCoherenceTheorem) compose Gleason—and, for Uhlhorn,
 Wigner—by construction; they are not self-contained results, as explained
 in the dedicated sections above. Despite this substantially broader
 dependency, there is no transitive axiom leakage: this was confirmed
 directly by #print axioms for every theorem in this repository, including
 uhlhorn_finite_dim, which depends both on external
 Gleason.gleason and internal QuantumFoundations.Wigner.wigner, and
 grainCoherenceTheorem, which depends both on external
 Gleason.gleason and internal Uhlhorn infrastructure U2/U3a. Neither case
 introduces an additional axiom. BornRule also reuses directly from Uhlhorn
 eq_projL_of_positive_le_one_trace_one_inner_one (U2),
 exists_projMeasure_of_frameFunctionOnLines (U3a), and
 isEffect_of_isDensityOperator (moved from U3b to Uhlhorn/Defs.lean
 during B3); no Gleason/Uhlhorn content is reproved. HistoriesKent does not
 invoke Gleason.gleason or
 Gleason.projL/Submodule.starProjection directly, but inherits them
 transitively through BornRule.Perspective (the three-level chain
 HistoriesKent → BornRule → external Uhlhorn/Gleason). The same absence of axiom
 leakage was confirmed for contrary_inferences and the other 35 public
 declarations in the block. **BornRule/EffectPerspectives** (the qubit/Busch
 extension) reuses, within the same already-pinned revision,
 Gleason.Busch.Effects/Gleason.Busch.Main: Gleason.IsEffect,
 Gleason.EffectMeasure, and above all Gleason.busch/Gleason.busch_born_rule
 (the full Busch theorem, applied directly at a single point,
 EffectMeasure.lean, never reproved). Unlike Gleason.gleason (dimension
 ≥ 3), Busch applies from dimension 1 onward, which is what makes the qubit
 case (n = 2) reachable without the projective route. No dependency
 declaration was added or changed: every one of these declarations already
 existed in the pinned revision.
- mathlib, rev = "8bba4200986270d3b30be2bb2f8840af47a7854f".

./setup.sh (lake exe cache get, then lake build) reproduces the exact
repository state on a fresh clone without manual intervention. This was
tested during every closing pass (lake clean + lake exe cache get +
lake build), most recently including HistoriesKent on 2026-07-16.

## Rules

No axiom, no native_decide (blocking CI, scripts/guard.sh). Every new
hypothesis structure receives a concrete inhabitant in Nonvacuity.lean in
the same commit. Use an honest sorry rather than silently weakening a
statement; see AGENTS.md for the complete rules.

## License

Apache License 2.0.
