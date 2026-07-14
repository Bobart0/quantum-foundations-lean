# quantum-foundations-lean — Formalisations Lean 4 : Naimark, Wigner, Uhlhorn et BornRule

**Statut : Naimark v2 COMPLET (`v2.0-naimark`, 2026-07-11), Wigner COMPLET avec
unicité/exclusivité optionnelles (`v2.0-wigner`, 2026-07-13), Uhlhorn COMPLET
(`v1.0-uhlhorn`, 2026-07-14) ET BornRule COMPLET avec Nonvacuity
(`v2.0-bornrule`, 2026-07-15).** Quatre formalisations mécanisées, **sans axiome**
(au sens des règles du projet — hors les trois axiomes standards du noyau Lean,
voir plus bas), en dimension finie sur ℂ.

**En chiffres (calculés, pas estimés) : 27 fichiers `.lean`, 4425 lignes,
131 déclarations publiques (structures, définitions, théorèmes), 0 `sorry`,
0 axiome — les 116 déclarations porteuses de contenu (hors `structure`/`Prop`/
`abbrev`) vérifiées individuellement par `#print axioms` dépendent toutes
d'exactement `[propext, Classical.choice, Quot.sound]`, le trio standard du
noyau Lean/Mathlib, sans exception.**

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

Ce dépôt s'appuie sur [`gleason-theorem-lean`](https://github.com/Bobart0/gleason-theorem-lean)
(tag `v1.0-gleason`). Naimark n'y réutilise que `IsPositiveOp`
(`Gleason.Busch.Effects`) ; Uhlhorn et BornRule, en revanche, invoquent
`Gleason.gleason` lui-même ainsi qu'une partie de sa machinerie interne — voir
la section « Dépendances » plus bas pour le détail et la vérification de
non-fuite d'axiome.

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
unique — voir `SORRIES.md` pour le détail des deux routes testées.

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

**Écarts documentés vs le plan initial** (voir `SORRIES.md`, sections W3–W5, pour le
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
`SORRIES.md`.

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
final) — détail complet et écarts favorables dans `SORRIES.md`.

`#print axioms grainCoherenceTheorem` ne dépend que de `[propext,
Classical.choice, Quot.sound]` : le théorème de Gleason est importé comme un
vrai théorème (`Gleason.gleason`), jamais postulé.

## Assistance IA

Ce développement (squelette, preuves, choix d'architecture) a été réalisé avec
l'assistance de Claude (Anthropic), sous supervision humaine à chaque étape : chaque
API Mathlib incertaine a été vérifiée en `stdin` avant usage (`lake env lean --stdin`),
chaque jalon a démarré par un squelette en `sorry` validé avant remplissage, et
`lake build` + `./scripts/guard.sh` ont tourné après chaque preuve fermée. Voir
`CLAUDE.md` pour les règles exactes suivies et l'historique des commits pour le détail
jalon par jalon.

## Démarrage

```bash
./setup.sh          # toolchain + mathlib + cache + build (~10 min avec cache)
./scripts/guard.sh  # audit : 0 axiome, 0 native_decide, compte des sorry
```

## Vérifier les preuves

```bash
lake build                    # doit terminer vert
./scripts/guard.sh            # 0 axiome, 0 native_decide, 0 sorry (Naimark v2 + Wigner + Uhlhorn)
```

`#print axioms` sur les théorèmes-têtes de chapitre (liste exhaustive des 116
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
'QuantumFoundations.BornRule.full_rho_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.hker_derivation' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.exists_rho' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.eq_projL_of_vanishes_on_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.E₀_satisfies_axioms' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.refine_filter_sup_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Ce sont les trois axiomes standards acceptés par Lean/Mathlib lui-même (extensionnalité
propositionnelle, axiome du choix, solidité des quotients) — aucun `sorryAx`, aucun
`axiom` spécifique au projet. **Points vérifiés spécifiquement** : `uhlhorn_finite_dim`
est le premier théorème du dépôt à dépendre à la fois de `Gleason.gleason`
(dépendance externe) ET de `QuantumFoundations.Wigner.wigner` (bloc interne) ;
`grainCoherenceTheorem` dépend à la fois de `Gleason.gleason` ET de
l'infrastructure Uhlhorn interne (U2, U3a) — dans les deux cas, cette double
chaîne de dépendances ne fait fuiter aucun axiome supplémentaire, confirmé
ci-dessus.

## Carte du dépôt

| Fichier                                     | Contenu                                                                            | Lignes |
|---|---|---:|
| `QuantumFoundations/Naimark/Defs.lean`      | `POVM n m` (réutilise `Gleason.IsPositiveOp`)                                      | 26 |
| `QuantumFoundations/Naimark/SqrtOp.lean`    | Racine carrée positive (construction spectrale)                                    | 123 |
| `QuantumFoundations/Naimark/DilSpace.lean`  | Espace de dilatation `K`, `singleL`/`coordL`/`dilProj`                             | 138 |
| `QuantumFoundations/Naimark/Main.lean`      | `dilV`, isométrie, théorème de Naimark, corollaire de Born                         | 114 |
| `QuantumFoundations/Naimark/Unitary.lean`   | N5 (optionnel) : extension unitaire, forme ancilla                                 | 137 |
| `QuantumFoundations/Wigner/Defs.lean`       | `e`, `eImg`, `InPerp`, `V`, `refVec`, `chidir`, `chi`, `U`, `IsWignerMap`          | 70 |
| `QuantumFoundations/Wigner/Scalar.lean`     | Kit scalaire ℂ (rigidité, dichotomie `id`/`conj`)                                  | 92 |
| `QuantumFoundations/Wigner/Bessel.lean`     | Identité de Bessel (égalité) ; images orthonormées                                 | 100 |
| `QuantumFoundations/Wigner/VConstruction.lean` | Construction B de Bargmann : `V`, colinéarité, (11)-(12a)                       | 355 |
| `QuantumFoundations/Wigner/Core.lean`       | Cœur : dichotomie de `chi`, additivité/homogénéité de `V`                          | 690 |
| `QuantumFoundations/Wigner/Main.lean`       | `U`, bijectivité, compatibilité avec `T`, théorème `wigner`                        | 356 |
| `QuantumFoundations/Wigner/Uniqueness.lean` | W6 (optionnel) : exclusivité (A), unicité restreinte (B)                           | 335 |
| `QuantumFoundations/Wigner/Nonvacuity.lean` | Témoins Wigner : `id` (branche unitaire), `conjCoords` (branche antiunitaire)      | 79 |
| `QuantumFoundations/Uhlhorn/Defs.lean` | `Proj1`, `TraceProd`, `PreservesOrthogonality`, `IsWignerSymmetryProj`, `IsFrameFunctionOnLines`, `SendsONBToONB` | 121 |
| `QuantumFoundations/Uhlhorn/WignerProjectionForm.lean` | U1 : corollaire (B) de Wigner en langage de projections                 | 86 |
| `QuantumFoundations/Uhlhorn/Spectral.lean`  | U2 : lemme spectral élémentaire                                                     | 108 |
| `QuantumFoundations/Uhlhorn/GleasonExtend.lean` | U3a : extension d'une fonction-cadre sur les droites en `ProjMeasure` complet  | 194 |
| `QuantumFoundations/Uhlhorn/GleasonTwice.lean` | U3b : « Gleason appliqué deux fois »                                            | 189 |
| `QuantumFoundations/Uhlhorn/Assembly.lean`  | U4 (assemblage) + U5 (réduction fini-dimensionnelle), théorème `uhlhorn_finite_dim` | 83 |
| `QuantumFoundations/Uhlhorn/Nonvacuity.lean` | Témoin Uhlhorn : `φ := id`                                                        | 37 |
| `QuantumFoundations/BornRule/Perspective.lean` | B1 : `Perspective`, `Refines`, `AxGrain`/`AxNorm`/`AxPos`/`AxNul`, `lemma4_noncontextual`, `basisPerspective`, `cellLines`, `refinePerspective` | 445 |
| `QuantumFoundations/BornRule/GleasonBridge.lean` | B2 : `g`, `g_isFrameFunctionOnLines`, `exists_rho` (remplace `axiom gleason`) | 81 |
| `QuantumFoundations/BornRule/Pinning.lean`   | B3 : `eq_projL_of_vanishes_on_orthogonal` (identification de `ρ` via U2)          | 70 |
| `QuantumFoundations/BornRule/Assembly.lean`  | B4 (assemblage), théorème final `grainCoherenceTheorem`                          | 136 |
| `QuantumFoundations/BornRule/Nonvacuity.lean` | Témoin BornRule : `E₀ v` (règle de Born) satisfait Grain+Norm+Pos+Null simultanément | 180 |
| `QuantumFoundations/Nonvacuity.lean`         | Témoin Naimark : POVM uniforme `n=2, m=2`                                         | 55 |
| `QuantumFoundations.lean`                    | Agrégateur d'imports racine                                                       | 30 |
| **Total**                                    | **27 fichiers**                                                                   | **4425** |

Documentation : `CLAUDE.md` (règles pour l'agent IA, à lire au démarrage),
`SORRIES.md` (suivi détaillé jalon par jalon), `ARCHITECTURE_NOTES.md` (mémoire
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

## Théorèmes principaux — table de référence

| Théorème | Énoncé informel | Référence | Fichier (lignes) | Statut | Tag |
|---|---|---|---:|---|---|
| `naimark` | Toute POVM finie se dilate en une mesure projective sous une isométrie | Watrous Thm 2.42 | `Naimark/Main.lean` (114) | 0 sorry, 0 axiome | `v2.0-naimark` |
| `naimark_born` | La formule de Born est préservée par cette dilation | Watrous Thm 2.42 | `Naimark/Main.lean` (114) | 0 sorry, 0 axiome | `v2.0-naimark` |
| `exists_unitary_extension` / `naimark_projective_form` | L'isométrie de dilatation s'étend en un unitaire global (forme ancilla) | Paris §3.2 Thm 4 / Watrous Cor. 2.43 | `Naimark/Unitary.lean` (137) | 0 sorry, 0 axiome | `v2.0-naimark` |
| `wigner` | Toute transformation préservant `\|⟨φ\|ψ⟩\|²` est induite par un unitaire ou un antiunitaire, sans hypothèse de bijectivité | Bargmann 1964 §1–§5 | `Wigner/Main.lean` (356) | 0 sorry, 0 axiome | `v1.0-wigner` |
| `exclusivity` | Un même `T` ne peut être compatible à la fois avec une équivalence unitaire et une antiunitaire (`n ≥ 2`) | Bargmann 1964 §1.5 | `Wigner/Uniqueness.lean` (335) | 0 sorry, 0 axiome | `v2.0-wigner` |
| `U_alt_eq_smul` | `U` est unique à phase globale près relativement au choix du représentant de `eImg` (version restreinte) | Bargmann 1964 §6 (restreint) | `Wigner/Uniqueness.lean` (335) | 0 sorry, 0 axiome | `v2.0-wigner` |
| `uhlhorn_finite_dim` | En dimension `n ≥ 3`, préserver l'orthogonalité dans un seul sens (ni injectivité ni surjectivité) suffit à être une symétrie de Wigner | Šemrl 2021, arXiv:2106.06182, Cor. 1.2 | `Uhlhorn/Assembly.lean` (83) | 0 sorry, 0 axiome | `v1.0-uhlhorn` |
| `grainCoherenceTheorem` | Sous (Grain)+(Norm)+(Pos)+(Null), la valeur d'une règle d'estimation sur une cellule est la règle de Born (`∑ᵢ‖⟨v,fᵢ⟩‖²`) | Gleason 1957 (théorème sous-jacent) | `BornRule/Assembly.lean` (136) | 0 sorry, 0 axiome | `v2.0-bornrule` |

Statut « 0 axiome » signifie : dépend uniquement de
`[propext, Classical.choice, Quot.sound]` (vérifié par `#print axioms` sur
chacun, voir section précédente et le rapport de clôture pour la liste
exhaustive des 116 déclarations vérifiées).

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
  lors de B3) — aucun contenu Gleason/Uhlhorn n'est reprouvé.
- `mathlib`, `rev = "8bba4200986270d3b30be2bb2f8840af47a7854f"`.

`./setup.sh` (`lake exe cache get` puis `lake build`) reproduit l'état exact
du dépôt sur un clone frais, sans intervention manuelle — testé lors de la
passe de clôture (`lake clean` + `lake exe cache get` + `lake build`).

## Règles

Aucun `axiom`, aucun `native_decide` (CI bloquante, `scripts/guard.sh`). Toute nouvelle
structure d'hypothèses reçoit un habitant concret dans `Nonvacuity.lean`, dans le même
commit. Un `sorry` honnête plutôt qu'un énoncé affaibli en silence — voir `CLAUDE.md`
pour l'ensemble des règles.

## Licence

[Apache License 2.0](LICENSE).
