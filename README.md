# quantum-foundations-lean — Formalisations Lean 4 : Naimark et Wigner

**Statut : Naimark v1 COMPLET (`v1.0-naimark`, 2026-07-11) ET Wigner COMPLET
(2026-07-13).** Deux formalisations mécanisées, **sans axiome** (au sens des règles
du projet — hors les trois axiomes standards du noyau Lean, voir plus bas), en
dimension finie sur ℂ.

Le **théorème de dilation de Naimark** pour les POVM finies (Watrous, *The Theory
of Quantum Information*, Theorem 2.42) : toute POVM `E : Fin m → (H n →ₗ[ℂ] H n)` se
réalise comme mesure projective (`dilProj`) sous l'action d'une isométrie `dilV`,
avec formule de Born préservée.

Le **théorème de Wigner** (Bargmann 1964, *Note on Wigner's Theorem on Symmetry
Operations*) : toute transformation sur les états purs qui préserve les probabilités
de transition `|⟨φ|ψ⟩|²` est induite par un opérateur unitaire ou antiunitaire —
formulation (A), **sans hypothèse de bijectivité** sur la transformation de départ
(strictement plus fort que Simon et al., eq. 2.8, qui la suppose).

Ce dépôt s'appuie sur [`gleason-theorem-lean`](https://github.com/Bobart0/gleason-theorem-lean)
(tag `v1.0-gleason`), dont il réutilise `IsPositiveOp` et la machinerie `rankOne`.

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
quasi tel quel) ; Simon et al. utilisé uniquement en contre-vérification (rejeté
comme blueprint principal — approche trigonométrique/`Real.Angle`).

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
./scripts/guard.sh            # 0 axiome, 0 native_decide, 0 sorry (Naimark v1 + N5 + Wigner)
```

`#print axioms` sur les théorèmes livrés :

```
'QuantumFoundations.naimark' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.naimark_born' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.exists_unitary_extension' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.naimark_projective_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Wigner.wigner' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Ce sont les trois axiomes standards acceptés par Lean/Mathlib lui-même (extensionnalité
propositionnelle, axiome du choix, solidité des quotients) — aucun `sorryAx`, aucun
`axiom` spécifique au projet.

## Carte du dépôt

```
QuantumFoundations/Naimark/Defs.lean       POVM n m (réutilise Gleason.IsPositiveOp)
QuantumFoundations/Naimark/SqrtOp.lean     Racine carrée positive (construction spectrale)
QuantumFoundations/Naimark/DilSpace.lean   Espace de dilatation K, singleL/coordL/dilProj
QuantumFoundations/Naimark/Main.lean       dilV, isométrie, théorème de Naimark, corollaire de Born
QuantumFoundations/Naimark/Unitary.lean    N5 (optionnel) : extension unitaire, forme ancilla
QuantumFoundations/Wigner/Defs.lean        e, eImg, InPerp, V, refVec, chidir, chi, U, IsWignerMap
QuantumFoundations/Wigner/Scalar.lean      Kit scalaire ℂ (rigidité, dichotomie id/conj)
QuantumFoundations/Wigner/Bessel.lean      Identité de Bessel (égalité) ; images orthonormées
QuantumFoundations/Wigner/VConstruction.lean  Construction B de Bargmann : V, colinéarité, (11)-(12a)
QuantumFoundations/Wigner/Core.lean        Cœur : dichotomie de chi, additivité/homogénéité de V
QuantumFoundations/Wigner/Main.lean        U, bijectivité, compatibilité avec T, théorème `wigner`
QuantumFoundations/Nonvacuity.lean         Test d'inhabitation obligatoire (POVM uniforme n=2, m=2)
CLAUDE.md                                  Règles pour l'agent IA (à lire au démarrage)
SORRIES.md                                 Suivi détaillé des jalons N0–N5 et W0–W5
```

## Jalons — Naimark

| Jalon | Contenu                                    | État |
|-------|---------------------------------------------|------|
| N0    | Squelette (POVM, DilSpace, Nonvacuity)       | ✅ |
| N1    | `sqrtOp` (racine carrée positive spectrale)  | ✅ |
| N2    | Briques de l'espace dilaté (`singleL`/`coordL`/`dilProj`) | ✅ |
| N3    | Dilation (`dilV`, `naimark`, `naimark_born`) | ✅ |
| N4    | Clôture (README, `#print axioms`, tag)       | ✅ |
| N5    | *Optionnel* : version unitaire/ancilla       | ✅ |

## Jalons — Wigner

| Jalon | Contenu                                              | État |
|-------|-------------------------------------------------------|------|
| W0    | Squelette (Defs, Nonvacuity, 24 sorry)                 | ✅ |
| W1    | Kit scalaire (`Scalar.lean` : rigidité, `scalar_dichotomy`) | ✅ |
| W2    | Identité de Bessel (égalité), images orthonormées      | ✅ |
| W3    | Construction `V` (colinéarité, eqs 11–12a)             | ✅ |
| W4    | Cœur : dichotomie de `chi`, additivité/homogénéité de `V` | ✅ |
| W5    | Assemblage (`U`, bijectivité, compatibilité, `wigner`) | ✅ |

## Règles

Aucun `axiom`, aucun `native_decide` (CI bloquante, `scripts/guard.sh`). Toute nouvelle
structure d'hypothèses reçoit un habitant concret dans `Nonvacuity.lean`, dans le même
commit. Un `sorry` honnête plutôt qu'un énoncé affaibli en silence — voir `CLAUDE.md`
pour l'ensemble des règles.
