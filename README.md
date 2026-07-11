# quantum-foundations-lean — Formalisation Lean 4 de la dilation de Naimark

**Statut : Naimark v1 COMPLET (`v1.0-naimark`, 2026-07-11).** Première formalisation
mécanisée, **sans axiome**, du **théorème de dilation de Naimark** pour les POVM
finies en dimension finie sur ℂ (Watrous, *The Theory of Quantum Information*,
Theorem 2.42) : toute POVM `E : Fin m → (H n →ₗ[ℂ] H n)` se réalise comme mesure
projective (`dilProj`) sous l'action d'une isométrie `dilV`, avec formule de Born
préservée.

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
./scripts/guard.sh            # 0 axiome, 0 native_decide, 0 sorry (Naimark v1 + N5)
```

`#print axioms` sur les quatre théorèmes livrés :

```
'QuantumFoundations.naimark' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.naimark_born' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.exists_unitary_extension' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.naimark_projective_form' depends on axioms: [propext, Classical.choice, Quot.sound]
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
QuantumFoundations/Nonvacuity.lean         Test d'inhabitation obligatoire (POVM uniforme n=2, m=2)
CLAUDE.md                                  Règles pour l'agent IA (à lire au démarrage)
SORRIES.md                                 Suivi détaillé des jalons N0–N5
```

## Jalons

| Jalon | Contenu                                    | État |
|-------|---------------------------------------------|------|
| N0    | Squelette (POVM, DilSpace, Nonvacuity)       | ✅ |
| N1    | `sqrtOp` (racine carrée positive spectrale)  | ✅ |
| N2    | Briques de l'espace dilaté (`singleL`/`coordL`/`dilProj`) | ✅ |
| N3    | Dilation (`dilV`, `naimark`, `naimark_born`) | ✅ |
| N4    | Clôture (README, `#print axioms`, tag)       | ✅ |
| N5    | *Optionnel* : version unitaire/ancilla       | ✅ |

## Règles

Aucun `axiom`, aucun `native_decide` (CI bloquante, `scripts/guard.sh`). Toute nouvelle
structure d'hypothèses reçoit un habitant concret dans `Nonvacuity.lean`, dans le même
commit. Un `sorry` honnête plutôt qu'un énoncé affaibli en silence — voir `CLAUDE.md`
pour l'ensemble des règles.
