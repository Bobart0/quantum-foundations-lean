# CLAUDE.md — quantum-foundations-lean

## Mission
Formaliser en Lean 4 / Mathlib, **sans aucun axiome**, en dimension finie sur ℂ :
1. **Théorème de dilation de Naimark** (POVM finie à m issues sur ℂⁿ) — ✅ TERMINÉ
   (tags `v1.0-naimark` et suivants ; N0–N4 + N5 optionnel, tous clos, 0 sorry).
2. **Théorème de Wigner** — ✅ TERMINÉ (2026-07-13, W0–W5 tous clos, 0 sorry, 0
   axiome). Toute transformation sur les états purs qui préserve `|⟨φ|ψ⟩|²` est
   induite par un unitaire ou un antiunitaire, SANS hypothèse de bijectivité sur
   la transformation de départ (formulation (A), strictement plus forte que Simon
   et al.). Blueprint mathématique : Bargmann 1964 (§1–§5 quasi tels quels) ; Simon
   et al. utilisé uniquement en contre-vérification (rejeté comme blueprint
   principal — trigonométrie/`Real.Angle`). Historique complet (stratégie,
   dérivations, écarts signalés et résolus) dans SORRIES.md, section « Wigner ».
   W6 (unicité à phase globale près, optionnel) : non attaqué.

## Sources (dans le dossier projet côté utilisateur)
- **Watrous**, *The Theory of Quantum Information* (2018), §2.3, **Theorem 2.42** (p. 109)
  — la source primaire : dilation par isométrie, preuve en 5 lignes via √μ(a).
  Prop. 2.40 (les opérateurs d'une mesure projective sont 2 à 2 orthogonaux) : dans
  notre construction, ces propriétés sont prouvées directement sur `dilProj`.
- **Paris**, *The modern tools of quantum mechanics* (2012), §3.2, Theorem 4
  — contexte physique (ancilla/unitaire). ATTENTION : son esquisse d'extension
  unitaire ("identité sur l'orthogonal de ω_B") est trop rapide — la vraie
  construction passe par l'égalité des dimensions des orthocompléments. Jalon N5
  (optionnel) : **résolu**, mais PAS par cette route ni par l'esquisse Submodule
  initialement envisagée (timeout Lean, voir SORRIES.md) — route finale : deux
  familles orthonormées de l'espace de dilatation entier, complétées en bases
  complètes (`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`) puis
  recollées (`Orthonormal.equiv`), sans jamais introduire de `Submodule`.

## Écart documenté vs Watrous
Watrous dilate dans X ⊗ ℂ^Σ (produit tensoriel). Nous dilatons dans la somme
directe hilbertienne K := ⊕_{i<m} H (canoniquement isomorphe ; API Mathlib
plus mûre : PiLp vs produit tensoriel hilbertien). `1_X ⊗ E_{a,a}` devient
`dilProj a` ; `√μ(a) ⊗ e_a` devient `singleL a ∘ₗ sqrtOp (E a)`.
À rappeler dans le README final.

## Dépendance gleason (tag v1.0-gleason)
Le paquet `gleason` est une dépendance Lake épinglée. **NE JAMAIS re-prouver ce
qui y existe** — importer : `IsPositiveOp`, `IsEffect`, la machinerie `rankOne`
(construction B8 de Busch), `symmetric_ext_of_quadratic`, l'outillage de bases
orthonormées. En cas de doute sur l'existence d'un lemme côté gleason : grep le
paquet AVANT d'écrire.

## Conventions
- Rester en `H n →ₗ[ℂ] H n`, `LinearMap.IsSymmetric`, `LinearMap.adjoint`
  (légitime : tout est de dimension finie). Éviter `star`/`ContinuousLinearMap`
  sauf si l'API Mathlib l'impose — le documenter alors dans le commit.
- Conventions à vérifier en stdin AVANT tout usage : sens de
  `LinearMap.adjoint_inner_left/right`, linéarité à droite de `⟪·,·⟫_ℂ`,
  smul ℝ vs ℂ (casts).
- Définitions dépendant d'hypothèses : pattern « définition TOTALE + valeur
  poubelle + lemmes de spec sous hypothèse » (comme `Real.sqrt`). Jamais de
  définition prenant une preuve en argument si évitable.

## Règles absolues (héritées du projet gleason, INCHANGÉES)
1. `axiom` INTERDIT. `native_decide` INTERDIT. La CI (guard.sh) échoue sinon.
2. `sorry` honnête : ne JAMAIS affaiblir un énoncé pour le fermer. Tout
   changement d'énoncé = commit dédié + message explicite.
3. **Nonvacuity** : toute nouvelle structure d'hypothèses reçoit un habitant
   concret dans `Nonvacuity.lean` DANS LE MÊME COMMIT (leçon fondatrice :
   c'est ce défaut qui a tué le projet pré-refondation).
4. `lake build` après CHAQUE modification. Commit + push après chaque sorry fermé.
5. `set_option maxHeartbeats` : valeur FINIE uniquement, portée locale (`in`).
   `maxHeartbeats 0` INTERDIT. Un dépassement = signal de restructuration
   (extraire un lemme privé, `generalize`), jamais d'augmentation aveugle.
6. Fichiers < 1500 lignes.
7. Pattern anti-lenteur : si un `rw` substitue une grosse expression (somme
   indexée) que des réécritures ultérieures doivent traverser → `generalize`
   immédiat sous un nom opaque ; assemblages lourds → lemme `private` à
   contexte minimal. (Réf. : gleason, `riesz_rep_assembly`, 307s→29s.)
8. `simp` toujours contraint (`simp only [...]`) dans les assemblages ;
   JAMAIS `simp [mul_comm]` nu (boucle connue).
9. API incertaine → test stdin (`cat <<'EOF' | lake env lean --stdin`) AVANT
   d'écrire contre elle. Montrer les signatures trouvées avant de continuer.
10. Skeleton-sorry-first : chaque jalon commence par un squelette compilable
    en sorry, validé par l'utilisateur, puis rempli dans l'ordre convenu.
11. Si un goal résiste > 20-30 min (casts, conventions d'inner) : MONTRER le
    goal exact plutôt qu'empiler des tactiques à l'aveugle.
12. Si un `obtain`/`refine` composant plusieurs lemmes (métavariables à
    inférer) timeout au `whnf` malgré une preuve mathématiquement immédiate :
    ne pas insister sur l'inlining ni augmenter `maxHeartbeats` à l'aveugle
    (rappel règle 5). Extraire l'énoncé combiné dans un lemme `private` à part
    entière, puis l'appliquer par simple application de fonction aux cas
    concrets. Symptôme rencontré et résolu ainsi lors de N5 (Naimark), avec
    `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` — indépendant de
    la présence ou non de `Submodule`/types dépendants dans la preuve.

## Ordre d'attaque Naimark — TERMINÉ (détail et historique dans SORRIES.md)
- **N0** squelette : POVM, DilSpace, énoncés en sorry, Nonvacuity, CI — ✅
- **N1** `sqrtOp` : racine carrée positive spectrale (LE seul morceau neuf) — ✅
- **N2** briques de K : `singleL`/`coordL`/`dilProj` + les 4 propriétés PVM — ✅
- **N3** dilation : `dilV`, isométrie, `adjoint V ∘ dilProj i ∘ V = E i` — ✅
- **N4** corollaires (born-style) + cérémonie (#print axioms, README, tag) — ✅
- **N5** (optionnel) version unitaire/ancilla — ✅ (3 tentatives, voir SORRIES.md
  pour l'architecture retenue et les deux impasses documentées)

## Git
- Branche `master`, commits atomiques, messages `feat|fix|chore(scope): ...`
- JAMAIS `git push --force` sans confirmation humaine explicite.
- Dépôt PRIVÉ jusqu'à décision contraire de l'utilisateur — ne jamais changer
  la visibilité soi-même.