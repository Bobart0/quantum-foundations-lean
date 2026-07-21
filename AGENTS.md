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
3. **Théorème de Cohérence de Grain (BornRule)** — ✅ TERMINÉ
   (`v1.0-bornrule`, puis Nonvacuity `v2.0-bornrule`). Le corollaire public
   `grainCoherenceTheorem_projector`, version en notation projecteur du
   théorème final existant, est publié dans `v2.1-bornrule` (2026-07-20).
   Il ne constitue pas un résultat mathématique indépendant : la preuve
   identifie la somme sur la base orthonormée à `‖projL c v‖²` par les lemmes
   publics de décomposition orthogonale/Parseval déjà présents.

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

---

## English translation

# CLAUDE.md — quantum-foundations-lean

## Mission
Formalize in Lean 4 / Mathlib, without any axioms, in finite dimension over ℂ:
1. Naimark dilation theorem (finite POVM with m outcomes on ℂⁿ) — ✅ COMPLETE
 (tags v1.0-naimark and later; N0–N4 + optional N5, all closed, 0 sorry).
2. Wigner's theorem — ✅ COMPLETE (2026-07-13, W0–W5 all closed, 0 sorry, 0
 axioms). Every transformation on pure states that preserves |⟨φ|ψ⟩|² is
 induced by a unitary or an antiunitary, WITHOUT a bijectivity hypothesis on
 the initial transformation (formulation (A), strictly stronger than Simon
 et al.). Mathematical blueprint: Bargmann 1964 (§1–§5 almost verbatim);
 Simon et al. used only as a cross-check (rejected as the primary blueprint
 because of trigonometry/Real.Angle). The complete history (strategy,
 derivations, documented and resolved deviations) is in SORRIES.md, section
 “Wigner.” W6 (uniqueness up to a global phase, optional): not attempted.
3. Grain Coherence Theorem (BornRule) — ✅ COMPLETE
 (v1.0-bornrule, followed by Nonvacuity in v2.0-bornrule). The public
 corollary grainCoherenceTheorem_projector, the projector-notation version
 of the existing final theorem, is published in v2.1-bornrule
 (2026-07-20). It is not an independent mathematical result: the proof
 identifies the sum over the orthonormal basis with ‖projL c v‖² using
 the public orthogonal-decomposition/Parseval lemmas already present.

## Sources (in the user's project directory)
- Watrous, The Theory of Quantum Information (2018), §2.3, Theorem 2.42 (p. 109)
 — the primary source: dilation by an isometry, with a five-line proof using
 √μ(a). Prop. 2.40 (operators of a projection-valued measure are pairwise
 orthogonal): in our construction, these properties are proved directly for
 dilProj.
- Paris, The modern tools of quantum mechanics (2012), §3.2, Theorem 4
 — physical context (ancilla/unitary). WARNING: its sketch of the unitary
 extension (“identity on the orthogonal complement of ω_B”) is too quick;
 the actual construction uses equality of the dimensions of the orthogonal
 complements. Milestone N5 (optional): resolved, but NOT by this route or
 by the initially proposed Submodule approach (Lean timeout; see SORRIES.md).
 Final route: two orthonormal families in the entire dilation space, extended
 to complete bases (Orthonormal.exists_orthonormalBasis_extension_of_card_eq)
 and then glued together (Orthonormal.equiv), without ever introducing a
 Submodule.

## Documented deviation from Watrous
Watrous dilates in X ⊗ ℂ^Σ (tensor product). We dilate in the Hilbert direct
sum K := ⊕_{i<m} H (canonically isomorphic; the Mathlib API is more mature for
PiLp than for Hilbert tensor products). 1_X ⊗ E_{a,a} becomes dilProj a;
√μ(a) ⊗ e_a becomes singleL a ∘ₗ sqrtOp (E a).
This must be recalled in the final README.

## gleason dependency (tag v1.0-gleason)
The gleason package is a pinned Lake dependency. NEVER reprove what already
exists there—import IsPositiveOp, IsEffect, the rankOne machinery
(Busch construction B8), symmetric_ext_of_quadratic, and the orthonormal-basis
tools. When in doubt about whether a lemma exists on the gleason side, grep
the package BEFORE writing anything.

## Conventions
- Remain in H n →ₗ[ℂ] H n, LinearMap.IsSymmetric, LinearMap.adjoint
 (legitimate because everything is finite-dimensional). Avoid
 star/ContinuousLinearMap unless the Mathlib API requires them; document
 such use in the commit.
- Conventions to check through stdin BEFORE any use: direction of
 LinearMap.adjoint_inner_left/right, right-linearity of ⟪·,·⟫_ℂ,
 and ℝ vs ℂ scalar multiplication (casts).
- Definitions depending on hypotheses: use the “TOTAL definition + junk value +
 specification lemmas under hypotheses” pattern (as with Real.sqrt).
 Never define an object by taking a proof as an argument when avoidable.

## Absolute rules (inherited from the gleason project, UNCHANGED)
1. axiom FORBIDDEN. native_decide FORBIDDEN. CI (guard.sh) fails otherwise.
2. Honest sorry: NEVER weaken a statement merely to close it. Every change
 to a statement = a dedicated commit + an explicit message.
3. Nonvacuity: every new hypothesis structure receives a concrete
 inhabitant in Nonvacuity.lean IN THE SAME COMMIT (foundational lesson:
 this omission killed the pre-refoundation project).
4. Run lake build after EVERY modification. Commit + push after every closed sorry.
5. set_option maxHeartbeats: finite value only, with local scope (in).
 maxHeartbeats 0 FORBIDDEN. Exceeding the limit = a signal to
 restructure (extract a private lemma, use generalize), never to increase
 it blindly.
6. Files < 1500 lines.
7. Anti-slowdown pattern: if an rw substitutes a large expression (indexed
 sum) that later rewrites must traverse → immediately generalize it under
 an opaque name; heavy assemblies → a minimal-context private lemma. (Reference: gleason, riesz_rep_assembly, 307s→29s.)
8. Always constrain simp (simp only [...]) in assemblies; NEVER use bare
 simp [mul_comm] (known loop).
9. Uncertain API → test via stdin
 (cat <<'EOF' | lake env lean --stdin) BEFORE writing against it.
 Show the discovered signatures before proceeding.
10. Skeleton-sorry-first: every milestone begins with a compilable skeleton
 containing sorries, validated by the user, then filled in the agreed order.
11. If a goal resists for > 20–30 min (casts, inner-product conventions), SHOW
 the exact goal rather than piling up tactics blindly.
12. If an obtain/refine that composes several lemmas (with metavariables to
 infer) times out at whnf despite a mathematically immediate proof, do not
 persist with inlining or blindly raise maxHeartbeats (recall rule 5).
 Extract the combined statement into a full-fledged separate private
 lemma, then apply it as an ordinary function to the concrete cases. This
 symptom was encountered and resolved in N5 (Naimark), with
 Orthonormal.exists_orthonormalBasis_extension_of_card_eq, independently
 of whether Submodule/dependent types occur in the proof.

## Naimark implementation order — COMPLETE (details and history in SORRIES.md)
- N0 skeleton: POVM, DilSpace, statements with sorry, Nonvacuity, CI — ✅
- N1 sqrtOp: spectral positive square root (THE only new component) — ✅
- N2 components of K: singleL/coordL/dilProj + the four PVM properties — ✅
- N3 dilation: dilV, isometry, adjoint V ∘ dilProj i ∘ V = E i — ✅
- N4 corollaries (Born-style) + release ceremony (#print axioms, README, tag) — ✅
- N5 (optional) unitary/ancilla version — ✅ (three attempts; see SORRIES.md
 for the adopted architecture and the two documented dead ends)

## Git
- Branch master, atomic commits, messages feat|fix|chore(scope): ...
- NEVER git push --force without explicit human confirmation.
- Repository PRIVATE until the user decides otherwise—never change visibility
 autonomously.
