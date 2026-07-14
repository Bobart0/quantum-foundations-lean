# SORRIES.md — quantum-foundations-lean

Suivi de l'avancement, sur le modèle de gleason-theorem-lean. Coché = `lake build`
vert, 0 axiome (guard.sh), commit + push fait. Sources : Watrous *TQI* Thm 2.42
(cœur), Paris §3.2 Thm 4 (contexte physique, N5 optionnel).

Compte total attendu (Naimark, hors N5) : **13 sorry** au sortir de N0 — **0 sorry**
restant depuis la clôture de N3, et toujours **0 sorry** après clôture de N5
(optionnel) le 2026-07-11. Wigner (W0) ajoute **24 sorry** le 2026-07-12 (dépôt
total : 24) — **21 sorry** après clôture de W1, **19 sorry** après clôture de W2,
**13 sorry** après clôture de W3, **7 sorry** après clôture de W4,
**0 sorry** après clôture de W5 (2026-07-13) — **théorème de Wigner intégralement
prouvé, 0 axiome, 0 sorry sur tout le dépôt.** W6 (optionnel, (A)+(B)) clos le
2026-07-13 sans jamais introduire de sorry (chaque lemme écrit directement en
preuve complète, skeleton-sorry-first non nécessaire vu la taille des étapes) —
**0 sorry sur tout le dépôt, y compris W6.**

Uhlhorn (U0, squelette) ajoute **6 sorry** le 2026-07-13 (dépôt total : 6) —
**5 sorry** après clôture de U3a (2026-07-13, attaqué en premier car pièce la
plus incertaine à l'issue de la reconnaissance), **4 sorry** après clôture de U1
(2026-07-13), **3 sorry** après clôture de U2 (2026-07-14). U3b, U4, U5 restent
ouverts.

---

## N0 — Squelette (Defs, SqrtOp, DilSpace, Main, Nonvacuity)
- [x] Étape 0 validée : signatures spectrales, racines carrées existantes,
      choix d'espace de dilatation (K₁ PiLp imbriqué vs K₂ plat) tranché.
      Décisions : (b) pas de raccourci `CFC.sqrt` retenu — construction spectrale
      maison (`eigenvectorBasis` + `rankOne`), fidèle à la convention `LinearMap` du
      projet et au calque interne de `ContinuousLinearMap.isPositive_iff_eq_sum_rankOne`.
      (d) K₂ := `EuclideanSpace ℂ (Fin m × Fin n)` retenu sur K₁ (friction de preuve
      égale, mais index plat unique, moins de couches `WithLp`/`.ofLp`).
- [x] `POVM n m` défini (réutilise `IsPositiveOp` de gleason)
- [x] Nonvacuity : POVM uniforme (n=2, m=2) prouvée habitée
- [x] Squelette compile, 13 sorry, 0 axiome, CI/guard.sh adaptés au nouveau nom

## N1 — `sqrtOp` (le seul contenu mathématique neuf)
- [x] `sqrtOp_isPositive : IsPositiveOp T → IsPositiveOp (sqrtOp T)`
- [x] `sqrtOp_mul_self : IsPositiveOp T → sqrtOp T ∘ₗ sqrtOp T = T`
      (extensionnalité sur la base propre, pas de double somme ; 3 lemmes privés
      auxiliaires : `sqrtOp_apply`, `sqrtOp_apply_basis`, `eigenvalues_nonneg`)
- [x] 11 sorry restants, `lake build` vert, `guard.sh` : 0 axiome

## N2 — Briques de l'espace dilaté `K`
- [x] Étape 0 validée : `LinearMap.adjoint` existe entre deux espaces de Hilbert
      distincts de dimension finie (`E →ₗ[𝕜] F`, `[FiniteDimensional 𝕜 E]` et
      `[FiniteDimensional 𝕜 F]` séparément) — confirmé en stdin, aucune restriction
      aux endomorphismes côté Mathlib (seul `IsSymmetric` de gleason est
      endomorphisme-only, mais inutile ici sauf pour `dilProj`).
- [x] `inner_singleL : ⟪singleL i x, w⟫ = ⟪x, coordL i w⟫`
- [x] `adjoint_singleL : adjoint (singleL i) = coordL i` (via `LinearMap.eq_adjoint_iff`)
- [x] `adjoint_coordL : adjoint (coordL i) = singleL i` (lemme auxiliaire ajouté,
      prouvé via `LinearMap.adjoint_adjoint`, pas supposé gratuit)
- [x] `coordL_singleL : coordL i ∘ₗ singleL j = if i = j then id else 0`
- [x] `dilProj_isSymmetric`
- [x] `dilProj_idempotent`
- [x] `dilProj_orthogonal : i ≠ j → dilProj i ∘ₗ dilProj j = 0`
- [x] `dilProj_sum_eq_one : ∑ i, dilProj i = 1` (résolution de l'identité via
      `Finset.sum_ite_eq`, aucun lemme de reconstruction Pi/PiLp dédié nécessaire)
- [x] 4 sorry restants (N3 seul), `lake build` vert, `guard.sh` : 0 axiome

## N3 — La dilation (Watrous Thm 2.42)
- [x] Étape 0 validée : conventions d'adjoint confirmées (`adjoint_inner_left`,
      `adjoint_inner_right`, `adjoint_comp`, `map_sum` pour l'adjoint d'une somme
      finie) — citées, pas re-dérivées.
- [x] `key1`, `key2` : pivots à somme simple (jamais de double somme, cf. règle 7
      CLAUDE.md / leçon `riesz_rep_assembly`)
- [x] `dilV_isometry : adjoint (dilV P) ∘ₗ dilV P = LinearMap.id`
- [x] `naimark_dilation : ∀ i, adjoint (dilV P) ∘ₗ dilProj i ∘ₗ dilV P = P.E i`
- [x] `theorem naimark` (assemblage direct des deux précédents)
- [x] `naimark_born` (corollaire statistique : les probabilités coïncident)
- [x] 0 sorry restant sur Naimark v1, `lake build` vert, `guard.sh` : 0 axiome,
      0 `native_decide` (bug latent corrigé : `grep` sans match sous
      `set -e -o pipefail` tuait le script pile au moment d'atteindre 0 sorry)

## N4 — Clôture
- [x] SORRIES.md à jour, `#print axioms` vérifié :
      `QuantumFoundations.naimark` et `QuantumFoundations.naimark_born` dépendent
      de `[propext, Classical.choice, Quot.sound]` uniquement
- [x] README : énoncé, écart documenté vs Watrous (somme directe vs ⊗),
      mention explicite de l'assistance IA
- [x] `git tag v1.0-naimark`, push --tags

## N5 — OPTIONNEL : version unitaire/ancilla (Paris Thm 4 / Watrous Cor. 2.43) — ✅ CLOS
Nécessitait un lemme non trivial et absent à ce jour : extension d'une isométrie
partielle `H n →ₗ K` en un unitaire global de `K`. L'esquisse de Paris
("identité sur l'orthogonal de ω_B") était insuffisante telle quelle — voir
CLAUDE.md. Résolu à la tentative 3 (ci-dessous) par une route n'utilisant aucun
`Submodule`, différente de l'esquisse de Paris comme du plan initial des
tentatives 1/2.

**Tentative du 2026-07-11 (budget 30 min, non concluante — arrêtée par prudence,
PAS de sorry ajouté, rien commité sur N5).** Recherche des briques Mathlib :
aucun lemme direct « extend isometry to unitary » trouvé, mais la route de
construction est claire et repose sur des briques qui EXISTENT :
- `Submodule.orthogonalDecomposition (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
  E ≃ₗᵢ[𝕜] WithLp 2 (K × Kᗮ)` (`Mathlib.Analysis.InnerProductSpace.ProdL2`) — décompose
  l'espace ambiant en produit L² du sous-espace et de son orthogonal.
- `Orthonormal.equiv {v : Basis ι 𝕜 E} (hv) {v' : Basis ι' 𝕜 E'} (hv') (e : ι ≃ ι') :
  E ≃ₗᵢ[𝕜] E'` (`Mathlib.Analysis.InnerProductSpace.Orthonormal`) — construit une
  isométrie linéaire entre deux espaces à partir de deux bases orthonormées indexées
  par des types équivalents.
- `stdOrthonormalBasis 𝕜 A : OrthonormalBasis (Fin (finrank 𝕜 A)) 𝕜 A` — donne une
  base orthonormée canonique indexée par `Fin k`, pour n'importe quel sous-espace.

Plan de preuve (non implémenté) : soit `A ≤ K` le sous-espace domaine (`A ≅ H n` via
`singleL 0` par ex.) et `B := range V₀` son image isométrique. `dim A = dim B`
(isométrie) ⟹ `dim Aᗮ = dim K - dim A = dim K - dim B = dim Bᗮ` ⟹ via
`stdOrthonormalBasis` + `Orthonormal.equiv` (avec `e := Equiv.refl (Fin k)`), une
isométrie `Aᗮ ≃ₗᵢ Bᗮ`. Recoller `V₀ : A ≃ₗᵢ B` et cette isométrie via
`orthogonalDecomposition A` et `orthogonalDecomposition B` (les deux `≃ₗᵢ WithLp 2 (_ × _ᗮ)`)
donne l'unitaire cherché sur `K`.

**Pourquoi arrêté ici** : l'assemblage (corestriction de `V₀` à son image en
`LinearIsometryEquiv`, navigation dans `WithLp 2 (_ × _)`, recollement final) est un
morceau de preuve substantiel en soi — la friction `WithLp`/`.ofLp` déjà rencontrée
sur N0–N3 pour des énoncés bien plus simples laisse penser que la fermeture réelle
dépasserait largement les 30 minutes allouées.

**Tentative 2 du 2026-07-11 (budget 60 min, non concluante — arrêtée, aucun sorry ni
code cassé committé).** Nouvelle architecture : projections orthogonales directes
(`Submodule.orthogonalProjectionOnto`), sans `orthogonalDecomposition`/`WithLp`.
Étape 0 confirmée en stdin :
- `Submodule.HasOrthogonalProjection` : instance automatique pour tout sous-espace
  d'un espace de dimension finie — OK.
- `Submodule.orthogonalProjectionOnto (K) : E →L[𝕜] ↥K` (`orthogonalProjection` est
  déprécié, alias vers `orthogonalProjectionOnto`) ; décomposition directe obtenue via
  `Submodule.starProjection_add_starProjection_orthogonal` + `starProjection_apply`
  (`K.starProjection v = ↑(K.orthogonalProjectionOnto v)`), PAS un lemme unique tout
  fait sous ce nom exact.
- `Submodule.norm_sq_eq_add_norm_sq_projection (x) (S) [HasOrthogonalProjection] :
  ‖x‖² = ‖S.orthogonalProjectionOnto x‖² + ‖Sᗮ.orthogonalProjectionOnto x‖²` — Pythagore,
  nom confirmé.
- `LinearMap.injective_iff_surjective [FiniteDimensional K V] {f : V →ₗ[K] V} :
  Injective f ↔ Surjective f` — confirmé (`Mathlib.LinearAlgebra.FiniteDimensional.Basic`).
- Pas de `LinearIsometryEquiv.ofBijective` ; la bonne brique est
  `LinearIsometryEquiv.ofSurjective (f : F →ₛₗᵢ E) (hf : Surjective f) : F ≃ₛₗᵢ E`, et
  pour construire une `LinearIsometry` depuis un `LinearMap` + preuve de norme :
  `LinearIsometry.mk (toLinearMap) (∀ x, ‖toLinearMap x‖ = ‖x‖)`.
- `LinearIsometry.equivRange (f : F →ₛₗᵢ E) : F ≃ₛₗᵢ (LinearMap.range f.toLinearMap)`
  existe (corestriction d'une isométrie à son image) — confirmé.
- `Orthonormal.equiv`/`stdOrthonormalBasis` : inchangés (tentative 1).

**Obstruction rencontrée — PAS mathématique, PERFORMANCE Lean** : dès N5-1/N5-2
(censés être mécaniques), composer deux `LinearIsometryEquiv` obtenus via
`.equivRange` avec `.symm.trans` sur des sous-espaces définis par
`LinearMap.range (...).toLinearMap` (`A := range(singleL i₀)`, `B := range(dilV P)`)
provoque un **timeout déterministe au `whnf`** (`maxHeartbeats`), y compris relevé à
1 000 000 puis 4 000 000 — l'élaborateur semble tenter de déplier ces définitions en
profondeur lors de la vérification de type de la composition, sans jamais aboutir
dans un temps raisonnable. Piste alternative testée avec succès : construire les
projecteurs `proj_B := dilV P ∘ₗ adjoint(dilV P)` directement comme endomorphismes de
`K` (formule standard `VV*` pour la projection orthogonale sur `range V` quand
`V*V = id` — idempotence et symétrie viennent gratuitement de `dilV_isometry`), ce qui
évite totalement `Submodule`/`↥A`/`LinearIsometryEquiv` composés et compile sans
timeout. Reste un point dur non résolu dans le temps imparti : construire `W`
(l'isométrie entre les complémentaires orthogonaux `Aᗮ`/`Bᗮ`) nécessite malgré tout un
minimum de structure de sous-espace (pour appliquer `Orthonormal.equiv`), donc la
route « 100% opérateurs, zéro submodule » n'est pas complètement praticable telle
quelle — mais limiter l'usage des submodules à CE seul endroit (au lieu de toute
l'architecture A/B) est la piste à explorer en premier lors d'une prochaine tentative.

**Tentative 3 du 2026-07-11 (budget 2h, RÉUSSIE — N5 clos, 0 sorry).**
Architecture définitive, radicalement différente des deux précédentes : ZÉRO
`Submodule`/`↥A` de bout en bout. Au lieu de décomposer l'espace en sous-espace +
orthogonal, on travaille avec deux **familles orthonormées de `K` tout entier**,
indexées par `Fin m × Fin n` (l'indice canonique de `DilSpace n m`) :
- `v p := singleL i₀ (eₚ.₂)` et `w p := dilV P (eₚ.₂)` (`e` = base standard de `H n`),
  chacune orthonormée sur le bloc `sSlice i₀ := {p | p.1 = i₀}` (immédiat depuis
  `inner_singleL`/`coordL_singleL`/`dilV_isometry`, aucune structure de sous-espace).
- `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` (nouveau, pas identifié
  aux tentatives précédentes) complète CHAQUE famille partielle en une base
  orthonormée COMPLÈTE de `K` (`finrank K = Fintype.card (Fin m × Fin n)` via
  `finrank_euclideanSpace`, version générique — pas besoin du suffixe `_fin`).
- `Orthonormal.equiv` recolle les deux bases complètes en un unique
  `U : K ≃ₗᵢ[ℂ] K`, avec `e := Equiv.refl (Fin m × Fin n)` (même indice des deux
  côtés) ⟹ `U (singleL i₀ (eₖ)) = dilV P (eₖ)` pour tout `k`.
- Conclusion par extensionnalité sur la base standard de `H n` (`Basis.ext`) :
  `U.toLinearMap ∘ₗ singleL i₀ = dilV P`.

**Cause exacte du timeout des tentatives 1/2, confirmée indépendante de
`Submodule`** : composer `(orthonormal_family ...).exists_orthonormalBasis_extension_of_card_eq
...` **inline** dans un `obtain` déclenche le MÊME timeout déterministe au `whnf`
que les tentatives précédentes (vérifié en isolant le phénomène : le premier
`obtain` seul passe, le second — avec `dilV P`, un terme bien plus profond — retimeout).
Le correctif : isoler l'énoncé combiné dans un lemme `private` séparé
(`orthonormalBasisExtension`), appelé ensuite par simple application de fonction aux
deux cas concrets (`singleL n m i₀` et `dilV P`). La leçon générale : quand un
`obtain`/`refine` composant plusieurs lemmes avec métavariables timeout au `whnf`
malgré une preuve mathématiquement immédiate, ne pas insister sur l'inlining —
extraire un lemme intermédiaire à énoncé entièrement explicite (règle 7 CLAUDE.md,
généralisée au-delà des sommes indexées).

- [x] `exists_unitary_extension (P) (i₀) : ∃ U : DilSpace n m ≃ₗᵢ[ℂ] DilSpace n m,
      U.toLinearMap ∘ₗ singleL n m i₀ = dilV P`
- [x] `naimark_projective_form (P) (i₀) : ∃ U, ∀ i x, ⟪x, P.E i x⟫ =
      ⟪U (singleL i₀ x), dilProj i (U (singleL i₀ x))⟫` (forme "ancilla" complète :
      préparation dans le bloc `i₀` + unitaire global + mesure projective)
- [x] `QuantumFoundations/Naimark/Unitary.lean` créé, importé, `lake build` vert
- [x] `#print axioms` : `exists_unitary_extension` et `naimark_projective_form`
      dépendent de `[propext, Classical.choice, Quot.sound]` uniquement
- [x] `guard.sh` : 0 axiome, 0 `native_decide`, 0 sorry (Naimark v1 + N5)

---

## Wigner — plan (stratégie établie avec Fable 5, 2026-07-12)

**Énoncé.** Toute transformation sur les états purs (vecteurs unitaires de `H n`)
qui préserve les probabilités de transition `|⟨φ|ψ⟩|²` est induite par un opérateur
unitaire ou antiunitaire, unique à une phase globale près. Sources : Bargmann,
*Note on Wigner's Theorem on Symmetry Operations* (J. Math. Phys. 1964) — blueprint
principal, quasi « proof-assistant ready » (§3–§5 finitaires, ponctuels, purement
algèbre de produits scalaires) ; Simon et al. — contre-vérification et plan B de
globalisation (Étape 6, invariant `c_jc_k·c_kc_ℓ·(c_jc_ℓ)`), rejeté comme blueprint
principal (trigonométrie sur des cercles de vecteurs, `Real.Angle`, friction connue).

**Verdict Mathlib upstream (scan complet mathlib4 master, juillet 2026, par Fable
5) : terrain totalement libre.** Aucun fichier/déclaration `Wigner`, `antiunitary`,
`Kadison`. Seul actif pertinent : `Mathlib.Analysis.Complex.Isometry`
(`linear_isometry_complex : ∀ f : ℂ ≃ₗᵢ[ℝ] ℂ, f = rotation a ∨ f = conjLIE.trans
(rotation a)`) — un atout optionnel pour W1, pas un précédent. PhysLean/PhysLib et
Lean-QuantumInfo (fusionnés) ne couvrent pas Wigner. Candidat Mathlib de premier
ordre : la machinerie semilinéaire (`≃ₛₗᵢ[starRingEnd ℂ]`) existe sans aucun
théorème qui la peuple côté antiunitaire.

**Formulation retenue — (A) en noyau, (B) en corollaire optionnel (W6).** Rejets
motivés : (C) quotient `Projectivization` — API purement algébrique, aucune API
métrique, tout passerait par des lifts constants pour zéro bénéfice (wrapper
cosmétique possible en W6 optionnel) ; (D) `∃ σ` quantifié sur le `RingHom` —
enfer d'instances `RingHomInvPair` dépendantes, remplacé par une disjonction `∨`
de deux existentiels concrets (les deux types cibles typent, confirmé en stdin).

```lean
theorem wigner (n : ℕ) (T : H n → H n)
    (hT : ∀ x y, ‖x‖ = 1 → ‖y‖ = 1 → ‖⟪T x, T y⟫_ℂ‖ = ‖⟪x, y⟫_ℂ‖) :
    (∃ U : H n ≃ₗᵢ[ℂ] H n,
        ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U x)
  ∨ (∃ U : H n ≃ₛₗᵢ[starRingEnd ℂ] H n,
        ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U x)
```

**Décisions de conception (dans l'ordre d'importance) :**
- **Pas d'hypothèse de bijectivité.** Bargmann §1.2 : l'injectivité au niveau des
  rayons découle de `hT` (Cauchy-Schwarz : deux rayons unités coïncident ssi leur
  produit vaut 1) ; en dimension finie `U` est automatiquement bijectif (isométrie).
  Énoncé strictement plus fort que Simon et al. (qui supposent `Ω` bijective,
  eq. 2.8), exactement le Main Theorem de Bargmann §1.3 spécialisé — à souligner
  dans le README final.
- **`∀ n`, sans seuil.** `n = 0` vacuité, `n = 1` trivial (les deux branches
  marchent, Bargmann §1.4), cœur uniforme pour `n ≥ 2`. Contrairement à Gleason
  (`n ≥ 3`), aucune contrainte de dimension dans le cœur.
- **Construire `U`, jamais étendre `T`.** `U` est défini par une formule fermée
  depuis des données finies (§W3/W5) ; aucun problème d'« extension depuis la
  sphère » n'existe dans cette architecture.
- **`χ` défonctionnalisé.** En interne : fonction nue `χ : ℂ → ℂ` (formule
  d'extraction explicite, W4) + des `Prop`. Bundling en `≃ₗᵢ`/`≃ₛₗᵢ` uniquement à
  la frontière (les deux branches du `rcases` final de W5).
- **Phases = paires `(c : ℂ) + ‖c‖ = 1`**, jamais `Circle`/`unitary ℂ`.
- **`𝒫 = e⊥` comme condition `Prop`** (`⟪e, z⟫ = 0`), jamais le type `Submodule` —
  la leçon Submodule/WithLp de Naimark (N5, tentatives 1-2) s'applique intégralement.
- **(B) en corollaire seulement**, forme `S (rankOne x x) = rankOne (U x) (U x)`
  — jamais `U ∘ P ∘ U⁻¹` (évite toute friction `RingHomCompTriple` avec la
  conjugaison semilinéaire). Réutilise la machinerie `rankOne` déjà éprouvée côté
  `gleason`, fournit le pont « à la Kadison » pour un futur papier.
- **Zéro trigonométrie, zéro angle** — critère qui départage Bargmann (retenu) de
  Simon et al. (rejeté comme blueprint principal, gardé en contre-vérification).

**Compte total attendu : ~24-26 sorry au sortir de W0.** Le seul contenu
mathématique neuf est **W4** (comme `sqrtOp` pour N1) ; W2-W3-W5 sont de la
plomberie disciplinée (comme N2-N3 pour Naimark). Ordre d'attaque :
W0 → W1 → W2 → W3 → W4 → W5 (→ W6). **W1 en premier** car il calibre le niveau de
difficulté réel (`nlinarith`/`Complex.ext` territoriaux) et W4 s'y appuie
entièrement.

### W0 — Squelette (Defs, énoncé principal, Nonvacuity) — ✅ CLOS (2026-07-12)
- [x] Étape 0 validée en stdin (résultats exacts ci-dessous)
- [x] Défs à formules fermées (junk hors domaine, aucune preuve prise en argument —
      pattern `dite` sur `0 < n`/`2 ≤ n`, comme `sqrtOp`) : `e`, `eImg` (=`e'`),
      `InPerp` (=`𝒫`, une `Prop`), `V`, `refVec`, `chidir`, `chi`, `U`,
      `IsWignerMap` — `QuantumFoundations/Wigner/Defs.lean`
- [x] Énoncé principal `wigner` + tous les lemmes de W1-W5 posés en `sorry`.
      Écart au plan, signalé explicitement : cas `n = 0` PROUVÉ directement
      (vacuité — `H 0` est `Subsingleton`, aucun vecteur unitaire) ; cas `n = 1`
      laissé en `sorry` (court et autonome — aucune dépendance sur W1-W5 — mais
      non attaqué à ce stade pour ne pas retarder la validation du squelette).
- [x] Nonvacuity : `T = id` habite la branche unitaire, `T = conjCoords`
      (conjugaison composante par composante, bundlée en isométrie
      conj-semilinéaire via `LinearEquiv.ofBijective` + involutivité) habite la
      branche antiunitaire — **entièrement prouvé, 0 sorry**, aucun fallback
      manuel exotique nécessaire. `QuantumFoundations/Wigner/Nonvacuity.lean`
- [x] `lake build` vert, `guard.sh` : 0 axiome, 0 `native_decide`, **24 sorry**
      (Naimark reste à 0 ; total dépôt 24 — dans la fourchette 24-26 prévue)

**Écart d'architecture, signalé** : namespace `QuantumFoundations.Wigner` (imbriqué),
contrairement au namespace plat `QuantumFoundations` utilisé pour tout Naimark —
délibéré, car les noms internes de Wigner (`e`, `V`, `U`, `chi`) sont génériques et
auraient pollué l'espace de noms plat. `wigner` s'invoque donc
`QuantumFoundations.Wigner.wigner`.

**Fichiers créés** :
```
QuantumFoundations/Wigner/Scalar.lean        W1 : 3 sorry (kit scalaire ℂ)
QuantumFoundations/Wigner/Defs.lean          e, eImg, InPerp, V, refVec, chidir, chi, U, IsWignerMap
QuantumFoundations/Wigner/Bessel.lean        W2 : 2 sorry
QuantumFoundations/Wigner/VConstruction.lean W3 : 6 sorry
QuantumFoundations/Wigner/Core.lean          W4 : 6 sorry (seul contenu mathématique neuf)
QuantumFoundations/Wigner/Main.lean          W5 : 5 sorry + théorème wigner (n=0 prouvé, n=1 et n≥2 sorry)
QuantumFoundations/Wigner/Nonvacuity.lean    0 sorry, témoins id/conjCoords complets
```

**Résultats Étape 0 (stdin, tous confirmés)** :
- `EuclideanSpace.single (i) (a) : EuclideanSpace 𝕜 ι` + `EuclideanSpace.inner_single_left/right`
  — confirmés (noms `PiLp.norm_single`/`PiLp.single_apply` désormais préférés aux
  alias `EuclideanSpace.*` dépréciés).
- `‖1+r‖² = 1+‖r‖²+2Re r` : PAS de lemme direct sous ce nom — dérivé en 2 lignes via
  `Complex.sq_norm` (`‖z‖² = normSq z`) + `Complex.normSq_add` + `Complex.normSq_one`.
- `orthonormal_iff_ite` confirmé (`Orthonormal 𝕜 v ↔ ∀ i j, ⟪v i,v j⟫ = if i=j then 1 else 0`).
- **Bessel-égalité (lemme (9) de Bargmann)** : aucun lemme exporté, mais la preuve de
  `Orthonormal.sum_inner_products_le` (Bessel INÉGALITÉ, `Mathlib.Analysis.InnerProductSpace.Orthonormal`)
  contient EXACTEMENT l'identité inconditionnelle recherchée comme étape interne
  (`hbf : ‖x − Σ⟪vᵢ,x⟫•vᵢ‖² = ‖x‖² − Σ‖⟪vᵢ,x⟫‖²`), non exportée — recette de preuve
  intégralement réutilisable : `norm_sub_sq`, `InnerProductSpace.norm_sq_eq_re_inner`,
  `inner_sum`/`sum_inner`, `inner_smul_left`/`right`, `inner_conj_symm`,
  `Orthonormal.inner_left_right_finset`.
- `LinearMap.injective_iff_surjective [FiniteDimensional K V] {f : V →ₗ[K] V}` confirmé
  (déjà utilisé en N5) — nécessitera la restriction ℝ-linéaire pour la branche
  antiunitaire (conj-semilinéaire ⟹ ℝ-linéaire par restriction des scalaires).
- `LinearIsometryEquiv.mk (toLinearEquiv : E ≃ₛₗ[σ] E₂) (norm_map) : E ≃ₛₗᵢ[σ] E₂` et
  `LinearEquiv.ofBijective (f : M →ₛₗ[σ] M₂) (hf : Bijective f) : M ≃ₛₗ[σ] M₂` — tous
  deux génériques en `σ` (confirmé, testés avec `σ = starRingEnd ℂ` directement sur
  `EuclideanSpace ℂ (Fin n)`), pas de `LinearIsometryEquiv.ofBijective` direct.
- `Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ` et `linear_isometry_complex` confirmés présents
  (`Mathlib.Analysis.Complex.Isometry`, nom RACINE, pas namespacé `Complex.`) —
  gardés en raccourci optionnel de W1, non utilisés dans le squelette (nécessiterait
  d'établir la ℝ-linéarité de `f` au préalable, travail supplémentaire non gratuit).
- `conjCoords` (témoin Nonvacuity) construit intégralement à la main
  (`WithLp.toLp`/`WithLp.ext_iff`, `LinearEquiv.ofBijective` sur son involutivité) —
  **aucun sorry**, pas besoin de fallback plus complexe qu'anticipé.

### W1 — Kit scalaire ℂ (zéro dépendance, dé-risque tout, à prouver en premier) — ✅ CLOS (2026-07-13)
- [x] `re_eq_of_norm_eq : ‖u‖ = ‖v‖ → ‖1+u‖ = ‖1+v‖ → u.re = v.re` — dérivé via
      `Complex.sq_norm`/`Complex.normSq_add`/`Complex.normSq_one` (2 lignes) puis
      `linarith`
- [x] `eq_one_of_norm_one_re_one : ‖u‖ = 1 → u.re = 1 → u = 1` — `normSq u = 1`
      + `re = 1` ⟹ `im² = 0` (`nlinarith`) ⟹ `im = 0` ⟹ `Complex.ext`
- [x] `scalar_dichotomy` : pour `f : ℂ → ℂ` avec `(∀ α, ‖f α‖ = ‖α‖)`, `f 1 = 1`,
      `(∀ α β, (conj (f α) * f β).re = (conj α * β).re)`, alors `f = id ∨ f = conj`
      — Bargmann §4.6 transposé ligne à ligne (Eq A via `α := 1` ; Étape B via
      `Complex.normSq`/`sq_eq_one_iff` ; Étape C via `hre α I`) ; identités clé
      établies en `have` locaux (`reI`, `conjMulSelf`), pas de lemme Mathlib direct
      pour `Re(conj w * I) = w.im` ni `Re(conj z * z) = normSq z` (simp ciblé suffit)
- [x] **Écart signalé** : l'hypothèse `hnorm` (préservation de la norme) s'avère
      INUTILE dans la preuve de `scalar_dichotomy` — confirmé par le compilateur
      (warning unused-variable) et cohérent avec la dérivation Bargmann fournie ;
      gardée dans la signature (renommée `_hnorm`, énoncé inchangé)
- [x] `guard.sh` : 0 axiome, 0 `native_decide`, **21 sorry** (24 − 3)

### W2 — Plomberie produit-scalaire — ✅ CLOS (2026-07-13)
- [x] `bessel_eq_of_norm_sq_eq` (lemme (9) de Bargmann, pièce maîtresse) : famille
      orthonormée finie `g` (`{ι : Type*} [Fintype ι]`, pas seulement `Fin m`),
      `‖u‖² = Σ ‖⟪g p, u⟫‖² → u = Σ ⟪g p, u⟫ • g p` — identité de Bessel avec
      égalité, élimine `exists_orthonormalBasis_extension` du chemin critique,
      aucune extension de base, aucun comptage de cardinal, aucune surjectivité.
      Preuve : `key : ⟪g p,y⟫=⟪g p,u⟫` (effondrement simple) réutilisé pour
      `hyy`/`hyu` (chacun un calcul à somme simple, jamais de double somme
      inlinée) puis `norm_sub_sq` + hypothèse ⟹ `‖u-y‖=0`.
- [x] `orthonormal_image` : moduli `δ_pq` + normes 1 ⇒ `Orthonormal` (cas `p = q` :
      `⟪Tf,Tf⟫ = (↑‖Tf‖:ℂ)²` via `inner_self_eq_norm_sq_to_K`, module 1 ⇒ `‖Tf‖²=1`)
      — signature complétée avec `[DecidableEq ι]` (requis par `orthonormal_iff_ite`,
      ajout d'hypothèse pure, aucune restriction d'usage réelle)
- [x] Bullet « identités d'homogénéité/scaling » du plan initial : ABSORBÉE dans
      `V_colinear` (W3) — pas un lemme séparé, aucun sorry dédié
- [x] `guard.sh` : 0 axiome, 0 `native_decide`, **19 sorry** (21 − 2)

**Piège Lean rencontré et documenté** (dans `Bessel.lean`) : un `rw` ciblant un
terme SANS métavariable (`⟪g p,u⟫` fixe, pas un pattern) réécrit TOUTES ses
occurrences syntaxiques identiques simultanément — après avoir substitué `⟪g p,y⟫`
par `⟪g p,u⟫` via `key p`, le but contenait deux copies syntaxiquement identiques
de `⟪g p,u⟫`, et un `rw [← inner_conj_symm ...]` les a toutes les deux réécrites au
lieu d'une seule (double `conj`). Parade : `mul_comm` puis appliquer le lemme
directement sur `conj(z)*z`, jamais de `rw` ciblant un sous-terme dupliqué sans
métavariable pour le distinguer des autres occurrences identiques.

Frictions de cast `ℝ→ℂ` documentées (non bloquantes mais coûteuses en essais) :
`inner_self_eq_norm_sq_to_K x : ⟪x,x⟫ = ↑‖x‖ ^ 2` élabore en `(↑‖x‖ : ℂ) ^ 2`
(cast AVANT la puissance, pas `↑(‖x‖^2)`) — `simpa`/`simp` gèrent la conversion
`‖(↑r)^2‖ → r^2` sans effort, mais pour re-fermer dans l'autre sens
(`r^2=1 → (↑r)^2=1`), ni `exact_mod_cast` ni `push_cast` seuls n'ont suffi ;
`norm_cast` (normalise vers `↑(r^2)`) suivi d'un `rw [h2]; norm_num` explicite a
fonctionné de façon fiable.

### W3 — Construction de `V` + propriétés de base (Bargmann §3, eqs 11-12a) — CLOS (2026-07-13)
- [x] `inner_eImg_V` : `⟪e', V z⟫ = 0` — calcul direct sur la formule dépliée de
      `V`, `⟪e',e'⟫=1` (`heImg_inner_self`) et `γ⁻¹*γ=1`
- [x] `V_colinear` : **écart signalé et corrigé** — l'énoncé squelette affirmait
      `‖δ‖ = 1`, ce qui est FAUX en général (contre-exemple : `T = id` donne
      `V T z = z`, mais `δ • T(‖z‖⁻¹•z)` a toujours norme 1, donc `‖δ‖=1`
      forcerait `‖z‖=1` pour tout `z ⊥ e`). Corrigé en `‖δ‖ = ‖z‖`, cohérent avec
      `norm_V` et avec le commentaire Bargmann §3.2 déjà présent dans le fichier
      (« `β'` a pour module `‖z‖` », pas nécessairement 1). Preuve : orthonormalise
      `{e, f_z}` (`f_z := ‖z‖⁻¹•z`), pousse via `orthonormal_image` (W2) à
      `{eImg T, T f_z}`, établit l'égalité de Bessel (9, W2) pour `T w` (`w` le
      représentant unitaire de `e+z`) via préservation des probabilités de
      transition sur chaque vecteur de la base, résout pour
      `T w = γ•eImg T + μ•T f_z`, d'où `V T z = (γ⁻¹μ) • T f_z`
- [x] `norm_V` : `‖V z‖ = ‖z‖` — cas `z=0` trivial (`V T 0 = 0` par calcul
      direct), cas `z≠0` via `V_colinear`
- [x] `norm_inner_V` (eq. 11) : `‖⟪Vw,Vx⟫‖ = ‖⟪w,x⟫‖` — preuve directe via
      `V_colinear` (Vw,Vx multiples scalaires de `T` appliqué aux représentants
      unitaires ; `IsWignerMap` donne directement le module du produit scalaire de
      ces images ; les facteurs `‖w‖,‖x‖` s'annulent contre leurs inverses) — PAS
      besoin de repasser par le vecteur bâti sur `e+z`, contrairement à
      l'approche suggérée initialement
- [x] `re_inner_V` (eq. 12) : partie réelle préservée — identité clé
      `⟪Vw,Vx⟫ = (conj γ)⁻¹γ'⁻¹⟪Tw,Tw'⟫ − 1` (les termes croisés `⟪Tw,e'⟫`/
      `⟪e',Tw'⟩` s'annulent EXACTEMENT contre `⟪e',e'⟫=1` en développant
      `V z = γ⁻¹•Tw − e'` sur les deux arguments) ; le module de `⟪Tw,Tw'⟫` se
      calcule en fonction de `⟪w,x⟫` seul (dépendance en `e+z` s'annule
      complètement après simplification), donnant `‖1+⟪Vw,Vx⟫‖ = ‖1+⟪w,x⟫‖` ;
      combiné à eq. 11, `re_eq_of_norm_eq` (W1, `Scalar.lean`) conclut directement
- [x] `inner_V_eq_of_im_eq_zero` (eq. 12a) : égalité exacte si réel — (11)+(12)
      forcent `Im⟪Vw,Vx⟫=0` via `|z|²=Re(z)²+Im(z)²` (même schéma que
      `eq_one_of_norm_one_re_one`, W1)
- [x] `hn : 2 ≤ n` ajouté aux 6 signatures (absent du squelette W0) : pour `n=0`,
      `e n = 0` (valeur poubelle) et `eImg T` peut être nul, auquel cas `γ` peut
      s'annuler et l'inversion `γ⁻¹•Tw` dégénère ; `2 ≤ n` choisi (plutôt que
      `0 < n`, techniquement suffisant pour W3 seul) pour cohérence avec
      `Core.lean` (W4), qui invoquera ces lemmes sous la même hypothèse
- [x] **Écart signalé** : la formule de `V` dans `Defs.lean` n'a PAS de branche
      `dite` séparée pour `z = 0` (contrairement à ce que supposait le plan
      initial) — une seule formule uniforme couvre tous les cas car
      `e n + z ≠ 0` est garanti dès que `n ≥ 1` et `z ⊥ e` (sinon `z = −e n`
      donnerait `⟪e n,z⟫=−1≠0`, contradiction) ; aucun `by_cases z = 0` n'est
      nécessaire dans les dérivations algébriques générales
- [x] `guard.sh` : 0 axiome, 0 `native_decide`, **13 sorry** (16 − 3, cumulé
      19 − 6 sur tout W3)

**Piège Lean rencontré et documenté** (règle 12 CLAUDE.md, généralisé) : déballer
`e n` via `unfold e; rw [dif_pos h0]` (ou `show` explicite de la valeur dépliée)
déclenche un timeout déterministe au `whnf` — la présence d'une instance `NeZero n`
construite localement dans la branche `dite` est coûteuse à unifier lors d'une
réécriture directe. Remède : `simp only [e, dif_pos h0, ...]` referme la même
égalité sans jamais timeout (`simp` gère la réduction du `dite` plus robustement
qu'un `rw`/`show` manuel).

**Diamant d'instances rencontré et documenté** (nouveau, spécifique à
`EuclideanSpace`/`Gleason.H n`) : `inner_self_eq_norm_sq_to_K` produit un terme
`(↑‖x‖ : ℂ) ^ 2` via `RCLike.ofReal` + une instance `SeminormedAddCommGroup`
dérivée de `PiLp.seminormedAddCommGroup`, DIFFÉRENTE (syntaxiquement, bien que
définitionnellement égale) de `Complex.ofReal` + `PiLp.instNorm` utilisée
ailleurs dans les mêmes calculs — un `rw`/`ring`/`exact_mod_cast` ciblant ce terme
échoue silencieusement en laissant un but pourtant affiché comme trivial
(`↑‖z‖ ^ 2 = ↑‖z‖ ^ 2` non fermé par `rfl` implicite). Parade fiable : isoler la
conversion dans un `have` dédié fermé par `rw [inner_self_eq_norm_sq_to_K]; norm_cast`
(le combo `rw` puis `norm_cast`, jamais `exact`/`exact_mod_cast` directement sur le
lemme, ferme le diamant) puis réutiliser ce `have` — jamais raisonner sur le
diamant après coup via `ring`/`field_simp` sur le terme brut.

### W4 — LE cœur : analyse de `V` (Bargmann §4 — l'analogue de `sqrtOp` pour N1) — CLOS (2026-07-13)
- [x] `chidir_dichotomy` : `chidir T f` (f unitaire QUELCONQUE de `𝒫`, pas
      seulement `refVec` — généralisation gratuite) vérifie les hypothèses de
      `scalar_dichotomy` (W1). Deux préliminaires privés : `T_phase` (Étape 1,
      cas d'égalité de Cauchy-Schwarz — `norm_inner_eq_norm_tfae`, index 0↔2 —
      appliqué à `T f, T(c•f)`) et `V_dir_colinear` (Étape 2, généralisée à `f`
      quelconque : `V(α•f) = chidir T f α • V f`, coefficient identifié par
      unicité contre `V f ≠ 0`)
- [x] `chi_dichotomy` : corollaire trivial de `chidir_dichotomy` en `f := refVec`
- [x] `chi_eq_chidir` (globalisation, **écart signalé et résolu** — généralisation
      aux repères NON orthogonaux, cf. note ci-dessous) : `chi T α = chidir T f α`
      pour tout `f` unitaire de `𝒫`, PAS seulement `refVec`
- [x] `V_chi_homogeneous` (18b) : généralise `V_dir_colinear`/`chi_eq_chidir` d'un
      `f` unitaire à un `z` quelconque, via `z = ‖z‖•(‖z‖⁻¹•z)` + `chi_real`
      (`chi` fixe les réels dans les deux branches id/conj)
- [x] `V_additive` (18a) : cas colinéaire direct via `chi_add_real` (`chi(r+a) =
      r+chi(a)`, `r` réel) ; cas général via Gram-Schmidt (`f₂` := composante de
      `z` orthogonale à `f₁ := y/‖y‖`, normalisée) + `V_two_dir` (privé,
      préliminaire clé : `V(a₁f₁+a₂f₂) = chi(a₁)•Vf₁+chi(a₂)•Vf₂` pour `f₁⊥f₂` —
      preuve DIRECTE sans Bessel/`orthonormal_image`, via rigidité
      `eq_of_norm_eq_re_eq` appliquée à `⟪V(a_p f_p), V x⟫`, contrairement à
      l'approche à 3 vecteurs orthonormés envisagée initialement)
- [x] `inner_V_eq_chi_inner` (18c) : réduit au cas unitaire
      (`V_inner_eq_chi_of_unit`, même rigidité que `V_two_dir` mais sans seconde
      direction) via `y = ‖y‖•f₁`, `V_chi_homogeneous`, `chi_mul_real`
      (`chi(r*w) = r*chi(w)`, `r` réel)
- [x] `guard.sh` : 0 axiome, 0 `native_decide`, **7 sorry** (10 − 3, cumulé
      13 − 6 sur tout W4)

**Écart signalé et résolu** (`chi_eq_chidir`, généralisation aux repères non
orthogonaux) : l'argument de Bargmann §4.3-4.5 (`w = f₁+f₂`, comparaison de
coefficients d'un développement de Bessel 2D) ne fonctionne QUE pour des
directions ORTHOGONALES — insuffisant dès que `n ≥ 3` et `f` n'est ni colinéaire
ni orthogonal à `refVec`. Route retenue (après confirmation utilisateur) :
réduire `chi_eq_chidir` à une comparaison en un SEUL point (`i`, où `id` et
`conj` se distinguent), via `chidir_branch_transfer` — pour `f1,f2` unitaires
avec `⟪f1,f2⟫ ≠ 0` (PAS besoin d'orthogonalité), deux vecteurs-test
`c1 := i·a/‖a‖`, `c1' := a/‖a‖` (`a := ⟪f1,f2⟫`) rendent `⟪c1•f1,i•f2⟫` et
`⟪c1'•f1,f2⟫` TOUS DEUX exactement `‖a‖` (réel positif, par construction
algébrique — aucune disjonction réel/non-réel sur `a`), ce qui pilote
`chidir f2` au point `i` via la rigidité `eq_of_norm_eq_re_eq`. Seul cas
dégénéré : `f = -refVec` (colinéaire), traité séparément par
`chidir_colinear_refVec`. 8 lemmes privés au total pour ce seul sorry
(`eq_of_norm_eq_re_eq`, `inner_I_smul_eq_norm`, `inner_smul_eq_norm`,
`chidir_branch_transfer`, `chidir_colinear_refVec`, `eq_branch_of_eq_at_I`,
`chi_real`, `sq_norm_eq_mul_conj`), contre les 2 (`T_phase`, `V_dir_colinear`)
qui ont suffi pour `chidir_dichotomy`/`chi_dichotomy`.

**Pièges Lean rencontrés et documentés** :
- (règle 12 CLAUDE.md, nouvelle instance) appliquer `norm_cast`/`Complex.mul_conj`
  directement à une expression comme `chi T b` (énorme une fois `chidir` déplié
  via `V`/`⟪·,·⟫`) déclenche un timeout `whnf`. Remède : extraire l'identité
  purement `ℂ` dans un lemme `private` à contexte minimal (`sq_norm_eq_mul_conj`)
  — jamais de `generalize` inline dans le gros contexte, ça ne suffit pas à
  éviter le timeout (contrairement à l'attente).
- `rw` sur un but/une hypothèse contenant À LA FOIS une variable `z` et une
  expression `‖z‖` qui en dépend réécrit LES DEUX simultanément dès qu'on
  substitue `z` (`hyf1 : z = ‖z‖•f`), produisant un terme absurde du type
  `‖‖z‖•f‖`. Parade systématique : `conv_lhs => rw [...]` pour restreindre la
  réécriture au seul membre qui doit changer, jamais un `rw` non contraint sur
  un but qui mentionne la norme du terme substitué ailleurs.

### W5 — Assemblage (Bargmann §5) + théorème principal — CLOS (2026-07-13)
- [x] `U_additive`, `U_chi_semilinear` : algèbre directe sur `U a := chi⟪e,a⟫•eImg +
      V(a−⟪e,a⟫•e)`, via `chi_add`/`chi_mul` (NOUVEAUX, généraux sur tout `ℂ` —
      distincts de `chi_add_real`/`chi_mul_real` de W4, qui ne couvrent qu'un
      facteur réel) + `V_additive`/`V_chi_homogeneous` (W4)
- [x] `inner_U_eq_chi_inner` : décomposition standard `⟪a,b⟫ = conj(αₐ)·α_b +
      ⟪zₐ,z_b⟫` + `inner_eImg_V` (W3, les termes croisés s'annulent) +
      `inner_V_eq_chi_inner` (W4) + nouvelle identité `chi_conj_mul`
      (`conj(chi a)·chi b = chi(conj(a)·b)`, vraie dans les deux branches)
- [x] `U_bijective` : **écart avantageux** — contrairement au plan initial, le
      fichier réel sépare `Function.Bijective (U T)` (une simple fonction) du
      bundling en `≃ₗᵢ`/`≃ₛₗᵢ`, reporté à `wigner` lui-même. Injectivité
      BRANCH-INDÉPENDANTE via `U_norm_eq` (`‖Ua‖=‖a‖`, conséquence directe de
      `inner_U_eq_chi_inner` + `chi_real`, valable simultanément dans les deux
      branches). Surjectivité : `rcases chi_dichotomy`, `LinearMap`
      littéral (`{toFun:=U T, map_add':=..., map_smul':=...}` — confirmé
      fonctionner sans constructeur nommé), branche `chi=id` → `→ₗ[ℂ]` direct,
      branche `chi=conj` → `→ₗ[ℝ]` (restriction aux scalaires réels, LA vraie
      inconnue du jalon : confirmé qu'AUCUN lemme semilinéaire direct n'existe
      dans Mathlib, la restriction à ℝ est la seule voie, et
      `LinearMap.injective_iff_surjective` s'applique tel quel avec `K:=ℝ`)
- [x] `exists_phase_U` : confirmé — le cas `⟪e,x⟫=0` est bien GRATUIT (juste
      `V_colinear`, W3, appliqué directement à `x`), aucun Cauchy-Schwarz. Cas
      `⟪e,x⟫≠0` : dérivation complète via `T_phase` (W4) + déballage
      DÉFINITIONNEL de `V ζ` (par `rfl`, aucun lemme dédié nécessaire) +
      `V_chi_homogeneous`
- [x] `wigner` n≥2 : assemblage sans surprise — `LinearEquiv.ofBijective` +
      `LinearIsometryEquiv.mk`, la coercion de l'équivalence bundlée se réduit à
      `U T` par `rfl` (confirmé par test stdin)
- [x] `wigner` n=1 : dérivation AUTONOME (indépendante de W1-W5, `hn:2≤n` jamais
      disponible) — `H 1` de dimension 1 (`H1_eq_inner_smul_e`, via `Fin 1`
      subsingleton), `U₁ x := ⟪e 1,x⟫•eImg T` directement ℂ-LINÉAIRE (pas
      seulement semilinéaire), placé dans la branche `chi=id` par convention
      (Bargmann §1.4 : les deux branches marchent, aucun moyen de les
      distinguer en dimension 1)
- [x] `guard.sh` : 0 axiome, 0 `native_decide`, **0 sorry** (7 − 7, cumulé
      24 − 24 sur tout Wigner) — **THÉORÈME DE WIGNER CLOS**.
      `#print axioms wigner` : `[propext, Classical.choice, Quot.sound]`
      (trio standard du noyau, aucun axiome ajouté)

**Pièges Lean rencontrés et documentés** :
- (RCLike/Complex diamond, 3e occurrence) appliquer `inner_self_eq_norm_sq_to_K`
  DEUX FOIS dans le même `rw ... at h` (une fois sur `⟪Ua,Ua⟫`, une fois sur
  `⟪a,a⟫` niché sous `chi T`) produit des formes syntaxiquement différentes bien
  qu'affichées identiques, cassant tout `rw` ultérieur. Remède définitif :
  isoler CHAQUE application dans son propre `have` fermé par
  `rw [...]; norm_cast`, jamais deux applications dans le même `rw ... at h`.
- Cast : après substitution de `‖e n+ζ‖` (réel) par `‖α‖⁻¹` À L'INTÉRIEUR d'un
  coefficient déjà casté en `ℂ`, le terme obtenu est `(↑(‖α‖⁻¹))⁻¹` (double
  inverse avec cast intercalé) — `inv_inv` seul ne matche pas ; `push_cast`
  avant `inv_inv` pousse le cast à l'intérieur de l'inverse et débloque.
- `simpa using h` peut sur-simplifier un but/une hypothèse de la forme `x^2=1`
  en la disjonction `x=1 ∨ x=-1` (via une lemme `sq_eq_one_iff`-like du simp
  set par défaut) au lieu de la fermer directement contre une hypothèse déjà
  disponible sous forme d'équation — se manifeste de façon inattendue quand
  deux dérivations quasi identiques du MÊME fait sont écrites séparément dans
  des contextes tactiques différents. Remède : fusionner les deux dérivations
  redondantes en une seule plutôt que d'essayer de déboguer la duplication.

### W6 — OPTIONNEL (façon `v2.0-naimark`) — CLOS (2026-07-13), 0 sorry, `QuantumFoundations/Wigner/Uniqueness.lean`

**(A) Exclusivité unitaire/antiunitaire pour `n ≥ 2`** — ✅ implémentée exactement
comme prévu, via l'invariant de rayons `Delta(a,b,c) := ⟪a,b⟫⟪b,c⟫⟪c,a⟫`
(Bargmann §1.5) :
- [x] `delta_transform_lin`/`delta_transform_conj` : invariance/conjugaison de
      `Delta` sous `T`, un lemme par branche CONCRÈTE du théorème `wigner`
      (`≃ₗᵢ[ℂ]` / `≃ₛₗᵢ[starRingEnd ℂ]`) plutôt qu'un `chi` abstrait paramétré
      — écart signalé par rapport au plan initial, voir `ARCHITECTURE_NOTES.md`.
      `conj_isometry_inner` (polarisation complexe) dérivé à la main : aucun
      analogue Mathlib de `LinearIsometryEquiv.inner_map_map` pour `≃ₛₗᵢ[σ]`.
- [x] `bargmann_delta_witness` : témoin explicite fini confirmé par Lean —
      `e₁=e`, `e₂=(e−refVec)/√2`, `e₃=(e+refVec(1−i))/√3` donnent bien
      `Delta = i/6 ∉ ℝ`
- [x] `exclusivity` : assemblage — `i/6 = -(i/6)` donne `i = 0`, contradiction

**(B) Unicité de `U` à phase globale près — version RESTREINTE** (pas le
Théorème 2 complet de Bargmann §6) — ✅ :
- [x] `Defs.lean` fixe `eImg T := T (e n)`, sans paramètre de choix de
      représentant : introduction LOCALE (dans `Uniqueness.lean` seul,
      `Defs.lean` non touché) d'une reconstruction paramétrée `Vp`/`chidirp`/
      `chip`/`Up` avec `eImg` explicite, reliée à `V`/`chi`/`U` par des
      lemmes-pont `rfl` (`V_eq_Vp`, `chi_eq_chip`, `U_eq_Up`)
- [x] `Vp_smul_eImg`, `chip_smul_eImg`, `Up_smul_eImg` : `V`/`chi`/`U` recalculés
      au représentant `λ • eImg` (`‖λ‖ = 1`) valent `λ • V`/`chi`/`λ • U` —
      `chi` INCHANGÉ (pas seulement sa branche), pas de disjonction de cas
- [x] `U_alt_eq_smul` : conclusion, `Up T (λ • eImg T) = λ • U T`
- [x] `guard.sh` : 0 axiome, 0 `native_decide`, **0 sorry**. `#print axioms` sur
      `exclusivity`/`bargmann_delta_witness`/`U_alt_eq_smul` :
      `[propext, Classical.choice, Quot.sound]`

**Non attaqué (hors périmètre, signalé au départ)** : le Théorème 2 complet de
Bargmann §6 (`U'` complètement arbitraire, pas seulement un autre représentant
de `eImg`) demanderait de rederiver l'homogénéité réelle depuis l'additivité +
l'isométrie — non nécessaire pour le cas d'usage réel du dépôt. Corollaire (B)
`rankOne`/wrapper `Projectivization` (mentionné comme basse priorité dans le
plan initial) : non implémenté.

### Ce qui ne bloquera PAS (contrairement aux craintes initiales)
Extension de bases orthonormées (éliminée par le lemme (9) de W2) ; gestion de
phase globale (les phases restent des scalaires LOCAUX `c` avec `‖c‖=1`, jamais un
choix cohérent global à construire) ; quotients (aucun, formulation (A)) ;
linéarité-depuis-métrique (l'additivité de `V` se démontre composante par
composante via (16), jamais extraite d'une hypothèse métrique abstraite).

### Frictions Lean à provisionner (analogues aux leçons Naimark)
Déballage de normes PiLp/WithLp dans les calculs de W3 (`γ⁻¹`, `‖e+z‖`) — mêmes
patterns que sur `gleason`/N0-N3, lemmes `private` à contexte minimal si timeout
`whnf` (règle 12 CLAUDE.md) ; junk values des défs totales (`V` hors `𝒫`, `chi` hors
domaine) — chaque lemme porte ses side conditions, discipline déjà rodée sur
`sqrtOp`/`dilProj`.

---

## Uhlhorn — Corollaire 1.2 de Šemrl (arXiv:2106.06182)

**Énoncé.** En dimension finie `n ≥ 3`, toute application `φ` sur les projections
de rang 1 qui préserve l'orthogonalité DANS UN SEUL SENS (`PQ = 0 ⟹
φ(P)φ(Q) = 0` ; ni injectivité ni surjectivité supposées) est automatiquement une
symétrie de Wigner (`∃ U` unitaire ou antiunitaire, `φ(P) = UPU*`). Source :
Šemrl, *Wigner symmetries and Gleason's theorem*, 2021 (arXiv:2106.06182),
Corollaire 1.2. Réutilise `wigner` (W0–W6, déjà clos) et `Gleason.gleason`
(dépendance épinglée `v1.0-gleason`) comme boîtes noires.

**Découpage de la preuve** (U1–U5, U3a inséré lors de la reconnaissance de U0,
voir ci-dessous) :
- **U1** — corollaire (B) de Wigner (jamais construit jusqu'ici) : `φ` préservant
  `tr(φ(P)φ(Q)) = tr(PQ)` pour toute paire est une symétrie de Wigner. Se déduit
  de `wigner` en choisissant un représentant unitaire par projection.
- **U2** — lemme spectral élémentaire (pure algèbre linéaire) : `E` positif,
  `E ≤ I`, `tr(E) = 1`, `⟨Ex,x⟩ = 1` pour `x` unitaire ⟹ `E = P_x`.
- **U3a** — extension d'une fonction-cadre sur les droites en `ProjMeasure`
  complet (pièce isolée lors de la reconnaissance, voir U0 ci-dessous).
- **U3b** — « Gleason appliqué deux fois » : combine `Gleason.gleason`, U3a et U2.
- **U4** — assemblage : U1 + U3b.
- **U5** — réduction fini-dimensionnelle (comptage de cardinalité) + théorème
  final `uhlhorn_finite_dim`, combiné à U4.

### U0 — Reconnaissance + squelette — ✅ CLOS (2026-07-13)

**Partie A (reconnaissance, obligatoire avant tout code) :**
- [x] `Gleason.gleason {n} (hn : 3 ≤ n) (m : ProjMeasure n) : ∃! ρ, IsDensityOperator ρ
      ∧ ∀ A, m.μ A = bornValue ρ A` — confirmé assez général pour être appliqué à
      un `ProjMeasure` construit depuis `φ_D(P) := tr(D·φ(P))` (`ProjMeasure` est
      un `Prop`-bundle générique sur `Submodule ℂ (H n) → ℝ`, sans référence à un
      contexte Busch/Gleason spécifique)
- [x] Représentation des projections de rang 1 côté `gleason` : AUCUN wrapper
      `rankOne`/structure bundlée — toujours `Submodule ℂ (H n)` (`ProjMeasure`,
      `bornValue`, `projL`) ou l'opérateur `InnerProductSpace.rankOne` de Mathlib
      (déjà utilisé côté Naimark, `sqrtOp`), jamais les deux mélangés dans un
      type dédié
- [x] Signature de `wigner` reconfirmée inchangée depuis W6
- [x] Aucune ébauche de corollaire (B) de Wigner (projection form) préexistante
- [x] API spectrale confirmée : `IsPositiveOp`, `IsEffect T := IsPositiveOp T ∧
      IsPositiveOp (1-T)` (= `0 ≤ T ≤ 1`), `LinearMap.trace`, et surtout
      `Gleason.positive_inner_self_eq_zero` (déjà prouvé côté `gleason`,
      directement réutilisable comme brique centrale de U2)
- [x] **Conception validée** : `Proj1 (n) := {A : Submodule ℂ (H n) //
      finrank ℂ A = 1}` (réutilise `Submodule`, aucun nouveau wrapper) ;
      `IsWignerSymmetryProj`, **Option 1 retenue** — égalité de droites
      `φ(ℂ∙x) = ℂ∙(Ux)`, PAS l'égalité opératorielle littérale `φ(P) = UPU*`
      (Option 2, mathématiquement équivalente pour du rang 1, mais qui aurait
      exigé `LinearMap.adjoint` d'une équivalence semilinéaire — jamais rencontré
      dans ce projet, laissée en remarque pour une passe ultérieure si besoin)
- [x] **Point supplémentaire de reconnaissance, avant le squelette** : audit
      exhaustif des sites de construction d'un `ProjMeasure` dans `gleason`
      (`EffectMeasure.toProjMeasure`, `pureState`) — aucun des deux n'étend une
      fonction-cadre définie seulement sur les droites, tous deux donnent une
      formule fermée directement sur tout sous-espace. **Ce lemme d'extension
      n'existe nulle part dans `gleason-theorem-lean`** : isolé en sous-jalon
      **U3a** à part entière (pas un détail interne de U3b), avec sa propre
      estimation (~100-150 lignes, 4-6 sous-buts). Décision : U3a reste dans
      `quantum-foundations-lean` (namespace `Uhlhorn`), pas dans
      `gleason-theorem-lean` — même générique, on ne rouvre pas le dépôt public
      tagué pour ce besoin

**Partie B (squelette, `QuantumFoundations/Uhlhorn/`) :**
- [x] `Defs.lean` : `Proj1`, `Proj1.mk_unit`, `TraceProd`, `PreservesOrthogonality`,
      `IsWignerSymmetryProj`, `IsFrameFunctionOnLines`, `SendsONBToONB` — 0 sorry
- [x] `WignerProjectionForm.lean` (U1, `wigner_projection_form`) — 1 sorry
- [x] `Spectral.lean` (U2, `eq_projL_of_positive_le_one_trace_one_inner_one`) —
      1 sorry
- [x] `GleasonExtend.lean` (U3a, `exists_projMeasure_of_frameFunctionOnLines`,
      signature complète posée sans sous-découper les 5 sous-buts internes en
      sorries séparés) — 1 sorry
- [x] `GleasonTwice.lean` (U3b, `traceProd_preserved_of_sendsONBToONB`) — 1 sorry
- [x] `Assembly.lean` (U4 `wignerSymmetryProj_of_sendsONBToONB`, U5
      `uhlhorn_finite_dim`) — 2 sorry
- [x] `Nonvacuity.lean` (0 sorry) : témoin `φ := id` habite `PreservesOrthogonality`
      et la branche unitaire de `IsWignerSymmetryProj` (`U := refl`, preuve par
      `rfl`) ; témoin antiunitaire (`conjCoords`) NON immédiat (aurait exigé
      `Submodule.map` pour une équivalence semilinéaire, jamais exercé dans ce
      projet) — écarté conformément à la consigne (un seul témoin suffit)
- [x] `lake build` vert, `guard.sh` : 0 axiome, 0 `native_decide`, **6 sorry**
      (un par jalon U1/U2/U3a/U3b/U4/U5)

**Écart mineur signalé et corrigé** : le premier jet du docstring de
`GleasonExtend.lean` employait littéralement le mot « sorry » pour décrire la
taille estimée du jalon, faisant remonter le compte `guard.sh` à 7 par un faux
positif (le script ne distingue pas commentaires et code) — reformulé en
« sous-buts intermédiaires ».

### U3a — Extension frame function → `ProjMeasure` complet — ✅ CLOS (2026-07-13)

Attaqué en premier, indépendamment du reste (U1/U2/U3b/U4/U5), car c'était la
pièce dont la difficulté réelle restait la plus incertaine à l'issue de la
reconnaissance de U0.

- [x] `gv` (pont `Proj1 n → ℝ` vers `H n → ℝ`, valeur poubelle `0` hors de la
      sphère unité) + `isCFrameFunction_gv` : `gv g` satisfait
      `Gleason.IsCFrameFunction (gv g) 1`
- [x] `orthonormal_stdBasis_coe`/`span_stdBasis_coe` : la base orthonormée
      standard de `↥A` (`stdOrthonormalBasis ℂ A`), coercée dans `H n`, est
      orthonormée et engendre `A` (`LinearIsometry.orthonormal_comp_iff`,
      `Submodule.map_subtype_top`)
- [x] `frameSum` (`μ A := ∑ i, gv g (stdOrthonormalBasis ℂ A i)`) +
      **`frameSum_eq_sum_of_orthonormal_spanning`** (Sous-lemme 1, indépendance
      du choix de base, sous forme générique — tout `Fintype ι` de bon cardinal,
      pas seulement `Fin (finrank A)`, via `Fintype.equivFinOfCardEq` +
      `Equiv.sum_comp`)
- [x] `frameSum_top` (Sous-lemme 3), `frameSum_nonneg` (Sous-lemme 4),
      `frameSum_add_isOrtho` (Sous-lemme 5, via `Sum.elim` — seule concaténation
      de bases construite à la main dans tout le fichier)
- [x] `exists_unit_vector_of_proj1` + `frameSum_proj1` : `μ` coïncide avec `g`
      sur chaque droite
- [x] `exists_projMeasure_of_frameFunctionOnLines` assemblé, 0 sorry
- [x] `guard.sh` : 0 axiome, 0 `native_decide`, **5 sorry** (6 − 1)

**Écart majeur signalé (change la difficulté anticipée du jalon)** : la
stratégie de reconnaissance envisageait de redémontrer l'indépendance de base
(Sous-lemme 1) depuis zéro par concaténation `Fin k ⊕ Fin l → Fin n`
(`finSumFinEquiv`/`Fin.append`). En lisant `Gleason.Complex.RealSections`
(importé transitivement mais jamais lu en détail avant ce jalon), j'ai trouvé
que cet argument y est **déjà entièrement prouvé** sous forme vectorielle :
`Gleason.cframe_sum_invariant` (pour une fonction-cadre `g : H n → ℝ`
satisfaisant `IsCFrameFunction g W`, deux familles orthonormées de même taille
engendrant le même sous-espace donnent la même somme). Stratégie retenue :
pont vers cette machinerie déjà prouvée (`gv`/`isCFrameFunction_gv`) plutôt que
réimplémentation indépendante — la seule concaténation de bases réellement
construite à la main dans tout le fichier est celle de `add_isOrtho` (Sous-lemme
5), sur un périmètre bien plus restreint (juste `A` et `B`) que la construction
générale de l'extension elle-même.

**Piège Lean rencontré et documenté** : `Module.finrank ℂ (A ⊔ B)` (sans
coercion explicite vers le type sous-jacent) fait échouer l'élaboration
(`failed to synthesize instance Max Type`) — Lean pousse le type attendu `Type`
dans l'application de `⊔` avant de réaliser qu'il doit d'abord élaborer
`A ⊔ B : Submodule ℂ (H n)` puis coercer le résultat. Remède systématique :
écrire `Module.finrank ℂ ↥(A ⊔ B)` avec la coercion `↥` explicite dès que
l'argument de `Module.finrank`/toute fonction attendant un `Type` est une
expression composée (pas une simple variable) construite avec un opérateur de
treillis sur des `Submodule`.

### U1 — Corollaire (B) de Wigner en langage de projections — ✅ CLOS (2026-07-13)

Attaqué juste après U3a, indépendamment de U2/U3a/U3b : `wigner_projection_form`
ne dépend que de `wigner` (W0–W6, déjà clos) et de `TraceProd`/`Proj1`
(`Defs.lean`), pas de `Gleason.gleason` ni de `ProjMeasure`.

- [x] `projL_singleton_unit` (privé) : `projL (ℂ∙x) y = ⟪x,y⟫•x` pour `x`
      unitaire, via `Submodule.starProjection_singleton`
- [x] **Étape 1** `traceProd_mk_unit_eq` : `TraceProd (mk_unit x) (mk_unit y) =
      ‖⟪x,y⟫‖²` — `bornValue_span_singleton` a suffi tel quel une fois
      `projL_singleton_unit` établi, aucun lemme intermédiaire supplémentaire
- [x] **Étape 2** `T`/`T_unit`/`T_repr` : construction de `T : H n → H n` par
      choix (`Classical.choose`) d'un représentant unitaire canonique de
      `φ (mk_unit x hx)`, via `exists_unit_vector_of_proj1`
- [x] **Étape 3** `isWignerMap_T` : `T` satisfait `IsWignerMap`, en appliquant
      l'Étape 1 dans les deux sens autour de l'hypothèse `hφ` (préservation de
      `TraceProd`), puis `a²=b² ∧ a,b≥0 ⟹ a=b` par `nlinarith`
      (`sq_nonneg (a-b)`/`sq_nonneg (a+b)`)
- [x] **Étape 4-5** `wigner_projection_form` : `rcases wigner n T (isWignerMap_T
      hφ)`, reconstruction de `IsWignerSymmetryProj φ` par égalité de droites
      (`Submodule.span_singleton_smul_eq`, `c ≠ 0` depuis `‖c‖=1`) dans les deux
      branches, symétriques
- [x] `guard.sh` : 0 axiome, 0 `native_decide`, **4 sorry** (5 − 1)

**Écart signalé (décision de l'Étape 0, point 3)** : `exists_unit_vector_of_proj1`
est nécessaire à la fois ici (U1) et dans U3a (`GleasonExtend.lean`, où il était
`private`). Plutôt que (a) l'y rendre public et importer tout
`GleasonExtend.lean` dans `WignerProjectionForm.lean` (créerait une dépendance
de fichier de U1 — censé être indépendant du reste — vers U3a), ou (b) le
redupliquer localement, **relocalisé dans `Defs.lean`** (public, partagé) — une
troisième option non listée explicitement dans les deux proposées, jugée
meilleure des deux : aucune duplication, aucune dépendance de fichier
superflue. `GleasonExtend.lean` mis à jour en conséquence (suppression de la
copie `private`, aucun changement de preuve).

### U2 — Lemme spectral élémentaire — ✅ CLOS (2026-07-14)

Pure algèbre linéaire, indépendant de `Gleason.gleason`/`wigner`/U3a. Stratégie
de référence directement inspirée de Šemrl §2 (preuve de la Claim) : `E` fixe
`x`, puis décomposition bloc `[[1,0],[0,T]]` sur `H = span{x} ⊕ x⊥`.

- [x] `one_le_of_norm_eq_one` (privé) : `‖x‖=1 ⟹ 1 ≤ n` (`H 0` est
      `Subsingleton`)
- [x] **Sous-lemme 1** `E_fixes_x` : `E x = x`, via
      `Gleason.positive_inner_self_eq_zero` appliqué à `1 - E` (positif par
      `hE.2`, symétrique — `IsPositiveOp` bundle déjà `LinearMap.IsSymmetric`
      comme première composante, confirmé en Étape 0, aucune dérivation séparée
      d'auto-adjonction nécessaire) au point `x` : `⟪(1-E)x,x⟫ = ⟪x,x⟫-⟪Ex,x⟫ =
      1-1 = 0` (`hEx` étant directement une égalité COMPLEXE `= 1`, pas
      seulement sa partie réelle — aucun chemin détourné nécessaire)
- [x] **Assemblage final** `eq_projL_of_positive_le_one_trace_one_inner_one` :
      `x` complété en base orthonormée COMPLÈTE de `H n`
      (`exists_orthonormalBasis_extension_complex`, déjà utilisé côté
      Naimark/Gleason, indexée directement par `Fin n` via `Fin.castLE` — pas
      de nouvelle gymnastique d'index), trace décomposée autour de la position
      de `x` (`LinearMap.trace_eq_sum_inner` + `Finset.add_sum_erase`) : le
      terme en `x` vaut `1`, la trace totale vaut `1`, donc le reste de la
      somme est nul ; chaque terme restant est positif (symétrie + positivité
      de `E`), une somme de positifs nulle force chaque terme à `0`
      (`Finset.sum_eq_zero_iff_of_nonneg`), d'où `E (b i) = 0` pour `i` autre
      que la position de `x` (`Gleason.positive_inner_self_eq_zero` appliqué à
      `E` directement, PAS à une restriction). Conclusion par décomposition de
      tout `z` sur la base (`OrthonormalBasis.sum_repr'`)
- [x] `guard.sh` : 0 axiome, 0 `native_decide`, **3 sorry** (4 − 1)

**Écart majeur signalé (change l'architecture de l'assemblage final)** : ni
`LinearMap.restrict` ni un « Sous-lemme 3 » générique (« opérateur positif de
trace nulle est nul ») n'ont été nécessaires — ce dernier n'existe d'ailleurs
pas dans `gleason-theorem-lean` (recherché en Étape 0, absent). La décomposition
de la trace autour de `x` donne DIRECTEMENT `E (b i) = 0` pour chaque `i` autre
que la position de `x`, en appliquant `positive_inner_self_eq_zero` à `E`
complet — sans jamais introduire d'opérateur restreint à `x⊥`. Conséquence : le
« Sous-lemme 2 » (stabilité de `x⊥`, `⟪x,Ey⟫=0` pour `y⊥x`) prévu dans la
stratégie de référence s'avère inutile et n'est jamais invoqué.

`projL_singleton_unit` (nécessaire ici ET dans U1) relocalisé de
`WignerProjectionForm.lean` (`private`) vers `Defs.lean` (public, partagé) —
même pattern que `exists_unit_vector_of_proj1`/U1.

### U3b, U4, U5 — non attaqués

Squelette posé (voir U0 ci-dessus), preuves non commencées. U3b dépend de U2
(clos) et U3a (clos) ; U4 dépend de U1 (clos) et U3b ; U5 dépend de U4 seul.