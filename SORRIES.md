# SORRIES.md — quantum-foundations-lean

Suivi de l'avancement, sur le modèle de gleason-theorem-lean. Coché = `lake build`
vert, 0 axiome (guard.sh), commit + push fait. Sources : Watrous *TQI* Thm 2.42
(cœur), Paris §3.2 Thm 4 (contexte physique, N5 optionnel).

Compte total attendu (Naimark, hors N5) : **13 sorry** au sortir de N0 — **0 sorry**
restant depuis la clôture de N3, et toujours **0 sorry** après clôture de N5
(optionnel) le 2026-07-11. Wigner (W0) ajoute **24 sorry** le 2026-07-12 (dépôt
total : 24) — **21 sorry** après clôture de W1 le 2026-07-13.

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

### W2 — Plomberie produit-scalaire
- [ ] Lemme (9) de Bargmann (pièce maîtresse) : famille orthonormée finie `g`,
      `‖u‖² = Σ ‖⟪g p, u⟫‖² → u = Σ ⟪g p, u⟫ • g p` (identité de Bessel avec égalité
      — élimine `exists_orthonormalBasis_extension` du chemin critique, aucune
      extension de base, aucun comptage de cardinal, aucune surjectivité requise)
- [ ] Images T-orthonormées : moduli `δ_pq` + normes 1 ⇒ `Orthonormal` (cas `p = q` :
      `⟪Tf,Tf⟫` réel ≥ 0 de module 1 ⇒ = 1)
- [ ] Identités d'homogénéité/scaling (remplace l'extension aux rayons de Bargmann §2)

### W3 — Construction de `V` + propriétés de base (Bargmann §3, eqs 11-12a)
- [ ] `V z := γ⁻¹ • T w − e'` où `w := ‖e+z‖⁻¹ • (e+z)`, `γ := ⟪e', T w⟫` (formule
      directe) — préférer les formes multiplicatives croisées dans les hypothèses
      (`γ • V z = T w − γ • e'`) plutôt que des `⁻¹` dans les buts
- [ ] `⟪e', V z⟫ = 0` ; `‖V z‖ = ‖z‖` ; colinéarité définitionnelle
      `V z = δ • T(‖z‖⁻¹ • z)`
- [ ] (11) `‖⟪Vw,Vx⟫‖ = ‖⟪w,x⟫‖` ; (12) partie réelle préservée ; (12a)
      `⟪Vw,Vx⟫ = ⟪w,x⟫` si réel

### W4 — LE cœur : analyse de `V` (Bargmann §4 — l'analogue de `sqrtOp` pour N1)
- [ ] `chidir f α := ⟪V f, V (α • f)⟫` (extraction directionnelle) ; (14) module,
      (15)(15a)(15b) identités de partie réelle
- [ ] Repère adapté à la paire : case split sur la dépendance LINÉAIRE (PAS sur
      `n`) ; Gram-Schmidt à la main `f₂ := normalisé de (z − ⟪f₁,z⟫•f₁)` — le cas
      `n = 2` est absorbé automatiquement (la dépendance y est forcée), aucune
      disjonction `n = 2` vs `n ≥ 3` dans le cœur
- [ ] Formule d'expansion (16) : coefficients `a'_p = χ_p(a_p)` via vecteurs tests
      `f_p•(conj a_p)⁻¹` + (12a) + rigidité (W1)
- [ ] `χ₂ = χ₁` via `w = f₁ + f₂` ; globalisation : `χdir` constant sur toutes les
      directions
- [ ] `chi := chidir ref` ; dichotomie `χ = id ∨ χ = conj` [application directe de
      `scalar_dichotomy`, W1]
- [ ] (18) : `V` additive, `V` χ-homogène, `⟪Vy,Vz⟫ = χ⟪y,z⟫` sur `𝒫`

### W5 — Assemblage (Bargmann §5) + théorème principal
- [ ] `U a := χ⟪e,a⟫ • e' + V(a − ⟪e,a⟫•e)` ; additivité, χ-semilinéarité,
      `⟪Ua,Ub⟫ = χ⟪a,b⟫` (calcul de deux lignes, `Vz ⊥ e'`)
- [ ] Compatibilité `∀ x` unitaire `∃ c` : cas `⟪e,x⟫ ≠ 0` par calcul direct ; cas
      `⟪e,x⟫ = 0` GRATUIT (colinéarité définitionnelle de W3 — aucun Cauchy-Schwarz
      nécessaire ici, contrairement à l'inquiétude initiale)
- [ ] Bijectivité : injectif (isométrie) → surjectif. Piège anticipé :
      `injective_iff_surjective` sur un endomorphisme conj-semilinéaire — parade :
      restreindre en ℝ-linéaire (une application conj-semilinéaire est ℝ-linéaire),
      faire la bijectivité en ℝ-linéaire sur l'espace ℝ-fini-dimensionnel, puis
      rapatrier ; aucune coordonnée nécessaire
- [ ] Bundling des deux branches ; `theorem wigner` ; dispatch `n ≤ 1`

### W6 — OPTIONNEL (façon `v2.0-naimark`)
- [ ] Unicité à phase globale près (Bargmann §6, Théorème 2, `dim ≥ 2` — ratio
      `τ(a)` constant via le déterminant de Gram (invariant) + additivité)
- [ ] Exclusivité unitaire/antiunitaire pour `n ≥ 2` via l'invariant de rayons
      `Δ(a₁,a₂,a₃) := ⟪a₁,a₂⟫⟪a₂,a₃⟫⟪a₃,a₁⟫` (Bargmann §1.5 — témoin explicite fini :
      `e₁=e`, `e₂=(e−f)/√2`, `e₃=(e+f(1−i))/√3` donnent `Δ = i/6 ∉ ℝ`, donc aucun
      unitaire et antiunitaire ne peuvent induire la même action sur les rayons dès
      `n ≥ 2` ; échoue en `n = 1`, comme attendu — calcul fini explicite)
- [ ] Corollaire (B) `rankOne` ; wrapper `Projectivization` éventuel (basse priorité)

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