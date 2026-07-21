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
(2026-07-13), **3 sorry** après clôture de U2 (2026-07-14), **2 sorry** après
clôture de U3b (2026-07-14), **1 sorry** après clôture de U4 (2026-07-14),
**0 sorry** après clôture de U5 (2026-07-14) — **Corollaire 1.2 de Šemrl
intégralement prouvé, 0 axiome, 0 sorry sur tout le dépôt.**

BornRule (B1–B4, 2026-07-14) : chaque jalon écrit directement en preuve
complète (skeleton-sorry-first non nécessaire, comme pour W6) — **0 sorry
introduit, 0 sorry sur tout le dépôt tout au long du développement.**
`grainCoherenceTheorem` intégralement prouvé, `Gleason.gleason` importé
comme vrai théorème (plus un axiome séparé comme dans l'ancien
`tstar-born-rule-lean`). `Nonvacuity.lean` (2026-07-15) comble l'écart
signalé lors de l'audit de clôture : `E₀ v` satisfait simultanément les
quatre axiomes (Grain)/(Norm)/(Pos)/(Null) — 0 sorry introduit.
Le corollaire `grainCoherenceTheorem_projector` est ajouté le 2026-07-20 et
publié sous `v2.1-bornrule` : simple forme projecteur du théorème final, sans
hypothèse ni contenu mathématique indépendant supplémentaire. Son audit ne
dépend que de `[propext, Classical.choice, Quot.sound]`.

Histories (K0, 2026-07-16) ajoute **5 sorry** (squelette Defs/Nonvacuity à
0 sorry + K1/K2/K3 en sorry ; estimation initiale 5-7, réduite par deux
factorisations paramétrées documentées dans les fichiers eux-mêmes) —
**3 sorry** après clôture de K1 (2026-07-16), **2 sorry** après clôture de
K2 (2026-07-16), **0 sorry** après clôture de K3 (2026-07-16) —
**théorème des inférences contraires de Kent intégralement prouvé, 0
axiome, 0 sorry sur tout le dépôt (cinq blocs).**

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

### U3b — L'argument « Gleason appliqué deux fois » — ✅ CLOS (2026-07-14)

Cœur du papier de Šemrl. Consomme U2 et U3a comme boîtes noires (aucune preuve
interne rouverte).

- [x] **Sous-lemme 0** `isEffect_of_isDensityOperator` (absent de
      `gleason-theorem-lean`, confirmé en reconnaissance) : positivité + trace
      `1` en dimension finie force `≤ 1`. Dérivé via `density_inner_le_one`
      (même décomposition de trace autour d'un point que U2) puis
      `sub_nonneg_of_density` (homogénéité pour passer d'un vecteur unitaire à
      un vecteur quelconque)
- [x] **Sous-lemme 2** `exists_density_born_eq` (première application de
      `Gleason.gleason`) : pour `D` densité fixée, `P ↦ bornValue D (φP)` est
      une `IsFrameFunctionOnLines` — nonneg via `hD.nonneg`, somme à `1` via
      `LinearMap.trace_eq_sum_inner D b'` sur la base `b'` (complète, garantie
      par `SendsONBToONB`) — U3a donne un `ProjMeasure`, `Gleason.gleason`
      donne `E` avec `bornValue D (φP) = bornValue E P` pour tout `P`
- [x] `traceProd_self_eq_one`, `isDensityOperator_projL_of_proj1` (utilitaires
      courts : `projL` d'une droite est une densité, via
      `Submodule.starProjection_isSymmetric`/`Submodule.re_inner_starProjection_nonneg`
      /`InnerProductSpace.trace_rankOne`)
- [x] **Sous-lemme 3 + assemblage** `traceProd_preserved_of_sendsONBToONB` : fixe
      `P` (premier argument du but), applique Sous-lemme 2 à `D := projL(φP)`,
      spécialise en `P` lui-même (`bornValue E P = TraceProd(φP)(φP) = 1`), en
      déduit (via U2) `E = projL P`, réinjecte en `Q` :
      `TraceProd(φP)(φQ) = bornValue D (φQ) = bornValue E Q = TraceProd P Q`
- [x] `guard.sh` : 0 axiome, 0 `native_decide`, **2 sorry** (3 − 1)

**Écart signalé** : le « Sous-lemme 1 » de la stratégie de reconnaissance
(résolution de l'identité comme identité D'OPÉRATEURS,
`∑ i, projL (ℂ ∙ (b i)) = 1`, via `Gleason.projL_sup_of_pairwise_isOrtho`)
s'est avéré **non nécessaire**. `LinearMap.trace_eq_sum_inner` donne
directement la trace de `D` comme somme sur N'IMPORTE QUELLE base orthonormée
— en particulier la base `b'` image de `φ` — sans jamais former explicitement
l'opérateur `∑ i, projL (ℂ ∙ (b' i))`.

`one_le_of_norm_eq_one` (nécessaire ici ET dans U2) relocalisé de
`Spectral.lean` (`private`) vers `Defs.lean` (public, partagé) — même pattern
que `projL_singleton_unit`/`exists_unit_vector_of_proj1`.

### U4 — Assemblage direct de U1 et U3b — ✅ CLOS (2026-07-14)

Jalon délibérément court : `wigner_projection_form` (U1) prend en hypothèse
exactement ce que `traceProd_preserved_of_sendsONBToONB` (U3b) produit.

- [x] `wignerSymmetryProj_of_sendsONBToONB (hn) (φ) (hφ : SendsONBToONB φ) :
      IsWignerSymmetryProj φ := wigner_projection_form n φ
      (traceProd_preserved_of_sendsONBToONB hn φ hφ)` — compile du premier
      coup, aucun ajustement de signature nécessaire
- [x] `guard.sh` : 0 axiome, 0 `native_decide`, **1 sorry** (2 − 1)

Aucun écart, aucun nouveau contenu mathématique — composition directe comme
anticipé.

### U5 — Réduction fini-dimensionnelle — ✅ CLOS (2026-07-14) — **COROLLAIRE 1.2 DE ŠEMRL CLOS**

Dernier jalon du projet Uhlhorn : réduit `PreservesOrthogonality` (orthogonalité
préservée dans un seul sens, ni injectivité ni surjectivité supposées) à
`SendsONBToONB` par un argument de comptage de cardinalité, puis conclut via U4.

- [x] **Sous-lemme A** (dans `sendsONBToONB_of_preservesOrthogonality`) : pour
      une base orthonormée `b`, les représentants unitaires choisis
      (`exists_unit_vector_of_proj1`) des images `φ(mk_unit(b i))` forment une
      famille orthonormée `x` — `PreservesOrthogonality` transporte
      l'orthogonalité de `b i ⊥ b j` (`⟪bi,bj⟫=0`) vers `x i ⊥ x j`, via
      l'aller-retour produit-scalaire-nul ↔ sous-espaces orthogonaux
      (`Submodule.isOrtho_span` pour convertir vers les droites,
      `Submodule.isOrtho_iff_inner_eq` + `Submodule.mem_span_singleton_self`
      pour reconvertir)
- [x] **Sous-lemme B** : une famille orthonormée de cardinal `n = finrank (H n)`
      forme automatiquement une base orthonormée COMPLÈTE
      (`basisOfOrthonormalOfCardEqFinrank` puis `Module.Basis.toOrthonormalBasis`)
      — **point d'incertitude principal du jalon, résolu favorablement** : les
      deux constructeurs préservent les valeurs POINTWISE
      (`coe_basisOfOrthonormalOfCardEqFinrank`/`Module.Basis.coe_toOrthonormalBasis`,
      tous deux `@[simp]`), donnant `b' i = x i` exactement — pas seulement à
      un reindexing près. Aucun lemme de compatibilité supplémentaire
      nécessaire, contrairement à ce que la reconnaissance envisageait comme
      risque principal
- [x] `uhlhorn_finite_dim := wignerSymmetryProj_of_sendsONBToONB hn φ
      (sendsONBToONB_of_preservesOrthogonality hn φ hφ)` (U4, assemblage direct)
- [x] `guard.sh` : 0 axiome, 0 `native_decide`, **0 SORRY sur tout le dépôt**.
      `#print axioms uhlhorn_finite_dim` /
      `wignerSymmetryProj_of_sendsONBToONB` : `[propext, Classical.choice,
      Quot.sound]`

Aucun écart par rapport à la stratégie de reconnaissance — le seul risque
identifié (comportement du constructeur `OrthonormalBasis` vis-à-vis des
valeurs pointwise) s'est résolu dans le cas le plus favorable dès le premier
essai. Cérémonie de clôture (tag, README, résumé chiffré) : objet d'un prompt
dédié, sur le modèle de ce qui a été fait pour le bloc Naimark+Wigner.
## BornRule — Théorème de Cohérence de Grain (« 𝒢 » des articles compagnons)

**Énoncé.** Reformalisation du théorème principal de « Deriving the Born Rule
from Grain Coherence and Dynamical Stability » (article informel « T* »,
renommé « 𝒢 »/*Grain Coherence Theorem* dans les articles — renommage HORS
SCOPE de ce développement Lean, voir « Hors scope » ci-dessous). Pour une
« perspective » `D` (partition de `H n` en cellules orthogonales non nulles)
et une cellule `c` de `D`, une règle d'estimation `Est` satisfaisant (Grain),
(Norm), (Pos) et, pour un vecteur unitaire `v` fixé, (Null), vérifie
`Est D c = ∑ᵢ ‖⟪v, fᵢ⟫‖²` sur toute base orthonormée `(fᵢ)` de `c` — la règle
de Born, en toute généralité, dérivée SANS supposer `Est` a priori de la forme
d'une trace. Source : prototype `tstar-born-rule-lean`
(`theorem1_general_en.lean`, `axiom gleason`) ; ce développement remplace
l'axiome par une vraie application de `Gleason.gleason` (dépendance épinglée
`v1.0-gleason`) et réutilise au maximum l'infrastructure Uhlhorn (U2, U3a).

**Découpage de la preuve** (B1–B4) :
- **B1** — scaffolding : `Perspective`, `Refines`, `AxGrain`/`AxNorm`/`AxPos`/
  `AxNul`, `lemma4_noncontextual` (non-contextualité, conséquence de (Grain)
  seule), `basisPerspective`, `cellLines`, `refinePerspective`.
- **B2** — pont vers Gleason : `g : Proj1 n → ℝ` construit directement via
  `Perspective.binary`, `IsFrameFunctionOnLines g`, puis U3a
  (`exists_projMeasure_of_frameFunctionOnLines`) et la vraie `Gleason.gleason`.
- **B3** — pinning : un opérateur densité qui s'annule sur l'orthogonal d'un
  vecteur unitaire `v` est exactement `projL (ℂ∙v)`, via décomposition de
  trace + U2 (`eq_projL_of_positive_le_one_trace_one_inner_one`).
- **B4** — assemblage : `hker_derivation` (relie (Null) à l'hypothèse abstraite
  de B3), `full_rho_facts` (une seule application de Gleason combinant B2+B3),
  `grainCoherenceTheorem` (théorème final).

### B1 — Perspective.lean (scaffolding) — ✅ CLOS (2026-07-14)

**Partie A (reconnaissance, obligatoire avant tout code) :**
- [x] `inner_conj_symm (x y : E) : (starRingEnd 𝕜) ⟪y, x⟫_𝕜 = ⟪x, y⟫_𝕜` —
      signature exacte confirmée en stdin (piège récurrent du projet : sens
      des arguments « inversé » par rapport à l'intuition naïve)
- [x] `Submodule.sup_orthogonal_of_hasOrthogonalProjection : K ⊔ Kᗮ = ⊤` et
      `Submodule.span_range_eq_iSup` confirmés en stdin : ferment directement,
      sur `H n`, les deux replis `first | ... | sorry` du prototype
      (`Perspective.binary.span`, `basisPerspective.span`) — zéro but ouvert,
      y compris en position de repli, contrairement au prototype qui en
      laisse deux non fermés
- [x] Décision de conception validée : reformulation directe pour
      `V := H n` (pas d'espace abstrait `V` générique) — `Gleason.gleason` est
      spécifique à `H n`, et `Module.finrank ℂ (H n) = n` (`simp`) élimine une
      couche de cast pour les bases de l'espace entier
- [x] Port complet : `Perspective`, `Refines`, `Perspective.unique_parent`,
      `Perspective.binary`, `Perspective.singleton_of_mem_top`,
      `AxGrain`/`AxNorm`/`AxPos`/`AxNul`, `lemma4_noncontextual`,
      `line_ne_bot`/`line_ne_top`/`line_injective`, `basisPerspective`,
      `cellLines` (+ 6 lemmes de spec), `refinePerspective` (+ 2 lemmes)
- [x] `guard.sh` : 0 axiome, 0 `native_decide`, 0 sorry (écrit directement en
      preuve complète, comme W6)

**Écarts signalés** (portage, 3 corrections trouvées en stdin) :
- `open scoped Classical` omis dans la première ébauche (nécessaire pour
  `Finset.filter (· ≤ c)`, présent dans le prototype)
- `inner_conj_symm` : ordre des arguments inversé par rapport à une lecture
  naïve du fallback `first | ... | ...` du prototype (qui couvrait les deux
  ordres par prudence) — fixé aux 4 occurrences après confirmation stdin
- `inner_self_eq_norm_sq_to_K` sur un sous-type `↥c` : `rw` nu échoue
  (unification), nécessite une instanciation explicite `(𝕜 := ℂ)` via `have`
  avant `rw` — fixé aux 2 occurrences
- `guard.sh` faux positif sur le mot « sorry » dans le docstring du module
  (même classe de bug que `GleasonExtend.lean` en Uhlhorn) — reformulé

### B2 — GleasonBridge.lean (remplace l'axiome) — ✅ CLOS (2026-07-14)

- [x] `g (hn2 : 2 ≤ n) (P : Proj1 n) : ℝ := Est (Perspective.binary (P:Submodule)
      _ _) (P:Submodule)` — écart favorable : construit directement sur
      `Proj1 n`, sans `gline` vectoriel intermédiaire (le prototype construit
      `gline` en premier). Bien défini car ne dépend que de la droite, jamais
      d'un représentant unitaire
- [x] `g_isFrameFunctionOnLines` : positivité directe depuis (Pos) ;
      somme-à-1 via `lemma4_noncontextual` (bascule vers `basisPerspective`) +
      `line_injective` (réindexation de la somme)
- [x] `exists_rho` : U3a (`exists_projMeasure_of_frameFunctionOnLines`) donne
      un `ProjMeasure`, puis la VRAIE `Gleason.gleason` donne `ρ` — remplace
      intégralement `axiom gleason` et `exists_rho` de l'ancien fichier
- [x] `guard.sh` : 0 axiome, 0 sorry. `#print axioms exists_rho` /
      `g_isFrameFunctionOnLines` : `[propext, Classical.choice, Quot.sound]`
      — `gleason` n'apparaît JAMAIS comme axiome séparé

**Écarts signalés** : reformulation `∀ x, ∀ hx, ...` (au lieu de
`∀ x, ‖x‖=1 → ...`) pour éviter un échec de recherche d'assumption anonyme
(assumption sur `‖x‖ = 1` non nommée) ; `guard.sh` faux positif sur le mot
« axiom » dans un docstring décrivant l'ancien prototype — reformulé (séparer
le mot-clé `axiom` de son nom `gleason` par une virgule au lieu de les
accoler).

**Relocalisation** (commit séparé) : `isEffect_of_isDensityOperator` (+
`density_inner_le_one`, `sub_nonneg_of_density`), `private` dans
`Uhlhorn/GleasonTwice.lean` (U3b), migré public vers `Uhlhorn/Defs.lean` —
nécessaire depuis B3 (`Pinning.lean`), même pattern de relocalisation que
`exists_unit_vector_of_proj1`/`projL_singleton_unit`/`one_le_of_norm_eq_one`
lors de U1/U2/U3a.

### B3 — Pinning.lean (identification de ρ) — ✅ CLOS (2026-07-14)

- [x] `eq_projL_of_vanishes_on_orthogonal` : un opérateur densité qui s'annule
      sur l'orthogonal d'un vecteur unitaire `v` est exactement `projL (ℂ∙v)`.
      Complète `v` en base orthonormée adaptée
      (`exists_orthonormalBasis_extension_complex`, déjà utilisé 3× dans
      Uhlhorn), décompose la trace pour obtenir `⟪ρv,v⟫ = 1`, applique
      directement U2 via `isEffect_of_isDensityOperator`
- [x] `guard.sh` : 0 axiome, 0 sorry. `#print axioms` :
      `[propext, Classical.choice, Quot.sound]`

**Écart favorable majeur** : le prototype reconstruit `lam = 1` via une
identité de Parseval/Bessel sur une base orthonormée QUELCONQUE
(`symmetric_pos_zero_of_diag_zero` + ~100 lignes). Ici, en partant de
l'hypothèse « `ρ` s'annule sur `v⊥` » (forme forte, pas seulement partie
réelle nulle) et en complétant `v` en base ADAPTÉE, la décomposition de trace
donne directement `⟪ρv,v⟫ = 1`, et U2 conclut l'égalité opératorielle COMPLÈTE
en une seule application — sans jamais reformuler l'argument de Parseval. Le
pas « diagonale nulle ⟹ `ρw = 0` » (`Gleason.positive_inner_self_eq_zero`) est
repoussé à B4, qui en a de toute façon besoin pour dériver `hker` depuis
(Null).

### B4 — Assembly.lean (théorème final) — ✅ CLOS (2026-07-14)

- [x] `hker_derivation` : dérive l'hypothèse `hker` de B3 depuis `AxNul`, via
      un recalibrage `w → u := w/‖w‖`. Écart favorable : le recollement
      `g(w) = g(u)` est un simple `congrArg`/`Subtype.ext` sur l'égalité de
      droites `ℂ∙w = ℂ∙u` — PAS une nouvelle application de
      `lemma4_noncontextual` comme dans le prototype (`gline` y recalculait un
      `Perspective.binary` distinct à chaque vecteur, nécessitant Lemme 4 pour
      recoller deux perspectives ; `g` étant une fonction ordinaire de
      `Proj1 n`, deux arguments égaux donnent des images égales sans argument
      de non-contextualité). Écart supplémentaire découvert en écrivant la
      preuve : ni `‖v‖=1` ni (Grain)/(Norm) ne sont nécessaires pour ce
      lemme — hypothèses retirées de la signature
- [x] `full_rho_facts` : une seule application de `Gleason.gleason` (B2)
      fournit un `ρ` à la fois `projL(ℂ∙v)` (B3 + `hker_derivation`) ET
      compatible avec `g` sur tout vecteur unitaire
- [x] `grainCoherenceTheorem` : théorème final, nommé exactement ainsi (PAS
      `𝒢` comme identifiant Lean — voir docstring). Assemblage via
      `refinePerspective`/`refine_filter_eq_cellLines` (B1, déjà prouvés — pas
      de nouveau contenu de comptage nécessaire ici, contrairement au
      prototype qui les développe au même endroit que B4)
- [x] `grainCoherenceTheorem_projector` (`v2.1-bornrule`, 2026-07-20) :
      corollaire public direct `Est D c = ‖projL c v‖²`. La somme produite par
      `grainCoherenceTheorem` est identifiée à la norme carrée de la projection
      via `sum_sq_projL_of_pairwise_isOrtho (cellLines c)`, `cellLines_sSup`,
      `cellLines_sum_eq` et `projL_singleton_unit`; aucune nouvelle hypothèse
      ni duplication d'une longue preuve de Parseval
- [x] `guard.sh` : 0 axiome, 0 `native_decide`, 0 sorry sur tout le dépôt.
      `#print axioms grainCoherenceTheorem` /
      `grainCoherenceTheorem_projector` / `full_rho_facts` /
      `hker_derivation` : `[propext, Classical.choice, Quot.sound]` —
      `gleason` n'apparaît JAMAIS comme axiome séparé, contrairement à
      `tstar-born-rule-lean` où `#print axioms theorem1_general` liste en plus
      `gleason`.

Aucun écart de fond par rapport à la stratégie de reconnaissance — les deux
écarts favorables (recollement par `congrArg` plutôt que Lemme 4 ;
hypothèses `hv`/(Grain)/(Norm) superflues dans `hker_derivation`) ont été
découverts en écrivant la preuve, pas anticipés en reconnaissance.

### Nonvacuity — la règle de Born satisfait les 4 axiomes — ✅ CLOS (2026-07-15)

Comble l'écart signalé lors de l'audit de clôture (dérogation à la règle
absolue 3 de `CLAUDE.md`, `BornRule` étant alors le seul bloc du dépôt sans
`Nonvacuity.lean`) : `E₀ v D c := ‖projL c v‖²` (règle de Born pour un
vecteur unitaire `v` fixé, ignore `D` — comme `g` en B2) satisfait
SIMULTANÉMENT `AxGrain`, `AxNorm`, `AxPos`, `AxNul` —
`grainCoherenceTheorem` n'est donc pas vacuement vrai.

- [x] **`refine_filter_sup_eq`** (Lemme 3, généralise `refine_filter_eq_cellLines`
      de B1 à un raffinement `D'` ARBITRAIRE plutôt qu'au seul
      `refinePerspective D` canonique) : les cellules de `D'` sous `c`
      couvrent exactement `c`. Direction non triviale (`c ≤ sup`) via
      résolution de l'identité restreinte à `D'.cells`
      (`Gleason.projL_sup_of_pairwise_isOrtho`) : tout `x ∈ c` s'écrit comme
      somme de ses projections sur les cellules de `D'`, celles hors de `c`
      (parent ≠ `c` dans `D`, via `unique_parent`) contribuant 0 car
      orthogonales à `c`
- [x] **`norm_sq_sum_of_pairwise_orthogonal`** (privé) : théorème de
      Pythagore fini par expansion bilinéaire directe du produit scalaire
      (`sum_inner`/`inner_sum` + collapse diagonal via `Finset.sum_eq_single`)
- [x] **`sum_sq_projL_of_pairwise_isOrtho`** (privé) : combine résolution de
      l'identité et Pythagore fini — additivité de `‖projL · v‖²` sur une
      famille orthogonale de cellules
- [x] `E₀_isPos`, `E₀_isNul` : immédiats (positivité d'un carré ;
      `Submodule.starProjection_apply_eq_zero_iff` pour l'annulation)
- [x] `E₀_isNorm`, `E₀_isGrain` : applications directes de
      `sum_sq_projL_of_pairwise_isOrtho`, respectivement à `D.cells` (sup `=
      ⊤` via `D.span`) et à `D'.cells.filter (· ≤ c)` (sup `= c` via
      `refine_filter_sup_eq`)
- [x] `E₀_satisfies_axioms`, témoin combiné, plus un `example`
      d'inhabitation concrète sur `H 3`
- [x] `guard.sh` : 0 axiome, 0 `native_decide`, 0 sorry sur tout le dépôt.
      `#print axioms` sur les 32 déclarations porteuses de contenu de
      `BornRule` (25 précédentes + 7 nouvelles) : `[propext, Classical.choice,
      Quot.sound]`, sans exception

**Coût réel** (répond explicitement à la question posée en reconnaissance) :
`Gleason.projL_sup_of_pairwise_isOrtho` (résolution de l'identité comme
identité D'OPÉRATEURS pour une famille finie orthogonale) était DÉJÀ
disponible dans `gleason-theorem-lean` (`Gleason/Operator.lean`, O2a(ii)) —
PAS re-dérivée ici, contrairement à ce que U3b avait initialement anticipé
puis jugé inutile pour son propre besoin (résolution via `bornValue`
directement). Le théorème de Pythagore fini sur `‖·‖²` (plutôt que sur
`bornValue`, seul cas déjà couvert côté `gleason-theorem-lean` via
`bornValue_sum_of_pairwise_isOrtho`) était en revanche absent tel quel et a
dû être dérivé ici (`norm_sq_sum_of_pairwise_orthogonal`, ~15 lignes,
expansion bilinéaire directe — pas une reconstruction lourde).

### Hors scope (extensions futures possibles, pas des manques de ce jalon)

- **Une seconde route de dérivation, indépendante de Gleason** : via un
  axiome de stabilité dynamique plutôt que de cohérence de grain. Ce
  développement couvre UNIQUEMENT la route descriptive (Gleason).
- **La convergence intersubjective entre observateurs** comme corollaire du
  théorème principal : non attaquée.

### Comparaison avec `tstar-born-rule-lean`

| | `tstar-born-rule-lean` (`theorem1_general_en.lean`) | `quantum-foundations-lean` (`BornRule`) |
|---|---|---|
| Espace | `V` abstrait (dimension finie) | `H n := EuclideanSpace ℂ (Fin n)` directement |
| Gleason | `axiom gleason` (non prouvé) | `Gleason.gleason` — vrai théorème, dépendance épinglée |
| Axiomes de `theorem1_general`/`grainCoherenceTheorem` | `propext, Classical.choice, Quot.sound, gleason` | `propext, Classical.choice, Quot.sound` |
| `pinning` | environ 100 lignes (Parseval/Bessel sur base quelconque) | environ 45 lignes (décomposition de trace sur base adaptée + U2) |
| Recalibrage de `hker_derivation` | `lemma4_noncontextual` (deux perspectives `binary` distinctes à recoller) | `congrArg`/`Subtype.ext` (fonction ordinaire de `Proj1 n`) |
| Replis (`Perspective.binary.span`, `basisPerspective.span`) | `first`/`sorry` (2 sorry potentiels) | fermés directement, 0 sorry |
| Sorries | 2 (repliés) | 0 |

**Conclusion : strictement plus fort** — mêmes résultats mathématiques (même
énoncé final, `grainCoherenceTheorem` équivalent à `theorem1_general`), un
axiome de moins (`gleason` prouvé plutôt que postulé), et une preuve plus
courte à plusieurs endroits grâce à la réutilisation de l'infrastructure
Uhlhorn (U2, U3a) et à la conception `Proj1`-first de `g`.

## Histories — Théorème des inférences contraires de Kent

**Énoncé.** Kent, *Quasiclassical Dynamics in a Closed Quantum System*, PRL 78,
2874 (1997), arXiv:gr-qc/9604012 : dans le cadre des histoires cohérentes en
dimension finie, deux ensembles cohérents d'histoires peuvent partager la
même préparation `ψ` et la même post-sélection `F`, tout en impliquant
chacun avec CERTITUDE une proposition différente, ces deux propositions
étant mutuellement ORTHOGONALES. Un étage temporel d'un ensemble d'histoires
EST une `Perspective` (`BornRule/Perspective.lean`) — réutilisée telle
quelle, sans redéfinition (confirmé en reconnaissance K0). Le théorème de
profusion générique de Dowker–Kent (J. Stat. Phys. 82, 1575 (1996),
comptage de paramètres/dimensions de variétés) est explicitement HORS SCOPE
de ce bloc — voir « Hors scope » ci-dessous.

**Découpage de la preuve** (K0–K3) :
- **K0** — squelette : `History`, `IsHistoryOf`, `chainOp` (produit ordonné
  des `projL`, dernier étage appliqué en dernier), `decFunctional`
  (conj-linéaire à gauche, `k` conjugué), `IsConsistent`, `histProb` ;
  `Nonvacuity.lean` (toute `Perspective`, vue comme famille à un étage, est
  cohérente) — 0 sorry, prouvé immédiatement (règle absolue 3).
- **K1** — `Basic.lean` : `decFunctional_last_stage_orthogonal` (deux
  histoires différant au dernier étage ont une fonctionnelle de décohérence
  automatiquement nulle) et `histProb_additivity_two_stage` (Pythagore fini,
  écho d'`AxGrain`).
- **K2** — `Witness.lean` : le témoin explicite de Kent en `H 3` (`ψ₀`, `φ₀`
  non normalisés, `P i := ℂ∙(e i)`, `F := ℂ∙φ₀`), `S_consistent`.
- **K3** — `ContraryInferences.lean` : `inference` (certitude conditionnelle,
  formulée sans quotient) et `contrary_inferences` (théorème final).

### K0 — Defs.lean + Nonvacuity.lean + squelette K1-K3 — ✅ CLOS (2026-07-16)

- [x] Reconnaissance (Partie A) : `Perspective`/`Perspective.binary`
      réutilisables tels quels ; `projL_singleton_unit` (Uhlhorn/Defs.lean)
      confirmé pour vecteur unitaire, et `Submodule.starProjection_singleton`
      (Mathlib) confirmé pour la formule générale non-unitaire (ratio,
      évite `Real.sqrt`) ; `LinearMap.adjoint_inner_left/right` confirmés
      (convention conj-linéaire à gauche) ; auto-adjonction/idempotence de
      `projL` dérivables en une ligne (`Submodule.starProjection_isSymmetric`,
      `Submodule.isIdempotentElem_starProjection`) — pas de contenu
      « histories »/« decoherence functional » préexistant (grep exhaustif).
- [x] `History (n L : ℕ) := Fin L → Submodule ℂ (H n)`, `IsHistoryOf`,
      `chainOp` (`Fin.foldl`, vérifié `Fin.foldl_succ_last`/`Fin.foldl_zero`
      pour `L = 1, 2`), `decFunctional`, `IsConsistent`, `histProb`
- [x] `isConsistent_single_stage` : 0 sorry, immédiat par orthogonalité des
      cellules d'une `Perspective`
- [x] Relocalisation PRÉALABLE (commit dédié) : `norm_sq_sum_of_pairwise_orthogonal`
      et `sum_sq_projL_of_pairwise_isOrtho`, `private` dans
      `BornRule/Nonvacuity.lean`, migrés public vers `BornRule/Perspective.lean`
      — faits géométriques génériques sur `Perspective`, pas spécifiques au
      témoin de Born de B-Nonvacuity, nécessaires à K1(b). Même pattern de
      relocalisation que `exists_unit_vector_of_proj1`/`projL_singleton_unit`
      (Uhlhorn) et `isEffect_of_isDensityOperator` (BornRule/B2).
- [x] Squelette K1 (2 sorry), K2 (1 sorry), K3 (2 sorry) — écart vs
      l'estimation initiale (3+2+2=7) justifié par deux factorisations
      paramétrées (voir K2/K3 ci-dessous)
- [x] `guard.sh` : 0 axiome, 0 `native_decide`, 5 sorry (K0 lui-même : 0)

**Écart signalé** : `guard.sh` compte `\bsorry\b` par grep naïf, y compris
dans les docstrings — les premières versions des fichiers K1-K3 discutaient
la discipline « squelette-sorry-first » en utilisant littéralement le mot
« sorry » en prose, faisant gonfler le compte à 13. Convention du dépôt
(confirmée : zéro occurrence ailleurs) : ne jamais écrire le mot en
commentaire, utiliser « but ouvert » — corrigé avant le commit K0.

### K1 — Basic.lean — ✅ CLOS (2026-07-16)

- [x] `decFunctional_last_stage_orthogonal` : via un lemme privé
      `chainOp_mem_last` (la classe d'opérateurs d'une histoire à `L+1`
      étages tombe toujours dans la cellule du dernier étage,
      `Fin.foldl_succ_last` déroulé une fois)
- [x] `histProb_additivity_two_stage` : même recette que `E₀_isNorm`
      (BornRule/Nonvacuity.lean) — `sum_sq_projL_of_pairwise_isOrtho`
      (désormais public) + résolution de l'identité (`D1.span`,
      `projL ⊤ = id`)
- [x] `guard.sh` : 3 sorry restants (K2, K3(a), K3(b))

**Écart signalé** : le troisième but prévu par la feuille de route
(auto-adjonction/idempotence de `projL`) supprimé — dérivable en une ligne
depuis Mathlib/gleason (reconnaissance A.2), jamais cité comme lemme séparé
faute d'un second consommateur avant K2/K3.

### K2 — Witness.lean — ✅ CLOS (2026-07-16)

- [x] Données explicites en `H 3` : `e i := EuclideanSpace.single i 1`,
      `ψ₀ := e0+e1+e2`, `φ₀ := e0+e1-e2` (non normalisés — toute la
      contrariété se lit sur des rapports où `1/√3` s'annule), `P i := ℂ∙(e i)`,
      `F := ℂ∙φ₀`
- [x] **CORRECTION D'ÉNONCÉ (règle 2 du projet).** Le squelette K0 énonçait
      `S_consistent (i : Fin 3)` SANS restriction sur `i`. Faux pour
      `i = 2` : l'annulation clé `⟪φ₀, ψ₀ - e i⟫ = 1 - ⟪φ₀, e i⟫` ne s'annule
      que pour `i ∈ {0,1}` (`⟪φ₀,e 0⟫ = ⟪φ₀,e 1⟫ = 1` mais `⟪φ₀,e 2⟫ = -1`,
      `φ₀` porte un signe négatif sur `e2`). Ajout de l'hypothèse
      `i = 0 ∨ i = 1`, seul domaine où le témoin est utilisé.
- [x] `S_consistent` : par `decFunctional_last_stage_orthogonal` (K1a),
      seules les paires différant à l'étage 0 restent à examiner. Cœur du
      calcul : `P_proj_psi0` (`projL (P i) ψ₀ = e i`), `projL_compl`
      (`projL Aᗮ = 1 - projL A`, via `Submodule.starProjection_orthogonal'`),
      `w_ortho` (le vecteur `w := ψ₀ - e i` est orthogonal à la fois à `e i`
      et à `φ₀` — cette dernière est L'ANNULATION CLÉ), `projL_proj_absorb`
      (absorption via auto-adjonction + idempotence). Les 4 cas résiduels
      (`c1 ∈ {F, Fᗮ}` × ordre de `{P i, (P i)ᗮ}`) se ferment tous via
      `w_ortho_projLc1_u`/`u_ortho_projLc1_w`.
- [x] **Écart vs la feuille de route** : un seul but ouvert paramétré
      (`S_consistent (i : Fin 3)`) plutôt que deux (`S₁_consistent`/
      `S₂_consistent`) — option explicitement autorisée par le plan « si la
      duplication est lourde ». `S1_consistent`/`S2_consistent` l'instancient
      sans sorry supplémentaire.
- [x] `guard.sh` : 2 sorry restants (K3(a), K3(b))

**Point de friction simp documenté** : `simp` non contraint réécrit
spontanément `⟪x,x⟫_ℂ` en `‖x‖²` (lemme par défaut) — dans les calculs de
normes, garder les rewrites `inner_self_eq_norm_sq_to_K` (ou l'expansion
bilinéaire complète) APRÈS l'expansion, jamais avant, sinon le calcul se
bloque sur une forme déjà repliée.

### K3 — ContraryInferences.lean — ✅ CLOS (2026-07-16)

- [x] **CORRECTION D'ÉNONCÉ (règle 2), même cause qu'en K2** :
      `inference (i : Fin 3)` restreint à `i = 0 ∨ i = 1`, même annulation
      en défaut à `i = 2`.
- [x] `inference` : branche `(P i)ᗮ` puis `F` de probabilité NULLE
      (annulation clé `w_ortho`, réutilisée depuis `Witness.lean` — rendue
      publique à cette occasion), branche `P i` puis `F` de probabilité NON
      NULLE (`projL F (e i) = (1/‖φ₀‖²) • φ₀ ≠ 0`, via le nouveau lemme
      public `φ₀_norm_sq` et `φ₀_ne_zero`)
- [x] `contrary_inferences` : assemblage mécanique, terme anonyme direct à
      partir de `P_ortho`, `S_consistent 0/1` (K2) et `inference 0/1` (K3a)
      — confirmé en reconnaissance avant l'écriture du squelette, aucune
      mathématique nouvelle à la fermeture
- [x] Rendus publics dans `Witness.lean` (nécessaires à K3, précédemment
      `private`) : `projL_compl`, `P_proj_psi0`, `projL_F_eq`, `w_ortho`,
      `chainOp_two_stage`, `phi0_inner_e01`, et le nouveau `φ₀_norm_sq`
- [x] `guard.sh` : 0 axiome, 0 `native_decide`, 0 sorry sur tout le dépôt
      (cinq blocs). `#print axioms` sur les 36 déclarations porteuses de
      contenu de `Histories` : `[propext, Classical.choice, Quot.sound]`,
      sans exception, y compris à travers la chaîne à trois niveaux
      Histories → BornRule (`Perspective`, `projL_sup_of_pairwise_isOrtho`
      relocalisé) → Uhlhorn/Gleason externe.

### Hors scope (extensions futures possibles, pas des manques de ce jalon)

- **Le théorème de profusion générique de Dowker–Kent** (J. Stat. Phys. 82,
  1575 (1996)) : comptage de paramètres montrant que la contrariété du
  témoin K2 n'est pas un cas isolé mais générique dans l'espace des
  ensembles cohérents — non attaqué, EXPLICITEMENT exclu par la demande
  initiale de ce bloc.
- **La cohérence faible** (partie réelle de `decFunctional` seulement,
  plutôt que la cohérence medium/forte utilisée ici) : mentionnée en
  docstring (`Defs.lean`), non formalisée.
- **La « single-framework rule » de Griffiths** (réponse usuelle à
  l'objection de Kent) : mentionnée en note de neutralité
  (`ContraryInferences.lean`), non formalisée — c'est un argument
  interprétatif, pas un énoncé mathématique supplémentaire à prouver.

---

## English translation

# SORRIES.md — quantum-foundations-lean

Progress tracking, following the model of gleason-theorem-lean. Checked = lake build
green, 0 axioms (guard.sh), commit + push completed. Sources: Watrous TQI Thm 2.42
(core), Paris §3.2 Thm 4 (physical context, optional N5).

Expected total count (Naimark, excluding N5): 13 sorry upon completion of N0 — 0 sorry
remaining since the completion of N3, and still 0 sorry after the completion of N5
(optional) on 2026-07-11. Wigner (W0) adds 24 sorry on 2026-07-12 (repository
total: 24) — 21 sorry after completion of W1, 19 sorry after completion of W2,
13 sorry after completion of W3, 7 sorry after completion of W4,
0 sorry after completion of W5 (2026-07-13) — Wigner's theorem fully
proved, 0 axioms, 0 sorry throughout the repository. W6 (optional, (A)+(B)) completed on
2026-07-13 without ever introducing any sorry (each lemma written directly with a
complete proof, skeleton-sorry-first unnecessary given the size of the steps) —
0 sorry throughout the repository, including W6.

Uhlhorn (U0, skeleton) adds 6 sorry on 2026-07-13 (repository total: 6) —
5 sorry after completion of U3a (2026-07-13, addressed first because it was the
most uncertain component after reconnaissance), 4 sorry after completion of U1
(2026-07-13), 3 sorry after completion of U2 (2026-07-14), 2 sorry after
completion of U3b (2026-07-14), 1 sorry after completion of U4 (2026-07-14),
0 sorry after completion of U5 (2026-07-14) — Šemrl's Corollary 1.2
fully proved, 0 axioms, 0 sorry throughout the repository.

BornRule (B1–B4, 2026-07-14): each milestone written directly with a complete
proof (skeleton-sorry-first unnecessary, as for W6) — 0 sorry
introduced, 0 sorry throughout the repository during the entire development.
grainCoherenceTheorem fully proved, with Gleason.gleason imported
as an actual theorem (rather than as a separate axiom as in the former
tstar-born-rule-lean). Nonvacuity.lean (2026-07-15) closes the gap
identified during the final audit: E₀ v simultaneously satisfies the
four axioms (Grain)/(Norm)/(Pos)/(Null) — 0 sorry introduced.
The corollary grainCoherenceTheorem_projector was added on 2026-07-20 and
released under v2.1-bornrule: it is simply the projector form of the final theorem,
with no additional assumption or independent mathematical content. Its audit
depends only on [propext, Classical.choice, Quot.sound].

Histories (K0, 2026-07-16) adds 5 sorry (Defs/Nonvacuity skeleton with
0 sorry + K1/K2/K3 containing sorry; initial estimate 5–7, reduced by two
parameterized factorizations documented in the files themselves) —
3 sorry after completion of K1 (2026-07-16), 2 sorry after completion of
K2 (2026-07-16), 0 sorry after completion of K3 (2026-07-16) —
Kent's contrary-inferences theorem fully proved, 0
axioms, 0 sorry throughout the repository (five blocks).

---

## N0 — Skeleton (Defs, SqrtOp, DilSpace, Main, Nonvacuity)
- [x] Step 0 validated: spectral signatures, existing square roots,
 and choice of dilation space (nested K₁ PiLp vs flat K₂) settled.
 Decisions: (b) no CFC.sqrt shortcut retained — in-house spectral
 construction (eigenvectorBasis + rankOne), faithful to the project's
 LinearMap convention and to the internal pattern of
 ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.
 (d) K₂ := EuclideanSpace ℂ (Fin m × Fin n) retained over K₁ (equal proof
 friction, but a single flat index and fewer WithLp/.ofLp layers).
- [x] POVM n m defined (reuses IsPositiveOp from gleason)
- [x] Nonvacuity: uniform POVM (n=2, m=2) proved inhabited
- [x] Skeleton compiles, 13 sorry, 0 axioms, CI/guard.sh adapted to the new name

## N1 — sqrtOp (the only new mathematical content)
- [x] sqrtOp_isPositive : IsPositiveOp T → IsPositiveOp (sqrtOp T)
- [x] sqrtOp_mul_self : IsPositiveOp T → sqrtOp T ∘ₗ sqrtOp T = T
 (extensionality on the eigenbasis, no double sum; 3 private auxiliary
 lemmas: sqrtOp_apply, sqrtOp_apply_basis, eigenvalues_nonneg)
- [x] 11 sorry remaining, lake build green, guard.sh: 0 axioms

## N2 — Building blocks of the dilated space K
- [x] Step 0 validated: LinearMap.adjoint exists between two distinct
 finite-dimensional Hilbert spaces (E →ₗ[𝕜] F, with
 [FiniteDimensional 𝕜 E] and [FiniteDimensional 𝕜 F] separately) —
 confirmed in stdin, with no Mathlib restriction to endomorphisms (only
 gleason's IsSymmetric is endomorphism-only, but it is unnecessary here
 except for dilProj).
- [x] inner_singleL : ⟪singleL i x, w⟫ = ⟪x, coordL i w⟫
- [x] adjoint_singleL : adjoint (singleL i) = coordL i (via LinearMap.eq_adjoint_iff)
- [x] adjoint_coordL : adjoint (coordL i) = singleL i (auxiliary lemma added,
 proved via LinearMap.adjoint_adjoint, not assumed for free)
- [x] coordL_singleL : coordL i ∘ₗ singleL j = if i = j then id else 0
- [x] dilProj_isSymmetric
- [x] dilProj_idempotent
- [x] dilProj_orthogonal : i ≠ j → dilProj i ∘ₗ dilProj j = 0
- [x] dilProj_sum_eq_one : ∑ i, dilProj i = 1 (resolution of the identity via
 Finset.sum_ite_eq, with no dedicated Pi/PiLp reconstruction lemma required)
- [x] 4 sorry remaining (N3 only), lake build green, guard.sh: 0 axioms

## N3 — The dilation (Watrous Thm 2.42)
- [x] Step 0 validated: adjoint conventions confirmed (adjoint_inner_left,
 adjoint_inner_right, adjoint_comp, map_sum for the adjoint of a finite
 sum) — cited, not rederived.
- [x] key1, key2: single-sum pivots (never a double sum; see rule 7 in
 CLAUDE.md / lesson from riesz_rep_assembly)
- [x] dilV_isometry : adjoint (dilV P) ∘ₗ dilV P = LinearMap.id
- [x] naimark_dilation : ∀ i, adjoint (dilV P) ∘ₗ dilProj i ∘ₗ dilV P = P.E i
- [x] theorem naimark (direct assembly of the preceding two results)
- [x] naimark_born (statistical corollary: the probabilities coincide)
- [x] 0 sorry remaining in Naimark v1, lake build green, guard.sh: 0 axioms,
 0 native_decide (latent bug fixed: grep with no match under
 set -e -o pipefail terminated the script precisely upon reaching 0 sorry)

## N4 — Completion
- [x] SORRIES.md updated, #print axioms checked:
 QuantumFoundations.naimark and QuantumFoundations.naimark_born depend
 only on [propext, Classical.choice, Quot.sound]
- [x] README: statement, documented difference from Watrous (direct sum vs ⊗),
 explicit mention of AI assistance
- [x] git tag v1.0-naimark, push --tags

## N5 — OPTIONAL: unitary/ancilla version (Paris Thm 4 / Watrous Cor. 2.43) — ✅ CLOSED
It required a nontrivial lemma that was not available at the time: extension of a
partial isometry H n →ₗ K to a global unitary on K. Paris's sketch
("identity on the orthogonal complement of ω_B") was insufficient as stated — see
CLAUDE.md. Resolved on attempt 3 (below) through an approach that uses no
Submodule, different from both Paris's sketch and the initial plan for
attempts 1/2.

Attempt of 2026-07-11 (30-minute budget, inconclusive — stopped as a precaution,
NO sorry added, nothing committed for N5). Search for Mathlib building blocks:
no direct “extend isometry to unitary” lemma found, but the construction route
is clear and rests on building blocks that DO EXIST:
- Submodule.orthogonalDecomposition (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
 E ≃ₗᵢ[𝕜] WithLp 2 (K × Kᗮ) (Mathlib.Analysis.InnerProductSpace.ProdL2) — decomposes
 the ambient space into the L² product of the subspace and its orthogonal complement.
- Orthonormal.equiv {v : Basis ι 𝕜 E} (hv) {v' : Basis ι' 𝕜 E'} (hv') (e : ι ≃ ι') :
 E ≃ₗᵢ[𝕜] E' (Mathlib.Analysis.InnerProductSpace.Orthonormal) — constructs a
 linear isometry between two spaces from two orthonormal bases indexed by
 equivalent types.
- stdOrthonormalBasis 𝕜 A : OrthonormalBasis (Fin (finrank 𝕜 A)) 𝕜 A — provides a
 canonical orthonormal basis indexed by Fin k for any subspace.

Proof plan (not implemented): let A ≤ K be the domain subspace (A ≅ H n via
singleL 0, for example) and B := range V₀ its isometric image. dim A = dim B
(isometry) ⟹ dim Aᗮ = dim K - dim A = dim K - dim B = dim Bᗮ ⟹ via
stdOrthonormalBasis + Orthonormal.equiv (with e := Equiv.refl (Fin k)), an
isometry Aᗮ ≃ₗᵢ Bᗮ. Gluing V₀ : A ≃ₗᵢ B and this isometry via
orthogonalDecomposition A and orthogonalDecomposition B (both ≃ₗᵢ WithLp 2 (_ × _ᗮ))
yields the desired unitary on K.

Why the attempt stopped here: the assembly (corestriction of V₀ to its range as a
LinearIsometryEquiv, navigation through WithLp 2 (_ × _), final gluing) is a
substantial proof component in its own right — the WithLp/.ofLp friction already
encountered in N0–N3 for much simpler statements suggested that actual completion
would far exceed the allotted 30 minutes.

Attempt 2 of 2026-07-11 (60-minute budget, inconclusive — stopped, no sorry or
broken code committed). New architecture: direct orthogonal projections
(Submodule.orthogonalProjectionOnto), without orthogonalDecomposition/WithLp.
Step 0 confirmed in stdin:
- Submodule.HasOrthogonalProjection: automatic instance for every subspace
 of a finite-dimensional space — OK.
- Submodule.orthogonalProjectionOnto (K) : E →L[𝕜] ↥K (orthogonalProjection is
 deprecated, an alias for orthogonalProjectionOnto); direct decomposition obtained via
 Submodule.starProjection_add_starProjection_orthogonal + starProjection_apply
 (K.starProjection v = ↑(K.orthogonalProjectionOnto v)), NOT through a single
 ready-made lemma under that exact name.
- Submodule.norm_sq_eq_add_norm_sq_projection (x) (S) [HasOrthogonalProjection] :
 ‖x‖² = ‖S.orthogonalProjectionOnto x‖² + ‖Sᗮ.orthogonalProjectionOnto x‖² — Pythagoras,
 name confirmed.
- LinearMap.injective_iff_surjective [FiniteDimensional K V] {f : V →ₗ[K] V} :
 Injective f ↔ Surjective f — confirmed (Mathlib.LinearAlgebra.FiniteDimensional.Basic).
- No LinearIsometryEquiv.ofBijective; the correct building block is
 LinearIsometryEquiv.ofSurjective (f : F →ₛₗᵢ E) (hf : Surjective f) : F ≃ₛₗᵢ E, and
 to construct a LinearIsometry from a LinearMap + a norm proof:
 LinearIsometry.mk (toLinearMap) (∀ x, ‖toLinearMap x‖ = ‖x‖).
- LinearIsometry.equivRange (f : F →ₛₗᵢ E) : F ≃ₛₗᵢ (LinearMap.range f.toLinearMap)
 exists (corestriction of an isometry to its range) — confirmed.
- Orthonormal.equiv/stdOrthonormalBasis: unchanged (attempt 1).

Obstruction encountered — not mathematical, but a Lean PERFORMANCE issue: as early as N5-1/N5-2
(expected to be mechanical), composing two LinearIsometryEquiv values obtained via
.equivRange with .symm.trans on subspaces defined by
LinearMap.range (...).toLinearMap (A := range(singleL i₀), B := range(dilV P))
causes a deterministic timeout at whnf (maxHeartbeats), even when raised to
1,000,000 and then 4,000,000 — the elaborator appears to attempt deeply unfolding
these definitions when type-checking the composition, without completing in a
reasonable time. An alternative approach was tested successfully: construct the
projectors proj_B := dilV P ∘ₗ adjoint(dilV P) directly as endomorphisms of
K (the standard VV* formula for the orthogonal projection onto range V when
V*V = id — idempotence and symmetry follow immediately from dilV_isometry), which
entirely avoids composed Submodule/↥A/LinearIsometryEquiv objects and compiles
without timeout. One unresolved hard point remained within the allotted time: constructing W
(the isometry between the orthogonal complements Aᗮ/Bᗮ) still requires at least
some subspace structure (to apply Orthonormal.equiv), so the
“100% operators, zero submodules” route is not fully practicable as stated —
but limiting the use of submodules to THIS single location (rather than throughout
the A/B architecture) is the first avenue to explore in a future attempt.

Attempt 3 of 2026-07-11 (2-hour budget, SUCCESSFUL — N5 completed, 0 sorry).
Final architecture, radically different from the first two: ZERO
Submodule/↥A from beginning to end. Instead of decomposing the space into a
subspace + its orthogonal complement, work with two orthonormal families of the
entire space K, indexed by Fin m × Fin n (the canonical index of
DilSpace n m):
- v p := singleL i₀ (eₚ.₂) and w p := dilV P (eₚ.₂) (e = standard basis of H n),
 each orthonormal on the block sSlice i₀ := {p | p.1 = i₀} (immediate from
 inner_singleL/coordL_singleL/dilV_isometry, with no subspace structure).
- Orthonormal.exists_orthonormalBasis_extension_of_card_eq (new, not identified
 in the preceding attempts) extends EACH partial family to a COMPLETE
 orthonormal basis of K (finrank K = Fintype.card (Fin m × Fin n) via
 finrank_euclideanSpace, generic version — no _fin suffix needed).
- Orthonormal.equiv glues the two complete bases into a single
 U : K ≃ₗᵢ[ℂ] K, with e := Equiv.refl (Fin m × Fin n) (same index on both
 sides) ⟹ U (singleL i₀ (eₖ)) = dilV P (eₖ) for every k.
- Conclusion by extensionality on the standard basis of H n (Basis.ext):
 U.toLinearMap ∘ₗ singleL i₀ = dilV P.

Exact cause of the timeout in attempts 1/2, confirmed to be independent of
Submodule: composing (orthonormal_family ...).exists_orthonormalBasis_extension_of_card_eq
... inline in an obtain triggers the SAME deterministic timeout at whnf
as the preceding attempts (verified by isolating the phenomenon: the first
obtain alone succeeds, while the second — with dilV P, a much deeper term — times out again).
The fix: isolate the combined statement in a separate private lemma
(orthonormalBasisExtension), then invoke it by ordinary function application in
the two concrete cases (singleL n m i₀ and dilV P). General lesson: when an
obtain/refine composing several lemmas with metavariables times out at whnf
despite a mathematically immediate proof, do not persist with inlining —
extract an intermediate lemma with a fully explicit statement (rule 7 in CLAUDE.md,
generalized beyond indexed sums).

- [x] exists_unitary_extension (P) (i₀) : ∃ U : DilSpace n m ≃ₗᵢ[ℂ] DilSpace n m,
 U.toLinearMap ∘ₗ singleL n m i₀ = dilV P
- [x] naimark_projective_form (P) (i₀) : ∃ U, ∀ i x, ⟪x, P.E i x⟫ =
 ⟪U (singleL i₀ x), dilProj i (U (singleL i₀ x))⟫ (complete “ancilla” form:
 preparation in block i₀ + global unitary + projective measurement)
- [x] QuantumFoundations/Naimark/Unitary.lean created, imported, lake build green
- [x] #print axioms: exists_unitary_extension and naimark_projective_form
 depend only on [propext, Classical.choice, Quot.sound]
- [x] guard.sh: 0 axioms, 0 native_decide, 0 sorry (Naimark v1 + N5)

---

## Wigner — plan (strategy established with Fable 5, 2026-07-12)

Statement. Every transformation on pure states (unit vectors of H n)
that preserves transition probabilities |⟨φ|ψ⟩|² is induced by a unitary
or antiunitary operator, unique up to a global phase. Sources: Bargmann,
Note on Wigner's Theorem on Symmetry Operations (J. Math. Phys. 1964) — main
blueprint, almost “proof-assistant ready” (finite, pointwise §§3–5, purely
inner-product algebra); Simon et al. — cross-check and plan B for
globalization (Step 6, invariant c_jc_k·c_kc_ℓ·(c_jc_ℓ)), rejected as the main
blueprint (trigonometry on circles of vectors, Real.Angle, known friction).

Upstream Mathlib verdict (complete scan of mathlib4 master, July 2026, by Fable
5): entirely open ground. No Wigner, antiunitary, or Kadison
file/declaration. The only relevant asset is Mathlib.Analysis.Complex.Isometry
(linear_isometry_complex : ∀ f : ℂ ≃ₗᵢ[ℝ] ℂ, f = rotation a ∨ f = conjLIE.trans
(rotation a)) — an optional asset for W1, not a precedent. PhysLean/PhysLib and
Lean-QuantumInfo (merged) do not cover Wigner. A first-rate candidate for Mathlib:
the semilinear machinery (≃ₛₗᵢ[starRingEnd ℂ]) exists without any theorem
instantiating it on the antiunitary side.

Retained formulation — (A) in the core, (B) as an optional corollary (W6).
Reasons for rejecting alternatives: (C) quotient Projectivization — purely
algebraic API, no metric API, everything would pass through constant lifts for
no benefit (a cosmetic wrapper remains possible in optional W6); (D) ∃ σ
quantified over the RingHom — dependent-RingHomInvPair instance hell,
replaced by a disjunction ∨ of two concrete existentials (both target types
type-check, confirmed in stdin).

lean
theorem wigner (n : ℕ) (T : H n → H n)
 (hT : ∀ x y, ‖x‖ = 1 → ‖y‖ = 1 → ‖⟪T x, T y⟫_ℂ‖ = ‖⟪x, y⟫_ℂ‖) :
 (∃ U : H n ≃ₗᵢ[ℂ] H n,
 ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U x)
 ∨ (∃ U : H n ≃ₛₗᵢ[starRingEnd ℂ] H n,
 ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U x)


Design decisions (in order of importance):
- No bijectivity assumption. Bargmann §1.2: injectivity at the ray level
 follows from hT (Cauchy–Schwarz: two unit rays coincide iff their inner
 product has modulus 1); in finite dimension U is automatically bijective
 (isometry). The statement is strictly stronger than Simon et al. (who assume
 Ω bijective, eq. 2.8), and is exactly Bargmann's Main Theorem §1.3
 specialized — to be emphasized in the final README.
- ∀ n, with no threshold. n = 0 is vacuous, n = 1 is trivial (both
 branches work, Bargmann §1.4), and the core is uniform for n ≥ 2. Unlike
 Gleason (n ≥ 3), there is no dimensional restriction in the core.
- Construct U; never extend T. U is defined by a closed formula from
 finite data (§W3/W5); no “extension from the sphere” problem arises in this
 architecture.
- Defunctionalized χ. Internally: a bare function χ : ℂ → ℂ (explicit
 extraction formula, W4) + Prop values. Bundling into ≃ₗᵢ/≃ₛₗᵢ occurs
 only at the boundary (the two branches of the final rcases in W5).
- Phases = pairs (c : ℂ) + ‖c‖ = 1, never Circle/unitary ℂ.
- 𝒫 = e⊥ as a Prop condition (⟪e, z⟫ = 0), never the Submodule type —
 the Submodule/WithLp lesson from Naimark (N5, attempts 1–2) applies in full.
- (B) only as a corollary, in the form
 S (rankOne x x) = rankOne (U x) (U x) — never U ∘ P ∘ U⁻¹ (avoids all
 RingHomCompTriple friction with semilinear conjugation). Reuses the
 rankOne machinery already tested in gleason, providing a “Kadison-style”
 bridge for a future paper.
- Zero trigonometry, zero angles — the criterion distinguishing Bargmann
 (retained) from Simon et al. (rejected as the main blueprint, kept as a
 cross-check).

Expected total count: ~24–26 sorry upon completion of W0. The only new
mathematical content is W4 (as sqrtOp was for N1); W2–W3–W5 are disciplined
plumbing (as N2–N3 were for Naimark). Order of attack:
W0 → W1 → W2 → W3 → W4 → W5 (→ W6). W1 first, because it calibrates the
actual difficulty level (territorial nlinarith/Complex.ext) and W4 depends
on it throughout.

### W0 — Skeleton (Defs, main statement, Nonvacuity) — ✅ CLOSED (2026-07-12)
- [x] Step 0 validated in stdin (exact results below)
- [x] Definitions by closed formulas (junk outside the domain, no proof passed
 as an argument — dite pattern on 0 < n/2 ≤ n, as for sqrtOp):
 e, eImg (=e'), InPerp (=𝒫, a Prop), V, refVec, chidir,
 chi, U, IsWignerMap — QuantumFoundations/Wigner/Defs.lean
- [x] Main statement wigner + all W1–W5 lemmas introduced with sorry.
 Difference from the plan, explicitly reported: case n = 0 PROVED
 directly (vacuity — H 0 is Subsingleton, with no unit vector); case
 n = 1 left as sorry (short and self-contained — no dependency on
 W1–W5 — but not addressed at this stage, so as not to delay validation
 of the skeleton).
- [x] Nonvacuity: T = id inhabits the unitary branch, while
 T = conjCoords (coordinatewise conjugation, bundled as a
 conjugate-semilinear isometry via LinearEquiv.ofBijective +
 involutivity) inhabits the antiunitary branch — fully proved, 0 sorry,
 with no exotic manual fallback required.
 QuantumFoundations/Wigner/Nonvacuity.lean
- [x] lake build green, guard.sh: 0 axioms, 0 native_decide, 24 sorry
 (Naimark remains at 0; repository total 24 — within the expected 24–26 range)

Architectural difference, reported: namespace QuantumFoundations.Wigner
(nested), unlike the flat namespace QuantumFoundations used for all of Naimark —
deliberate, because Wigner's internal names (e, V, U, chi) are generic and
would have polluted the flat namespace. wigner is therefore invoked as
QuantumFoundations.Wigner.wigner.

Files created:

QuantumFoundations/Wigner/Scalar.lean W1 : 3 sorry (kit scalaire ℂ)
QuantumFoundations/Wigner/Defs.lean e, eImg, InPerp, V, refVec, chidir, chi, U, IsWignerMap
QuantumFoundations/Wigner/Bessel.lean W2 : 2 sorry
QuantumFoundations/Wigner/VConstruction.lean W3 : 6 sorry
QuantumFoundations/Wigner/Core.lean W4 : 6 sorry (seul contenu mathématique neuf)
QuantumFoundations/Wigner/Main.lean W5 : 5 sorry + théorème wigner (n=0 prouvé, n=1 et n≥2 sorry)
QuantumFoundations/Wigner/Nonvacuity.lean 0 sorry, témoins id/conjCoords complets


Step 0 results (stdin, all confirmed):
- EuclideanSpace.single (i) (a) : EuclideanSpace 𝕜 ι + EuclideanSpace.inner_single_left/right
 — confirmed (names PiLp.norm_single/PiLp.single_apply now preferred over
 deprecated aliases EuclideanSpace.*).
- ‖1+r‖² = 1+‖r‖²+2Re r: NO direct lemma under that name — derived in 2 lines via
 Complex.sq_norm (‖z‖² = normSq z) + Complex.normSq_add + Complex.normSq_one.
- orthonormal_iff_ite confirmed (Orthonormal 𝕜 v ↔ ∀ i j, ⟪v i,v j⟫ = if i=j then 1 else 0).
- Bessel equality (Bargmann's lemma (9)): no exported lemma, but the proof of
 Orthonormal.sum_inner_products_le (Bessel INEQUALITY,
 Mathlib.Analysis.InnerProductSpace.Orthonormal) contains EXACTLY the
 unconditional identity sought as an internal step
 (hbf : ‖x − Σ⟪vᵢ,x⟫•vᵢ‖² = ‖x‖² − Σ‖⟪vᵢ,x⟫‖²), not exported — fully reusable
 proof recipe: norm_sub_sq, InnerProductSpace.norm_sq_eq_re_inner,
 inner_sum/sum_inner, inner_smul_left/right, inner_conj_symm,
 Orthonormal.inner_left_right_finset.
- LinearMap.injective_iff_surjective [FiniteDimensional K V] {f : V →ₗ[K] V} confirmed
 (already used in N5) — will require restriction to an ℝ-linear map for the
 antiunitary branch (conjugate-semilinear ⟹ ℝ-linear by restriction of scalars).
- LinearIsometryEquiv.mk (toLinearEquiv : E ≃ₛₗ[σ] E₂) (norm_map) : E ≃ₛₗᵢ[σ] E₂ and
 LinearEquiv.ofBijective (f : M →ₛₗ[σ] M₂) (hf : Bijective f) : M ≃ₛₗ[σ] M₂ — both
 generic in σ (confirmed, tested with σ = starRingEnd ℂ directly on
 EuclideanSpace ℂ (Fin n)), with no direct LinearIsometryEquiv.ofBijective.
- Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ and linear_isometry_complex confirmed present
 (Mathlib.Analysis.Complex.Isometry, ROOT name, not namespaced under Complex.) —
 retained as an optional shortcut for W1, not used in the skeleton (would first
 require proving ℝ-linearity of f, additional nontrivial work).
- conjCoords (Nonvacuity witness) constructed entirely by hand
 (WithLp.toLp/WithLp.ext_iff, LinearEquiv.ofBijective using its involutivity) —
 no sorry, with no need for a more complex fallback than anticipated.

### W1 — ℂ scalar kit (zero dependencies, de-risks everything, to prove first) — ✅ CLOSED (2026-07-13)
- [x] re_eq_of_norm_eq : ‖u‖ = ‖v‖ → ‖1+u‖ = ‖1+v‖ → u.re = v.re — derived via
 Complex.sq_norm/Complex.normSq_add/Complex.normSq_one (2 lines), then
 linarith
- [x] eq_one_of_norm_one_re_one : ‖u‖ = 1 → u.re = 1 → u = 1 — normSq u = 1
 + re = 1 ⟹ im² = 0 (nlinarith) ⟹ im = 0 ⟹ Complex.ext
- [x] scalar_dichotomy: for f : ℂ → ℂ with (∀ α, ‖f α‖ = ‖α‖), f 1 = 1,
 (∀ α β, (conj (f α) * f β).re = (conj α * β).re), then f = id ∨ f = conj
 — Bargmann §4.6 transposed line by line (Eq A via α := 1; Step B via
 Complex.normSq/sq_eq_one_iff; Step C via hre α I); key identities
 established as local have statements (reI, conjMulSelf), with no
 direct Mathlib lemma for Re(conj w * I) = w.im or
 Re(conj z * z) = normSq z (targeted simp suffices)
- [x] Reported difference: the hypothesis hnorm (norm preservation) turns
 out to be UNUSED in the proof of scalar_dichotomy — confirmed by the
 compiler (unused-variable warning) and consistent with the supplied
 Bargmann derivation; retained in the signature (renamed _hnorm,
 statement unchanged)
- [x] guard.sh: 0 axioms, 0 native_decide, 21 sorry (24 − 3)

### W2 — Inner-product plumbing — ✅ CLOSED (2026-07-13)
- [x] bessel_eq_of_norm_sq_eq (Bargmann's lemma (9), centerpiece): finite
 orthonormal family g ({ι : Type*} [Fintype ι], not only Fin m),
 ‖u‖² = Σ ‖⟪g p, u⟫‖² → u = Σ ⟪g p, u⟫ • g p — Bessel identity with
 equality, removes exists_orthonormalBasis_extension from the critical
 path, with no basis extension, cardinality count, or surjectivity.
 Proof: key : ⟪g p,y⟫=⟪g p,u⟫ (simple collapse) reused for
 hyy/hyu (each a single-sum calculation, never an inlined double sum),
 then norm_sub_sq + hypothesis ⟹ ‖u-y‖=0.
- [x] orthonormal_image: moduli δ_pq + norms 1 ⇒ Orthonormal (case p = q:
 ⟪Tf,Tf⟫ = (↑‖Tf‖:ℂ)² via inner_self_eq_norm_sq_to_K, modulus 1 ⇒
 ‖Tf‖²=1) — signature completed with [DecidableEq ι] (required by
 orthonormal_iff_ite, a purely logical additional hypothesis imposing no
 genuine restriction in use)
- [x] Bullet “homogeneity/scaling identities” from the initial plan: ABSORBED
 into V_colinear (W3) — not a separate lemma, no dedicated sorry
- [x] guard.sh: 0 axioms, 0 native_decide, 19 sorry (21 − 2)

Lean pitfall encountered and documented (in Bessel.lean): an rw targeting
a term WITHOUT a metavariable (⟪g p,u⟫ fixed, not a pattern) rewrites ALL
syntactically identical occurrences simultaneously — after substituting
⟪g p,y⟫ with ⟪g p,u⟫ via key p, the goal contained two syntactically
identical copies of ⟪g p,u⟫, and rw [← inner_conj_symm ...] rewrote both
instead of only one (double conj). Workaround: use mul_comm, then apply the
lemma directly to conj(z)*z; never use rw targeting a duplicated subterm
without a metavariable that distinguishes it from other identical occurrences.

Documented ℝ→ℂ cast frictions (nonblocking, but costly in trial and error):
inner_self_eq_norm_sq_to_K x : ⟪x,x⟫ = ↑‖x‖ ^ 2 elaborates as (↑‖x‖ : ℂ) ^ 2
(cast BEFORE exponentiation, not ↑(‖x‖^2)) — simpa/simp handle the
conversion ‖(↑r)^2‖ → r^2 effortlessly, but to close in the other direction
(r^2=1 → (↑r)^2=1), neither exact_mod_cast nor push_cast alone sufficed;
norm_cast (normalizes to ↑(r^2)) followed by explicit rw [h2]; norm_num
worked reliably.

### W3 — Construction of V + basic properties (Bargmann §3, eqs. 11–12a) — CLOSED (2026-07-13)
- [x] inner_eImg_V: ⟪e', V z⟫ = 0 — direct calculation from the unfolded
 formula for V, ⟪e',e'⟫=1 (heImg_inner_self), and γ⁻¹*γ=1
- [x] V_colinear: reported and corrected discrepancy — the skeleton
 statement asserted ‖δ‖ = 1, which is FALSE in general (counterexample:
 T = id gives V T z = z, whereas δ • T(‖z‖⁻¹•z) always has norm 1, so ‖δ‖=1 would force ‖z‖=1 for every z ⊥ e). Corrected to
 ‖δ‖ = ‖z‖, consistently with norm_V and with the Bargmann §3.2
 comment already present in the file (“β' has modulus ‖z‖”, not
 necessarily 1). Proof: orthonormalize {e, f_z}
 (f_z := ‖z‖⁻¹•z), send it through orthonormal_image (W2) to
 {eImg T, T f_z}, establish Bessel equality (9, W2) for T w (w the
 unit representative of e+z) using transition-probability preservation
 on each basis vector, solve for
 T w = γ•eImg T + μ•T f_z, hence V T z = (γ⁻¹μ) • T f_z
- [x] norm_V: ‖V z‖ = ‖z‖ — case z=0 trivial (V T 0 = 0 by direct
 calculation), case z≠0 via V_colinear
- [x] norm_inner_V (eq. 11): ‖⟪Vw,Vx⟫‖ = ‖⟪w,x⟫‖ — direct proof via
 V_colinear (Vw,Vx are scalar multiples of T applied to their unit
 representatives; IsWignerMap directly gives the modulus of the inner
 product of these images; the factors ‖w‖,‖x‖ cancel their inverses) —
 NO need to return through the vector built from e+z, contrary to the
 initially suggested approach
- [x] re_inner_V (eq. 12): real part preserved — key identity
 ⟪Vw,Vx⟫ = (conj γ)⁻¹γ'⁻¹⟪Tw,Tw'⟫ − 1 (the cross terms
 ⟪Tw,e'⟫/⟪e',Tw'⟩ cancel EXACTLY against ⟪e',e'⟫=1 when expanding
 V z = γ⁻¹•Tw − e' in both arguments); the modulus of ⟪Tw,Tw'⟫ is
 computed solely in terms of ⟪w,x⟫ (the dependence on e+z cancels
 completely after simplification), yielding
 ‖1+⟪Vw,Vx⟫‖ = ‖1+⟪w,x⟫‖; combined with eq. 11,
 re_eq_of_norm_eq (W1, Scalar.lean) concludes directly
- [x] inner_V_eq_of_im_eq_zero (eq. 12a): exact equality in the real case —
 (11)+(12) force Im⟪Vw,Vx⟫=0 via |z|²=Re(z)²+Im(z)² (same pattern as
 eq_one_of_norm_one_re_one, W1)
- [x] hn : 2 ≤ n added to all 6 signatures (absent from the W0 skeleton):
 for n=0, e n = 0 (junk value) and eImg T may be zero, in which case
 γ may vanish and the inversion γ⁻¹•Tw degenerates; 2 ≤ n was chosen
 (rather than 0 < n, technically sufficient for W3 alone) for
 consistency with Core.lean (W4), which invokes these lemmas under the
 same hypothesis
- [x] Reported discrepancy: the formula for V in Defs.lean has NO
 separate dite branch for z = 0 (contrary to the initial plan) — a
 single uniform formula covers all cases because e n + z ≠ 0 is
 guaranteed as soon as n ≥ 1 and z ⊥ e (otherwise z = −e n would
 give ⟪e n,z⟫=−1≠0, a contradiction); no by_cases z = 0 is needed in
 the general algebraic derivations
- [x] guard.sh: 0 axioms, 0 native_decide, 13 sorry (16 − 3,
 cumulatively 19 − 6 over all of W3)

Lean pitfall encountered and documented (rule 12 in CLAUDE.md, generalized):
unfolding e n via unfold e; rw [dif_pos h0] (or an explicit show of the
unfolded value) triggers a deterministic timeout at whnf — the presence of a
locally constructed NeZero n instance in the dite branch is expensive to
unify during direct rewriting. Remedy: simp only [e, dif_pos h0, ...] closes
the same equality without ever timing out (simp handles reduction of the
dite more robustly than a manual rw/show).

Instance diamond encountered and documented (new, specific to
EuclideanSpace/Gleason.H n): inner_self_eq_norm_sq_to_K produces a term
(↑‖x‖ : ℂ) ^ 2 via RCLike.ofReal + a SeminormedAddCommGroup instance
derived from PiLp.seminormedAddCommGroup, DIFFERENT (syntactically, although
definitionally equal) from Complex.ofReal + PiLp.instNorm used elsewhere
in the same calculations — an rw/ring/exact_mod_cast targeting this term
silently fails, leaving a goal displayed as trivial
(↑‖z‖ ^ 2 = ↑‖z‖ ^ 2 but not closed by implicit rfl). Reliable workaround:
isolate the conversion in a dedicated have closed by
rw [inner_self_eq_norm_sq_to_K]; norm_cast (the combination rw then
norm_cast, never exact/exact_mod_cast directly on the lemma, closes the
diamond), then reuse this have — never reason about the diamond after the
fact using ring/field_simp on the raw term.

### W4 — THE core: analysis of V (Bargmann §4 — the analogue of sqrtOp for N1) — CLOSED (2026-07-13)
- [x] chidir_dichotomy: chidir T f (for an ARBITRARY unit f of 𝒫, not
 only refVec — free generalization) satisfies the hypotheses of
 scalar_dichotomy (W1). Two private preliminaries: T_phase (Step 1,
 equality case of Cauchy–Schwarz — norm_inner_eq_norm_tfae, index 0↔2 —
 applied to T f, T(c•f)) and V_dir_colinear (Step 2, generalized to an
 arbitrary f: V(α•f) = chidir T f α • V f, coefficient identified by
 uniqueness against V f ≠ 0)
- [x] chi_dichotomy: trivial corollary of chidir_dichotomy at
 f := refVec
- [x] chi_eq_chidir (globalization, reported and resolved discrepancy —
 generalized to NONorthogonal frames; see note below):
 chi T α = chidir T f α for every unit f of 𝒫, NOT only refVec
- [x] V_chi_homogeneous (18b): generalizes V_dir_colinear/chi_eq_chidir
 from a unit f to an arbitrary z, via
 z = ‖z‖•(‖z‖⁻¹•z) + chi_real (chi fixes real numbers in both
 id/conj branches)
- [x] V_additive (18a): collinear case directly via chi_add_real
 (chi(r+a) =
 r+chi(a), r real); general case via Gram–Schmidt
 (f₂ := component of z orthogonal to f₁ := y/‖y‖, normalized) +
 V_two_dir (private, key preliminary:
 V(a₁f₁+a₂f₂) = chi(a₁)•Vf₁+chi(a₂)•Vf₂ for f₁⊥f₂ — DIRECT proof
 without Bessel/orthonormal_image, via rigidity
 eq_of_norm_eq_re_eq applied to ⟪V(a_p f_p), V x⟫, unlike the
 initially contemplated approach with 3 orthonormal vectors)
- [x] inner_V_eq_chi_inner (18c): reduces to the unit case
 (V_inner_eq_chi_of_unit, the same rigidity as V_two_dir but without a
 second direction) via y = ‖y‖•f₁, V_chi_homogeneous,
 chi_mul_real (chi(r*w) = r*chi(w), r real)
- [x] guard.sh: 0 axioms, 0 native_decide, 7 sorry (10 − 3,
 cumulatively 13 − 6 over all of W4)

Reported and resolved discrepancy (chi_eq_chidir, generalization to
nonorthogonal frames): the argument in Bargmann §§4.3–4.5 (w = f₁+f₂,
comparison of coefficients in a 2D Bessel expansion) works ONLY for ORTHOGONAL
directions — insufficient when n ≥ 3 and f is neither collinear nor
orthogonal to refVec. Retained route (after user confirmation): reduce
chi_eq_chidir to a comparison at a SINGLE point (i, where id and conj
differ), via chidir_branch_transfer — for unit f1,f2 with
⟪f1,f2⟫ ≠ 0 (NO orthogonality needed), two test vectors
c1 := i·a/‖a‖, c1' := a/‖a‖ (a := ⟪f1,f2⟫) make
⟪c1•f1,i•f2⟫ and ⟪c1'•f1,f2⟫ BOTH exactly ‖a‖ (positive real, by
algebraic construction — no real/nonreal case split on a), which determines
chidir f2 at the point i through the rigidity eq_of_norm_eq_re_eq. The
only degenerate case is f = -refVec (collinear), handled separately by
chidir_colinear_refVec. A total of 8 private lemmas for this single sorry
(eq_of_norm_eq_re_eq, inner_I_smul_eq_norm, inner_smul_eq_norm,
chidir_branch_transfer, chidir_colinear_refVec, eq_branch_of_eq_at_I,
chi_real, sq_norm_eq_mul_conj), versus the 2 (T_phase, V_dir_colinear)
that sufficed for chidir_dichotomy/chi_dichotomy.

Lean pitfalls encountered and documented:
- (rule 12 in CLAUDE.md, new instance) applying norm_cast/Complex.mul_conj
 directly to an expression such as chi T b (enormous once chidir is
 unfolded through V/⟪·,·⟫) triggers a whnf timeout. Remedy: extract the
 purely ℂ identity into a private lemma with a minimal context
 (sq_norm_eq_mul_conj) — never use inline generalize in the large context;
 it does not prevent the timeout (contrary to expectation).
- An rw on a goal/hypothesis containing BOTH a variable z and an expression
 ‖z‖ depending on it rewrites BOTH simultaneously as soon as z is
 substituted (hyf1 : z = ‖z‖•f), producing an absurd term of the form
 ‖‖z‖•f‖. Systematic workaround: conv_lhs => rw [...] to restrict the
 rewrite to the single side that must change; never use an unconstrained rw
 on a goal that mentions the norm of the substituted term elsewhere.

### W5 — Assembly (Bargmann §5) + main theorem — CLOSED (2026-07-13)
- [x] U_additive, U_chi_semilinear: direct algebra on
 U a := chi⟪e,a⟫•eImg +
 V(a−⟪e,a⟫•e), via chi_add/chi_mul (NEW,
 general over all of ℂ — distinct from chi_add_real/chi_mul_real
 from W4, which cover only a real factor) +
 V_additive/V_chi_homogeneous (W4)
- [x] inner_U_eq_chi_inner: standard decomposition
 ⟪a,b⟫ = conj(αₐ)·α_b +
 ⟪zₐ,z_b⟫ + inner_eImg_V (W3, cross terms
 vanish) + inner_V_eq_chi_inner (W4) + new identity chi_conj_mul
 (conj(chi a)·chi b = chi(conj(a)·b), true in both branches)
- [x] U_bijective: advantageous discrepancy — unlike the initial plan,
 the actual file separates Function.Bijective (U T) (a plain function)
 from bundling into ≃ₗᵢ/≃ₛₗᵢ, deferred to wigner itself. Injectivity
 is BRANCH-INDEPENDENT via U_norm_eq (‖Ua‖=‖a‖, a direct consequence
 of inner_U_eq_chi_inner + chi_real, valid simultaneously in both
 branches). Surjectivity: rcases chi_dichotomy, literal LinearMap
 ({toFun:=U T, map_add':=..., map_smul':=...} — confirmed to work
 without a named constructor), branch chi=id → direct →ₗ[ℂ], branch
 chi=conj → →ₗ[ℝ] (restriction to real scalars, THE actual unknown of
 the milestone: confirmed that NO direct semilinear lemma exists in
 Mathlib, restriction to ℝ is the only route, and
 LinearMap.injective_iff_surjective applies unchanged with K:=ℝ)
- [x] exists_phase_U: confirmed — the case ⟪e,x⟫=0 is indeed FREE (just
 V_colinear, W3, applied directly to x), with no Cauchy–Schwarz. Case
 ⟪e,x⟫≠0: full derivation via T_phase (W4) + DEFINITIONAL unfolding of
 V ζ (by rfl, no dedicated lemma needed) + V_chi_homogeneous
- [x] wigner for n≥2: unsurprising assembly — LinearEquiv.ofBijective +
 LinearIsometryEquiv.mk, coercion of the bundled equivalence reduces to
 U T by rfl (confirmed by stdin test)
- [x] wigner for n=1: SELF-CONTAINED derivation (independent of W1–W5,
 hn:2≤n never available) — H 1 has dimension 1
 (H1_eq_inner_smul_e, via Fin 1 being a subsingleton),
 U₁ x := ⟪e 1,x⟫•eImg T directly ℂ-LINEAR (not merely semilinear), placed
 in the chi=id branch by convention (Bargmann §1.4: both branches work,
 with no way to distinguish them in dimension 1)
- [x] guard.sh: 0 axioms, 0 native_decide, 0 sorry (7 − 7,
 cumulatively 24 − 24 over all of Wigner) — WIGNER'S THEOREM CLOSED.
 #print axioms wigner: [propext, Classical.choice, Quot.sound]
 (standard kernel trio, no added axiom)

Lean pitfalls encountered and documented:
- (RCLike/Complex diamond, 3rd occurrence) applying
 inner_self_eq_norm_sq_to_K TWICE in the same rw ... at h (once to
 ⟪Ua,Ua⟫, once to ⟪a,a⟫ nested under chi T) produces syntactically
 distinct forms although they display identically, breaking every subsequent
 rw. Definitive remedy: isolate EACH application in its own have closed
 by rw [...]; norm_cast; never apply it twice in the same rw ... at h.
- Cast: after substituting ‖e n+ζ‖ (real) with ‖α‖⁻¹ INSIDE a coefficient
 already cast to ℂ, the resulting term is (↑(‖α‖⁻¹))⁻¹ (double inverse
 with an intervening cast) — inv_inv alone does not match; apply
 push_cast before inv_inv to push the cast inside the inverse and unblock.
- simpa using h may oversimplify a goal/hypothesis of the form x^2=1 into
 the disjunction x=1 ∨ x=-1 (through a sq_eq_one_iff-like lemma in the
 default simp set), instead of closing it directly against an already
 available equation-shaped hypothesis — this appears unexpectedly when two
 nearly identical derivations of the SAME fact are written separately in
 different tactic contexts. Remedy: merge the two redundant derivations into
 one instead of trying to debug the duplication.

### W6 — OPTIONAL (in the style of v2.0-naimark) — CLOSED (2026-07-13), 0 sorry, QuantumFoundations/Wigner/Uniqueness.lean

**(A) Unitary/antiunitary exclusivity for n ≥ 2** — ✅ implemented exactly as
planned, through the ray invariant
Delta(a,b,c) := ⟪a,b⟫⟪b,c⟫⟪c,a⟫ (Bargmann §1.5):
- [x] delta_transform_lin/delta_transform_conj: invariance/conjugation of
 Delta under T, one lemma per CONCRETE branch of theorem wigner
 (≃ₗᵢ[ℂ] / ≃ₛₗᵢ[starRingEnd ℂ]) rather than an abstract parameterized
 chi — discrepancy from the initial plan reported; see
 ARCHITECTURE_NOTES.md. conj_isometry_inner (complex polarization)
 derived manually: Mathlib has no analogue of
 LinearIsometryEquiv.inner_map_map for ≃ₛₗᵢ[σ].
- [x] bargmann_delta_witness: explicit finite witness confirmed by Lean —
 e₁=e, e₂=(e−refVec)/√2, e₃=(e+refVec(1−i))/√3 indeed give
 Delta = i/6 ∉ ℝ
- [x] exclusivity: assembly — i/6 = -(i/6) gives i = 0, contradiction

**(B) Uniqueness of U up to a global phase — RESTRICTED version** (not the
full Theorem 2 of Bargmann §6) — ✅:
- [x] Defs.lean fixes eImg T := T (e n), with no parameter for choosing a
 representative: LOCAL introduction (in Uniqueness.lean only,
 Defs.lean untouched) of a parameterized reconstruction
 Vp/chidirp/chip/Up with explicit eImg, related to
 V/chi/U by rfl bridge lemmas (V_eq_Vp, chi_eq_chip, U_eq_Up)
- [x] Vp_smul_eImg, chip_smul_eImg, Up_smul_eImg: V/chi/U
 recomputed at the representative λ • eImg (‖λ‖ = 1) equal
 λ • V/chi/λ • U — chi UNCHANGED (not merely its branch), with no
 case split
- [x] U_alt_eq_smul: conclusion, Up T (λ • eImg T) = λ • U T
- [x] guard.sh: 0 axioms, 0 native_decide, 0 sorry. #print axioms on
 exclusivity/bargmann_delta_witness/U_alt_eq_smul:
 [propext, Classical.choice, Quot.sound]

Not addressed (out of scope, reported from the outset): Bargmann §6's full
Theorem 2 (U' completely arbitrary, not merely another representative of
eImg) would require rederiving real homogeneity from additivity + isometry —
unnecessary for the repository's actual use case. Corollary (B)
rankOne/Projectivization wrapper (mentioned as low priority in the initial
plan): not implemented.

### What will NOT be a blocker (contrary to initial concerns)
Extension of orthonormal bases (eliminated by lemma (9) of W2); management of
global phase (phases remain LOCAL scalars c with ‖c‖=1, never a globally
coherent choice to construct); quotients (none, formulation (A));
linearity-from-metric (additivity of V is proved componentwise through (16),
never extracted from an abstract metric hypothesis).

### Lean friction to budget for (analogous to the Naimark lessons)
Unfolding PiLp/WithLp norms in W3 calculations (γ⁻¹, ‖e+z‖) — same
patterns as in gleason/N0–N3, with private lemmas in a minimal context if
a whnf timeout occurs (rule 12 in CLAUDE.md); junk values of total definitions
(V outside 𝒫, chi outside its domain) — each lemma carries its side
conditions, following the discipline already established for
sqrtOp/dilProj.

---

## Uhlhorn — Šemrl's Corollary 1.2 (arXiv:2106.06182)

Statement. In finite dimension n ≥ 3, every map φ on rank-one
projections that preserves orthogonality IN ONE DIRECTION only (PQ = 0 ⟹
φ(P)φ(Q) = 0; with neither injectivity nor surjectivity assumed) is
automatically a Wigner symmetry (∃ U unitary or antiunitary,
φ(P) = UPU*). Source: Šemrl, Wigner symmetries and Gleason's theorem,
2021 (arXiv:2106.06182), Corollary 1.2. Reuses wigner (W0–W6, already
completed) and Gleason.gleason (pinned dependency v1.0-gleason) as black
boxes.

Proof decomposition (U1–U5, with U3a inserted during U0 reconnaissance;
see below):
- U1 — Wigner corollary (B) (not previously constructed): if φ preserves
 tr(φ(P)φ(Q)) = tr(PQ) for every pair, then it is a Wigner symmetry. This
 follows from wigner by choosing a unit representative for each projection.
- U2 — elementary spectral lemma (pure linear algebra): E positive,
 E ≤ I, tr(E) = 1, and ⟨Ex,x⟩ = 1 for unit x ⟹ E = P_x.
- U3a — extension of a frame function on lines to a complete
 ProjMeasure (component isolated during reconnaissance; see U0 below).
- U3b — “Gleason applied twice”: combines Gleason.gleason, U3a, and U2.
- U4 — assembly: U1 + U3b.
- U5 — finite-dimensional reduction (cardinality counting) + final theorem
 uhlhorn_finite_dim, combined with U4.

### U0 — Reconnaissance + skeleton — ✅ CLOSED (2026-07-13)

Part A (reconnaissance, mandatory before any code):
- [x] Gleason.gleason {n} (hn : 3 ≤ n) (m : ProjMeasure n) : ∃! ρ, IsDensityOperator ρ
 ∧ ∀ A, m.μ A = bornValue ρ A — confirmed sufficiently general to apply
 to a ProjMeasure constructed from
 φ_D(P) := tr(D·φ(P)) (ProjMeasure is a generic Prop bundle over
 Submodule ℂ (H n) → ℝ, with no reference to a specific
 Busch/Gleason context)
- [x] Representation of rank-one projections on the gleason side: NO
 rankOne wrapper/bundled structure — always either
 Submodule ℂ (H n) (ProjMeasure, bornValue, projL) or Mathlib's
 InnerProductSpace.rankOne operator (already used on the Naimark side,
 sqrtOp), never both mixed in a dedicated type
- [x] Signature of wigner reconfirmed unchanged since W6
- [x] No preexisting sketch of Wigner corollary (B) (projection form)
- [x] Spectral API confirmed: IsPositiveOp, IsEffect T := IsPositiveOp T ∧
 IsPositiveOp (1-T) (= 0 ≤ T ≤ 1), LinearMap.trace, and especially
 Gleason.positive_inner_self_eq_zero (already proved on the gleason
 side and directly reusable as the central building block of U2)
- [x] Validated design: Proj1 (n) := {A : Submodule ℂ (H n) //
 finrank ℂ A = 1} (reuses Submodule, with no new wrapper);
 IsWignerSymmetryProj, Option 1 retained — equality of lines
 φ(ℂ∙x) = ℂ∙(Ux), NOT literal operator equality φ(P) = UPU*
 (Option 2, mathematically equivalent in rank one, but would have
 required LinearMap.adjoint for a semilinear equivalence — never
 encountered in this project, left as a remark for a later pass if needed)
- [x] Additional reconnaissance point, before the skeleton: exhaustive
 audit of all ProjMeasure construction sites in gleason
 (EffectMeasure.toProjMeasure, pureState) — neither extends a frame
 function defined only on lines; both provide a closed formula directly
 on every subspace. This extension lemma does not exist anywhere in
 gleason-theorem-lean: isolated as a full submilestone U3a (not an
 internal detail of U3b), with its own estimate (~100–150 lines, 4–6
 subgoals). Decision: U3a remains in quantum-foundations-lean
 (namespace Uhlhorn), not in gleason-theorem-lean — despite being
 generic, the tagged public repository will not be reopened for this need

Part B (skeleton, QuantumFoundations/Uhlhorn/):
- [x] Defs.lean: Proj1, Proj1.mk_unit, TraceProd,
 PreservesOrthogonality, IsWignerSymmetryProj,
 IsFrameFunctionOnLines, SendsONBToONB — 0 sorry
- [x] WignerProjectionForm.lean (U1, wigner_projection_form) — 1 sorry
- [x] Spectral.lean (U2,
 eq_projL_of_positive_le_one_trace_one_inner_one) — 1 sorry
- [x] GleasonExtend.lean (U3a,
 exists_projMeasure_of_frameFunctionOnLines, complete signature
 introduced without splitting the 5 internal subgoals into separate
 sorry declarations) — 1 sorry
- [x] GleasonTwice.lean (U3b,
 traceProd_preserved_of_sendsONBToONB) — 1 sorry
- [x] Assembly.lean (U4 wignerSymmetryProj_of_sendsONBToONB, U5
 uhlhorn_finite_dim) — 2 sorry
- [x] Nonvacuity.lean (0 sorry): witness φ := id inhabits
 PreservesOrthogonality and the unitary branch of
 IsWignerSymmetryProj (U := refl, proof by rfl); antiunitary witness
 (conjCoords) NOT immediate (would have required Submodule.map for a
 semilinear equivalence, never exercised in this project) — omitted in
 accordance with the instruction (one witness suffices)
- [x] lake build green, guard.sh: 0 axioms, 0 native_decide, 6 sorry
 (one per milestone U1/U2/U3a/U3b/U4/U5)

Minor discrepancy reported and corrected: the first draft of the
GleasonExtend.lean docstring literally used the word “sorry” to describe the
estimated size of the milestone, causing the guard.sh count to rise to 7
through a false positive (the script does not distinguish comments from code)
— rephrased as “intermediate subgoals.”

### U3a — Extension of a frame function → complete ProjMeasure — ✅ CLOSED (2026-07-13)

Addressed first, independently of the rest (U1/U2/U3b/U4/U5), because this was
the component whose actual difficulty remained most uncertain after U0
reconnaissance.

- [x] gv (bridge from Proj1 n → ℝ to H n → ℝ, junk value 0 outside the
 unit sphere) + isCFrameFunction_gv: gv g satisfies
 Gleason.IsCFrameFunction (gv g) 1
- [x] orthonormal_stdBasis_coe/span_stdBasis_coe: the standard
 orthonormal basis of ↥A (stdOrthonormalBasis ℂ A), coerced into
 H n, is orthonormal and spans A
 (LinearIsometry.orthonormal_comp_iff, Submodule.map_subtype_top)
- [x] frameSum (μ A := ∑ i, gv g (stdOrthonormalBasis ℂ A i)) +
 frameSum_eq_sum_of_orthonormal_spanning (Sublemma 1,
 basis-independence in generic form — any Fintype ι of the correct
 cardinality, not only Fin (finrank A), via Fintype.equivFinOfCardEq +
 Equiv.sum_comp)
- [x] frameSum_top (Sublemma 3), frameSum_nonneg (Sublemma 4),
 frameSum_add_isOrtho (Sublemma 5, via Sum.elim — the only
 concatenation of bases constructed by hand in the entire file)
- [x] exists_unit_vector_of_proj1 + frameSum_proj1: μ agrees with g
 on every line
- [x] exists_projMeasure_of_frameFunctionOnLines assembled, 0 sorry
- [x] guard.sh: 0 axioms, 0 native_decide, 5 sorry (6 − 1)

Major discrepancy reported (changes the anticipated difficulty of the
milestone): the reconnaissance strategy contemplated reproving
basis-independence (Sublemma 1) from scratch by concatenating
Fin k ⊕ Fin l → Fin n (finSumFinEquiv/Fin.append). Upon reading
Gleason.Complex.RealSections (transitively imported but never examined in
detail before this milestone), I found that this argument is already fully
proved there in vector form: Gleason.cframe_sum_invariant (for a frame
function g : H n → ℝ satisfying IsCFrameFunction g W, two orthonormal
families of the same size spanning the same subspace yield the same sum).
Retained strategy: bridge to this already proved machinery
(gv/isCFrameFunction_gv) rather than independently reimplementing it —
the only basis concatenation actually constructed by hand in the entire file
is that for add_isOrtho (Sublemma 5), over a much narrower scope (only A
and B) than the general construction of the extension itself.

Lean pitfall encountered and documented: Module.finrank ℂ (A ⊔ B)
(without explicit coercion to the underlying type) makes elaboration fail
(failed to synthesize instance Max Type) — Lean propagates the expected
type Type into the application of ⊔ before realizing that it must first
elaborate A ⊔ B : Submodule ℂ (H n) and then coerce the result. Systematic
remedy: write Module.finrank ℂ ↥(A ⊔ B) with explicit coercion ↥ whenever
the argument to Module.finrank/any function expecting a Type is a compound
expression (rather than a simple variable) built with a lattice operator on
Submodule values.

### U1 — Wigner corollary (B) in the language of projections — ✅ CLOSED (2026-07-13)

Addressed immediately after U3a, independently of U2/U3a/U3b:
wigner_projection_form depends only on wigner (W0–W6, already completed)
and on TraceProd/Proj1 (Defs.lean), not on Gleason.gleason or
ProjMeasure.

- [x] projL_singleton_unit (private): projL (ℂ∙x) y = ⟪x,y⟫•x for unit x,
 via Submodule.starProjection_singleton
- [x] Step 1 traceProd_mk_unit_eq:
 TraceProd (mk_unit x) (mk_unit y) =
 ‖⟪x,y⟫‖² —
 bornValue_span_singleton sufficed unchanged once
 projL_singleton_unit had been established, with no additional
 intermediate lemma
- [x] Step 2 T/T_unit/T_repr: construction of T : H n → H n by
 choosing (Classical.choose) a canonical unit representative of
 φ (mk_unit x hx), via exists_unit_vector_of_proj1
- [x] Step 3 isWignerMap_T: T satisfies IsWignerMap, by applying
 Step 1 in both directions around hypothesis hφ (preservation of
 TraceProd), then a²=b² ∧ a,b≥0 ⟹ a=b by nlinarith
 (sq_nonneg (a-b)/sq_nonneg (a+b))
- [x] Steps 4–5 wigner_projection_form:
 rcases wigner n T (isWignerMap_T
 hφ), reconstruction of
 IsWignerSymmetryProj φ by equality of lines
 (Submodule.span_singleton_smul_eq, c ≠ 0 from ‖c‖=1) in the two
 symmetric branches
- [x] guard.sh: 0 axioms, 0 native_decide, 4 sorry (5 − 1)

Reported discrepancy (Step 0 decision, point 3):
exists_unit_vector_of_proj1 is needed both here (U1) and in U3a
(GleasonExtend.lean, where it was private). Rather than (a) making it
public there and importing all of GleasonExtend.lean into
WignerProjectionForm.lean (which would create a file dependency from U1 —
intended to be independent of the rest — to U3a), or (b) duplicating it
locally, it was relocated to Defs.lean (public, shared) — a third option
not explicitly listed among the two proposed, judged superior to both: no
duplication and no superfluous file dependency. GleasonExtend.lean was
updated accordingly (private copy removed, proof unchanged).

### U2 — Elementary spectral lemma — ✅ CLOSED (2026-07-14)

Pure linear algebra, independent of Gleason.gleason/wigner/U3a. Reference
strategy directly inspired by Šemrl §2 (proof of the Claim): E fixes x,
then use the block decomposition [[1,0],[0,T]] over
H = span{x} ⊕ x⊥.

- [x] one_le_of_norm_eq_one (private): ‖x‖=1 ⟹ 1 ≤ n (H 0 is
 Subsingleton)
- [x] Sublemma 1 E_fixes_x: E x = x, via
 Gleason.positive_inner_self_eq_zero applied to 1 - E (positive by
 hE.2, symmetric — the IsPositiveOp bundle already contains
 LinearMap.IsSymmetric as its first component, confirmed in Step 0, so
 no separate self-adjointness derivation is needed) at x:
 ⟪(1-E)x,x⟫ = ⟪x,x⟫-⟪Ex,x⟫ =
 1-1 = 0 (hEx is directly a COMPLEX
 equality = 1, not merely an equality of real parts — no detour needed)
- [x] Final assembly
 eq_projL_of_positive_le_one_trace_one_inner_one: extend x to a
 COMPLETE orthonormal basis of H n
 (exists_orthonormalBasis_extension_complex, already used 3× in
 Uhlhorn), decompose the trace to obtain ⟪ρv,v⟫ = 1, and apply U2
 directly via isEffect_of_isDensityOperator
- [x] guard.sh: 0 axioms, 0 sorry. #print axioms:
 [propext, Classical.choice, Quot.sound]

Major advantageous discrepancy: the prototype reconstructs lam = 1
through a Parseval/Bessel identity on an ARBITRARY orthonormal basis
(symmetric_pos_zero_of_diag_zero + ~100 lines). Here, starting from the
hypothesis “ρ vanishes on v⊥” (strong form, not merely zero real part) and
extending v to an ADAPTED basis, the trace decomposition directly gives
⟪ρv,v⟫ = 1, and U2 establishes the COMPLETE operator equality in one
application — without ever reformulating the Parseval argument. The step
“zero diagonal ⟹ ρw = 0” (Gleason.positive_inner_self_eq_zero) is deferred
to B4, which needs it in any event to derive hker from (Null).

### B4 — Assembly.lean (final theorem) — ✅ CLOSED (2026-07-14)

- [x] hker_derivation: derives B3 hypothesis hker from AxNul, through a
 rescaling w → u := w/‖w‖. Advantageous difference: gluing
 g(w) = g(u) is a simple congrArg/Subtype.ext on equality of lines
 ℂ∙w = ℂ∙u — NOT another application of lemma4_noncontextual as in
 the prototype (gline there recomputed a distinct Perspective.binary
 for each vector, requiring Lemma 4 to glue two perspectives; since g
 is an ordinary function of Proj1 n, equal arguments have equal images
 with no additional noncontextuality argument). Further discrepancy
 discovered while writing the proof: neither ‖v‖=1 nor (Grain)/(Norm)
 is needed for this lemma — hypotheses removed from the signature
- [x] full_rho_facts: a single application of Gleason.gleason (B2)
 supplies a ρ that is both projL(ℂ∙v) (B3 + hker_derivation) AND
 compatible with g on every unit vector
- [x] grainCoherenceTheorem: final theorem, named exactly this way (NOT 𝒢
 as a Lean identifier — see docstring). Assembly via
 refinePerspective/refine_filter_eq_cellLines (B1, already proved —
 no new counting content needed here, unlike the prototype, which
 develops it at the same location as B4)
- [x] grainCoherenceTheorem_projector (v2.1-bornrule, 2026-07-20):
 direct public corollary Est D c = ‖projL c v‖². The sum produced by
 grainCoherenceTheorem is identified with the squared norm of the
 projection via sum_sq_projL_of_pairwise_isOrtho (cellLines c),
 cellLines_sSup, cellLines_sum_eq, and projL_singleton_unit;
 no new hypothesis and no duplication of a long Parseval proof
- [x] guard.sh: 0 axioms, 0 native_decide, 0 sorry throughout the
 repository. #print axioms grainCoherenceTheorem /
 grainCoherenceTheorem_projector / full_rho_facts /
 hker_derivation: [propext, Classical.choice, Quot.sound] —
 gleason NEVER appears as a separate axiom, unlike in
 tstar-born-rule-lean, where #print axioms theorem1_general
 additionally lists gleason.

No substantive discrepancy from the reconnaissance strategy — both
advantageous differences (gluing by congrArg rather than Lemma 4;
superfluous hv/(Grain)/(Norm) hypotheses in hker_derivation) were
discovered while writing the proof, not anticipated during reconnaissance.

### Nonvacuity — the Born rule satisfies all 4 axioms — ✅ CLOSED (2026-07-15)

Closes the gap identified during the final audit (departure from absolute
rule 3 of CLAUDE.md, since BornRule was then the only repository block
without Nonvacuity.lean): E₀ v D c := ‖projL c v‖² (Born rule for a fixed
unit vector v, ignores D — as does g in B2) SIMULTANEOUSLY satisfies
AxGrain, AxNorm, AxPos, AxNul — hence grainCoherenceTheorem is not
vacuously true.

- [x] refine_filter_sup_eq (Lemma 3, generalizes
 refine_filter_eq_cellLines from B1 to an ARBITRARY refinement D'
 rather than only the canonical refinePerspective D): the cells of
 D' below c cover exactly c. Nontrivial direction (c ≤ sup) via
 the resolution of the identity restricted to D'.cells
 (Gleason.projL_sup_of_pairwise_isOrtho): every x ∈ c is the sum of
 its projections onto the cells of D', while those outside c
 (parent ≠ c in D, via unique_parent) contribute 0 because they are
 orthogonal to c
- [x] norm_sq_sum_of_pairwise_orthogonal (private): finite Pythagorean
 theorem by direct bilinear expansion of the inner product
 (sum_inner/inner_sum + diagonal collapse via
 Finset.sum_eq_single)
- [x] sum_sq_projL_of_pairwise_isOrtho (private): combines resolution of
 the identity and finite Pythagoras — additivity of ‖projL · v‖² over
 an orthogonal family of cells
- [x] E₀_isPos, E₀_isNul: immediate (nonnegativity of a square;
 Submodule.starProjection_apply_eq_zero_iff for vanishing)
- [x] E₀_isNorm, E₀_isGrain: direct applications of
 sum_sq_projL_of_pairwise_isOrtho, respectively to D.cells
 (supremum =
 ⊤ via D.span) and to D'.cells.filter (· ≤ c)
 (supremum = c via refine_filter_sup_eq)
- [x] E₀_satisfies_axioms, combined witness, plus an example of concrete
 inhabitation on H 3
- [x] guard.sh: 0 axioms, 0 native_decide, 0 sorry throughout the
 repository. #print axioms on the 32 content-bearing declarations of
 BornRule (25 preceding + 7 new): [propext, Classical.choice,
 Quot.sound], without exception

Actual cost (explicitly answers the question raised during
reconnaissance): Gleason.projL_sup_of_pairwise_isOrtho (resolution of the
identity as an OPERATOR identity for a finite orthogonal family) was ALREADY
available in gleason-theorem-lean (Gleason/Operator.lean, O2a(ii)) — NOT
rederived here, unlike what U3b initially anticipated and then found
unnecessary for its own purpose (resolution directly through bornValue).
The finite Pythagorean theorem for ‖·‖² (rather than for bornValue, the
only case already covered in gleason-theorem-lean through
bornValue_sum_of_pairwise_isOrtho) was, however, not available as stated
and had to be derived here (norm_sq_sum_of_pairwise_orthogonal, ~15 lines,
direct bilinear expansion — not a heavy reconstruction).

### Out of scope (possible future extensions, not deficiencies of this milestone)

- A second derivation route, independent of Gleason: through a dynamical
 stability axiom rather than grain coherence. This development covers ONLY
 the descriptive route (Gleason).
- Intersubjective convergence between observers as a corollary of the main
 theorem: not addressed.

### Comparison with tstar-born-rule-lean

| | tstar-born-rule-lean (theorem1_general_en.lean) | quantum-foundations-lean (BornRule) |
|---|---|---|
| Space | abstract V (finite-dimensional) | directly H n := EuclideanSpace ℂ (Fin n) |
| Gleason | axiom gleason (unproved) | Gleason.gleason — actual theorem, pinned dependency |
| Axioms of theorem1_general/grainCoherenceTheorem | propext, Classical.choice, Quot.sound, gleason | propext, Classical.choice, Quot.sound |
| pinning | approximately 100 lines (Parseval/Bessel on arbitrary basis) | approximately 45 lines (trace decomposition on adapted basis + U2) |
| Rescaling in hker_derivation | lemma4_noncontextual (two distinct binary perspectives to glue) | congrArg/Subtype.ext (ordinary function of Proj1 n) |
| Fallbacks (Perspective.binary.span, basisPerspective.span) | first/sorry (2 potential sorry) | closed directly, 0 sorry |
| Sorries | 2 (fallback) | 0 |

Conclusion: strictly stronger — the same mathematical results (the same
final statement, with grainCoherenceTheorem equivalent to
theorem1_general), one fewer axiom (gleason proved rather than postulated),
and a shorter proof at several points thanks to reuse of the Uhlhorn
infrastructure (U2, U3a) and the Proj1-first design of g.

## Histories — Kent's contrary-inferences theorem

Statement. Kent, Quasiclassical Dynamics in a Closed Quantum System,
PRL 78, 2874 (1997), arXiv:gr-qc/9604012: within the finite-dimensional
consistent-histories framework, two consistent sets of histories may share
the same preparation ψ and the same postselection F, while each implies
with CERTAINTY a different proposition, the two propositions being mutually
ORTHOGONAL. A temporal stage of a history set IS a Perspective
(BornRule/Perspective.lean) — reused unchanged, with no redefinition
(confirmed during K0 reconnaissance). The generic profusion theorem of
Dowker–Kent (J. Stat. Phys. 82, 1575 (1996), parameter/dimension counting on
manifolds) is explicitly OUT OF SCOPE for this block — see “Out of scope”
below.

Proof decomposition (K0–K3):
- K0 — skeleton: History, IsHistoryOf, chainOp (ordered product of
 the projL values, with the final stage applied last), decFunctional
 (conjugate-linear on the left, with k conjugated), IsConsistent,
 histProb; Nonvacuity.lean (every Perspective, regarded as a one-stage
 family, is consistent) — 0 sorry, proved immediately (absolute rule 3).
- K1 — Basic.lean: decFunctional_last_stage_orthogonal (two histories
 differing at the last stage automatically have zero decoherence
 functional) and histProb_additivity_two_stage (finite Pythagoras, echoing
 AxGrain).
- K2 — Witness.lean: Kent's explicit witness in H 3 (ψ₀, φ₀
 unnormalized, P i := ℂ∙(e i), F := ℂ∙φ₀), S_consistent.
- K3 — ContraryInferences.lean: inference (conditional certainty,
 formulated without a quotient) and contrary_inferences (final theorem).

### K0 — Defs.lean + Nonvacuity.lean + K1–K3 skeleton — ✅ CLOSED (2026-07-16)

- [x] Reconnaissance (Part A): Perspective/Perspective.binary reusable as
 is; projL_singleton_unit (Uhlhorn/Defs.lean) confirmed for a unit
 vector, and Submodule.starProjection_singleton (Mathlib) confirmed for
 the general nonunit formula (ratio, avoids Real.sqrt);
 LinearMap.adjoint_inner_left/right confirmed (conjugate-linear-on-the-
 left convention); self-adjointness/idempotence of projL derivable in
 one line (Submodule.starProjection_isSymmetric,
 Submodule.isIdempotentElem_starProjection) — no preexisting
 “histories”/“decoherence functional” content (exhaustive grep).
- [x] History (n L : ℕ) := Fin L → Submodule ℂ (H n), IsHistoryOf,
 chainOp (Fin.foldl, with Fin.foldl_succ_last/Fin.foldl_zero
 checked for L = 1, 2), decFunctional, IsConsistent, histProb
- [x] isConsistent_single_stage: 0 sorry, immediate from orthogonality of
 the cells of a Perspective
- [x] PRIOR relocation (dedicated commit):
 norm_sq_sum_of_pairwise_orthogonal and
 sum_sq_projL_of_pairwise_isOrtho, private in
 BornRule/Nonvacuity.lean, moved to public scope in
 BornRule/Perspective.lean — generic geometric facts about
 Perspective, not specific to the Born witness of B-Nonvacuity, needed
 by K1(b). Same relocation pattern as
 exists_unit_vector_of_proj1/projL_singleton_unit (Uhlhorn) and
 isEffect_of_isDensityOperator (BornRule/B2).
- [x] K1 skeleton (2 sorry), K2 (1 sorry), K3 (2 sorry) — discrepancy from the
 initial estimate (3+2+2=7) justified by two parameterized factorizations
 (see K2/K3 below)
- [x] guard.sh: 0 axioms, 0 native_decide, 5 sorry (K0 itself: 0)

Reported discrepancy: guard.sh counts \bsorry\b by naive grep,
including in docstrings — the first versions of the K1–K3 files discussed the
“skeleton-sorry-first” discipline using the word “sorry” literally in prose,
inflating the count to 13. Repository convention (confirmed: zero occurrence
elsewhere): never write the word in comments; use “open goal” — corrected
before the K0 commit.

### K1 — Basic.lean — ✅ CLOSED (2026-07-16)

- [x] decFunctional_last_stage_orthogonal: through a private lemma
 chainOp_mem_last (the operator chain of a history with L+1 stages
 always lands in the cell at the final stage, with
 Fin.foldl_succ_last unfolded once)
- [x] histProb_additivity_two_stage: same recipe as E₀_isNorm
 (BornRule/Nonvacuity.lean) —
 sum_sq_projL_of_pairwise_isOrtho (now public) + resolution of the
 identity (D1.span, projL ⊤ = id)
- [x] guard.sh: 3 sorry remaining (K2, K3(a), K3(b))

Reported discrepancy: the third goal planned in the roadmap
(self-adjointness/idempotence of projL) was removed — derivable in one line
from Mathlib/gleason (reconnaissance A.2), never cited as a separate lemma for
lack of a second consumer before K2/K3.

### K2 — Witness.lean — ✅ CLOSED (2026-07-16)

- [x] Explicit data in H 3: e i := EuclideanSpace.single i 1,
 ψ₀ := e0+e1+e2, φ₀ := e0+e1-e2 (unnormalized — all contrary behavior
 is expressed through ratios in which 1/√3 cancels),
 P i := ℂ∙(e i), F := ℂ∙φ₀
- [x] STATEMENT CORRECTION (project rule 2). The K0 skeleton stated
 S_consistent (i : Fin 3) WITHOUT restricting i. False for i = 2:
 the key cancellation ⟪φ₀, ψ₀ - e i⟫ = 1 - ⟪φ₀, e i⟫ occurs only for
 i ∈ {0,1} (⟪φ₀,e 0⟫ = ⟪φ₀,e 1⟫ = 1, but
 ⟪φ₀,e 2⟫ = -1; φ₀ carries a negative sign on e2). Added the
 hypothesis i = 0 ∨ i = 1, the only domain in which the witness is used.
- [x] S_consistent: by decFunctional_last_stage_orthogonal (K1a), only
 pairs differing at stage 0 remain to be examined. Core calculation:
 P_proj_psi0 (projL (P i) ψ₀ = e i), projL_compl
 (projL Aᗮ = 1 - projL A, via
 Submodule.starProjection_orthogonal'), w_ortho (the vector
 w := ψ₀ - e i is orthogonal both to e i and to φ₀ — the latter is
 THE KEY CANCELLATION), projL_proj_absorb (absorption via
 self-adjointness + idempotence). The 4 residual cases
 (c1 ∈ {F, Fᗮ} × the two orders of {P i, (P i)ᗮ}) all close through
 w_ortho_projLc1_u/u_ortho_projLc1_w.
- [x] Difference from the roadmap: one parameterized open goal
 (S_consistent (i : Fin 3)) rather than two
 (S₁_consistent/S₂_consistent) — an option explicitly permitted by
 the plan “if duplication is burdensome.” S1_consistent/S2_consistent
 instantiate it without additional sorry.
- [x] guard.sh: 2 sorry remaining (K3(a), K3(b))

Documented simp friction point: unconstrained simp spontaneously rewrites
⟪x,x⟫_ℂ as ‖x‖² (default lemma) — in norm calculations, retain the
inner_self_eq_norm_sq_to_K rewrites (or the full bilinear expansion) UNTIL
AFTER expansion, never before, otherwise the calculation becomes stuck on an
already folded form.

### K3 — ContraryInferences.lean — ✅ CLOSED (2026-07-16)

- [x] STATEMENT CORRECTION (rule 2), for the same reason as in K2:
 inference (i : Fin 3) restricted to i = 0 ∨ i = 1, with the same
 cancellation failing at i = 2.
- [x] inference: branch (P i)ᗮ followed by F has ZERO probability
 (key cancellation w_ortho, reused from Witness.lean — made public on
 this occasion), while branch P i followed by F has NONZERO
 probability (projL F (e i) = (1/‖φ₀‖²) • φ₀ ≠ 0, via the new public
 lemmas φ₀_norm_sq and φ₀_ne_zero)
- [x] contrary_inferences: mechanical assembly, direct anonymous term from
 P_ortho, S_consistent 0/1 (K2), and inference 0/1 (K3a) —
 confirmed during reconnaissance before the skeleton was written, with
 no new mathematics at completion
- [x] Made public in Witness.lean (needed by K3, previously private):
 projL_compl, P_proj_psi0, projL_F_eq, w_ortho,
 chainOp_two_stage, phi0_inner_e01, and the new φ₀_norm_sq
- [x] guard.sh: 0 axioms, 0 native_decide, 0 sorry throughout the
 repository (five blocks). #print axioms on the 36 content-bearing
 declarations of Histories: [propext, Classical.choice, Quot.sound],
 without exception, including through the three-level chain
 Histories → BornRule (Perspective,
 projL_sup_of_pairwise_isOrtho relocated) → external Uhlhorn/Gleason.

### Out of scope (possible future extensions, not deficiencies of this milestone)

- The generic profusion theorem of Dowker–Kent (J. Stat. Phys. 82,
 1575 (1996)): parameter counting showing that the contrary behavior of the
 K2 witness is not an isolated case but generic in the space of consistent
 sets — not addressed, EXPLICITLY excluded by the initial request for this
 block.
- Weak consistency (only the real part of decFunctional, rather than the
 medium/strong consistency used here): mentioned in the docstring
 (Defs.lean), not formalized.
- Griffiths's “single-framework rule” (the usual response to Kent's
 objection): mentioned in the neutrality note
 (ContraryInferences.lean), not formalized — it is an interpretive
 argument, not an additional mathematical statement to prove.
