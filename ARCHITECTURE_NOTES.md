# ARCHITECTURE_NOTES.md — quantum-foundations-lean

Mémoire technique unique des écarts entre les plans initiaux (annoncés au
début de chaque jalon, dans les squelettes ou dans `MILESTONES.md`) et l'état
réel du code, tel qu'il a fini par être prouvé. Consolidé lors de la passe de
clôture arXiv (bloc N0–N5 Naimark, W0–W6 Wigner). Chaque entrée renvoie à la
section `MILESTONES.md` correspondante pour le détail de la dérivation.

## Naimark (N0–N5)

- **`DilSpace n m := EuclideanSpace ℂ (Fin m × Fin n)`** choisi sur
  `PiLp 2 (fun _ : Fin m => H n)` dès N0, à friction de preuve égale, pour son
  index plat unique (moins de couches `WithLp`/`.ofLp`). Voir `MILESTONES.md` N0.
- **Somme directe hilbertienne au lieu du produit tensoriel** (`K := ⊕ H n`
  plutôt que `X ⊗ ℂ^Σ` chez Watrous) : API `PiLp`/`EuclideanSpace` plus mûre
  côté Mathlib à la date du projet que celle du produit tensoriel hilbertien.
  Correspondance : `1_X ⊗ E_{a,a} ↦ dilProj a`, `√μ(a) ⊗ e_a ↦ singleL a ∘ₗ
  sqrtOp (E a)`. Contenu mathématique identique, seule la réalisation concrète
  de l'espace de dilatation diffère (README, section « Écart documenté »).
- **N5 (extension unitaire)** : l'esquisse de Paris §3.2 Thm 4 (« identité sur
  l'orthogonal de `ω_B` ») et les deux premières tentatives (`Submodule` +
  `orthogonalDecomposition`, puis `orthogonalProjectionOnto`) ont toutes deux
  échoué sur un **timeout déterministe au `whnf`** en composant des
  `LinearIsometryEquiv` construits par `.equivRange`/`.symm.trans` sur des
  sous-espaces définis par `LinearMap.range`. Route finale (tentative 3,
  réussie) : ZÉRO `Submodule` de bout en bout — deux familles orthonormées de
  `K` tout entier, complétées en bases complètes via
  `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` (isolé en lemme
  `private` pour éviter le timeout, cf. règle 12 AGENTS.md), puis recollées via
  `Orthonormal.equiv`. Voir `MILESTONES.md` N5, les trois tentatives datées.

## Wigner (W0–W6)

- **Namespace imbriqué `QuantumFoundations.Wigner`**, contrairement au
  namespace plat `QuantumFoundations` utilisé pour tout Naimark — délibéré :
  les noms internes de Wigner (`e`, `V`, `U`, `chi`, `T`) sont des lettres
  isolées calquées sur la notation de Bargmann, et auraient pollué l'espace de
  noms plat. `wigner` s'invoque donc `QuantumFoundations.Wigner.wigner`.
- **`hn : 2 ≤ n` filé dans toutes les signatures de W3 à W6** (absent du
  squelette W0) : pour `n < 2`, `eImg T` peut être nul et l'inversion
  `γ⁻¹ • T w` dégénère (`refVec` lui-même n'est défini que pour `n ≥ 2`,
  valeur poubelle sinon). `2 ≤ n` retenu (plutôt que `0 < n`, techniquement
  suffisant pour W3 seul) pour cohérence avec `Core.lean` (W4).
- **Cas `n = 1` traité de façon entièrement autonome** dans `wigner`, sans
  aucune dépendance sur W1–W5 (`hn : 2 ≤ n` jamais disponible dans cette
  branche) : `H 1` est de dimension 1 (`H1_eq_inner_smul_e`), et
  `U₁ x := ⟪e 1, x⟫ • eImg T` est directement ℂ-linéaire (pas seulement
  semilinéaire) ; placé par convention dans la branche `chi = id` (Bargmann
  §1.4 : les deux branches marchent, aucun moyen de les distinguer en
  dimension 1).
- **`V_colinear` (W3) : `‖δ‖ = ‖z‖`, PAS `‖δ‖ = 1` comme annoncé au départ.**
  L'énoncé squelette affirmait `‖δ‖ = 1`, réfuté par le contre-exemple
  `T = id` (`V T z = z` a pour norme `‖z‖`, pas nécessairement 1). Corrigé
  dès la preuve, cohérent avec `norm_V` et avec le commentaire Bargmann §3.2
  déjà présent dans `Defs.lean` (« `β'` a pour module `‖z‖` »).
- **`chidir_dichotomy` généralisée à tout `f` unitaire de `𝒫`** dès le
  squelette W4, pas seulement `refVec` — généralisation gratuite (la preuve ne
  simplifie pas en spécialisant à `refVec`), qui simplifie ensuite
  `chi_dichotomy` à un corollaire trivial en `f := refVec`.
- **`chi_eq_chidir` (W4) : réduction à un seul point de comparaison.**
  L'argument de Bargmann §4.3–4.5 (`w = f₁+f₂`, comparaison de coefficients
  d'un développement de Bessel 2D) ne fonctionne QUE pour des directions
  orthogonales — insuffisant dès que `n ≥ 3` et que `f` n'est ni colinéaire ni
  orthogonal à `refVec`. Résolu par réduction à un seul point `i` (où `id` et
  `conj` se distinguent) via `chidir_branch_transfer`, au lieu de l'identité
  fonctionnelle complète envisagée initialement. 8 lemmes privés au total pour
  ce seul sorry (contre 2 pour `chidir_dichotomy`/`chi_dichotomy`).
- **W6 (A)/(B) formulées en lemmes concrets plutôt qu'un `chi` abstrait
  paramétré.** Le plan initial de `MILESTONES.md` envisageait l'exclusivité comme
  un unique résultat paramétré par une notion abstraite de « `U` compatible de
  branche `chi` ». Formalisé en pratique comme DEUX lemmes séparés
  (`delta_transform_lin`/`delta_transform_conj`), un par branche concrète du
  théorème `wigner` (`≃ₗᵢ[ℂ]` / `≃ₛₗᵢ[starRingEnd ℂ]`), sans jamais introduire
  de `chi` abstrait — plus proche du théorème `wigner` réellement livré.
- **W6 (B) restreinte au périmètre effectif de `wigner`.** `Defs.lean` fixe
  `eImg T := T (e n)` (pas de paramètre pour choisir un autre représentant
  unitaire de la même classe). Plutôt que de rederiver le Théorème 2 complet
  de Bargmann §6 (un `U'` complètement arbitraire), l'unicité est établie par
  une reconstruction paramétrée LOCALE à `Uniqueness.lean` (`Vp`/`chidirp`/
  `chip`/`Up`, `eImg` explicite en argument), reliée à `V`/`chi`/`U` par des
  lemmes-pont `rfl` (`V_eq_Vp`, `chi_eq_chip`, `U_eq_Up`) — sans aucune
  modification de `Defs.lean`. Portée volontairement plus étroite que
  Bargmann §6 : seule la liberté effectivement exploitée par `wigner` (le
  choix du représentant de `eImg`) est couverte.
- **`conj_isometry_inner` (W6/A) dérivé à la main.**
  `LinearIsometryEquiv.inner_map_map` n'a pas d'analogue Mathlib pour les
  équivalences semilinéaires (`≃ₛₗᵢ[σ]`, `σ ≠ id`) — recherche confirmée dans
  le code source de `Mathlib/Analysis/InnerProductSpace/*`. Dérivé à la main
  via l'identité de polarisation complexe (parties réelle et imaginaire
  séparément, à partir de `norm_add_sq`/`norm_sub_sq`).

## Uhlhorn (U0–U5)

- **`Proj1 (n) := {A : Submodule ℂ (H n) // Module.finrank ℂ A = 1}`**, égalité
  de droites (`IsWignerSymmetryProj`, Option 1) plutôt que l'égalité
  opératorielle littérale `φ(P) = UPU*` (Option 2) — validé en reconnaissance
  U0 : les deux formulations sont équivalentes pour du rang 1, mais l'Option 2
  aurait exigé `LinearMap.adjoint` d'une équivalence semilinéaire
  (`≃ₛₗᵢ[starRingEnd ℂ]`), jamais rencontré ailleurs dans ce projet. Option 2
  laissée en remarque pour une passe ultérieure si le papier final en a besoin.
- **U3a isolé comme sous-jalon à part entière**, pas un détail interne de U3b.
  Découvert pendant la reconnaissance de U0 : aucun lemme « fonction-cadre sur
  les droites → `ProjMeasure` complet » n'existe dans `gleason-theorem-lean`
  (audité exhaustivement : les deux seuls sites de construction d'un
  `ProjMeasure`, `EffectMeasure.toProjMeasure` et `pureState`, donnent tous
  deux une formule fermée directement sur tout sous-espace). Décision : ce
  lemme reste dans `quantum-foundations-lean` (namespace `Uhlhorn`), pas dans
  `gleason-theorem-lean`, même génériquement Gleason — on ne rouvre pas le
  dépôt public tagué pour ce besoin. Découpage final à 6 jalons (U1, U2, U3a,
  U3b, U4, U5) au lieu des 5 initialement esquissés.
- **U3a — réutilisation de `Gleason.cframe_sum_invariant` au lieu d'une
  reconstruction manuelle de l'indépendance de base.** Le point délicat anticipé
  (indépendance du choix de base orthonormée pour l'extension) n'a pas été
  redémontré depuis zéro par concaténation `Fin k ⊕ Fin l → Fin n`
  (`finSumFinEquiv`/`Fin.append`) : `Gleason.Complex.RealSections` contient déjà
  cet argument sous forme vectorielle (`cframe_sum_invariant`, pour une
  fonction-cadre `H n → ℝ`). La seule concaténation de bases construite à la
  main dans tout U3a est celle d'`add_isOrtho` (via `Sum.elim`), sur un
  périmètre bien plus restreint que la construction générale de l'extension.
- **U3b — Sous-lemme « densité ⟹ effet » absent de `gleason-theorem-lean`,
  dérivé localement.** Confirmé absent en reconnaissance (positivité + trace 1
  en dimension finie ⟹ `≤ 1`, car les valeurs propres d'une densité sont
  positives et somment à 1) ; dérivé via la même technique de décomposition de
  trace autour d'un point que U2 (`isEffect_of_isDensityOperator`,
  `GleasonTwice.lean`).
- **U3b — la résolution de l'identité comme identité D'OPÉRATEURS
  (`∑ i, projL (ℂ∙(bi)) = 1`, via `Gleason.projL_sup_of_pairwise_isOrtho`)
  s'est avérée NON nécessaire.** `LinearMap.trace_eq_sum_inner` donne
  directement la trace d'un opérateur comme somme sur N'IMPORTE QUELLE base
  orthonormée — en particulier la base image de `φ` (garantie complète par
  `SendsONBToONB`) — sans jamais former l'opérateur somme explicitement.
- **U5 — le point d'incertitude principal (comportement du constructeur
  `OrthonormalBasis` vis-à-vis des valeurs pointwise) s'est résolu
  favorablement dès le premier essai.** `basisOfOrthonormalOfCardEqFinrank`
  (famille orthonormée + cardinalité → `Basis`) suivi de
  `Module.Basis.toOrthonormalBasis` préservent tous deux les valeurs POINTWISE
  exactement (`coe_basisOfOrthonormalOfCardEqFinrank`/
  `Module.Basis.coe_toOrthonormalBasis`, deux lemmes `@[simp]` existants) — pas
  seulement à un reindexing près. Aucun lemme de compatibilité supplémentaire
  n'a été nécessaire.
- **`exists_unit_vector_of_proj1` et `projL_singleton_unit` relocalisés en
  `Defs.lean`** (public, partagé) au fil des jalons plutôt que dupliqués ou
  laissés `private` dans un seul fichier — même pattern que
  `one_le_of_norm_eq_one` (nécessaire en U2 et U3b). Discipline systématique
  dès qu'un même besoin réapparaît dans un second fichier : relocalisation
  immédiate, jamais de copie.
- **Dépendance double, sans fuite d'axiome.** `uhlhorn_finite_dim` (U5) est le
  premier théorème du dépôt à dépendre à la fois de `Gleason.gleason`
  (dépendance externe épinglée) ET de `QuantumFoundations.Wigner.wigner`
  (bloc interne). `#print axioms` confirme le trio standard malgré cette
  double chaîne — voir README, section « Dépendances ».

## BornRule (B1–B4)

- **Formulé directement pour `V := H n`**, plutôt qu'un espace abstrait `V`
  générique — `Gleason.gleason` est spécifique à `H n`, et
  `Module.finrank ℂ (H n) = n` (`simp`) élimine une couche de cast pour les
  bases de l'espace entier (`basisPerspective`/`line_ne_bot`/`line_ne_top`/
  `line_injective`).
- **B1 — les deux replis potentiels (`Perspective.binary.span`,
  `basisPerspective.span`) se referment directement sur `H n`**, sans
  reconstruction : respectivement `Submodule.sup_orthogonal_of_hasOrthogonalProjection`
  (instance `HasOrthogonalProjection` automatique en dimension finie) et
  `Submodule.span_range_eq_iSup` (déjà exploité côté
  `Gleason.ProjMeasure.isCFrameFunction`).
- **B2 — `g : Proj1 n → ℝ` construit directement sur les droites**
  (`Perspective.binary (P:Submodule) ...`), sans intermédiaire vectoriel : la
  valeur ne dépend que de la droite `(P : Submodule)`, jamais d'un
  représentant unitaire. Conséquence favorable en cascade sur B4 (voir
  plus bas).
- **B2 — relocalisation de `isEffect_of_isDensityOperator`** (+
  `density_inner_le_one`, `sub_nonneg_of_density`), `private` dans
  `Uhlhorn/GleasonTwice.lean` (U3b), migré public vers `Uhlhorn/Defs.lean` —
  nécessaire depuis B3, même pattern de relocalisation systématique que
  `exists_unit_vector_of_proj1`/`projL_singleton_unit`/`one_le_of_norm_eq_one`
  lors de U1/U2/U3a.
- **B3 — identification de `ρ` par décomposition de trace sur une base
  ADAPTÉE à `v`** (`exists_orthonormalBasis_extension_complex`), donnant
  directement `⟪ρv,v⟫ = 1`, puis U2
  (`eq_projL_of_positive_le_one_trace_one_inner_one`) conclut l'égalité
  opératorielle complète en une seule application — pas de détour par une
  identité de Parseval/Bessel sur une base quelconque.
- **B4 — le recalibrage `w → u := w/‖w‖` de `hker_derivation` ne nécessite PAS
  `lemma4_noncontextual`** : puisque `g` (B2) est une fonction ordinaire de
  `Proj1 n`, l'égalité de droites `ℂ∙w = ℂ∙u` se transporte directement en
  égalité de `Proj1 n` (`Subtype.ext`) et `g(w) = g(u)` suit par simple
  `congrArg` — conséquence directe de la conception `Proj1`-first de B2.
- **B4 — hypothèses superflues retirées de `hker_derivation`** : ni `‖v‖ = 1`
  ni (Grain)/(Norm) ne sont nécessaires (découvert en écrivant la preuve, pas
  anticipé en reconnaissance) — `AxNul` ne suppose pas `v` unitaire, et le
  recollement ci-dessus ne passe pas par la non-contextualité.
- **Dépendance double, sans fuite d'axiome.** `grainCoherenceTheorem` (B4) est
  le second théorème du dépôt (après `uhlhorn_finite_dim`) à dépendre à la
  fois d'une dépendance externe (`Gleason.gleason`) et de contenu interne
  substantiel (infrastructure Uhlhorn U2/U3a). `#print axioms` confirme le
  trio standard sur les deux maillons de cette chaîne — voir README, section
  « Dépendances ».
- **Corollaire projecteur (`v2.1-bornrule`, 2026-07-20).**
  `grainCoherenceTheorem_projector` reformule directement le membre droit de
  `grainCoherenceTheorem` en `‖projL c v‖²`. Ce n'est pas une nouvelle route
  mathématique : `sum_sq_projL_of_pairwise_isOrtho` est appliqué à
  `cellLines c`, `Finset.sup_id_eq_sSup` et `cellLines_sSup` identifient leur
  supremum à `c`, `cellLines_sum_eq` réindexe la somme, puis
  `projL_singleton_unit` et `norm_inner_symm` identifient chaque terme.
  L'audit `#print axioms` reste exactement
  `[propext, Classical.choice, Quot.sound]`.
- **Hors scope explicite** (extensions futures possibles, pas des manques de
  ce jalon) : une seconde route de dérivation indépendante de Gleason (via un
  axiome de stabilité dynamique plutôt que de cohérence de grain),
  l'existence/consistance des axiomes (Grain)/(Norm)/(Pos)/(Null) eux-mêmes,
  et la convergence intersubjective entre observateurs comme corollaire du
  théorème principal — voir `MILESTONES.md`, section « Hors scope ».

## HistoriesKent (K0–K3)

- **Relocalisation préalable de `norm_sq_sum_of_pairwise_orthogonal` et
  `sum_sq_projL_of_pairwise_isOrtho`**, `private` dans `BornRule/Nonvacuity.lean`,
  migrés public vers `BornRule/Perspective.lean`, dans un commit dédié AVANT
  le début de K0. Justification : ce sont des faits géométriques génériques
  sur `Perspective` (Pythagore fini + valeur de Born additive sur un sup
  orthogonal), pas spécifiques au témoin de Born construit dans
  `BornRule/Nonvacuity.lean` — leur place naturelle est à côté de la
  définition de `Perspective`, dans le fichier que `HistoriesKent` importe déjà.
  Même logique que les relocalisations antérieures
  (`exists_unit_vector_of_proj1`/`projL_singleton_unit` en Uhlhorn,
  `isEffect_of_isDensityOperator` U3b→Uhlhorn/Defs.lean lors de B2) :
  dès qu'un même besoin réapparaît dans un second fichier/bloc, relocalisation
  immédiate, jamais de copie. Vérifié sans impact sur les axiomes de
  `BornRule` (audit de clôture HistoriesKent, Bloc 1 point spécifique 2 —
  35 déclarations après ajout du corollaire projecteur, trio standard sans
  exception).
- **Deux corrections d'énoncé (règle 2 du projet), même cause, découvertes
  au moment de remplir les preuves (pas anticipées en reconnaissance) :**
  `S_consistent` (K2, `Witness.lean`) et `inference` (K3, `ContraryInferences.lean`)
  étaient énoncés dans le squelette K0 pour `i : Fin 3` SANS restriction.
  Faux pour `i = 2` : `⟪φ₀, e i⟫ = 1` pour `i ∈ {0,1}` mais `= -1` pour
  `i = 2` (`φ₀ := e0+e1-e2` porte un signe négatif sur `e2`), donc
  l'annulation clé `⟪φ₀, ψ₀ - e i⟫ = 1 - ⟪φ₀, e i⟫` ne s'annule que pour
  `i ∈ {0,1}`. Ajout de l'hypothèse `i = 0 ∨ i = 1` dans les deux cas,
  commise avec message explicite plutôt que silencieusement affaiblie.
- **Point de friction `simp` documenté** : `simp` non contraint réécrit
  spontanément `⟪x,x⟫_ℂ` en `‖x‖²` (lemme par défaut de la bibliothèque),
  ce qui bloque tout calcul voulant D'ABORD expanser bilinéairement un
  produit scalaire puis SEULEMENT ENSUITE revenir à une norme. Règle
  retenue dans `Witness.lean`/`ContraryInferences.lean` : les rewrites
  `inner_self_eq_norm_sq_to_K` (ou l'expansion bilinéaire complète via
  `simp only` contraint) viennent TOUJOURS après l'expansion, jamais avant.
- **Convention d'ordre de `chainOp`, fixée dès `Defs.lean` et vérifiée par
  calcul explicite** : la classe d'opérateurs d'une histoire
  `h : Fin L → Submodule ℂ (H n)` est `C_h = P_{h(L-1)} ∘ ⋯ ∘ P_{h(0)}`, le
  DERNIER étage appliqué EN DERNIER — implémentée par `Fin.foldl L (fun acc
  t => projL (h t) ∘ₗ acc) LinearMap.id`, dont le déroulement a été vérifié
  explicitement pour `L = 1, 2` via `Fin.foldl_succ_last`/`Fin.foldl_zero`
  (`chainOp_two_stage` en `L = 2` : `projL (h 1) ∘ₗ projL (h 0)`, exactement
  la convention physique standard).
- **Orientation de `decFunctional`, fixée dès `Defs.lean`** :
  `decFunctional ψ h k := ⟪chainOp k ψ, chainOp h ψ⟫_ℂ` porte `k` conjugué —
  cohérent avec la convention conj-linéaire à GAUCHE du produit scalaire
  Mathlib utilisée dans tout le dépôt (confirmée via
  `LinearMap.adjoint_inner_left`/`right` en reconnaissance).
- **Un seul but ouvert paramétré au lieu de deux, à K2 ET K3** :
  `S_consistent (i : Fin 3)` (au lieu de `S₁_consistent`/`S₂_consistent`) et
  `inference (i : Fin 3)` (au lieu de `inference_S₁`/`inference_S₂`) — les
  deux preuves ne diffèrent que par l'indice `i ∈ {0,1}`, structurellement
  identiques. Option explicitement autorisée par le plan initial
  (« si la duplication est lourde, factorise »). Conséquence en cascade :
  `contrary_inferences` (K3b) s'est avéré s'assembler MÉCANIQUEMENT une fois
  `inference` clos — un simple terme anonyme, sans tactique ni mathématiques
  nouvelles, confirmé en reconnaissance avant l'écriture du squelette et
  vérifié à la fermeture.

## Résidus documentaires identifiés lors de l'audit de clôture

- `QuantumFoundations/Wigner/Uniqueness.lean` : les lemmes-pont privés
  `V_eq_Vp` et `chi_eq_chip` (destinés à documenter que `Vp`/`chip` redonnent
  `V`/`chi` au représentant canonique) ne sont en réalité invoqués par aucune
  preuve — seul `U_eq_Up` est consommé par `U_alt_eq_smul`. Ils restent
  cependant la seule vérification machine de l'affirmation faite dans le
  commentaire de section (B). `chidir_eq_chidirp` (même fichier) va plus
  loin : ni consommé ni mentionné dans le commentaire — candidat naturel à la
  suppression, non supprimé ici (décision laissée à l'utilisateur).
- `QuantumFoundations/Wigner/VConstruction.lean:340`,
  `inner_V_eq_of_im_eq_zero` (eq. 12a de Bargmann) : prouvé mais jamais utilisé
  par une preuve ultérieure — la route finalement empruntée par `Core.lean`
  (W4) passe par `inner_V_eq_chi_inner`, qui ne redérive pas ce corollaire.
  Fidèle au blueprint (Bargmann énonce explicitement 12a), gardé pour cette
  raison malgré l'absence de consommateur interne.
- `QuantumFoundations/Naimark/DilSpace.lean` : `dilProj_isSymmetric`,
  `dilProj_idempotent`, `dilProj_orthogonal`, `dilProj_sum_eq_one` ne sont
  utilisés par aucune preuve ultérieure de `Main.lean` (`naimark`/`naimark_born`
  passent par les pivots `key1`/`key2`, pas par ces quatre faits). Ce n'est
  PAS un oubli : ils formalisent explicitement Watrous Prop. 2.40 (les
  opérateurs d'une mesure projective sont deux à deux orthogonaux, idempotents,
  de somme l'identité) — un engagement mathématique documenté dans `AGENTS.md`
  indépendant du chemin de preuve de `naimark` lui-même.
- `QuantumFoundations/Uhlhorn/` : audit spécifique lors de la clôture du bloc —
  **aucun résidu identifié**. Les deux seules déclarations publiques sans
  second point d'usage dans le dossier (`isWignerSymmetryProj_id`,
  `uhlhorn_finite_dim`) sont l'une un témoin de non-vacuité terminal, l'autre
  le théorème final du bloc — toutes deux attendues comme points d'entrée, pas
  des orphelins. `sendsONBToONB_of_preservesOrthogonality` est `private` comme
  prévu (consommé uniquement par `uhlhorn_finite_dim`, dans le même fichier).
- `QuantumFoundations/HistoriesKent/Basic.lean`, `histProb_additivity_two_stage` :
  prouvé (K1(b), tel que demandé par la feuille de route : « version minimale
  suffisante pour K3 ») mais jamais consommé par aucune preuve ultérieure — la
  route finalement empruntée par `inference` (K3a) passe directement par
  `projL_F_eq`/`w_ortho` sur le témoin concret, sans repasser par l'additivité
  générique des probabilités d'histoires. Gardé pour la même raison que
  `inner_V_eq_of_im_eq_zero` en Wigner : c'est l'écho explicitement demandé
  d'`AxGrain` (BornRule), un engagement mathématique documenté indépendant du
  chemin de preuve finalement suivi par K3. Reste de `HistoriesKent` audité sans
  autre résidu : toutes les autres déclarations publiques ont au moins un
  second point d'usage (directement ou via `S1_consistent`/`S2_consistent`,
  eux-mêmes non consommés en interne mais explicitement demandés par la
  feuille de route comme spécialisations terminales de `S_consistent`, au
  même titre que `isWignerSymmetryProj_id` en Uhlhorn).

## Divergences de convention de nommage Naimark ↔ Wigner (listées, non corrigées)

- **Style des identifiants d'objets centraux.** Naimark utilise des noms
  composés en camelCase orientés implémentation (`dilV`, `dilProj`, `singleL`,
  `coordL`, `sqrtOp`). Wigner utilise des lettres isolées calquant directement
  la notation de Bargmann (`e`, `V`, `U`, `T`, `chi`, `eImg`). Les deux styles
  sont cohérents en interne mais tranchent nettement entre les deux blocs —
  reflet du fait que Naimark n'a pas de notation source unique à respecter
  (Watrous n'introduit pas de symboles aussi courts), alors que Wigner suit
  Bargmann lettre à lettre.
- **Structure vs Prop pour l'hypothèse principale.** Naimark bundle ses trois
  propriétés dans une `structure POVM` (accès par projection : `P.pos`,
  `P.sum_eq_one`). Wigner utilise un unique `def IsWignerMap (T) : Prop`
  (une seule propriété, threadée comme hypothèse `hT`). Différence dictée par
  le nombre de propriétés à bundler, pas un choix de style arbitraire.
- Le reste (docstrings `/-- ... -/` juste au-dessus de la déclaration,
  français partout, préfixe `h` pour les hypothèses, `private` pour les
  lemmes internes) est identique entre les deux blocs.

Ces deux points de nommage sont cosmétiques et ne cassent aucune référence
externe (aucun autre dépôt n'importe ce projet à ce jour) — harmonisation
laissée à la discrétion de l'utilisateur avant publication.

## Cohérence de nommage Uhlhorn vs Naimark/Wigner

- **Namespace imbriqué `QuantumFoundations.Uhlhorn`**, comme Wigner (pas plat
  comme Naimark) — cohérent avec la règle « nouveau bloc mathématique = son
  propre namespace » déjà établie.
- **Style des identifiants** : ni le style camelCase-implémentation de Naimark
  (`dilV`, `singleL`) ni les lettres isolées à la Bargmann de Wigner (`e`, `V`,
  `U`) — Uhlhorn utilise des noms complets descriptifs
  (`SendsONBToONB`, `PreservesOrthogonality`, `TraceProd`,
  `exists_projMeasure_of_frameFunctionOnLines`). Cohérent avec le fait
  qu'Uhlhorn n'a pas de notation source à respecter lettre à lettre (Šemrl
  2021 n'introduit pas de symboles aussi courts que Bargmann) — un TROISIÈME
  style, mais chacun interne cohérent et justifié par sa source.
- Docstrings (`/-- ... -/`), commentaires de jalon (`/-! # Ux — titre ... -/`
  avec écarts signalés en tête de fichier), français partout, préfixe `h` pour
  les hypothèses, `private` pour les lemmes internes : identiques aux deux
  blocs précédents, aucune divergence.

## Cohérence de nommage BornRule vs Naimark/Wigner/Uhlhorn

- **Namespace imbriqué `QuantumFoundations.BornRule`**, comme Wigner/Uhlhorn —
  cohérent.
- **Style des identifiants : hybride, un QUATRIÈME style.** `g` (une lettre)
  suit le style Bargmann/Wigner ; `Perspective`, `Refines`, `hker_derivation`,
  `full_rho_facts` suivent le style descriptif d'Uhlhorn ; mais
  `AxGrain`/`AxNorm`/`AxPos`/`AxNul` introduisent un préfixe `Ax*` inédit dans
  ce dépôt — les trois blocs précédents nomment leurs `Prop` d'hypothèse soit
  par un préfixe `Is*` (`IsWignerMap`, `IsWignerSymmetryProj`,
  `IsFrameFunctionOnLines`), soit par un nom descriptif nu
  (`PreservesOrthogonality`, `SendsONBToONB`). Non harmonisé ici (listé,
  non corrigé), la source de référence de ce bloc n'ayant pas de préfixe
  `Is*` naturel pour des axiomes numérotés.
- **`grainCoherenceTheorem` (camelCase) tranche avec la convention
  snake_case** des autres théorèmes-têtes de chapitre (`naimark`,
  `naimark_born`, `wigner`, `uhlhorn_finite_dim`) — choix délibéré (nom ASCII
  pour un objet mathématique noté par un symbole non-ASCII), listé, non
  corrigé.
- Docstrings, préfixe `h` pour les hypothèses, `private` pour les lemmes
  internes : identiques aux trois blocs précédents, aucune divergence.
- **Écart de conformité à la règle 3 (Nonvacuity), identifié lors de l'audit
  de clôture — RÉSOLU (2026-07-15, `BornRule/Nonvacuity.lean`).**
  `E₀ v D c := ‖projL c v‖²` (règle de Born pour un vecteur unitaire `v` fixé)
  habite simultanément `AxGrain`/`AxNorm`/`AxPos`/`AxNul`. Le point technique
  central (`refine_filter_sup_eq`, généralisant `refine_filter_eq_cellLines`
  de B1 à un raffinement arbitraire) réutilise
  `Gleason.projL_sup_of_pairwise_isOrtho` (résolution de l'identité comme
  opérateur, déjà disponible dans `gleason-theorem-lean`) — seul le théorème
  de Pythagore fini sur `‖·‖²` (absent tel quel, `gleason-theorem-lean` ne
  couvrant que l'additivité de `bornValue`) a dû être dérivé, en ~15 lignes.

## Cohérence de nommage HistoriesKent vs Naimark/Wigner/Uhlhorn/BornRule

- **Namespace imbriqué `QuantumFoundations.HistoriesKent`**, comme
  Wigner/Uhlhorn/BornRule — cohérent.
- **Style des identifiants : hybride, comme BornRule, mais selon un clivage
  différent.** Les définitions structurelles (`Defs.lean`) suivent le style
  descriptif d'Uhlhorn/BornRule (`History`, `IsHistoryOf`, `chainOp`,
  `decFunctional`, `IsConsistent`, `histProb`) ; le témoin concret
  (`Witness.lean`) bascule vers des lettres/symboles isolés à la Bargmann/Wigner
  (`e`, `ψ₀`, `φ₀`, `P`, `F`, `S`) — mais ici le clivage suit une frontière
  claire (infrastructure générique vs données numériques concrètes d'un
  exemple), contrairement au mélange BornRule (`g` isolé au milieu de noms
  descriptifs sans séparation par fichier). `IsHistoryOf`/`IsConsistent`
  suivent le préfixe `Is*` déjà établi par Uhlhorn (`IsWignerMap`,
  `IsWignerSymmetryProj`) — PAS le préfixe `Ax*` introduit par BornRule pour
  ses quatre hypothèses, cohérence restaurée avec le style majoritaire du
  dépôt plutôt qu'avec le bloc immédiatement précédent.
- **`ψ₀`/`φ₀` (indice zéro explicite) plutôt que `psi`/`phi` bruts** :
  notation empruntée à la physique des états quantiques (état initial
  indicé), absente des blocs précédents (aucun n'introduit de vecteur d'état
  concret nommé par une lettre grecque) — cohérente en interne, nouvelle par
  nécessité (premier bloc à construire un témoin numérique explicite plutôt
  que de raisonner sur des objets génériques).
- **`S` (une lettre) pour la famille d'histoires**, `D1`/`Dstage`/`DF` pour
  les perspectives d'étage : mélange same-file du style Bargmann (`S`) et
  descriptif (`Dstage`, `DF`) — non harmonisé plus finement, mais chacun
  suffisamment local (utilisé seulement dans `Witness.lean`/
  `ContraryInferences.lean`) pour ne pas créer d'ambiguïté.
- Docstrings, préfixe `h` pour les hypothèses, `private` pour les lemmes
  internes : identiques aux quatre blocs précédents, aucune divergence.

---

## English translation

# ARCHITECTURE_NOTES.md — quantum-foundations-lean

Single technical record of deviations between the initial plans (announced at
the beginning of each milestone, in the skeletons, or in MILESTONES.md) and the
actual state of the code as ultimately proved. Consolidated during the arXiv
closing pass (Naimark block N0–N5, Wigner block W0–W6). Each entry refers to the
corresponding section of MILESTONES.md for details of the derivation.

## Naimark (N0–N5)

- DilSpace n m := EuclideanSpace ℂ (Fin m × Fin n) was chosen over
 PiLp 2 (fun _ : Fin m => H n) at N0, at equal proof-engineering cost,
 because of its single flat index (fewer WithLp/.ofLp layers). See
 MILESTONES.md N0.
- Hilbert direct sum rather than tensor product (K := ⊕ H n rather than
 Watrous's X ⊗ ℂ^Σ): at the time of the project, the Mathlib API for
 PiLp/EuclideanSpace was more mature than that for Hilbert tensor
 products. Correspondence:
 1_X ⊗ E_{a,a} ↦ dilProj a,
 √μ(a) ⊗ e_a ↦ singleL a ∘ₗ
 sqrtOp (E a). The mathematical content is
 identical; only the concrete realization of the dilation space differs
 (README, section “Documented deviation”).
- N5 (unitary extension): the sketch in Paris §3.2 Thm 4 (“identity on the
 orthogonal complement of ω_B”) and the first two attempts (Submodule +
 orthogonalDecomposition, then orthogonalProjectionOnto) both failed with
 a deterministic timeout at whnf when composing LinearIsometryEquiv
 values constructed through .equivRange/.symm.trans on subspaces defined
 by LinearMap.range. Final route (attempt 3, successful): ZERO Submodule
 throughout—two orthonormal families in the whole space K, extended to
 complete bases via
 Orthonormal.exists_orthonormalBasis_extension_of_card_eq (isolated in a
 private lemma to avoid the timeout; see rule 12 in AGENTS.md), and then
 glued together via Orthonormal.equiv. See MILESTONES.md N5 for the three
 dated attempts.

## Wigner (W0–W6)

- Nested namespace QuantumFoundations.Wigner, unlike the flat
 QuantumFoundations namespace used throughout Naimark—deliberate: Wigner's
 internal names (e, V, U, chi, T) are single letters matching
 Bargmann's notation and would have polluted the flat namespace. wigner is
 therefore invoked as QuantumFoundations.Wigner.wigner.
- hn : 2 ≤ n threaded through all signatures from W3 to W6 (absent from
 the W0 skeleton): for n < 2, eImg T may be zero and the inversion
 γ⁻¹ • T w degenerates (refVec itself is defined only for n ≥ 2, with a
 junk value otherwise). 2 ≤ n was selected rather than 0 < n, which is
 technically sufficient for W3 alone, for consistency with Core.lean (W4).
- The case n = 1 is handled entirely independently in wigner, with no
 dependence on W1–W5 (hn : 2 ≤ n is never available in this branch):
 H 1 has dimension 1 (H1_eq_inner_smul_e), and
 U₁ x := ⟪e 1, x⟫ • eImg T is directly ℂ-linear, not merely semilinear. By
 convention it is placed in the chi = id branch (Bargmann §1.4: both
 branches work and cannot be distinguished in dimension 1).
- V_colinear (W3): ‖δ‖ = ‖z‖, NOT ‖δ‖ = 1 as initially announced.
 The skeleton statement asserted ‖δ‖ = 1, refuted by the counterexample
 T = id (V T z = z has norm ‖z‖, not necessarily 1). It was corrected
 while proving the result, consistently with norm_V and with the comment
 from Bargmann §3.2 already present in Defs.lean (“β' has modulus
 ‖z‖”).
- chidir_dichotomy generalized to every unit f in 𝒫 already in the
 W4 skeleton, not only to refVec—a free generalization, since specializing
 to refVec does not simplify the proof, and it makes chi_dichotomy a
 trivial corollary with f := refVec.
- chi_eq_chidir (W4): reduction to a single comparison point.
 Bargmann's argument in §4.3–§4.5 (w = f₁+f₂, comparison of coefficients in
 a two-dimensional Bessel expansion) works ONLY for orthogonal directions,
 which is insufficient when n ≥ 3 and f is neither collinear nor
 orthogonal to refVec. This was resolved by reducing to the single point
 i, at which id and conj differ, via chidir_branch_transfer, rather
 than proving the full functional identity initially envisaged. Eight
 private lemmas were needed for this single sorry, compared with two for
 chidir_dichotomy/chi_dichotomy.
- W6 (A)/(B) formulated as concrete lemmas rather than through an abstract
 parameterized chi. The initial MILESTONES.md plan envisaged exclusivity
 as a single result parameterized by an abstract notion of a “compatible U
 in branch chi.” In practice it was formalized as TWO separate lemmas
 (delta_transform_lin/delta_transform_conj), one for each concrete branch
 of the theorem wigner (≃ₗᵢ[ℂ] / ≃ₛₗᵢ[starRingEnd ℂ]), without ever
 introducing an abstract chi, which is closer to the theorem wigner actually delivered.
- W6 (B) restricted to the effective scope of wigner. Defs.lean fixes
 eImg T := T (e n) and has no parameter for choosing another unit
 representative of the same class. Rather than rederiving the full
 Bargmann §6 Theorem 2 for a completely arbitrary U', uniqueness is proved
 using a reconstruction parameterized LOCALLY in Uniqueness.lean
 (Vp/chidirp/chip/Up, with eImg as an explicit argument), related to
 V/chi/U by rfl bridge lemmas
 (V_eq_Vp, chi_eq_chip, U_eq_Up)—without any modification of
 Defs.lean. The scope is intentionally narrower than Bargmann §6: only the
 freedom actually used by wigner, the choice of representative of eImg,
 is covered.
- conj_isometry_inner (W6/A) derived manually.
 LinearIsometryEquiv.inner_map_map has no Mathlib analogue for semilinear
 equivalences (≃ₛₗᵢ[σ], σ ≠ id), as confirmed by searching the source of
 Mathlib/Analysis/InnerProductSpace/*. It was derived manually through the
 complex polarization identity, treating real and imaginary parts
 separately from norm_add_sq/norm_sub_sq.

## Uhlhorn (U0–U5)

- Proj1 (n) := {A : Submodule ℂ (H n) // Module.finrank ℂ A = 1}, with
 equality of lines (IsWignerSymmetryProj, Option 1) rather than literal
 operator equality φ(P) = UPU* (Option 2)—validated during U0
 reconnaissance: the two formulations are equivalent for rank-one
 projections, but Option 2 would have required LinearMap.adjoint of a
 semilinear equivalence (≃ₛₗᵢ[starRingEnd ℂ]), never encountered elsewhere
 in this project. Option 2 is left as a remark for a later pass if the final
 paper requires it.
- U3a isolated as a full submilestone, not an internal detail of U3b.
 Discovered during U0 reconnaissance: no lemma “frame function on lines →
 full ProjMeasure” exists in gleason-theorem-lean (exhaustive audit: the
 only two ProjMeasure construction sites,
 EffectMeasure.toProjMeasure and pureState, both provide a closed formula
 directly on every subspace). Decision: this lemma remains in
 quantum-foundations-lean (namespace Uhlhorn), not in
 gleason-theorem-lean, although it is a generic Gleason fact; the tagged
 public repository is not reopened for this need. The final plan therefore
 has six milestones (U1, U2, U3a, U3b, U4, U5) rather than the five initially
 sketched.
- U3a—reuse of Gleason.cframe_sum_invariant rather than a manual
 reconstruction of basis independence. The anticipated delicate point,
 independence of the choice of orthonormal basis for the extension, was not
 reproved from scratch by concatenating
 Fin k ⊕ Fin l → Fin n (finSumFinEquiv/Fin.append):
 Gleason.Complex.RealSections already contains this argument in vector
 form (cframe_sum_invariant, for a frame function H n → ℝ). The only
 basis concatenation constructed manually in all of U3a is that of
 add_isOrtho (via Sum.elim), over a much narrower scope than the general
 construction of the extension.
- U3b—Sublemma “density ⟹ effect” absent from gleason-theorem-lean,
 derived locally. Its absence was confirmed during reconnaissance
 (positivity + trace 1 in finite dimension ⟹ ≤ 1, because the eigenvalues
 of a density operator are nonnegative and sum to 1); it was derived using
 the same trace-decomposition-around-a-point technique as U2
 (isEffect_of_isDensityOperator, GleasonTwice.lean).
- U3b—the resolution of the identity as an OPERATOR identity
 (∑ i, projL (ℂ∙(bi)) = 1, via
 Gleason.projL_sup_of_pairwise_isOrtho) proved UNNECESSARY.
 LinearMap.trace_eq_sum_inner directly gives the trace of an operator as a
 sum over ANY orthonormal basis—in particular the image basis under φ,
 whose completeness is guaranteed by SendsONBToONB—without ever explicitly
 forming the sum operator.
- U5—the main uncertainty (behavior of the OrthonormalBasis constructor
 with respect to pointwise values) was resolved favorably on the first
 attempt. basisOfOrthonormalOfCardEqFinrank (orthonormal family +
 cardinality → Basis), followed by Module.Basis.toOrthonormalBasis,
 preserve values exactly POINTWISE
 (coe_basisOfOrthonormalOfCardEqFinrank/
 Module.Basis.coe_toOrthonormalBasis, two existing @[simp] lemmas), not
 merely up to reindexing. No additional compatibility lemma was needed.
- exists_unit_vector_of_proj1 and projL_singleton_unit moved to
 Defs.lean (public, shared) over the course of the milestones rather than
 duplicated or left private in a single file—the same pattern as
 one_le_of_norm_eq_one (needed in U2 and U3b). Systematic discipline:
 whenever the same need reappears in a second file, move it immediately;
 never copy it.
- Dual dependency, without axiom leakage. uhlhorn_finite_dim (U5) is the
 first theorem in the repository to depend both on Gleason.gleason
 (pinned external dependency) AND on
 QuantumFoundations.Wigner.wigner (internal block). #print axioms
 confirms the standard trio despite this dual chain; see README, section
 “Dependencies.”

## BornRule (B1–B4)

- Formulated directly for V := H n, rather than for a generic abstract
 space V: Gleason.gleason is specific to H n, and
 Module.finrank ℂ (H n) = n (simp) eliminates one layer of casts for
 bases of the whole space (basisPerspective/line_ne_bot/line_ne_top/
 line_injective).
- B1—the two potential fallback proofs (Perspective.binary.span,
 basisPerspective.span) close directly over H n, without
 reconstruction: respectively through
 Submodule.sup_orthogonal_of_hasOrthogonalProjection
 (automatic finite-dimensional HasOrthogonalProjection instance) and
 Submodule.span_range_eq_iSup (already used in
 Gleason.ProjMeasure.isCFrameFunction).
- B2—g : Proj1 n → ℝ constructed directly on lines
 (Perspective.binary (P:Submodule) ...), without a vector intermediary:
 the value depends only on the line (P : Submodule), never on a unit
 representative. This has favorable downstream consequences for B4 (see
 below).
- B2—relocation of isEffect_of_isDensityOperator (+
 density_inner_le_one, sub_nonneg_of_density), previously private in
 Uhlhorn/GleasonTwice.lean (U3b), to public declarations in
 Uhlhorn/Defs.lean. This was required by B3, following the same systematic
 relocation pattern as
 exists_unit_vector_of_proj1/projL_singleton_unit/one_le_of_norm_eq_one
 during U1/U2/U3a.
- B3—identification of ρ by trace decomposition in a basis ADAPTED to
 v (exists_orthonormalBasis_extension_complex), directly giving
 ⟪ρv,v⟫ = 1; U2
 (eq_projL_of_positive_le_one_trace_one_inner_one) then concludes the full
 operator equality in a single application, with no detour through a
 Parseval/Bessel identity in an arbitrary basis.
- B4—the rescaling w → u := w/‖w‖ in hker_derivation does NOT require
 lemma4_noncontextual: because g (B2) is an ordinary function on
 Proj1 n, the equality of lines ℂ∙w = ℂ∙u transports directly to an
 equality in Proj1 n (Subtype.ext), and g(w) = g(u) follows from a
 simple congrArg. This is a direct consequence of the Proj1-first design
 of B2.
- B4—superfluous hypotheses removed from hker_derivation: neither
 ‖v‖ = 1 nor (Grain)/(Norm) is needed (discovered while writing the proof,
 not anticipated during reconnaissance). AxNul does not assume that v
 is unit, and the gluing above does not pass through non-contextuality.
- Dual dependency, without axiom leakage. grainCoherenceTheorem (B4) is
 the second theorem in the repository, after uhlhorn_finite_dim, to depend
 both on an external dependency (Gleason.gleason) and on substantial
 internal content (Uhlhorn infrastructure U2/U3a). #print axioms confirms
 the standard trio at both links in this chain; see README, section
 “Dependencies.”
- Projector corollary (v2.1-bornrule, 2026-07-20).
 grainCoherenceTheorem_projector directly reformulates the right-hand side
 of grainCoherenceTheorem as ‖projL c v‖². This is not a new
 mathematical route: sum_sq_projL_of_pairwise_isOrtho is applied to
 cellLines c; Finset.sup_id_eq_sSup and cellLines_sSup identify their
 supremum with c; cellLines_sum_eq reindexes the sum; and
 projL_singleton_unit and norm_inner_symm identify each term.
 The #print axioms audit remains exactly
 [propext, Classical.choice, Quot.sound].
- Explicitly out of scope (possible future extensions, not omissions from
 this milestone): a second derivation route independent of Gleason (using a
 dynamic-stability axiom rather than grain coherence), existence/consistency
 of the axioms (Grain)/(Norm)/(Pos)/(Null) themselves, and intersubjective
 convergence between observers as a corollary of the main theorem—see
 MILESTONES.md, section “Out of scope.”

## HistoriesKent (K0–K3)

- Prior relocation of norm_sq_sum_of_pairwise_orthogonal and
 sum_sq_projL_of_pairwise_isOrtho, previously private in
 BornRule/Nonvacuity.lean, to public declarations in
 BornRule/Perspective.lean, in a dedicated commit BEFORE K0 began.
 Rationale: these are generic geometric facts about Perspective (finite
 Pythagoras + additivity of the Born value over an orthogonal supremum), not
 specific to the Born witness constructed in BornRule/Nonvacuity.lean.
 Their natural location is next to the definition of Perspective, in the
 file already imported by HistoriesKent. This follows the same logic as
 previous relocations (exists_unit_vector_of_proj1/projL_singleton_unit
 in Uhlhorn, isEffect_of_isDensityOperator U3b→Uhlhorn/Defs.lean during B2): whenever the same need reappears in a second
 file/block, relocate it immediately; never copy it. Verified to have no
 effect on the axioms of BornRule (HistoriesKent closing audit, Block 1,
 specific point 2—35 declarations after adding the projector corollary,
 with the standard trio and no exceptions).
- Two corrections to statements (project rule 2), with the same cause,
 discovered while filling the proofs rather than anticipated during
 reconnaissance: S_consistent (K2, Witness.lean) and inference
 (K3, ContraryInferences.lean) were stated in the K0 skeleton for
 unrestricted i : Fin 3. This is false for i = 2:
 ⟪φ₀, e i⟫ = 1 for i ∈ {0,1} but = -1 for i = 2
 (φ₀ := e0+e1-e2 has a negative sign on e2), so the key cancellation
 ⟪φ₀, ψ₀ - e i⟫ = 1 - ⟪φ₀, e i⟫ holds only for i ∈ {0,1}. The
 hypothesis i = 0 ∨ i = 1 was added in both cases and committed with an
 explicit message rather than silently weakened.
- Documented simp friction point: unconstrained simp spontaneously
 rewrites ⟪x,x⟫_ℂ as ‖x‖² using a default library lemma, which blocks a
 calculation that must FIRST expand an inner product bilinearly and ONLY
 THEN return to a norm. Rule adopted in
 Witness.lean/ContraryInferences.lean: rewrites by
 inner_self_eq_norm_sq_to_K (or the full bilinear expansion through
 constrained simp only) ALWAYS occur after expansion, never before.
- Ordering convention for chainOp, fixed in Defs.lean and verified by
 explicit calculation: the class operator of a history
 h : Fin L → Submodule ℂ (H n) is
 C_h = P_{h(L-1)} ∘ ⋯ ∘ P_{h(0)}, with the FINAL stage APPLIED LAST. It is
 implemented by
 Fin.foldl L (fun acc
 t => projL (h t) ∘ₗ acc) LinearMap.id, whose
 unfolding was explicitly checked for L = 1, 2 using
 Fin.foldl_succ_last/Fin.foldl_zero
 (chainOp_two_stage at L = 2:
 projL (h 1) ∘ₗ projL (h 0), exactly the standard physical convention).
- Orientation of decFunctional, fixed in Defs.lean:
 decFunctional ψ h k := ⟪chainOp k ψ, chainOp h ψ⟫_ℂ has k conjugated,
 consistently with Mathlib's LEFT-conjugate-linear inner-product convention
 used throughout the repository (confirmed through
 LinearMap.adjoint_inner_left/right during reconnaissance).
- One parameterized open goal rather than two in BOTH K2 and K3:
 S_consistent (i : Fin 3) rather than
 S₁_consistent/S₂_consistent, and inference (i : Fin 3) rather than
 inference_S₁/inference_S₂. The two proofs differ only in the index
 i ∈ {0,1} and are structurally identical. This option was explicitly
 permitted by the initial plan (“if duplication is substantial, factor it
 out”). A downstream consequence is that contrary_inferences (K3b) proved
 to assemble MECHANICALLY once inference was closed: a simple anonymous
 term, with no tactics or new mathematics, as confirmed during
 reconnaissance before the skeleton was written and verified upon closure.

## Documentary residues identified during the closing audit

- QuantumFoundations/Wigner/Uniqueness.lean: the private bridge lemmas
 V_eq_Vp and chi_eq_chip, intended to document that Vp/chip reproduce
 V/chi at the canonical representative, are in fact invoked by no proof;
 only U_eq_Up is consumed by U_alt_eq_smul. They nevertheless remain the
 only machine verification of the claim made in the comment for section (B).
 chidir_eq_chidirp in the same file goes further: it is neither consumed
 nor mentioned in the comment and is a natural candidate for deletion, but
 was not deleted here (decision left to the user).
- QuantumFoundations/Wigner/VConstruction.lean:340,
 inner_V_eq_of_im_eq_zero (Bargmann's Eq. 12a): proved but never used in a
 later proof. The route ultimately taken in Core.lean (W4) proceeds through
 inner_V_eq_chi_inner, which does not rederive this corollary. It remains
 faithful to the blueprint, since Bargmann explicitly states 12a, and is
 retained for that reason despite having no internal consumer.
- QuantumFoundations/Naimark/DilSpace.lean: dilProj_isSymmetric,
 dilProj_idempotent, dilProj_orthogonal, and dilProj_sum_eq_one are not
 used by any later proof in Main.lean; naimark/naimark_born proceed
 through the pivots key1/key2, not through these four facts. This is NOT
 an omission: they explicitly formalize Watrous Prop. 2.40 (the operators
 of a projection-valued measure are pairwise orthogonal, idempotent, and sum
 to the identity), a mathematical commitment documented in AGENTS.md and
 independent of the proof path for naimark itself.
- QuantumFoundations/Uhlhorn/: a specific audit during closure of the block
 identified no residue. The only two public declarations without a
 second point of use in the directory (isWignerSymmetryProj_id,
 uhlhorn_finite_dim) are respectively a terminal nonvacuity witness and the
 final theorem of the block—both expected entry points, not orphans.
 sendsONBToONB_of_preservesOrthogonality is private as intended and is
 consumed only by uhlhorn_finite_dim in the same file.
- QuantumFoundations/HistoriesKent/Basic.lean,
 histProb_additivity_two_stage: proved (K1(b), as requested by the roadmap:
 “minimal version sufficient for K3”) but never consumed by a later proof.
 The route ultimately taken by inference (K3a) proceeds directly through
 projL_F_eq/w_ortho on the concrete witness, without returning to generic
 additivity of history probabilities. It is retained for the same reason as
 inner_V_eq_of_im_eq_zero in Wigner: it is the explicitly requested echo of
 AxGrain (BornRule), an independently documented mathematical commitment
 regardless of the proof route ultimately followed by K3. The rest of
 HistoriesKent was audited with no additional residue: every other public
 declaration has at least a second use (directly or through
 S1_consistent/S2_consistent, themselves not consumed internally but
 explicitly requested by the roadmap as terminal specializations of
 S_consistent, in the same way as isWignerSymmetryProj_id in Uhlhorn).

## Naimark ↔ Wigner naming-convention divergences (listed, not corrected)

- Style of central-object identifiers. Naimark uses implementation-oriented
 compound camelCase names (dilV, dilProj, singleL, coordL, sqrtOp).
 Wigner uses isolated letters directly matching Bargmann's notation
 (e, V, U, T, chi, eImg). Both styles are internally coherent
 but sharply differ between the two blocks. This reflects the fact that
 Naimark has no single source notation to preserve—Watrous does not
 introduce such short symbols—whereas Wigner follows Bargmann letter for
 letter.
- Structure vs Prop for the principal hypothesis. Naimark bundles its three
 properties in a structure POVM, accessed through projections P.pos and
 P.sum_eq_one. Wigner uses a single
 def IsWignerMap (T) : Prop, since there is only one property, threaded as
 hypothesis hT. The difference is dictated by the number of properties to
 bundle, not by an arbitrary stylistic choice.
- Everything else (docstrings /-- ... -/ immediately above declarations,
 French throughout, prefix h for hypotheses, and private for internal
 lemmas) is identical between the two blocks.

These two naming points are cosmetic and break no external references, since
no other repository currently imports this project. Harmonization is left to
the user's discretion before publication.

## Uhlhorn naming consistency relative to Naimark/Wigner

- Nested namespace QuantumFoundations.Uhlhorn, as in Wigner rather than
 flat as in Naimark—consistent with the established rule “new mathematical
 block = its own namespace.”
- Identifier style: neither Naimark's implementation-oriented camelCase
 (dilV, singleL) nor Wigner's isolated Bargmann-style letters
 (e, V, U). Uhlhorn uses full descriptive names
 (SendsONBToONB, PreservesOrthogonality, TraceProd,
 exists_projMeasure_of_frameFunctionOnLines). This is consistent with the
 fact that Uhlhorn has no source notation to reproduce letter for letter
 (Šemrl 2021 does not introduce symbols as short as Bargmann's)—a THIRD
 style, but each block is internally coherent and justified by its source.
- Docstrings (/-- ... -/), milestone comments
 (/-! # Ux — titre ... -/ with documented deviations at the beginning of
 the file), French throughout, prefix h for hypotheses, and private for
 internal lemmas are identical to the two preceding blocks, with no
 divergence.

## BornRule naming consistency relative to Naimark/Wigner/Uhlhorn

- Nested namespace QuantumFoundations.BornRule, as in Wigner/Uhlhorn—
 consistent.
- Identifier style: hybrid, a FOURTH style. g, a single letter, follows
 the Bargmann/Wigner style; Perspective, Refines, hker_derivation, and
 full_rho_facts follow Uhlhorn's descriptive style; but
 AxGrain/AxNorm/AxPos/AxNul introduce an Ax* prefix not previously
 used in this repository. The previous three blocks name hypothesis Prop
 values either with an Is* prefix (IsWignerMap,
 IsWignerSymmetryProj, IsFrameFunctionOnLines) or with a bare descriptive
 name (PreservesOrthogonality, SendsONBToONB). This is not harmonized
 here (listed, not corrected), because the reference source for this block
 has no natural Is* prefix for numbered axioms.
- grainCoherenceTheorem (camelCase) differs from the snake_case convention
 of the other chapter-level theorems (naimark, naimark_born, wigner,
 uhlhorn_finite_dim). This was a deliberate choice—an ASCII name for a
 mathematical object denoted by a non-ASCII symbol—and is listed but not
 corrected.
- Docstrings, prefix h for hypotheses, and private for internal lemmas are
 identical to the three preceding blocks, with no divergence.
- Deviation from compliance with rule 3 (Nonvacuity), identified during the
 closing audit—RESOLVED (2026-07-15,
 BornRule/Nonvacuity.lean).
 E₀ v D c := ‖projL c v‖², the Born rule for a fixed unit vector v,
 simultaneously inhabits AxGrain/AxNorm/AxPos/AxNul. The central
 technical point (refine_filter_sup_eq, generalizing
 refine_filter_eq_cellLines from B1 to an arbitrary refinement) reuses
 Gleason.projL_sup_of_pairwise_isOrtho (resolution of the identity as an
 operator, already available in gleason-theorem-lean). Only the finite
 Pythagorean theorem for ‖·‖², absent in that exact form because
 gleason-theorem-lean covers only additivity of bornValue, had to be
 derived, in ~15 lines.

## HistoriesKent naming consistency relative to Naimark/Wigner/Uhlhorn/BornRule

- Nested namespace QuantumFoundations.HistoriesKent, as in
 Wigner/Uhlhorn/BornRule—consistent.
- Identifier style: hybrid, as in BornRule, but along a different divide.
 The structural definitions in Defs.lean follow the descriptive
 Uhlhorn/BornRule style (History, IsHistoryOf, chainOp,
 decFunctional, IsConsistent, histProb); the concrete witness in
 Witness.lean switches to isolated Bargmann/Wigner-style letters and
 symbols (e, ψ₀, φ₀, P, F, S). Here, however, the divide follows
 a clear boundary—generic infrastructure versus concrete numerical data for
 an example—unlike the BornRule mixture, where isolated g appears among
 descriptive names without a file boundary. IsHistoryOf/IsConsistent
 follow the Is* prefix already established by Uhlhorn (IsWignerMap,
 IsWignerSymmetryProj), NOT the Ax* prefix introduced by BornRule for its
 four hypotheses, restoring consistency with the predominant repository
 style rather than with the immediately preceding block.
- ψ₀/φ₀ (explicit zero subscript) rather than bare psi/phi:
 notation borrowed from quantum-state physics, where initial states are
 indexed, and absent from the preceding blocks because none introduced a
 concrete state vector named by a Greek letter. It is internally coherent
 and newly required here, since this is the first block to construct an
 explicit numerical witness rather than reason only about generic objects.
- S (a single letter) for the history family, with
 D1/Dstage/DF for stage perspectives: a same-file mixture of the
 Bargmann style (S) and descriptive style (Dstage, DF). It is not
 harmonized further, but each identifier is sufficiently local—used only in
 Witness.lean/ContraryInferences.lean—to avoid ambiguity.
- Docstrings, prefix h for hypotheses, and private for internal lemmas are
 identical to the four preceding blocks, with no divergence.

## Complexity (C0–C11) — exact, robust, and explicit 2-local proxy gaps

- **Syntax and evaluation.** `TwoLocalGate N d` stores a linear isometric
  equivalence on `BranchesRiedel.Sites N d`, a region `Finset (Fin N)`, the
  existing proof `IsLocalTo`, and a support-cardinality proof `≤ 2`.
  `Circuit N d` is a `List`; its chronological convention is
  `[G₁,G₂,G₃].eval x = G₃ (G₂ (G₁ x))`. Consequently,
  `eval (C ++ D) = eval D ∘ₗ eval C`.
- **Representation bridge.** Riedel's branches live on `H (d ^ N)`, whereas
  locality lives on `Sites N d`. The API therefore requires the same
  explicit isometry `e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d` already used by
  `BranchesRiedel.Local`; `Circuit.evalOnH` conjugates circuit evaluation by `e`.
- **Reused Riedel facts.** C1 uses `commute_of_disjoint` gate by gate,
  `branch_wellDefined` plus `rproj_contract_apply` for the two record
  identities, and `Submodule.starProjection_isSymmetric` for self-adjointness.
  No general projection theory is reconstructed.
- **Composition closure.** The circuit commutation proof explicitly combines
  commuting factors with `Commute.mul_left`; it does not rely on simp to infer
  closure under composition.
- **Counting separation.** `Counting.lean` is independent of Hilbert spaces.
  It injects each pairwise disjoint touched region into the finite union
  support and then composes this bound with
  `Circuit.circuit_support_card_le`.
- **Why `pigeonhole_corollary` is not reused.** Its exact conclusion is
  `¬ PairCovers recA recB`; it assumes two equally indexed families, requires
  `3 ≤ R`, and bounds every member of the first family by one site. The C2
  problem instead has an arbitrary number of gate supports, each of cardinal
  at most two, and must produce a quantitative inequality for every `R`.
  Wrapping the old lemma would obscure the stronger generic counting fact.
- **Proof-engineering friction.** Dot notation for the `Circuit` list abbrev
  becomes ambiguous inside list induction, so recursive proofs use explicit
  `Circuit.eval`/`Circuit.support`. The only analytic bridge needed was
  deconjugating commutation through `e`; the cross-amplitude calculation then
  follows the four transparent projector equalities directly.
- **Exact proxies (C3).** `DistinguishesAt` and `InterferesAt` use the
  division-free inequalities `2 * δ ≤ ‖diagonal difference‖` and
  `2 * δ ≤ ‖cross₁‖ + ‖cross₂‖`. `normalizedBranch` is a complex scalar
  multiple of the existing unnormalized `branch`; unit norm and nonzeroness
  are only asserted under an explicit nonzero-branch hypothesis. The
  relational `HasInterferenceLowerBound`,
  `HasDistinguishabilityUpperBound`, and `HasProxyGapAtLeast` certificates
  were completed before defining any infimum.
- **Two cross orientations (C4).** A positive interference proxy only gives a
  disjunction between oppositely oriented cross amplitudes. C2 is therefore
  applied once with `(i,j)` and once with swapped labels. Locality of the
  transported record projector is required separately for both target labels;
  assuming it only for `j` would be unsound.
- **Explicit readout cost (C5).** `ImplementsRecordPhaseFlip e D Λ j` is the
  exact operator equality `Circuit.evalOnH D e = 2 • rproj Λ j - id`.
  The circuit `D` is supplied as a witness: spatial locality alone does not
  imply a constant-size synthesis. No optional one-gate corollary was needed.
- **Certificates before minima (C6).** The physical gap theorem first combines
  the C4 lower certificate and C5 witness with
  `D.length + g ≤ ceilHalf R`. Only then is
  `minCircuitLength P := ⨅ C, if P C then ↑C.length else ⊤` introduced in
  `WithTop ℕ`. Subtraction is avoided because it is truncated on naturals and
  interacts poorly with `⊤`; the final statement is
  `distinguishabilityComplexity + g ≤ interferenceComplexity`.
- **C3–C6 API friction.** The normalization proof needed explicit complex
  coercions for the inverse real norm. The `iInf` encoding needed a local
  classical decidability choice for `if P C`; casts between `ℕ` and
  `WithTop ℕ` were discharged explicitly with `exact_mod_cast`. No attainment
  theorem was required.
- **Finite reversible evolution (C7).**
  `ReversibleCircuitEvolution N d` contains separate `forward` and `backward`
  circuits and proofs that their evaluations are mutual inverses on
  `Sites N d`. Its overhead is exactly
  `forward.length + backward.length`; the general theorem deliberately does
  not assume that an inverse can be synthesized for free.
- **Concatenation and conjugation direction.** Since
  `eval (C ++ D) = eval D ∘ₗ eval C`, the list
  `backward ++ C ++ forward` is `pushForward` and evaluates to
  `forward ∘ₗ C ∘ₗ backward`. Conversely,
  `forward ++ C ++ backward` is `pullBack` and evaluates to
  `backward ∘ₗ C ∘ₗ forward`. The same formulas are proved after transport
  to `H (d ^ N)` through `evalOnH`.
- **Canonical inverse.** C7 proves locality of a unitary inverse directly
  from the kernel witness in `IsLocalTo`, defines `TwoLocalGate.inverse`, and
  reverses/inverts circuit lists in `Circuit.inverse`. It proves equal length
  and support, both evaluation cancellation laws, involutivity, and builds
  `ReversibleCircuitEvolution.ofCircuit E` with overhead `2 * E.length`.
- **Exact proxy transport.** Circuit evaluation preserves complex inner
  products, norms, nonzeroness, and unit norm. The push-forward and pullback
  theorems identify the underlying complex matrix elements exactly, so both
  Taylor–McCulloch proxy predicates are transported by equivalences. Evolved
  normalized branches are not normalized again.
- **Why the gap budget loses twice the overhead.** A distinguishing witness
  is pushed forward at cost one overhead, while an evolved interference
  circuit is pulled back at cost one overhead. Thus the certificate budget is
  `D + 2 * overhead + g ≤ B`. For `ofCircuit E`, the overhead itself is
  `2 * E.length`, yielding the derived factor `4 * E.length`.
- **Certificates and minima remain distinct.** `Persistence.lean` and
  `RecordPersistence.lean` prove the finite relational statements first.
  `PersistenceMinima.lean` then proves a generic witness-map theorem directly
  under the `WithTop ℕ` infimum using `ENat.iInf_add`; it handles `⊤` without
  assuming attainment. No subtraction is used in either `Nat` or
  `WithTop ℕ`.
- **C7 scope.** This is conditional circuit-complexity persistence for an
  explicit finite reversible evolution. It is not persistence for arbitrary
  Hamiltonian time evolution, generic complexity growth, approximate-record
  robustness, macroscopic irreversibility, branch uniqueness, an equivalence
  with Weingarten's proposal, a Brown–Susskind result, or a proof of an
  interpretation of quantum mechanics.

- **Aggregated approximate records (C8).** The primary predicate is exactly
  `ApproxRecordFor P target other η :=
  ‖P target - target‖ + ‖P other‖ ≤ η`.  The fixing defect and leakage are
  aggregated because the untouched-cross-amplitude proof consumes their sum
  directly, with no factor loss. `ApproxRecordedPairOn` assigns independent
  budgets `ηi` and `ηj` to the two target labels on every region.
- **Sharp untouched-region estimate.** The proof splits the target vector
  into its projected part and defect, moves the symmetric projector across
  the inner product, commutes it through the untouched circuit, and applies
  Cauchy–Schwarz plus the unitary norm bound. It obtains
  `‖cross amplitude‖ ≤ η`, hence the two proxy orientations total at most
  `ηi + ηj`. Therefore the strict threshold `ηi + ηj < 2 * δ` forces every
  record region to be touched; the existing C2 counting theorem is reused.
- **Approximate explicit readout.** `ApproximatesRecordPhaseFlipOn` bounds the
  sum of the circuit's pointwise errors on the two supplied unit vectors by
  `ξ`. The ideal phase reflection together with the target-label approximate
  record yields diagonal separation at least `2 - (2 * ηj + ξ)`. Thus
  `2 * δ + 2 * ηj + ξ ≤ 2` is the exact sufficient distinguishability
  threshold. The readout circuit remains explicit; locality alone still does
  not provide a synthesis theorem.
- **Robust gaps and persistence.** C8 first combines the robust lower and
  upper relational certificates, then reuses the existing `WithTop ℕ`
  minimum layer. Exact records and exact phase flips instantiate the new
  predicates at errors zero, recovering C4–C6. C7's exact proxy conjugation
  transports the resulting certificate without adding analytic error; only
  the combinatorial budget pays `2 * Evo.overhead`, or `4 * E.length` for the
  canonical inverse, recovering the exact C7 interface at zero error.
- **C8 scope.** The results are quantitative consequences of supplied
  approximate records and a supplied approximate readout on finite systems.
  They do not construct such records from decoherence, synthesize arbitrary
  record readouts, treat continuous-time/Hamiltonian simulation or complexity
  growth, prove irreversible branching or branch uniqueness, establish a
  Weingarten equivalence, or support an interpretive claim.
- **Deferred operator-norm bridge.** `Circuit.evalOnH` and
  `recordPhaseFlip` currently use plain `LinearMap`; the Complexity and
  BranchesRiedel APIs contain no `ContinuousLinearMap`/operator-norm layer.
  Adding one solely for the optional `2ε` pointwise bridge would be a broad
  representation change, so that bridge remains future C12 work.

- **Explicit repetition model (C9).** `configurationEquiv R` uses
  `finFunctionFinEquiv.symm`, and `sitesEquivR` reindexes the standard
  `H (2^R)` coordinates onto binary site configurations. `zeroBranch` and
  `oneBranch` are the constant-zero/constant-one basis vectors transported
  back through this equivalence. `repetitionState` is their unnormalized sum;
  only its component branches are required and proved to have unit norm.
- **Coordinate records.** At site `r`, `sitesCell R r b` is the span of basis
  configurations with coordinate `b`. Its transported pair of orthogonal
  subspaces is `siteResolution R r`. Orthogonal-projection transport uses
  `Submodule.starProjection_map_apply`; locality is proved directly from the
  diagonal matrix kernel. Singleton regions are independent because distinct
  singletons are disjoint.
- **Concrete readout.** The readout gate is the Mathlib orthogonal reflection
  in the bit-one cell at `firstSite R`, hence exactly `2 P₁ - I`. Its locality
  proof computes the `±1` diagonal kernel rather than unfolding the internal
  `LinearIsometryEquiv` structure. The singleton circuit has length one and
  gives `distinguishabilityComplexity = 1`; the reverse inequality uses that
  every zero-length list is empty and acts identically.
- **Concrete interference.** `bitFlipConfigurationEquiv` is a pointwise
  `Equiv.swap 0 1` at one coordinate, lifted by `piLpCongrLeft`. The circuit
  maps `bitFlipGate` over `List.finRange R`; a fold invariant proves that each
  coordinate is flipped exactly once. Thus it exchanges the two branches,
  has length `R`, and proves the interference minimum is finite.
- **C9 quantitative closure.** Instantiating C4–C7, rather than reproving them,
  gives `ceilHalf R ≤ C_I ≤ R`, `C_D = 1`, every gap satisfying
  `1 + g ≤ ceilHalf R`, and the evolved certificate under
  `1 + 4 * E.length + g ≤ ceilHalf R`.
- **Optional sharpness not implemented.** No existing Mathlib equivalence
  directly pairs consecutive elements of arbitrary `Fin R`. Exact attainment
  at `ceilHalf R` would require new paired-support coverage, cardinality, and
  simultaneous-flip locality infrastructure. C9 therefore makes only the
  mandatory linear bounds and no false exactness claim.

- **Explicit noisy repetition model (C10).** `R + 1` sites: source qubit `0`
  plus `R` record qubits at `recordSite r := Fin.succ r`. Four computational
  configurations cross the source bit with the constant record bit
  (`config00`/`config01`/`config10`/`config11`, built with `Fin.cases`, not
  classical choice). `NoiseProfile` packages a normalized `keep`/`leak` pair;
  `noisyZeroBranch`/`noisyOneBranch` mix the two same-source configurations,
  staying exactly orthogonal because the source bit differs between them —
  the Pythagorean norm identity for orthogonal unit vectors (via
  `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`) and `p.norm_sq`
  give unit norm without any smallness assumption on `leak`.
- **Additive C9 generalizations, not replacements.** C10 needed three pieces
  of C9 infrastructure at a generality C9 itself never required: a basis
  vector at an arbitrary (not just constant) configuration
  (`configurationBranch`, added to `States.lean`), a reflection readout at an
  arbitrary (not just `firstSite`) site (`recordReadoutGateAt`/
  `recordReadoutCircuitAt`, added to `Readout.lean`), and the all-bit-flip
  action on an arbitrary (not just constant) configuration
  (`allBitFlipCircuit_maps_configurationBranch`, added to `Interference.lean`).
  In each case the existing C9 declaration was reproved as the new generic
  lemma's special case, with no change to its public type. A fourth addition,
  `one_le_distinguishabilityComplexity_of_pos` in `Distinguishability.lean`,
  generalizes the existing threshold-one zero-length non-distinguishability
  argument to an arbitrary positive threshold — the argument never used that
  the threshold was exactly one, only that it was positive.
- **Exact per-site record errors, not `IsRecordedOn`.** Reusing C9's generic
  `siteProj_apply_configuration`, every record projector's action on each of
  the four basis vectors is an exact equality (fixes or kills outright,
  depending on whether the projector's label matches the site's constant
  record bit). Linearity then gives the *exact* norms
  `‖P_b(noisyBranch) − noisyBranch‖ = ‖leak‖` (fixing defect) and
  `‖P_b(other noisyBranch)‖ = ‖leak‖` (leakage) at every record site, which
  sum to the aggregate `ApproxRecordedPairOn` budget `2 * ‖leak‖` per label —
  an equality-derived bound, not an estimate.
- **Threshold `δ = 1/2` makes the robust condition exactly `4‖leak‖ < 1`.**
  With `ηi = ηj = 2‖leak‖` and `ξ = 0` (the readout is exact), the C8
  interference threshold `ηi + ηj < 2δ` becomes `4‖leak‖ < 1`
  (`NoiseProfile.IsRobust`) and the distinguishability threshold
  `2δ + 2ηj + ξ ≤ 2` becomes `1 + 4‖leak‖ ≤ 2`, implied by the same strict
  condition. Both robust theorems (C10e) are therefore direct instantiations
  of the untouched-record and phase-flip-approximation C8 machinery, with no
  new analytic argument.
- **Unconditional finite interference witness.** Flipping every one of the
  `R + 1` sites (not just the `R` record sites) swaps the source bit too,
  exchanging the two noisy branches exactly regardless of `leak`. This gives
  `C_I ≤ R + 1` (C10f) without any robustness hypothesis — only the lower
  bound needs `IsRobust`.
- **Gap and persistence are direct C8 instantiations.** C10g introduces no
  new generic machinery: `approximate_records_give_proxy_gap_certificate` and
  `approximate_records_gap_persists_under_circuit_evolution` are applied with
  `noisyRecords`/`noisyRegions`/`noisyReadoutCircuit` supplied as data. The
  minimal record count for a nonzero gap (`3 ≤ R`) is unchanged from C9,
  since `ceilHalf` depends only on the record count `R`, not on the extra
  source qubit.
- **Concrete rational witness.** `99² + 20² = 101²` gives an exact rational
  `NoiseProfile` (`keep = 99/101`, `leak = 20/101`) via `norm_div` and
  `norm_num`; `4 * (20/101) = 80/101 < 1` is checked the same way. No
  floating-point evaluation or `native_decide` is used anywhere.
- **C10 scope.** This is a static explicit family with nonzero record
  leakage, not a dynamical derivation of noisy records from decoherence, a
  claim of typicality, an operator-norm robustness result, a Hamiltonian
  persistence result, or a complexity-growth/branch-uniqueness/Many-Worlds
  claim.

- **Unitary generation, not an assumed branched state (C11).** C11 closes
  precisely the gap flagged at the end of C10 ("dynamical (unitary
  fanout/measurement) generation of the noisy records" was future work): an
  explicit finite circuit of 1- and 2-local gates turns an uncorrelated
  source qubit `α|0⟩ + β|1⟩` plus `R` blank record qubits into the C10
  branched states, by construction rather than by hypothesis.
- **Controlled bit flip, reusing C9's permutation machinery.**
  `controlledBitFlipMap control target f := Function.update f target
  (f target + f control)` XORs one coordinate by another; its unitary lift
  `controlledBitFlipEquiv` and locality proof follow the same pattern as C9's
  `bitFlipConfigurationEquiv`/`bitFlipUnitary`, just with a two-site (not
  one-site) permutation. No new locality-proof technique was needed.
- **Ideal fanout is label copying, not state cloning.** `idealFanoutCircuit R`
  lists one `sourceRecordGate` per record site; a `Nodup`-indexed fold lemma
  (`foldl_sourceRecord_record_apply_of_nodup`) shows each record's bit gains
  the source bit exactly once. This is deliberately described throughout as
  computational-basis label fanout: the source qubit's own amplitudes
  `α, β` never appear inside the fold, only its classical `0`/`1` value does,
  so no-cloning is not at stake.
- **The genuinely hard construction: a single-qubit amplitude-mixing unitary
  lifted to `N` sites with no tensor-factor infrastructure.** The repository's
  `Sites N d` is a *flat* `EuclideanSpace ℂ (Fin N → Fin d)`, deliberately not
  a tensor product (per existing repository convention), so there is no
  ready-made "apply this single-qubit unitary to factor `t`, identity
  elsewhere" combinator to reuse. C11e instead builds the rotation directly
  from existing primitives: `P₀`/`P₁` (site-`t` cell `starProjection`s, which
  sum to the identity) and `F` (the existing C9 `bitFlipUnitary`, involutive
  and self-adjoint), via
  `prepLinearMap p t := keep • P₀ + leak • (F ∘ P₀) − conj(leak) • (F ∘ P₁) +
  conj(keep) • P₁`. Unitarity is not obtained from a generic rotation lemma;
  it is proved by hand, decomposing an arbitrary `x` into its `P₀`/`P₁` parts,
  establishing eight orthogonality/self-adjointness facts, and closing the
  resulting 16-term inner-product expansion with `linear_combination
  (⟪x₀,x₀⟫ + ⟪x₁,x₁⟫) * hsum` where `hsum : keep·conj(keep) + leak·conj(leak)
  = 1`. `LinearIsometry.toLinearIsometryEquiv` (isometry + matching finrank)
  then upgrades the isometry to the required equivalence. This succeeded
  **unconditionally** for every `NoiseProfile`: no supplied-gate fallback (the
  two-layer strategy's second, harder branch) was ever needed.
- **`ImplementsNoisePreparation`'s local action is an intermediate state, not
  the final branch.** The certificate states the gate's action on
  `basis00`/`basis10` as `keep • basis00 + leak •
  (bitFlip-at-firstRecord of config00)` — i.e. only the *first* record's bit
  flips, producing one excited record, not all of them. This is intentional:
  the subsequent cat-fanout (C11f) is what copies that single bit to every
  other record, so the certificate must describe the gate's genuinely local
  effect, not the eventual global one.
- **The `keep`/`leak` "swap" is resolved by composing with the source fanout,
  not a proof error.** Applying `recordCatPreparationCircuit` alone to
  `basis10` (source `1`, all records `0`) produces `keep • basis10 + leak •
  basis11` — the *opposite* pairing from `noisyOneBranch := leak • basis10 +
  keep • basis11`. This is not a bug: the *subsequent* `idealFanoutCircuit`
  stage (C11g) also touches record `0`, unlike the cat-fanout alone, and
  `idealFanout_maps_basis10 = basis11`/`idealFanout_maps_basis11 = basis10`
  exchanges the two terms, landing on exactly `noisyOneBranch`. Diagnosing
  this by hand (rather than trusting the first derivation) was the key
  insight that fixed the intended circuit order,
  `recordCatPreparationCircuit ++ idealFanoutCircuit`.
- **Generic fold lemmas needed an explicit embedding parameter.** The first
  draft of the controlled-flip fold lemmas assumed the control site and the
  folded list shared one `Fin M` index type; this broke for the cat-fanout,
  where the control is `firstRecord R : Fin (R+1)` but the folded list is
  `List (Fin R)` (`nonFirstRecords R`) embedded via `recordSite`. Both fold
  lemmas were generalized to take an explicit `emb : Fin R → Fin M` plus
  `Function.Injective emb`, and the "untouched site" lemma was further
  generalized from "the control is unchanged" to "any site not among the
  embedded targets is unchanged," unifying the control-fixed and
  source-fixed cases into one proof.
- **A `dite` with an unused witness elaborates as a genuine `dite`, not an
  `ite`, and needs `dif_pos`/`dif_neg`.** Writing `if h : P then a else b`
  with `a`/`b` not mentioning `h` does *not* make Lean elaborate a plain
  `ite`; the term is `dite` regardless, and `if_pos`/`if_neg` (for `ite`)
  fail to rewrite it in a fresh goal even though they may appear to succeed
  when chained after a separate `ite` rewrite in the same tactic block
  (a false positive caused by the *first* `if_neg`/`if_pos` in the chain
  matching a genuine outer `ite`, masking that the *second* call was
  targeting the inner `dite` and silently failing to typecheck until
  rebuilt in a new context). The fix is `dif_pos`/`dif_neg` for every branch
  actually guarded by a named existential witness.
- **`noisyMeasurementCircuit p R := recordCatPreparationCircuit p R ++
  idealFanoutCircuit R` (length `2R`) reaches exactly C10's states, so C10's
  gap and persistence theorems apply with no new argument.** C11i does not
  reprove `HasProxyGapAtLeast`; it rewrites the generated state to
  `noisyZeroBranch`/`noisyOneBranch` via `noisyMeasurement_maps_basis00`/
  `_maps_basis10` and then invokes `noisy_repetition_has_proxy_gap`/
  `noisy_repetition_gap_persists_under_circuit` directly. Generation and
  persistence are proved to be about the *same* vectors, not merely
  analogous ones.
- **Concrete witness uses a second, independent Pythagorean triple.**
  `concreteSourceProfile` (`amp0 = 3/5`, `amp1 = 4/5`, from `3² + 4² = 5²`)
  is deliberately a different triple from C10h's noise profile
  (`99² + 20² = 101²`), so the two concrete witnesses are visibly independent
  rather than one being a disguised copy of the other.
- **C11 scope.** This is an explicit finite unitary circuit generating exact
  and noisy redundant records from an initially uncorrelated source qubit
  and blank records. It is not Hamiltonian time evolution, Brown–Susskind
  complexity growth, an operator-norm approximation bridge, a canonical
  branch-uniqueness result, a generic decoherence derivation, cloning of an
  arbitrary quantum state, or optional paired-flip sharpness.

### English summary

The Complexity block keeps circuit syntax, operator locality, finite counting,
proxy certificates, and order-theoretic minima in separate files. Gates are
exact unitaries on `Sites N d`, circuit lists act head-first, and `evalOnH`
explicitly conjugates through the chosen site/Hilbert-space isometry. C1
reuses `commute_of_disjoint`, `branch_wellDefined`, `rproj_contract_apply`,
and `Submodule.starProjection_isSymmetric`. C2 uses a new Hilbert-space-free
injection lemma because `pigeonhole_corollary` does not match arbitrary
2-local circuit lists. C3–C6 add exact normalized-branch proxies, handle both
cross-amplitude orientations, use a supplied phase-flip circuit, prove the
subtraction-free certificate first, and only then package minima in
`WithTop ℕ`. C7 adds exact push-forward/pullback conjugation through an
explicit reversible pair of finite circuits. General certificates lose at
most two conjugation overheads; the constructed equal-length canonical
inverse makes this `4 * E.length`. This is an exact conditional bound, not a
Hamiltonian or asymptotic persistence claim. C8 replaces exact projector
actions by an aggregated fixing-plus-leakage budget, obtains the sharp
one-record cross bound `η`, uses the two-label threshold
`ηi + ηj < 2δ`, and accounts for approximate readout by the diagonal loss
`2ηj + ξ`. Exact C7 transport adds no further analytic error. C9 then
instantiates the whole stack in the binary repetition model: exact singleton
records, a one-gate phase readout, an `R`-gate all-bit-flip witness,
`C_D = 1`, `ceilHalf R ≤ C_I ≤ R`, and the concrete finite-circuit
persistence budget `1 + 4 * E.length + g ≤ ceilHalf R`. C10 shows the same
robust C8 stack is inhabited by a genuinely noisy family on `R + 1` sites: a
`keep`/`leak` mix of two same-source configurations stays exactly orthogonal,
gives an exact aggregate record error `2 * ‖leak‖` per label, and — whenever
`4 * ‖leak‖ < 1` — the same qualitative bounds as C9 (`C_D = 1`,
`ceilHalf R ≤ C_I ≤ R + 1`, and persistence budget
`1 + 4 * E.length + g ≤ ceilHalf R`), instantiated concretely at
`(keep, leak) = (99/101, 20/101)`. C11 finally closes the "static family, not
a derived one" gap left open by C10: an explicit finite circuit of 1- and
2-local unitary gates dynamically generates the branched states from an
uncorrelated source qubit and blank records. A controlled-bit-flip permutation
gate (reusing C9's fold techniques) gives computational-basis label fanout,
never cloning of an arbitrary state. The genuinely hard step is a single-qubit
amplitude-mixing unitary lifted to all `N` sites through the flat `Sites N d`
representation — built from site cell projectors and the existing bit-flip
involution, proved unitary by a direct 16-term inner-product expansion, and
constructed unconditionally for every `NoiseProfile`. The full generation
circuit reaches *exactly* C10's `noisyZeroBranch`/`noisyOneBranch`, so C10's
robust proxy gap and its conditional persistence transport immediately, with
a concrete rational witness `(amp0, amp1) = (3/5, 4/5)` independent of C10h's
noise-profile triple.

## Renommage des blocs Riedel et Kent (2026-07-22)

- Le répertoire, les imports et le namespace `QuantumFoundations.Branches`
  sont renommés uniformément en `QuantumFoundations.BranchesRiedel`.
- Le répertoire, les imports et le namespace `QuantumFoundations.Histories`
  sont renommés uniformément en `QuantumFoundations.HistoriesKent`.
- Aucun alias de compatibilité n'est conservé : le changement demandé porte
  explicitement sur les namespaces publics eux-mêmes. Les types des
  déclarations sont inchangés ; seuls leurs noms pleinement qualifiés et leurs
  chemins de modules changent.

### English summary

The directory, import path, and namespace renames are uniform:
`QuantumFoundations.BranchesRiedel` and
`QuantumFoundations.HistoriesKent`. No compatibility aliases are retained;
declaration types are unchanged, while fully qualified names and module paths
change.
