# ARCHITECTURE_NOTES.md — quantum-foundations-lean

Mémoire technique unique des écarts entre les plans initiaux (annoncés au
début de chaque jalon, dans les squelettes ou dans `SORRIES.md`) et l'état
réel du code, tel qu'il a fini par être prouvé. Consolidé lors de la passe de
clôture arXiv (bloc N0–N5 Naimark, W0–W6 Wigner). Chaque entrée renvoie à la
section `SORRIES.md` correspondante pour le détail de la dérivation.

## Naimark (N0–N5)

- **`DilSpace n m := EuclideanSpace ℂ (Fin m × Fin n)`** choisi sur
  `PiLp 2 (fun _ : Fin m => H n)` dès N0, à friction de preuve égale, pour son
  index plat unique (moins de couches `WithLp`/`.ofLp`). Voir `SORRIES.md` N0.
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
  `private` pour éviter le timeout, cf. règle 12 CLAUDE.md), puis recollées via
  `Orthonormal.equiv`. Voir `SORRIES.md` N5, les trois tentatives datées.

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
  paramétré.** Le plan initial de `SORRIES.md` envisageait l'exclusivité comme
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
- **Hors scope explicite** (extensions futures possibles, pas des manques de
  ce jalon) : une seconde route de dérivation indépendante de Gleason (via un
  axiome de stabilité dynamique plutôt que de cohérence de grain),
  l'existence/consistance des axiomes (Grain)/(Norm)/(Pos)/(Null) eux-mêmes,
  et la convergence intersubjective entre observateurs comme corollaire du
  théorème principal — voir `SORRIES.md`, section « Hors scope ».

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
  de somme l'identité) — un engagement mathématique documenté dans `CLAUDE.md`
  indépendant du chemin de preuve de `naimark` lui-même.
- `QuantumFoundations/Uhlhorn/` : audit spécifique lors de la clôture du bloc —
  **aucun résidu identifié**. Les deux seules déclarations publiques sans
  second point d'usage dans le dossier (`isWignerSymmetryProj_id`,
  `uhlhorn_finite_dim`) sont l'une un témoin de non-vacuité terminal, l'autre
  le théorème final du bloc — toutes deux attendues comme points d'entrée, pas
  des orphelins. `sendsONBToONB_of_preservesOrthogonality` est `private` comme
  prévu (consommé uniquement par `uhlhorn_finite_dim`, dans le même fichier).

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
