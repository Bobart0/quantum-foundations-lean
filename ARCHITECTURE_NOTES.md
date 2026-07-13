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
