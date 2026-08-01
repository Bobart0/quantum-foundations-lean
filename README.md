# Quantum Foundations in Lean

## English

This repository is the formal companion to the manuscript *One State, Many
Perspectives: Branch Structure and Born Weights in Everettian Quantum
Mechanics*, prepared for *Foundations of Physics*. It contains a Lean 4 /
Mathlib formalization, checked mechanically and free of project-specific
axioms, of the theorem chains the manuscript relies on.

### Purpose

The repository formalizes, in finite dimension over â„‚, a sequence of
representation and stability theorems connecting perspective-relative
estimation rules to Born-rule weights, together with the auxiliary results
(Naimark dilation, Wigner's theorem, Uhlhorn-type uniqueness, Kent's
contrary-inference construction) that the manuscript's argument uses or
contrasts itself with. Every declaration is machine-checked; the axiom
audit below records the exact trust base.

### Main formal results

Contributions original to this integrated development (stated cautiously;
"original" means original to this formalization, not necessarily to the
literature â€” see `docs/FOP_THEOREM_MAP.md` for exact attribution per
theorem):

- derivation of context independence from refinement coherence for an
  initially perspective-indexed estimation rule, in both the projective
  (`BornRule`) and effect-based (`BornRule.EffectPerspectives`)
  developments;
- explicit lower bounds on interference complexity derived from spatially
  disjoint redundant records, together with robust (noisy-record) and
  dynamical (simulated-evolution) persistence extensions;
- the C14 connection from record-induced branch cells (Riedel's
  decomposition) to Born weights;
- derivation, in `BornRule.EffectPerspectives`, of the effect measure
  required by Busch's representation theorem from contextual
  effect-perspective refinement coherence, reaching the qubit case
  (`n = 2`) where Gleason-based routes require `n â‰¥ 3`;
- C17 and C17b, the first quantitative weight-stability results within this
  formal development, connecting proximity of projected components to
  proximity of restricted-sector Born weights, with state, operator-norm,
  and simulated-evolution bridges.

Known results formalized, adapted, or reused as dependencies rather than
claimed as original: Gleason's theorem and Busch's generalized-measurement
representation theorem (via the pinned `gleason-theorem-lean` dependency);
Riedel's branch-decomposition theorem; the Naimark dilation theorem; Kent's
contrary-inference construction; Wigner's theorem; Uhlhorn-type uniqueness
(Å emrl's Corollary 1.2); and Lela's restricted-sector uniqueness theorem
underlying the C15 development. See `docs/FOP_THEOREM_MAP.md` for the
per-theorem status of every manuscript-facing declaration, and
`docs/SCOPE_AND_LIMITATIONS.md` for what is deliberately not claimed.

### Relation to the Foundations of Physics manuscript

The repository's architecture mirrors the manuscript's central chains:
grain coherence to context independence to Born representation; unitary
record formation to Riedel branch uniqueness to record-induced branch
cells to Born weights (C14); redundant records to complexity separation
to robust and dynamical persistence; restricted record sectors to
quadratic uniqueness (C15) to quantitative weight stability (C17) to the
C17b state/operator/simulation/branch bridges; and effect perspectives to
context independence to effect additivity to the Busch qubit
representation to its Naimark projective realization. Naimark dilation is
an auxiliary operational result; HistoriesKent is a conceptual contrast
with the branch-theoretic development, not a premise of it; Wigner and the
full Uhlhorn theorem are infrastructural results reused only through
specific lemmas, not presented as substantive premises of the manuscript's
argument. See `docs/FOP_THEOREM_MAP.md` for the complete correspondence.

### Theorem and module map

`docs/FOP_THEOREM_MAP.md` records, for every theorem used substantively in
the manuscript: its exact Lean declaration and module, its mathematical
status (original result, connection theorem, new reduction to a known
theorem, formalization of a known theorem, auxiliary operational theorem,
conceptual contrast, or nonvacuity witness), its principal dependencies,
dimension assumptions, and axiom-audit status.

### Scope and limitations

`docs/SCOPE_AND_LIMITATIONS.md` states explicitly what this release does
not establish, including (among other points) that Born weights are not
derived from unitarity alone, that no universal decoherence theorem is
proved, that no absolute or uniquely fundamental branch ontology is
asserted, that C15 is not shown stable under approximate hypotheses, and
that C16 remains open.

### Repository structure

The Lean sources live under `QuantumFoundations/`, organized by subsystem
(`Naimark/`, `Wigner/`, `Uhlhorn/`, `BornRule/` and its
`EffectPerspectives/` and `RestrictedRecordSectors/` subdirectories,
`HistoriesKent/`, `BranchesRiedel/` and its `BornBridge/` subdirectory,
`Complexity/`). Each subsystem directory that reaches a public theorem
carries its own `README.md` with a detailed, subsystem-specific account.
`MILESTONES.md` and `ARCHITECTURE_NOTES.md` are the project's detailed
internal development record (milestone-by-milestone history and
architectural decisions); they are retained for engineering continuity and
are not required reading for assessing the manuscript's formal claims,
which are summarized in `docs/FOP_THEOREM_MAP.md`.

### Reproducibility

See `docs/REPRODUCIBILITY.md` for exact, copy-pasteable build, audit, and
guard commands (POSIX shell and PowerShell), the exact Lean toolchain and
dependency revisions, and the expected outputs.

### Axiom audit

`QuantumFoundations/Audit/FoP.lean` runs `#print axioms` on the principal
manuscript-facing declarations. Every one of them depends only on the
standard Lean/Mathlib kernel trio `[propext, Classical.choice, Quot.sound]`
â€” that is, there are no project-specific axioms, no `sorry`, and no
`native_decide` anywhere in the release. See `docs/REPRODUCIBILITY.md` for
the exact audit commands and `RELEASE_NOTES_v1.0.1-fop-companion.md` for
the recorded output at the release commit.

### Software and code availability

The source is available at
`https://github.com/Bobart0/quantum-foundations-lean`, pinned to the
dependency revisions recorded in `lake-manifest.json` and
`docs/REPRODUCIBILITY.md`. The recommended immutable release is the
annotated tag `v1.0.1-fop-companion` (a documentation- and metadata-only
corrective release; see `RELEASE_NOTES_v1.0.1-fop-companion.md`). The
earlier `v1.0-fop-companion` tag remains available as historical evidence
and is not moved, deleted, or recreated.

### Downstream API

`QuantumFoundations.ProbabilityAPI` is a single, deliberately minimal entry
point re-exporting exactly the declarations that downstream developments
(currently: a Born-weight decision-theory layer,
`Bobart0/everettian-probability-lean`) may rely on. It has **no role in
this repository's manuscript**: it contains no new mathematical result,
only reformulations and immediate consequences of already-validated
declarations (reflexivity/transitivity of refinement, a total parent map
built by classical choice on an existing uniqueness lemma, and a stabilized
decidability instance for an existing filter). Any declaration not
re-exported from `ProbabilityAPI` is internal and may change without
notice. `QuantumFoundations/Audit/DownstreamAPI.lean` is a regression
module exercising every wrapper, so that a future refactor breaking a
downstream-consumed contract fails here rather than downstream.

### Citation

See `CITATION.cff` for structured citation metadata. In brief: Bertrand
Dalimier, *Quantum Foundations in Lean: Formal Companion to One State, Many
Perspectives*, version 1.1.0.

### AI-assisted development

AI coding assistance was used throughout this project's development. See
`docs/AI_ASSISTANCE.md` for the full disclosure; the author reviewed every
theorem statement, scientific claim, and proof dependency, and accepts full
responsibility for the content.

## FranÃ§ais

Ce dÃ©pÃ´t est le compagnon formel du manuscrit *One State, Many
Perspectives: Branch Structure and Born Weights in Everettian Quantum
Mechanics*, prÃ©parÃ© pour *Foundations of Physics*. Il contient une
formalisation Lean 4 / Mathlib, vÃ©rifiÃ©e mÃ©caniquement et sans axiome
propre au projet, des chaÃ®nes de thÃ©orÃ¨mes sur lesquelles s'appuie le
manuscrit.

### Objet du dÃ©pÃ´t

Le dÃ©pÃ´t formalise, en dimension finie sur â„‚, une suite de thÃ©orÃ¨mes de
reprÃ©sentation et de stabilitÃ© reliant des rÃ¨gles d'estimation relatives Ã 
une perspective aux poids de la rÃ¨gle de Born, ainsi que les rÃ©sultats
auxiliaires (dilatation de Naimark, thÃ©orÃ¨me de Wigner, unicitÃ© de type
Uhlhorn, construction des infÃ©rences contraires de Kent) que l'argument du
manuscrit utilise ou dont il se distingue explicitement. Chaque dÃ©claration
est vÃ©rifiÃ©e mÃ©caniquement ; l'audit des axiomes ci-dessous enregistre
exactement la base de confiance.

### Principaux rÃ©sultats formalisÃ©s

Contributions propres Ã  ce dÃ©veloppement intÃ©grÃ© (formulation prudente :
Â« propre Â» signifie propre Ã  cette formalisation, pas nÃ©cessairement Ã  la
littÃ©rature â€” voir `docs/FOP_THEOREM_MAP.md` pour l'attribution exacte de
chaque thÃ©orÃ¨me) :

- dÃ©rivation de l'indÃ©pendance du contexte Ã  partir de la cohÃ©rence sous
  raffinement pour une rÃ¨gle d'estimation initialement indexÃ©e par les
  perspectives, dans les deux dÃ©veloppements, projectif (`BornRule`) et Ã 
  base d'effets (`BornRule.EffectPerspectives`) ;
- bornes infÃ©rieures explicites sur la complexitÃ© d'interfÃ©rence dÃ©rivÃ©es
  de records redondants spatialement disjoints, avec des extensions de
  persistance robuste (records bruitÃ©s) et dynamique (Ã©volution simulÃ©e) ;
- le pont C14 des cellules de branche induites par les records (issues de
  la dÃ©composition de Riedel) vers les poids de Born ;
- dÃ©rivation, dans `BornRule.EffectPerspectives`, de la mesure d'effets
  requise par le thÃ©orÃ¨me de reprÃ©sentation de Busch Ã  partir de la
  cohÃ©rence sous raffinement des perspectives d'effets contextuelles,
  atteignant le cas du qubit (`n = 2`) lÃ  oÃ¹ les voies fondÃ©es sur Gleason
  exigent `n â‰¥ 3` ;
- C17 et C17b, les premiers rÃ©sultats quantitatifs de stabilitÃ© des poids
  au sein de ce dÃ©veloppement formel, reliant la proximitÃ© des composantes
  projetÃ©es Ã  la proximitÃ© des poids de Born sur des secteurs restreints,
  avec des ponts d'Ã©tat, de norme d'opÃ©rateur et d'Ã©volution simulÃ©e.

RÃ©sultats connus formalisÃ©s, adaptÃ©s ou rÃ©utilisÃ©s comme dÃ©pendances,
sans revendication d'originalitÃ© : le thÃ©orÃ¨me de Gleason et le thÃ©orÃ¨me
de reprÃ©sentation gÃ©nÃ©ralisÃ©e de Busch (via la dÃ©pendance Ã©pinglÃ©e
`gleason-theorem-lean`) ; le thÃ©orÃ¨me de dÃ©composition en branches de
Riedel ; le thÃ©orÃ¨me de dilatation de Naimark ; la construction des
infÃ©rences contraires de Kent ; le thÃ©orÃ¨me de Wigner ; l'unicitÃ© de type
Uhlhorn (Corollaire 1.2 de Å emrl) ; et le thÃ©orÃ¨me d'unicitÃ© sur les
secteurs restreints de Lela, sous-jacent au dÃ©veloppement C15. Voir
`docs/FOP_THEOREM_MAP.md` pour le statut prÃ©cis de chaque dÃ©claration
pertinente pour le manuscrit, et `docs/SCOPE_AND_LIMITATIONS.md` pour ce
qui n'est dÃ©libÃ©rÃ©ment pas revendiquÃ©.

### Relation avec le manuscrit Foundations of Physics

L'architecture du dÃ©pÃ´t reflÃ¨te les chaÃ®nes centrales du manuscrit :
cohÃ©rence de grain vers indÃ©pendance du contexte vers reprÃ©sentation de
Born ; formation unitaire des records vers unicitÃ© des branches de Riedel
vers cellules de branche induites par les records vers poids de Born
(C14) ; records redondants vers sÃ©paration de complexitÃ© vers persistance
robuste et dynamique ; secteurs de records restreints vers unicitÃ©
quadratique (C15) vers stabilitÃ© quantitative des poids (C17) vers les
ponts d'Ã©tat/opÃ©rateur/simulation/branche de C17b ; et perspectives
d'effets vers indÃ©pendance du contexte vers additivitÃ© des effets vers la
reprÃ©sentation qubit de Busch vers sa rÃ©alisation projective de Naimark.
La dilatation de Naimark est un rÃ©sultat opÃ©rationnel auxiliaire ;
HistoriesKent constitue un contraste conceptuel avec le dÃ©veloppement
fondÃ© sur les branches, non une prÃ©misse de celui-ci ; Wigner et le
thÃ©orÃ¨me d'Uhlhorn complet sont des rÃ©sultats infrastructurels rÃ©utilisÃ©s
seulement via des lemmes ponctuels, non prÃ©sentÃ©s comme des prÃ©misses
substantielles de l'argument du manuscrit. Voir `docs/FOP_THEOREM_MAP.md`
pour la correspondance complÃ¨te.

### Carte des thÃ©orÃ¨mes et modules

`docs/FOP_THEOREM_MAP.md` enregistre, pour chaque thÃ©orÃ¨me utilisÃ© de
faÃ§on substantielle dans le manuscrit : sa dÃ©claration Lean exacte et son
module, son statut mathÃ©matique (rÃ©sultat original, thÃ©orÃ¨me de connexion,
nouvelle rÃ©duction Ã  un thÃ©orÃ¨me connu, formalisation d'un thÃ©orÃ¨me connu,
thÃ©orÃ¨me opÃ©rationnel auxiliaire, contraste conceptuel, ou tÃ©moin de
non-vacuitÃ©), ses dÃ©pendances principales, ses hypothÃ¨ses de dimension, et
son statut d'audit des axiomes.

### PortÃ©e et limites

`docs/SCOPE_AND_LIMITATIONS.md` Ã©nonce explicitement ce que cette version
n'Ã©tablit pas, notamment (entre autres points) que les poids de Born ne
sont pas dÃ©rivÃ©s de l'unitaritÃ© seule, qu'aucun thÃ©orÃ¨me de dÃ©cohÃ©rence
universelle n'est prouvÃ©, qu'aucune ontologie de branches absolue ou
uniquement fondamentale n'est affirmÃ©e, que la stabilitÃ© de C15 sous
hypothÃ¨ses approximatives n'est pas Ã©tablie, et que C16 reste ouvert.

### Structure du dÃ©pÃ´t

Les sources Lean se trouvent sous `QuantumFoundations/`, organisÃ©es par
sous-systÃ¨me (`Naimark/`, `Wigner/`, `Uhlhorn/`, `BornRule/` et ses
sous-rÃ©pertoires `EffectPerspectives/` et `RestrictedRecordSectors/`,
`HistoriesKent/`, `BranchesRiedel/` et son sous-rÃ©pertoire `BornBridge/`,
`Complexity/`). Chaque rÃ©pertoire de sous-systÃ¨me aboutissant Ã  un
thÃ©orÃ¨me public possÃ¨de son propre `README.md` dÃ©taillÃ© et spÃ©cifique.
`MILESTONES.md` et `ARCHITECTURE_NOTES.md` constituent le registre interne
dÃ©taillÃ© du dÃ©veloppement du projet (historique jalon par jalon et
dÃ©cisions d'architecture) ; ils sont conservÃ©s pour la continuitÃ© du gÃ©nie
logiciel et ne sont pas nÃ©cessaires Ã  l'Ã©valuation des affirmations
formelles du manuscrit, rÃ©sumÃ©es dans `docs/FOP_THEOREM_MAP.md`.

### ReproductibilitÃ©

Voir `docs/REPRODUCIBILITY.md` pour des commandes de compilation, d'audit
et de garde exactes et directement utilisables (shell POSIX et
PowerShell), la chaÃ®ne d'outils Lean exacte, les rÃ©visions de dÃ©pendances,
et les sorties attendues.

### Audit des axiomes

`QuantumFoundations/Audit/FoP.lean` exÃ©cute `#print axioms` sur les
principales dÃ©clarations pertinentes pour le manuscrit. Chacune d'entre
elles ne dÃ©pend que du trio standard du noyau Lean/Mathlib
`[propext, Classical.choice, Quot.sound]` â€” autrement dit, aucun axiome
propre au projet, aucun `sorry`, et aucun `native_decide` nulle part dans
cette version. Voir `docs/REPRODUCIBILITY.md` pour les commandes d'audit
exactes et `RELEASE_NOTES_v1.0.1-fop-companion.md` pour la sortie
enregistrÃ©e au commit de la version.

### DisponibilitÃ© du logiciel et du code

Les sources sont disponibles Ã  l'adresse
`https://github.com/Bobart0/quantum-foundations-lean`, Ã©pinglÃ©es aux
rÃ©visions de dÃ©pendances enregistrÃ©es dans `lake-manifest.json` et dans
`docs/REPRODUCIBILITY.md`. La version immuable recommandÃ©e est l'Ã©tiquette
annotÃ©e `v1.0.1-fop-companion` (version corrective, ne portant que sur la
documentation et les mÃ©tadonnÃ©es ; voir
`RELEASE_NOTES_v1.0.1-fop-companion.md`). L'Ã©tiquette antÃ©rieure
`v1.0-fop-companion` reste disponible comme trace historique ; elle n'est
ni dÃ©placÃ©e, ni supprimÃ©e, ni recrÃ©Ã©e.

### API pour dÃ©veloppements aval

`QuantumFoundations.ProbabilityAPI` est un point d'entrÃ©e unique et
dÃ©libÃ©rÃ©ment minimal, rÃ©exportant exactement les dÃ©clarations dont peuvent
avoir besoin les dÃ©veloppements aval (actuellement : une couche de thÃ©orie
de la dÃ©cision fondÃ©e sur les poids de Born,
`Bobart0/everettian-probability-lean`). Il **n'a aucun rÃ´le dans le
manuscrit** de ce dÃ©pÃ´t : il ne contient aucun rÃ©sultat mathÃ©matique
nouveau, seulement des reformulations et des consÃ©quences immÃ©diates de
dÃ©clarations dÃ©jÃ  validÃ©es (rÃ©flexivitÃ©/transitivitÃ© du raffinement, une
carte parent totale construite par choix classique sur un lemme d'unicitÃ©
existant, et une instance de dÃ©cidabilitÃ© stabilisÃ©e pour un filtre dÃ©jÃ 
existant). Toute dÃ©claration non rÃ©exportÃ©e depuis `ProbabilityAPI` est
interne et peut changer sans prÃ©avis. `QuantumFoundations/Audit/
DownstreamAPI.lean` est un module de non-rÃ©gression exerÃ§ant chaque
wrapper, pour qu'un futur refactor cassant un contrat consommÃ© en aval
Ã©choue ici plutÃ´t qu'en aval.

### Citation

Voir `CITATION.cff` pour les mÃ©tadonnÃ©es de citation structurÃ©es. En bref :
Bertrand Dalimier, *Quantum Foundations in Lean: Formal Companion to One
State, Many Perspectives*, version 1.1.0.

### Assistance par intelligence artificielle

Une assistance au codage par IA a Ã©tÃ© utilisÃ©e tout au long du
dÃ©veloppement de ce projet. Voir `docs/AI_ASSISTANCE.md` pour la
divulgation complÃ¨te ; l'auteur a vÃ©rifiÃ© chaque Ã©noncÃ© de thÃ©orÃ¨me,
chaque affirmation scientifique et chaque dÃ©pendance de preuve, et assume
l'entiÃ¨re responsabilitÃ© du contenu.

---

## Documentation bilingue dÃ©taillÃ©e (contenu historique prÃ©servÃ©) / Detailed bilingual reference documentation (preserved)

Les sections qui suivent reproduisent intÃ©gralement la documentation
bilingue (franÃ§ais puis anglais), dÃ©veloppÃ©e sous-systÃ¨me par
sous-systÃ¨me au fil du projet. Elles sont conservÃ©es en totalitÃ© pour la
continuitÃ© et la rÃ©fÃ©rence technique dÃ©taillÃ©e ; le rÃ©sumÃ© ci-dessus
constitue le point d'entrÃ©e destinÃ© Ã  la relecture externe.

The sections that follow reproduce in full the bilingual (French, then
English) documentation accumulated subsystem by subsystem over the course
of the project. They are retained in full for continuity and detailed
technical reference; the summary above is the publication-facing entry
point intended for external review.

# quantum-foundations-lean â€” Formalisations Lean 4 : Naimark, Wigner, Uhlhorn, BornRule, HistoriesKent, BranchesRiedel et Complexity

**Statut : Naimark v2 COMPLET (`v2.0-naimark`, 2026-07-11), Wigner COMPLET avec
unicitÃ©/exclusivitÃ© optionnelles (`v2.0-wigner`, 2026-07-13), Uhlhorn COMPLET
(`v1.0-uhlhorn`, 2026-07-14), BornRule COMPLET avec Nonvacuity
(`v2.0-bornrule`, 2026-07-15) ET HistoriesKent COMPLET (`v1.0-histories`,
2026-07-16), avec les blocs BranchesRiedel et Complexity C0â€“C13, et dÃ©sormais
le pont **C14 records â†’ poids de Born** ainsi que **C15, unicitÃ© quadratique
sur les secteurs de records restreints**, dÃ©sormais complÃ©tÃ© par **C17,
premiÃ¨re stabilitÃ© quantitative des poids restreints**.** Sept blocs
mÃ©canisÃ©s, **sans axiome**
(au sens des rÃ¨gles du projet â€” hors les trois axiomes standards du noyau Lean,
voir plus bas), en dimension finie sur â„‚.

**En chiffres (recalculÃ©s le 2026-07-23, fichiers du projet hors scratch) :
119 fichiers `.lean`, 19598 lignes, 663 dÃ©clarations publiques (`theorem`), 0
`sorry`, 0 axiome propre au projet. Le bloc Complexity compte 70 fichiers et
9490 lignes, dont 12 fichiers et 1224 lignes pour le jalon C13 de
persistance sous Ã©volution simulÃ©e. Le bloc BranchesRiedel compte 17 fichiers
et 3250 lignes, dont 11 fichiers et 1438 lignes pour le nouveau
sous-rÃ©pertoire `BornBridge/` (jalon C14, pont entre la dÃ©composition en
branches de Riedel et le poids de Born). Les
thÃ©orÃ¨mes principaux des blocs Complexity et BornBridge ont Ã©tÃ© vÃ©rifiÃ©s par
`#print axioms` et dÃ©pendent exactement de
`[propext, Classical.choice, Quot.sound]`, le trio standard Lean/Mathlib.**

**Noms de modules actuels :** le bloc Riedel est
`QuantumFoundations.BranchesRiedel` et le bloc des infÃ©rences contraires de
Kent est `QuantumFoundations.HistoriesKent`. Les anciens chemins/namespaces
`QuantumFoundations.Branches` et `QuantumFoundations.Histories` ne sont plus
exposÃ©s.

Le **thÃ©orÃ¨me de dilation de Naimark** pour les POVM finies (Watrous, *The Theory
of Quantum Information*, Theorem 2.42) : toute POVM `E : Fin m â†’ (H n â†’â‚—[â„‚] H n)` se
rÃ©alise comme mesure projective (`dilProj`) sous l'action d'une isomÃ©trie `dilV`,
avec formule de Born prÃ©servÃ©e.

Le **thÃ©orÃ¨me de Wigner** (Bargmann 1964, *Note on Wigner's Theorem on Symmetry
Operations*) : toute transformation sur les Ã©tats purs qui prÃ©serve les probabilitÃ©s
de transition `|âŸ¨Ï†|ÏˆâŸ©|Â²` est induite par un opÃ©rateur unitaire ou antiunitaire â€”
formulation (A), **sans hypothÃ¨se de bijectivitÃ©** sur la transformation de dÃ©part
(strictement plus fort que Simonâ€“Mukundaâ€“Chaturvediâ€“Srinivasan 2008, eq. 2.8, qui
la suppose). ComplÃ©tÃ© (W6, optionnel) par l'**exclusivitÃ©** unitaire/antiunitaire
et l'**unicitÃ© Ã  phase globale prÃ¨s** (version restreinte), Bargmann Â§1.5 et Â§6.

Le **Corollaire 1.2 de Å emrl** (Å emrl 2021, *Wigner symmetries and Gleason's
theorem*, arXiv:2106.06182) : en dimension finie `n â‰¥ 3`, toute application sur
les projections de rang 1 qui prÃ©serve l'orthogonalitÃ© **dans un seul sens**
(ni injectivitÃ© ni surjectivitÃ© supposÃ©es) est automatiquement une symÃ©trie de
Wigner. Contrairement Ã  Naimark et Wigner, ce n'est PAS un rÃ©sultat autonome :
il **compose** le thÃ©orÃ¨me de Gleason (`gleason-theorem-lean`, dÃ©pendance
externe Ã©pinglÃ©e) et le thÃ©orÃ¨me de Wigner (bloc interne ci-dessus) â€” voir la
section dÃ©diÃ©e plus bas pour le dÃ©tail de cette double dÃ©pendance et sa
vÃ©rification d'axiomes.

Le **ThÃ©orÃ¨me de CohÃ©rence de Grain** (Gleason 1957, *Measures on the closed
subspaces of a Hilbert space*, comme thÃ©orÃ¨me sous-jacent) : pour une
Â« perspective Â» (partition orthogonale de `H n` en cellules) et une rÃ¨gle
d'estimation satisfaisant quatre axiomes purement combinatoires (Grain, Norm,
Pos, Null), la valeur de la rÃ¨gle sur toute cellule est EXACTEMENT la rÃ¨gle de
Born (`âˆ‘áµ¢ â€–âŸ¨v,fáµ¢âŸ©â€–Â²` sur une base orthonormÃ©e de la cellule) â€” sans jamais
supposer a priori que la rÃ¨gle est de la forme d'une trace. Comme Uhlhorn,
c'est un rÃ©sultat qui **compose** un bloc interne (l'infrastructure Uhlhorn,
U2 et U3a) et une dÃ©pendance externe (`Gleason.gleason`, importÃ© comme vrai
thÃ©orÃ¨me plutÃ´t que comme axiome) â€” voir la section dÃ©diÃ©e plus bas.

Le **thÃ©orÃ¨me des infÃ©rences contraires** (Kent 1997, *Quasiclassical Dynamics
in a Closed Quantum System*, PRL 78, 2874, arXiv:gr-qc/9604012), dans le cadre
des histoires cohÃ©rentes en dimension finie : deux ensembles cohÃ©rents
d'histoires peuvent partager la mÃªme prÃ©paration et la mÃªme post-sÃ©lection,
tout en impliquant chacun avec CERTITUDE une proposition diffÃ©rente, ces deux
propositions Ã©tant mutuellement orthogonales. Un Ã©tage temporel d'un ensemble
d'histoires **rÃ©utilise directement** `BornRule.Perspective`, sans
redÃ©finition â€” comme Uhlhorn et BornRule le font dÃ©jÃ  pour d'autres briques,
`HistoriesKent` **compose** l'infrastructure interne du dÃ©pÃ´t (`BornRule` â†’
`Uhlhorn`/`Gleason`) plutÃ´t que de repartir de zÃ©ro. Le thÃ©orÃ¨me de profusion
gÃ©nÃ©rique de Dowkerâ€“Kent (1996) â€” qui montrerait que la contrariÃ©tÃ© du tÃ©moin
n'est pas un cas isolÃ© â€” est explicitement hors scope de ce bloc.

Ce dÃ©pÃ´t s'appuie sur [`gleason-theorem-lean`](https://github.com/Bobart0/gleason-theorem-lean)
(tag `v1.0-gleason`). Naimark n'y rÃ©utilise que `IsPositiveOp`
(`Gleason.Busch.Effects`) ; Uhlhorn et BornRule, en revanche, invoquent
`Gleason.gleason` lui-mÃªme ainsi qu'une partie de sa machinerie interne ;
HistoriesKent n'invoque pas `Gleason.gleason` directement mais en hÃ©rite par
transitivitÃ© via `BornRule.Perspective`/`projL` â€” voir la section
Â« DÃ©pendances Â» plus bas pour le dÃ©tail et la vÃ©rification de non-fuite
d'axiome.

## Ã‰noncÃ©

```lean
structure POVM (n m : â„•) where
  E : Fin m â†’ (H n â†’â‚—[â„‚] H n)
  pos : âˆ€ i, IsPositiveOp (E i)
  sum_eq_one : âˆ‘ i, E i = 1

theorem naimark (P : POVM n m) :
    âˆƒ V : H n â†’â‚—[â„‚] DilSpace n m, LinearMap.adjoint V âˆ˜â‚— V = LinearMap.id âˆ§
      âˆ€ i, LinearMap.adjoint V âˆ˜â‚— dilProj n m i âˆ˜â‚— V = P.E i

theorem naimark_born (P : POVM n m) (i : Fin m) (x : H n) :
    âŸªx, P.E i xâŸ«_â„‚ = âŸªdilV P x, dilProj n m i (dilV P x)âŸ«_â„‚
```

`DilSpace n m := EuclideanSpace â„‚ (Fin m Ã— Fin n)` et `dilProj i` est la projection
orthogonale sur le `i`-Ã¨me bloc.

**N5 (optionnel, clos)** : `dilV` s'Ã©tend en un vrai unitaire de `DilSpace n m` (pas
seulement une isomÃ©trie), pour tout indice ancilla `iâ‚€` fixÃ© (Watrous Cor. 2.43 /
Paris Â§3.2 Thm 4) :

```lean
theorem exists_unitary_extension (P : POVM n m) (iâ‚€ : Fin m) :
    âˆƒ U : DilSpace n m â‰ƒâ‚—áµ¢[â„‚] DilSpace n m, U.toLinearMap âˆ˜â‚— singleL n m iâ‚€ = dilV P

theorem naimark_projective_form (P : POVM n m) (iâ‚€ : Fin m) :
    âˆƒ U : DilSpace n m â‰ƒâ‚—áµ¢[â„‚] DilSpace n m, âˆ€ (i : Fin m) (x : H n),
      âŸªx, P.E i xâŸ«_â„‚ = âŸªU (singleL n m iâ‚€ x), dilProj n m i (U (singleL n m iâ‚€ x))âŸ«_â„‚
```

## Ã‰cart documentÃ© vs Watrous

Watrous dilate dans un produit tensoriel `X âŠ— â„‚^Î£`. Nous dilatons dans la **somme
directe hilbertienne** `K := âŠ•_{i<m} H n`, canoniquement isomorphe (l'API Mathlib
pour `PiLp`/`EuclideanSpace` est plus mÃ»re que celle du produit tensoriel hilbertien
Ã  cette date). Correspondance : `1_X âŠ— E_{a,a}` devient `dilProj a` ; `âˆšÎ¼(a) âŠ— e_a`
devient `singleL a âˆ˜â‚— sqrtOp (E a)`. Le contenu mathÃ©matique (isomÃ©trie + formule de
Born) est identique ; seule la rÃ©alisation concrÃ¨te de l'espace de dilatation diffÃ¨re.

`DilSpace n m := EuclideanSpace â„‚ (Fin m Ã— Fin n)` a Ã©tÃ© choisi (Ã©tape 0, jalon N0)
sur `PiLp 2 (fun _ : Fin m => H n)` Ã  friction de preuve Ã©gale, pour son index plat
unique â€” voir `MILESTONES.md` pour le dÃ©tail des deux routes testÃ©es.

## ThÃ©orÃ¨me de Wigner

```lean
def IsWignerMap (T : H n â†’ H n) : Prop :=
  âˆ€ x y : H n, â€–xâ€– = 1 â†’ â€–yâ€– = 1 â†’ â€–âŸªT x, T yâŸ«_â„‚â€– = â€–âŸªx, yâŸ«_â„‚â€–

theorem wigner (n : â„•) (T : H n â†’ H n) (hT : IsWignerMap T) :
    (âˆƒ U' : H n â‰ƒâ‚—áµ¢[â„‚] H n, âˆ€ x, â€–xâ€– = 1 â†’ âˆƒ c : â„‚, â€–câ€– = 1 âˆ§ T x = c â€¢ U' x)
  âˆ¨ (âˆƒ U' : H n â‰ƒâ‚›â‚—áµ¢[starRingEnd â„‚] H n, âˆ€ x, â€–xâ€– = 1 â†’ âˆƒ c : â„‚, â€–câ€– = 1 âˆ§ T x = c â€¢ U' x)
```

Aucune hypothÃ¨se de bijectivitÃ© sur `T` : en dimension finie, l'isomÃ©trie construite
`U'` est automatiquement bijective (`U_bijective`), et l'injectivitÃ© au niveau des
rayons dÃ©coule de `hT` seul. Blueprint mathÃ©matique : Bargmann 1964, Â§1â€“Â§5 (repris
quasi tel quel) ; Simonâ€“Mukundaâ€“Chaturvediâ€“Srinivasan 2008 utilisÃ© uniquement en
contre-vÃ©rification (rejetÃ© comme blueprint principal â€” approche
trigonomÃ©trique/`Real.Angle`).

Construction (Bargmann Â§3â€“Â§5) : `V` (colinÃ©aritÃ© dÃ©finitionnelle sur `ð’« := eâŠ¥`, W3)
puis `Ï‡` (dichotomie `id`/`conj` Ã©tablie sur CHAQUE direction indÃ©pendamment, puis
globalisÃ©e sans hypothÃ¨se de repÃ¨re orthogonal, W4) puis `U := Ï‡âŸ¨e,Â·âŸ©â€¢e' + V(Â· âˆ’ âŸ¨e,Â·âŸ©â€¢e)`
Ã©tendant `V`/`Ï‡` Ã  tout l'espace (W5). Aucune coordonnÃ©e, aucune extension de base
orthonormÃ©e, aucun `Submodule` pour `ð’«` (une simple `Prop`, `InPerp`).

**Ã‰carts documentÃ©s vs le plan initial** (voir `MILESTONES.md`, sections W3â€“W5, pour le
dÃ©tail complet) :
- W3 (`V_colinear`) : le squelette initial affirmait `â€–Î´â€– = 1` pour le coefficient de
  colinÃ©aritÃ© â€” FAUX en gÃ©nÃ©ral (rÃ©futÃ© par le contre-exemple `T = id`) ; corrigÃ© en
  `â€–Î´â€– = â€–zâ€–`.
- W4 (`chi_eq_chidir`) : l'argument de Bargmann Â§4.3â€“4.5 (`w = fâ‚+fâ‚‚`, orthogonal
  uniquement) est insuffisant dÃ¨s que `n â‰¥ 3` et que le second vecteur n'est ni
  colinÃ©aire ni orthogonal Ã  `refVec`. RÃ©solu par rÃ©duction Ã  un seul point de
  comparaison (`i`, oÃ¹ `id` et `conj` se distinguent) plutÃ´t que l'identitÃ©
  fonctionnelle complÃ¨te.
- W5 (`U_bijective`) : la bijectivitÃ© semilinÃ©aire (branche antiunitaire) ne dispose
  d'aucun lemme Mathlib direct ; rÃ©solue par restriction aux scalaires rÃ©els
  (`starRingEnd â„‚` est â„-linÃ©aire), sur laquelle `LinearMap.injective_iff_surjective`
  s'applique tel quel.

Voir `ARCHITECTURE_NOTES.md` pour la liste consolidÃ©e de tous les Ã©carts
signalÃ©s (N0â€“N5 et W0â€“W6), compilÃ©e en un seul endroit.

## W6 (optionnel) â€” ExclusivitÃ© et unicitÃ© (Bargmann Â§1.5, Â§6 restreint)

```lean
def Delta (a b c : H n) : â„‚ := âŸªa, bâŸ«_â„‚ * âŸªb, câŸ«_â„‚ * âŸªc, aâŸ«_â„‚

theorem exclusivity (hT : IsWignerMap T) (hn : 2 â‰¤ n) :
    Â¬ ((âˆƒ U : H n â‰ƒâ‚—áµ¢[â„‚] H n, âˆ€ x, â€–xâ€– = 1 â†’ âˆƒ c : â„‚, â€–câ€– = 1 âˆ§ T x = c â€¢ U x)
     âˆ§ (âˆƒ U' : H n â‰ƒâ‚›â‚—áµ¢[starRingEnd â„‚] H n, âˆ€ x, â€–xâ€– = 1 â†’ âˆƒ c : â„‚, â€–câ€– = 1 âˆ§ T x = c â€¢ U' x))

theorem U_alt_eq_smul (T : H n â†’ H n) (lam : â„‚) (hlam : â€–lamâ€– = 1) (a : H n) :
    Up T (lam â€¢ eImg T) a = lam â€¢ U T a
```

**(A) ExclusivitÃ©** (Bargmann Â§1.5) : un mÃªme `T` ne peut jamais Ãªtre compatible
Ã  la fois avec une Ã©quivalence unitaire et une Ã©quivalence antiunitaire, pour
`n â‰¥ 2`. Preuve par tÃ©moin explicite : le triplet `e, eâ‚‚ := (eâˆ’refVec)/âˆš2,
eâ‚ƒ := (e+refVec(1âˆ’i))/âˆš3` donne `Delta(e,eâ‚‚,eâ‚ƒ) = i/6 âˆ‰ â„`
(`bargmann_delta_witness`, confirmÃ© par Lean au chiffre prÃ¨s) ; or `Delta` est
invariant sous une branche unitaire et conjuguÃ© sous une branche antiunitaire
(`delta_transform_lin`/`delta_transform_conj`), ce qui forcerait `i/6 = -i/6`.

**(B) UnicitÃ© Ã  phase globale prÃ¨s â€” version RESTREINTE** : si l'on reconstruit
`U` en remplaÃ§ant, dans les formules mÃªmes de `Defs.lean`, le reprÃ©sentant
unitaire `eImg T := T(e n)` par un autre reprÃ©sentant unitaire `Î» â€¢ eImg T` de
la mÃªme classe (`â€–Î»â€– = 1`), le nouveau `U` vaut exactement `Î» â€¢ U`
(`U_alt_eq_smul`). Version strictement plus faible que le ThÃ©orÃ¨me 2 complet
de Bargmann Â§6 (qui couvrirait un `U'` complÃ¨tement arbitraire, pas seulement
la libertÃ© de reprÃ©sentant de `eImg`) â€” suffisante pour le cas d'usage rÃ©el du
dÃ©pÃ´t. `Defs.lean` n'est pas modifiÃ© : la reconstruction paramÃ©trÃ©e (`Vp`,
`chidirp`, `chip`, `Up`) est locale Ã  `Uniqueness.lean`, reliÃ©e Ã  `V`/`chi`/`U`
par des lemmes-pont prouvÃ©s `rfl`.

## Corollaire 1.2 de Å emrl (Uhlhorn)

```lean
def PreservesOrthogonality (Ï† : Proj1 n â†’ Proj1 n) : Prop :=
  âˆ€ P Q : Proj1 n, (P : Submodule â„‚ (H n)) âŸ‚ (Q : Submodule â„‚ (H n)) â†’
    (Ï† P : Submodule â„‚ (H n)) âŸ‚ (Ï† Q : Submodule â„‚ (H n))

theorem uhlhorn_finite_dim (hn : 3 â‰¤ n) (Ï† : Proj1 n â†’ Proj1 n)
    (hÏ† : PreservesOrthogonality Ï†) : IsWignerSymmetryProj Ï†
```

`Proj1 n := {A : Submodule â„‚ (H n) // Module.finrank â„‚ A = 1}` (une projection
de rang 1, pas de wrapper `rankOne` dÃ©diÃ© â€” convention identique Ã  celle de
`gleason-theorem-lean`). Toute application sur les projections de rang 1 qui
prÃ©serve l'orthogonalitÃ© **dans un seul sens** (`PQ = 0 âŸ¹ Ï†(P)Ï†(Q) = 0`, ni
injectivitÃ© ni surjectivitÃ© supposÃ©es) est, en dimension finie `n â‰¥ 3`, une
symÃ©trie de Wigner â€” Å emrl 2021, *Wigner symmetries and Gleason's theorem*
(arXiv:2106.06182), Corollaire 1.2.

**Ce rÃ©sultat COMPOSE deux thÃ©orÃ¨mes plutÃ´t que d'introduire un contenu
mathÃ©matique autonome** : le cÅ“ur de la preuve applique `Gleason.gleason`
(dÃ©pendance externe) DEUX FOIS â€” une fois pour construire, Ã  partir d'une
densitÃ©-test `D` et de l'hypothÃ¨se de prÃ©servation, une seconde densitÃ© `E` ;
une seconde fois implicitement en spÃ©cialisant `D := projL(Ï†Q)` pour identifier
`E = projL Q` via le lemme spectral Ã©lÃ©mentaire (U2) â€” puis conclut avec
`wigner` (bloc interne ci-dessus) via le corollaire (B) de Wigner en langage de
projections (U1, jamais construit avant ce jalon). DÃ©coupage complet en six
sous-jalons (U1 : corollaire de Wigner en projections ; U2 : lemme spectral ;
U3a : extension d'une fonction-cadre sur les droites en `ProjMeasure` complet,
absente de `gleason-theorem-lean` et donc dÃ©rivÃ©e dans ce dÃ©pÃ´t ; U3b :
Â« Gleason appliquÃ© deux fois Â» ; U4 : assemblage ; U5 : rÃ©duction
fini-dimensionnelle par comptage de cardinalitÃ©) â€” dÃ©tail complet dans
`MILESTONES.md`.

## ThÃ©orÃ¨me de CohÃ©rence de Grain (BornRule)

```lean
structure Perspective (n : â„•) where
  cells : Finset (Submodule â„‚ (H n))
  nz    : âˆ€ c âˆˆ cells, c â‰  âŠ¥
  ortho : âˆ€ c âˆˆ cells, âˆ€ c' âˆˆ cells, c â‰  c' â†’ c â‰¤ c'á—®
  span  : sSup (cells : Set (Submodule â„‚ (H n))) = âŠ¤

theorem grainCoherenceTheorem (hn3 : 3 â‰¤ n) (hA : AxGrain Est) (hN : AxNorm Est)
    (hPos : AxPos Est) {v : H n} (hv : â€–vâ€– = 1) (hNul : AxNul Est v)
    (D : Perspective n) {c : Submodule â„‚ (H n)} (hc : c âˆˆ D.cells) :
    Est D c = âˆ‘ i : Fin (Module.finrank â„‚ c),
      â€–âŸªv, ((stdOrthonormalBasis â„‚ c i : c) : H n)âŸ«_â„‚â€– ^ 2

theorem grainCoherenceTheorem_projector (hn3 : 3 â‰¤ n) (hA : AxGrain Est)
    (hN : AxNorm Est) (hPos : AxPos Est) {v : H n} (hv : â€–vâ€– = 1)
    (hNul : AxNul Est v) (D : Perspective n) {c : Submodule â„‚ (H n)}
    (hc : c âˆˆ D.cells) :
    Est D c = â€–projL c vâ€– ^ 2
```

Pour une perspective `D` (partition orthogonale de `H n` en cellules non
nulles) et une cellule `c` de `D`, toute rÃ¨gle d'estimation `Est` satisfaisant
(Grain), (Norm), (Pos) et, pour un vecteur unitaire `v` fixÃ©, (Null), vÃ©rifie
`Est D c = âˆ‘áµ¢ â€–âŸ¨v,fáµ¢âŸ©â€–Â²` sur toute base orthonormÃ©e `(fáµ¢)` de `c` â€” la rÃ¨gle de
Born en toute gÃ©nÃ©ralitÃ©, dÃ©rivÃ©e des quatre axiomes de cohÃ©rence seuls, sans
supposer `Est` a priori de la forme d'une trace. Couvre la route descriptive
(via le thÃ©orÃ¨me de Gleason) ; une seconde route de dÃ©rivation indÃ©pendante
(via un axiome de stabilitÃ© dynamique plutÃ´t que de cohÃ©rence de grain),
l'existence/consistance des quatre axiomes eux-mÃªmes, et la convergence
intersubjective entre observateurs comme corollaire sont des extensions
futures possibles, non attaquÃ©es ici.

**Ce rÃ©sultat COMPOSE Gleason et l'infrastructure Uhlhorn plutÃ´t que
d'introduire un contenu mathÃ©matique autonome** : B2 construit une fonction-
cadre sur les droites directement depuis la rÃ¨gle d'estimation (via
`Perspective.binary`) et invoque U3a + `Gleason.gleason` (rÃ©el, pas un axiome)
pour obtenir une densitÃ© `Ï` ; B3 rÃ©utilise U2 pour montrer qu'un opÃ©rateur
densitÃ© qui s'annule sur l'orthogonal d'un vecteur unitaire `v` est exactement
`projL (â„‚âˆ™v)` ; B4 relie (Null) Ã  cette hypothÃ¨se d'annulation et assemble le
tout via `refinePerspective`/`refine_filter_eq_cellLines` (dÃ©jÃ  prouvÃ©s en B1).
DÃ©coupage complet en quatre jalons (B1 : scaffolding â€” perspectives, axiomes,
non-contextualitÃ© ; B2 : pont vers Gleason ; B3 : pinning ; B4 : assemblage
final) â€” dÃ©tail complet et Ã©carts favorables dans `MILESTONES.md`.

`#print axioms grainCoherenceTheorem` ne dÃ©pend que de `[propext,
Classical.choice, Quot.sound]` : le thÃ©orÃ¨me de Gleason est importÃ© comme un
vrai thÃ©orÃ¨me (`Gleason.gleason`), jamais postulÃ©.

`grainCoherenceTheorem_projector` est uniquement la version en notation
projecteur du thÃ©orÃ¨me prÃ©cÃ©dent : l'identitÃ© de Parseval identifie sa somme
sur la base orthonormÃ©e Ã  `â€–projL c vâ€–Â²`. Ce n'est pas un nouveau rÃ©sultat
mathÃ©matique indÃ©pendant.

## ThÃ©orÃ¨me des infÃ©rences contraires de Kent (HistoriesKent)

```lean
abbrev History (n L : â„•) := Fin L â†’ Submodule â„‚ (H n)

def IsConsistent (Ïˆ : H n) (Ps : Fin L â†’ Perspective n) : Prop :=
  âˆ€ h k : History n L, IsHistoryOf Ps h â†’ IsHistoryOf Ps k â†’ h â‰  k â†’
    decFunctional Ïˆ h k = 0

def histProb (Ïˆ : H n) (h : History n L) : â„ := â€–chainOp h Ïˆâ€– ^ 2

theorem contrary_inferences :
    âˆƒ (Ps Ps' : Fin 2 â†’ Perspective 3) (Ïˆ : H 3),
      P 0 âŸ‚ P 1 âˆ§
      IsConsistent Ïˆ Ps âˆ§ IsConsistent Ïˆ Ps' âˆ§
      (histProb Ïˆ (![(P 0)á—®, F] : History 3 2) = 0 âˆ§ histProb Ïˆ (![P 0, F] : History 3 2) â‰  0) âˆ§
      (histProb Ïˆ (![(P 1)á—®, F] : History 3 2) = 0 âˆ§ histProb Ïˆ (![P 1, F] : History 3 2) â‰  0)
```

En franÃ§ais : il existe deux familles cohÃ©rentes d'histoires Ã  deux Ã©tages sur
`H 3`, partageant la mÃªme prÃ©paration `Ïˆ` et le mÃªme Ã©tage final de
post-sÃ©lection `F`, telles que la premiÃ¨re implique avec certitude la
proposition `P 0`, la seconde implique avec certitude `P 1`, et `P 0` est
orthogonale Ã  `P 1` â€” Kent 1997, PRL 78, 2874, arXiv:gr-qc/9604012. Un Ã©tage
temporel d'un ensemble d'histoires **est** une `BornRule.Perspective`,
rÃ©utilisÃ©e telle quelle. La cohÃ©rence utilisÃ©e est la version Â« medium/forte Â»
de Kent (`decFunctional Ïˆ h k = 0` pour toute paire d'histoires distinctes de
la famille, pas seulement sa partie rÃ©elle). TÃ©moin explicite construit en
dimension 3 : `Ïˆâ‚€ := eâ‚€+eâ‚+eâ‚‚`, `Ï†â‚€ := eâ‚€+eâ‚âˆ’eâ‚‚` (non normalisÃ©s), `P i :=
â„‚âˆ™(e i)`, `F := â„‚âˆ™Ï†â‚€` â€” l'annulation clÃ© du tÃ©moin est `âŸªÏ†â‚€, e iâŸ« = 1` pour
`i âˆˆ {0,1}` (`= -1` pour `i = 2`, hors tÃ©moin).

**Note de neutralitÃ©.** Le contenu mathÃ©matique ci-dessus â€” deux ensembles
cohÃ©rents impliquant chacun avec certitude une proposition, ces deux
propositions Ã©tant orthogonales â€” est un fait incontestÃ©. Son interprÃ©tation
comme objection Ã  la prÃ©dictibilitÃ© des histoires cohÃ©rentes est dÃ©battue :
la rÃ©ponse usuelle (Griffiths) invoque la Â« single-framework rule Â» â€” les
deux infÃ©rences ne sont valides que chacune dans son propre cadre, jamais
combinÃ©es dans un mÃªme raisonnement. Ce dÃ©pÃ´t fixe l'Ã©noncÃ© mathÃ©matique,
sans trancher le dÃ©bat interprÃ©tatif.

Le thÃ©orÃ¨me de profusion gÃ©nÃ©rique de Dowkerâ€“Kent (J. Stat. Phys. 82, 1575
(1996), comptage de paramÃ¨tres/dimensions de variÃ©tÃ©s montrant que la
contrariÃ©tÃ© n'est pas un cas isolÃ©) est explicitement hors scope de ce bloc â€”
extension future possible, voir `MILESTONES.md`.

## Borne de circuit dâ€™interfÃ©rence par records redondants (Complexity)

Le bloc `QuantumFoundations.Complexity` relie les records spatiaux exacts ou
approximatifs de
Riedel aux circuits quantiques 2-locaux. Les circuits sont des listes finies
de portes unitaires, chacune locale Ã  un `Finset (Fin N)` de cardinal au plus
deux. Pour `[Gâ‚, Gâ‚‚, Gâ‚ƒ]`, la convention est
`eval C x = Gâ‚ƒ (Gâ‚‚ (Gâ‚ x))`.

Le thÃ©orÃ¨me principal a le type exact suivant :

```lean
theorem regions_card_le_two_mul_circuit_length_of_cross_amplitude_ne_zero
    {N d K R : â„•} [NeZero R]
    (e : H (d ^ N) â‰ƒâ‚—áµ¢[â„‚] Sites N d) (C : Circuit N d)
    (regions : Fin R â†’ Finset (Fin N))
    (recs : Fin R â†’ LabeledResolution (d ^ N) K) (Ïˆ : H (d ^ N))
    (hrec : IsRecordedOn Ïˆ recs) (i j : Fin K) (hij : i â‰  j)
    (hlocal : âˆ€ r, IsLocalTo (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : âˆ€ r r', r â‰  r' â†’ Disjoint (regions r) (regions r'))
    (hcross : âŸªbranch recs Ïˆ j, Circuit.evalOnH C e (branch recs Ïˆ i)âŸ«_â„‚ â‰  0) :
    R â‰¤ 2 * Circuit.length C
```

Ainsi, toute amplitude croisÃ©e exacte non nulle entre deux branches
distinctes force le circuit Ã  toucher chaque rÃ©gion-record ; les rÃ©gions
Ã©tant deux-Ã -deux disjointes et chaque porte touchant au plus deux sites, on
obtient la borne explicite `R â‰¤ 2 * C.length`.

Les jalons C3â€“C6 ajoutent les proxies exacts, sans division :

```lean
DistinguishesAt e a b Î´ C :=
  2 * Î´ â‰¤ â€–âŸªa, C.evalOnH e aâŸ«_â„‚ - âŸªb, C.evalOnH e bâŸ«_â„‚â€–

InterferesAt e a b Î´ C :=
  2 * Î´ â‰¤ â€–âŸªa, C.evalOnH e bâŸ«_â„‚â€– + â€–âŸªb, C.evalOnH e aâŸ«_â„‚â€–
```

Pour deux branches enregistrÃ©es distinctes et non nulles, normalisÃ©es par
`normalizedBranch`, avec `0 < Î´ â‰¤ 1`, des rÃ©gions-records deux-Ã -deux
disjointes et la localitÃ© des projecteurs cibles pour **les deux** Ã©tiquettes,
`redundant_records_give_interference_lower_bound` prouve que tout circuit
interfÃ©rant a longueur au moins `ceilHalf R := (R + 1) / 2`. Si un circuit
explicite `D` implÃ©mente exactement `2 P_j - I`, alors
`record_phase_flip_gives_distinguishability_upper_bound` donne un tÃ©moin de
distinguabilitÃ© de longueur `D.length`. Finalement,
`redundant_records_give_proxy_gap_certificate` prouve le certificat sans
soustraction `D.length + g â‰¤ ceilHalf R`, et
`redundant_records_complexity_gap` en donne la version minimale dans
`WithTop â„•` :

```lean
distinguishabilityComplexity e a b Î´ + (g : WithTop â„•)
  â‰¤ interferenceComplexity e a b Î´
```

Le jalon C7 ajoute une persistance conditionnelle sous Ã©volution rÃ©versible
par circuits finis. Une `ReversibleCircuitEvolution` contient deux circuits
explicites `forward` et `backward`, dont les Ã©valuations sont inverses, et le
surcoÃ»t `forward.length + backward.length`. Comme
`eval (C ++ D) = eval D âˆ˜â‚— eval C`, `backward ++ C ++ forward` implÃ©mente
`forward âˆ˜â‚— C âˆ˜â‚— backward`, tandis que `forward ++ C ++ backward` implÃ©mente
le pullback opposÃ©. Les proxies sont exactement invariants sous ces
conjugaisons. Une borne supÃ©rieure de distinguabilitÃ© augmente d'au plus un
surcoÃ»t, une borne infÃ©rieure d'interfÃ©rence diminue d'au plus un surcoÃ»t, et
le gap certifiÃ© diminue donc d'au plus deux surcoÃ»ts.

L'inverse canonique a Ã©galement Ã©tÃ© construit : chaque porte inverse garde le
mÃªme support local, et le circuit inverse renverse la liste en inversant ses
portes. Ainsi `ofCircuit E` a un surcoÃ»t `2 * E.length`, d'oÃ¹ la condition
exacte sur les records
`D.length + 4 * E.length + g â‰¤ ceilHalf R`. Les versions minimales dans
`WithTop â„•` sont prouvÃ©es directement sous l'infimum, y compris dans le cas
`âŠ¤`, sans supposer qu'un minimum est atteint et sans soustraction.

Le jalon C8 remplace les identitÃ©s de record exactes par le budget agrÃ©gÃ©
`ApproxRecordFor P target other Î· :=
â€–P target - targetâ€– + â€–P otherâ€– â‰¤ Î·`. Cette agrÃ©gation correspond exactement
aux deux termes produits par la dÃ©composition projecteur/dÃ©faut : une rÃ©gion
non touchÃ©e donne la constante nette `â€–cross amplitudeâ€– â‰¤ Î·`. Pour les deux
orientations du proxy, le budget devient `Î·i + Î·j`; la condition stricte
`Î·i + Î·j < 2 * Î´` force donc encore chaque rÃ©gion Ã  Ãªtre touchÃ©e.

Le circuit de lecture explicite peut lui-mÃªme Ãªtre approchÃ© sur les deux
vecteurs, avec erreur agrÃ©gÃ©e `Î¾`. La sÃ©paration diagonale idÃ©ale `2` se
dÃ©grade d'au plus `2 * Î·j + Î¾`, d'oÃ¹ le seuil suffisant
`2 * Î´ + 2 * Î·j + Î¾ â‰¤ 2`. Ces certificats donnent le gap robuste et sa version
minimale. Le transport C7 Ã©tant une conjugaison unitaire exacte, il n'ajoute
aucune erreur analytique : seul subsiste le coÃ»t combinatoire
`2 * Evo.overhead`, ou `4 * E.length`. Ã€ `Î·i = Î·j = Î¾ = 0`, les rÃ©sultats
exacts C4â€“C7 sont retrouvÃ©s.

Les trois prÃ©dicats robustes publics sont exactement :

```lean
ApproxRecordFor P target other Î· :=
  â€–P target - targetâ€– + â€–P otherâ€– â‰¤ Î·

ApproxRecordedPairOn recs a b i j Î·i Î·j := âˆ€ r,
  ApproxRecordFor (rproj (recs r) i) a b Î·i âˆ§
  ApproxRecordFor (rproj (recs r) j) b a Î·j

ApproximatesRecordPhaseFlipOn e D Î› j a b Î¾ :=
  â€–Circuit.evalOnH D e a - recordPhaseFlip Î› j aâ€– +
  â€–Circuit.evalOnH D e b - recordPhaseFlip Î› j bâ€– â‰¤ Î¾
```

Le jalon C9 instancie cette architecture dans le modÃ¨le binaire explicite de
rÃ©pÃ©tition. `zeroBranch R` et `oneBranch R` sont les vecteurs de base des
configurations constantes zÃ©ro et un, transportÃ©s par `sitesEquivR`; leur somme
`repetitionState R` n'est volontairement pas normalisÃ©e. Chaque singleton
`{r}` porte la rÃ©solution computationnelle locale et constitue un record
indÃ©pendant du mÃªme label binaire. La rÃ©flexion `2 Pâ‚ - I` au premier site est
une porte de lecture unique, tandis que le circuit ordonnÃ© de `R` portes
Pauli-X Ã©change exactement les deux branches. On obtient donc

```lean
distinguishabilityComplexity (sitesEquivR R) (zeroBranch R) (oneBranch R) 1 = 1
ceilHalf R â‰¤ interferenceComplexity (sitesEquivR R) (zeroBranch R) (oneBranch R) 1
interferenceComplexity (sitesEquivR R) (zeroBranch R) (oneBranch R) 1 â‰¤ R
```

ainsi que le gap pour `1 + g â‰¤ ceilHalf R` et sa persistance conditionnelle
sous le budget exact `1 + 4 * E.length + g â‰¤ ceilHalf R`. Le majorant fini
prouve en particulier que l'interference complexity n'est pas `âŠ¤`.
L'option de sharpness par flips appariÃ©s n'est pas revendiquÃ©e : les bornes
fermÃ©es sont `ceilHalf R â‰¤ C_I â‰¤ R`.

Le jalon C10 instancie enfin la thÃ©orie robuste C8 sur une famille Ã  bruit
**non nul** explicite, sur `R + 1` sites : un qubit source (site `0`) plus
`R` qubits de mÃ©moire (`recordSite r := Fin.succ r`). Un `NoiseProfile`
normalisÃ© `(keep, leak)` (`â€–keepâ€–Â² + â€–leakâ€–Â² = 1`) mÃ©lange deux
configurations de mÃªme bit source, `noisyZeroBranch := keep â€¢ basis00 + leak
â€¢ basis01` et `noisyOneBranch := leak â€¢ basis10 + keep â€¢ basis11`, qui restent
**exactement orthogonales pour tout `leak`** puisque le qubit source diffÃ¨re
entre elles. Chaque record a une erreur exacte calculÃ©e : il fixe
exactement la configuration alignÃ©e et fuit exactement `â€–leakâ€–` vers
l'autre, d'oÃ¹ l'erreur agrÃ©gÃ©e exacte `2 * â€–leakâ€–` par Ã©tiquette â€” un
habitant non trivial de `ApproxRecordedPairOn`, sans jamais invoquer
`IsRecordedOn`. Au seuil `Î´ = 1/2`, la condition robuste est exactement

```lean
def NoiseProfile.IsRobust (p : NoiseProfile) : Prop := 4 * â€–p.leakâ€– < 1
```

sous laquelle on obtient exactement les mÃªmes bornes que C9 :

```lean
distinguishabilityComplexity (sitesEquivR (R+1)) (noisyZeroBranch p R) (noisyOneBranch p R) (1/2) = 1
ceilHalf R â‰¤ interferenceComplexity (sitesEquivR (R+1)) (noisyZeroBranch p R) (noisyOneBranch p R) (1/2)
interferenceComplexity (sitesEquivR (R+1)) (noisyZeroBranch p R) (noisyOneBranch p R) (1/2) â‰¤ R + 1
```

ainsi que le gap robuste et sa persistance conditionnelle sous le mÃªme budget
`1 + 4 * E.length + g â‰¤ ceilHalf R`. Le triplet pythagoricien
`99Â² + 20Â² = 101Â²` fournit un tÃ©moin rationnel concret
`(keep, leak) = (99/101, 20/101)` avec `4 * (20/101) = 80/101 < 1`, auquel
tous les thÃ©orÃ¨mes C10aâ€“C10g s'appliquent sans hypothÃ¨se supplÃ©mentaire.
Trois gÃ©nÃ©ralisations additives de C9 (jamais nÃ©cessaires Ã  C9 lui-mÃªme) ont
servi de brique : une branche de base Ã  configuration arbitraire
(`configurationBranch`), une lecture par rÃ©flexion Ã  site arbitraire
(`recordReadoutGateAt`/`recordReadoutCircuitAt`), et l'action du circuit
Â« flip tous les bits Â» sur une configuration arbitraire
(`allBitFlipCircuit_maps_configurationBranch`) â€” dans chaque cas la
dÃ©claration C9 existante est reprouvÃ©e comme cas particulier, sans changer
son type public.

Le jalon C11 comble prÃ©cisÃ©ment l'Ã©cart signalÃ© Ã  la fin de C10 : un circuit
fini explicite de portes `1`- et `2`-locales gÃ©nÃ¨re **unitairement** les
branches source-record Ã  partir d'un qubit source non corrÃ©lÃ©
`Î±|0âŸ© + Î²|1âŸ©` et de `R` qubits de mÃ©moire vierges, au lieu de les supposer
dÃ©jÃ  formÃ©es. `controlledBitFlipGate` (C11a) est une porte de permutation
`2`-locale; `idealFanoutCircuit R` (C11b) copie l'Ã©tiquette classique du
qubit source vers chaque record â€” un fanout d'Ã©tiquette en base de calcul,
jamais un clonage d'un Ã©tat quantique arbitraire (le no-cloning n'est pas
violÃ© : seule l'Ã©tiquette classique `0`/`1` est propagÃ©e, jamais les
amplitudes propres du qubit source). La construction la plus dÃ©licate
(C11e) est une vÃ©ritable rotation unitaire de mÃ©lange d'amplitude sur un
qubit, Ã©levÃ©e Ã  tous les `N` sites via la reprÃ©sentation plate `Sites N d`
(aucune infrastructure de facteur tensoriel n'existait dans le dÃ©pÃ´t pour
cela) : `prepLinearMap p t := keep â€¢ Pâ‚€ + leak â€¢ (F âˆ˜ Pâ‚€) - conj(leak) â€¢
(F âˆ˜ Pâ‚) + conj(keep) â€¢ Pâ‚`, prouvÃ©e unitaire par expansion directe du
produit scalaire Ã  16 termes. Cette construction rÃ©ussit **sans condition**
pour chaque `NoiseProfile` â€” aucune porte supplÃ©mentaire n'a dÃ» Ãªtre
supposÃ©e. `noisyMeasurementCircuit p R` (C11fâ€“g, longueur `2R`) transforme
`Î± â€¢ basis00 + Î² â€¢ basis10` en exactement
`Î± â€¢ noisyZeroBranch p R + Î² â€¢ noisyOneBranch p R` : ce sont les *mÃªmes*
Ã©tats que ceux de C10, si bien que le gap robuste et sa persistance
conditionnelle sous un circuit ultÃ©rieur arbitraire s'y transportent
immÃ©diatement (C11i), sans nouvel argument de distinguabilitÃ©. Le triplet
pythagoricien `3Â² + 4Â² = 5Â²` fournit un tÃ©moin rationnel concret
`(amp0, amp1) = (3/5, 4/5)` (C11j), auquel s'applique â€” combinÃ© au profil de
bruit rationnel `(99/101, 20/101)` de C10h â€” toute la chaÃ®ne C11 sans
hypothÃ¨se supplÃ©mentaire.

Le jalon C12 comble le pont optionnel en norme d'opÃ©rateur laissÃ© de cÃ´tÃ©
depuis C8 : `toContinuousLinearMapFD` (C12a) est la vue canonique en
application linÃ©aire continue d'une application linÃ©aire issue d'un espace
normÃ© complexe de dimension finie (`LinearMap.toContinuousLinearMap` de
Mathlib) â€” `Circuit.evalOnH`, `recordPhaseFlip` et toute l'API `LinearMap`
existante restent inchangÃ©es; c'est une vue supplÃ©mentaire, pas un
remplacement. `ApproximatesOperator A B Îµ := â€–A - Bâ€– â‰¤ Îµ` (C12b) est une
erreur de norme d'opÃ©rateur gÃ©nÃ©rique, sans rÃ©fÃ©rence aux records ou
circuits; l'estimation centrale `â€–A x - B xâ€– â‰¤ Îµâ€–xâ€–` donne, sur deux Ã©tats
unitaires `a, b`, l'accumulation `â€–A a - B aâ€– + â€–A b - B bâ€– â‰¤ 2Îµ` â€” le
facteur `2` dÃ©rivÃ© par arithmÃ©tique simple, jamais postulÃ©.
`ApproximatesRecordPhaseFlipOp` (C12c) spÃ©cialise ce pont Ã 
`recordPhaseFlip` : un budget d'erreur en norme d'opÃ©rateur `Îµ` implique le
budget ponctuel C8 `Î¾ = 2Îµ`, ce qui restitue directement (C12d) le seuil de
lecture `2Î´ + 2Î·j + 2Îµ â‰¤ 2` et (C12e) le gap proxy robuste ainsi que sa
persistance conditionnelle, en rÃ©utilisant tel quel l'estimation analytique
de C8 â€” aucune nouvelle estimation n'est introduite. Au modÃ¨le bruitÃ© C10
(C12f), ce seuil devient exactement `4â€–leakâ€– + 2Îµ â‰¤ 1`; l'hypothÃ¨se
`p.IsRobust` (`4â€–leakâ€– < 1`, stricte) reste nÃ©anmoins nÃ©cessaire en plus de
ce seuil â€” non redondante, car `hreadout` seul (avec `Îµ â‰¥ 0`) ne donne que
l'inÃ©galitÃ© large `4â€–leakâ€– â‰¤ 1`, insuffisante pour l'argument
d'interfÃ©rence strict. Aux branches dynamiquement engendrÃ©es par C11
(C12g), le mÃªme seuil s'applique directement au couple de branches gÃ©nÃ©rÃ©.
Le tÃ©moin rationnel concret `Îµ = 1/20` vÃ©rifie exactement
`80/101 + 2Â·(1/20) â‰¤ 1` par arithmÃ©tique rationnelle exacte. Des lois de
composition gÃ©nÃ©riques (C12h, facultatives) prÃ©parent l'accumulation
d'erreur de simulation de C13.

Le jalon C13 Ã©tablit la persistance robuste du gap sous une vÃ©ritable
Ã©volution `U` prÃ©servant la norme (pas nÃ©cessairement un circuit), tant
qu'un circuit exact `E` l'approche en norme d'opÃ©rateur Ã  erreur `Îµ`. Le
point mathÃ©matique central est qu'une persistance au **mÃªme** seuil `Î´` sans
marge n'est en gÃ©nÃ©ral **pas** justifiÃ©e : perturber deux Ã©tats unitaires de
`Îµ` chacun dÃ©place la diffÃ©rence diagonale d'au plus `4Îµ` et la somme
croisÃ©e d'au plus `4Îµ` (C13b), ce qui dÃ©place le seuil de proxy de `2Îµ`
(puisque les dÃ©finitions utilisent `2Â·seuil`). C13 introduit donc une marge
`Î¼` : un certificat Ã  seuils Ã©cartÃ©s `Î´-Î¼` (interfÃ©rence) et `Î´+Î¼`
(distinguabilitÃ©) â€” `HasProxyGapMarginAtLeast` (C13d) â€” persiste sous circuit
exact (C13e) puis se transporte vers le seuil central `Î´` pour les Ã©tats
Ã©voluÃ©s par `U`, dÃ¨s que `2Îµ â‰¤ Î¼` (C13f, le thÃ©orÃ¨me principal). Le
certificat de simulation `CircuitSimulatesEvolutionAt`/`HasCircuitSimulationAt`
(C13f) et son extension dÃ©pendante du temps `HasCircuitSimulationBound`
(C13j) rendent ce rÃ©sultat directement rÃ©utilisable. InstanciÃ© au modÃ¨le
bruitÃ© C10 (C13g) puis aux branches engendrÃ©es par C11 (C13h), avec le
tÃ©moin rationnel concret `Î´=1/2, Î¼=1/10, Îµ=1/20` (C13i,
`80/101 < 4/5`, `6/5+80/101 â‰¤ 2`, `2Â·(1/20) â‰¤ 1/10`). Une interface
optionnelle (C13k) construit une Ã©volution *effectivement* engendrÃ©e par un
gÃ©nÃ©rateur auto-adjoint `H` â€” `evolve t := exp(-itH)`, via l'exponentielle
opÃ©ratorielle existante de Mathlib pour les Câ‹†-algÃ¨bres bornÃ©es, sans aucune
hypothÃ¨se supplÃ©mentaire â€” dont seule la loi de groupe additive reste non
prouvÃ©e (obstruction de rÃ©solution d'instances Mathlib prÃ©cisÃ©ment
documentÃ©e dans le fichier, non une lacune mathÃ©matique).

Le jalon **C14** relie deux thÃ©orÃ¨mes dÃ©jÃ  Ã©tablis plutÃ´t que d'en dÃ©river un
depuis l'autre : la dÃ©composition en branches jointes, uniques et
orthogonales de `Induction.riedel` (BranchesRiedel), et le poids de Born
`grainCoherenceTheorem_projector` (BornRule), qui assigne `â€–projL c vâ€–Â²` Ã 
toute cellule `c` d'une perspective, sous (Pos), (Norm), (Grain), (Null).
`BranchesRiedel/BornBridge/` distingue quatre objets : un vecteur de branche
`B f`, sa cellule active `span â„‚ {B f}` (dÃ©finie seulement si `B f â‰  0` â€”
un vecteur nul n'a pas de cellule formelle), le support `branchSupport`
(la borne supÃ©rieure des cellules actives, pas nÃ©cessairement tout
l'espace) et la cellule rÃ©siduelle orthogonale `residualCell` (qui peut
Ãªtre `âŠ¥`). L'identitÃ© de projection centrale,
`starProjection_branchCell_apply_state : (branchCell B f).starProjection Ïˆ
= activeBranchVector B f` (C14c), est un fait d'algÃ¨bre linÃ©aire pur â€” via
`Submodule.eq_starProjection_of_mem_orthogonal'` â€” indÃ©pendant de toute
pondÃ©ration. `BranchPerspectivePackage` (C14e) construit une vÃ©ritable
`Perspective` Ã  partir des cellules actives, en ajoutant la cellule
rÃ©siduelle seulement si elle est non nulle (`Perspective` interdit les
cellules `âŠ¥`). `recordBranch_weight_eq_norm_sq` (C14f) chaÃ®ne alors
`grainCoherenceTheorem_projector` et l'identitÃ© de projection : le poids de
Born de chaque cellule active vaut exactement `â€–B fâ€–Â²`, le poids rÃ©siduel
est nul, et les poids actifs somment Ã  `1`. L'invariance de choix de
record (C14a) â€” `chainProj_choice_invariant`, prouvÃ©e par remplacement
d'observable un par un via `Induction.tunneling`, sans jamais composer deux
records diffÃ©rents de la mÃªme observable â€” donne l'invariance du poids par
rapport au record choisi (C14f.5), au niveau des vecteurs, pas seulement
des normes. `record_induced_Born_decomposition` (C14g) assemble le tout en
un thÃ©orÃ¨me abstrait unique, spÃ©cialisÃ© au modÃ¨le multi-sites local (C14h)
puis Ã  la gÃ©nÃ©ration unitaire exacte de C11 (C14i) â€” deux branches
`q.amp0 â€¢ basis00 R`/`q.amp1 â€¢ basis11 R`, poids `â€–amp0â€–Â²`/`â€–amp1â€–Â²` â€”,
concrÃ¨tement Ã  `(3/5, 4/5)` donnant les poids rationnels exacts `9/25` et
`16/25` (C14l). Le modÃ¨le bruitÃ© C10 ne satisfait que la redondance
approximative (`ApproxRecordedPairOn`), pas l'exacte `IsRecordedOn` :
l'unicitÃ© exacte de branche n'est donc pas conclue pour lui, seule
l'extraction exacte des composantes de source (C14j) demeure. Enfin, les
poids de Born des branches Ã©voluÃ©es sous une Ã©volution norm-prÃ©servante
(C13) conservent leur norme au carrÃ© â€” via l'identitÃ© de polarisation en
termes de normes, `inner_eq_sum_norm_sq_div_four` â€” sans que la branche
Ã©voluÃ©e soit encore sÃ©lectionnÃ©e par les projecteurs de record d'origine
(C14k).

Le rÃ©sultat porte uniquement
sur un nombre fini de sites, une dimension locale finie, des records exacts
ou des records approximatifs fournis,
des rÃ©gions deux-Ã -deux disjointes, des portes exactement 2-locales et une
amplitude/proxy au-dessus du seuil explicite. Il ne traite pas
la formation gÃ©nÃ©rique de records approximatifs par dÃ©cohÃ©rence (distincte de
la construction unitaire explicite de C11), la synthÃ¨se
efficace de projecteurs locaux arbitraires, la complÃ©tion en norme
d'opÃ©rateur de toute l'API du dÃ©pÃ´t (C12 ne couvre que le pont de lecture de
record), le
critÃ¨re physique complet de Taylorâ€“McCulloch, une borne de simulation de
Trotter/formule produit ou de Liebâ€“Robinson, une croissance linÃ©aire ou
polynomiale du coÃ»t de simulation en temps (C13 ne formalise aucune notation
`O(t)`), la croissance gÃ©nÃ©rique de complexitÃ©, la croissance
de Brownâ€“Susskind, l'irrÃ©versibilitÃ© macroscopique, l'Ã©quivalence avec
Weingarten, ni une interprÃ©tation de la mÃ©canique quantique. C14 relie
records redondants et poids de Born pour un modÃ¨le donnÃ©, sous (Pos),
(Norm), (Grain), (Null) â€” il ne prÃ©tend pas que les records seuls
impliquent la rÃ¨gle de Born, ni que (Grain) n'a besoin de valoir que sur
les perspectives physiquement rÃ©alisÃ©es, ni une unicitÃ© de dÃ©composition
en branches approximative ou gÃ©nÃ©rique en systÃ¨me Ã  N corps.

**C15** est la formalisation Lean et lâ€™intÃ©gration au dÃ©pÃ´t du ThÃ©orÃ¨me 3 et
du Corollaire 2 de Marko Lela, Â« The Born Rule as the Unique
Refinement-Stable Induced Weight on Robust Record Sectors Â»
(arXiv:2603.24619v1). Son objet est un poids induit sur des situations de
record admissibles, pas une mesure sur le treillis complet des projecteurs.
Lâ€™Ã©quivalence interne est dâ€™abord lâ€™Ã©galitÃ© des profils de raffinement
binaire; la saturation binaire exacte prouve ensuite que ces profils sont
classifiÃ©s par la norme projetÃ©e. Lâ€™Ã©quation fonctionnelle qui en rÃ©sulte
force `W = c â€–P_R Î¨â€–Â²`, et une normalisation finie fixe `c = 1`.
Lâ€™additivitÃ© peut Ãªtre hÃ©ritÃ©e dâ€™une valuation extensive sur des faisceaux de
continuations disjoints. Aucun thÃ©orÃ¨me de Gleason, Busch,
dÃ©cision-thÃ©orique ou dâ€™envariance nâ€™est utilisÃ©. La saturation binaire est
supposÃ©e, non dÃ©rivÃ©e de la dynamique C14; saturation dense plus continuitÃ©,
le pont physique C14/C15 et C16 sont explicitement diffÃ©rÃ©s.

**C17** est le premier thÃ©orÃ¨me de stabilitÃ© quantitative de ce
dÃ©veloppement. Il suppose que les deux poids satisfont dÃ©jÃ  la loi
quadratique exacte fournie par C15 et mesure la perturbation par la distance
entre composantes projetÃ©es `u = P_(Râ‚)x Î¨â‚x` et `v = P_(Râ‚‚)x Î¨â‚‚x`. Il prouve
`|Wâ‚-Wâ‚‚| â‰¤ (â€–uâ€–+â€–vâ€–)â€–u-vâ€–`, puis `|Wâ‚-Wâ‚‚| â‰¤ 2â€–u-vâ€–` sur la boule unitÃ©, ainsi
que les bornes finies `LÂ¹`, `2Â·card(s)Â·Îµ` et demi-`LÂ¹`. Il ne traite ni des
hypothÃ¨ses C15 approximatives, ni de lâ€™unicitÃ© approximative des branches, ni
de la production dynamique de la proximitÃ© des composantes. Aucune
revendication de prioritÃ© historique nâ€™est faite.

**C17b** est un jalon dâ€™intÃ©gration, pas un renforcement du cÅ“ur C17 dÃ©jÃ 
clos. Sur la boule unitÃ©, un secteur fixÃ© vÃ©rifie
`|w_R(Ïˆ)-w_R(Ï†)| â‰¤ 2â€–Ïˆ-Ï†â€–`; deux projecteurs Ã  distance au plus `Îµ` en norme
dâ€™opÃ©rateur vÃ©rifient `|w_R(Ïˆ)-w_S(Ïˆ)| â‰¤ 2Îµ`. Un certificat de simulation C13
donne donc, pour chaque secteur fixÃ©,
`|w_R(U(t)Ïˆ)-w_R(CÏˆ)| â‰¤ 2Îµ`. Les poids de branches C14 hÃ©ritent aussi de la
borne gÃ©nÃ©rique sur les vecteurs de branches lorsquâ€™une correspondance entre
branches est fournie explicitement. Ces ponts ne prouvent ni unicitÃ© ou
appariement approximatif des branches, ni saturation approximative, ni
persistance physique de la sÃ©lection des records.

## Assistance IA

Ce dÃ©veloppement (squelette, preuves, choix d'architecture) a Ã©tÃ© rÃ©alisÃ© avec
l'assistance de Claude (Anthropic), sous supervision humaine Ã  chaque Ã©tape : chaque
API Mathlib incertaine a Ã©tÃ© vÃ©rifiÃ©e en `stdin` avant usage (`lake env lean --stdin`),
chaque jalon a dÃ©marrÃ© par un squelette en `sorry` validÃ© avant remplissage, et
`lake build` + `./scripts/guard.sh` ont tournÃ© aprÃ¨s chaque preuve fermÃ©e. Voir
`AGENTS.md` pour les rÃ¨gles exactes suivies et l'historique des commits pour le dÃ©tail
jalon par jalon.

## DÃ©marrage

```bash
./setup.sh          # toolchain + mathlib + cache + build (~10 min avec cache)
./scripts/guard.sh  # audit : 0 axiome, 0 native_decide, compte des sorry
```

## VÃ©rifier les preuves

```bash
lake build                    # doit terminer vert
./scripts/guard.sh            # 0 axiome, 0 native_decide, 0 sorry (sept blocs)
```

`#print axioms` sur les thÃ©orÃ¨mes-tÃªtes de chapitre (liste exhaustive des 155
dÃ©clarations publiques porteuses de contenu dans `ARCHITECTURE_NOTES.md`/le
rapport de clÃ´ture â€” toutes dÃ©pendent du mÃªme trio) :

```
'QuantumFoundations.naimark' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.naimark_born' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.exists_unitary_extension' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.naimark_projective_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Wigner.wigner' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Wigner.exclusivity' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Wigner.bargmann_delta_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Wigner.U_alt_eq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Uhlhorn.uhlhorn_finite_dim' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Uhlhorn.wignerSymmetryProj_of_sendsONBToONB' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Uhlhorn.traceProd_preserved_of_sendsONBToONB' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Uhlhorn.exists_projMeasure_of_frameFunctionOnLines' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.grainCoherenceTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.grainCoherenceTheorem_projector' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.full_rho_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.hker_derivation' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.exists_rho' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.eq_projL_of_vanishes_on_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.Eâ‚€_satisfies_axioms' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.refine_filter_sup_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.HistoriesKent.contrary_inferences' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.HistoriesKent.inference' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.HistoriesKent.S_consistent' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.HistoriesKent.isConsistent_single_stage' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Ce sont les trois axiomes standards acceptÃ©s par Lean/Mathlib lui-mÃªme (extensionnalitÃ©
propositionnelle, axiome du choix, soliditÃ© des quotients) â€” aucun `sorryAx`, aucun
`axiom` spÃ©cifique au projet. **Points vÃ©rifiÃ©s spÃ©cifiquement** : `uhlhorn_finite_dim`
est le premier thÃ©orÃ¨me du dÃ©pÃ´t Ã  dÃ©pendre Ã  la fois de `Gleason.gleason`
(dÃ©pendance externe) ET de `QuantumFoundations.Wigner.wigner` (bloc interne) ;
`grainCoherenceTheorem` dÃ©pend Ã  la fois de `Gleason.gleason` ET de
l'infrastructure Uhlhorn interne (U2, U3a) â€” dans les deux cas, cette double
chaÃ®ne de dÃ©pendances ne fait fuiter aucun axiome supplÃ©mentaire, confirmÃ©
ci-dessus. `contrary_inferences` dÃ©pend transitivement d'une chaÃ®ne Ã  TROIS
niveaux (`HistoriesKent` â†’ `BornRule.Perspective` â†’ `Uhlhorn`/`Gleason` externe) â€”
mÃªme trio, confirmÃ© lors de la clÃ´ture de `HistoriesKent` (2026-07-16), ainsi que
la non-rÃ©gression des axiomes de `BornRule` suite Ã  la relocalisation de
`norm_sq_sum_of_pairwise_orthogonal`/`sum_sq_projL_of_pairwise_isOrtho`
(`private` dans `Nonvacuity.lean`, migrÃ©s public vers `Perspective.lean`) :
les 34 dÃ©clarations PUBLIQUES de `BornRule` (32 prÃ©cÃ©dentes + les 2 lemmes
relocalisÃ©s, dÃ©sormais publics) re-vÃ©rifiÃ©es individuellement, aucune
affectÃ©e.

## Carte du dÃ©pÃ´t

| Fichier                                     | Contenu                                                                            | Lignes |
|---|---|---:|
| `QuantumFoundations/Naimark/Defs.lean`      | `POVM n m` (rÃ©utilise `Gleason.IsPositiveOp`)                                      | 46 |
| `QuantumFoundations/Naimark/SqrtOp.lean`    | Racine carrÃ©e positive (construction spectrale)                                    | 191 |
| `QuantumFoundations/Naimark/DilSpace.lean`  | Espace de dilatation `K`, `singleL`/`coordL`/`dilProj`                             | 194 |
| `QuantumFoundations/Naimark/Main.lean`      | `dilV`, isomÃ©trie, thÃ©orÃ¨me de Naimark, corollaire de Born                         | 157 |
| `QuantumFoundations/Naimark/Unitary.lean`   | N5 (optionnel) : extension unitaire, forme ancilla                                 | 210 |
| `QuantumFoundations/Wigner/Defs.lean`       | `e`, `eImg`, `InPerp`, `V`, `refVec`, `chidir`, `chi`, `U`, `IsWignerMap`          | 119 |
| `QuantumFoundations/Wigner/Scalar.lean`     | Kit scalaire â„‚ (rigiditÃ©, dichotomie `id`/`conj`)                                  | 117 |
| `QuantumFoundations/Wigner/Bessel.lean`     | IdentitÃ© de Bessel (Ã©galitÃ©) ; images orthonormÃ©es                                 | 126 |
| `QuantumFoundations/Wigner/VConstruction.lean` | Construction B de Bargmann : `V`, colinÃ©aritÃ©, (11)-(12a)                       | 449 |
| `QuantumFoundations/Wigner/Core.lean`       | CÅ“ur : dichotomie de `chi`, additivitÃ©/homogÃ©nÃ©itÃ© de `V`                          | 833 |
| `QuantumFoundations/Wigner/Main.lean`       | `U`, bijectivitÃ©, compatibilitÃ© avec `T`, thÃ©orÃ¨me `wigner`                        | 399 |
| `QuantumFoundations/Wigner/Uniqueness.lean` | W6 (optionnel) : exclusivitÃ© (A), unicitÃ© restreinte (B)                           | 439 |
| `QuantumFoundations/Wigner/Nonvacuity.lean` | TÃ©moins Wigner : `id` (branche unitaire), `conjCoords` (branche antiunitaire)      | 112 |
| `QuantumFoundations/Uhlhorn/Defs.lean` | `Proj1`, `TraceProd`, `PreservesOrthogonality`, `IsWignerSymmetryProj`, `IsFrameFunctionOnLines`, `SendsONBToONB` | 278 |
| `QuantumFoundations/Uhlhorn/WignerProjectionForm.lean` | U1 : corollaire (B) de Wigner en langage de projections                 | 117 |
| `QuantumFoundations/Uhlhorn/Spectral.lean`  | U2 : lemme spectral Ã©lÃ©mentaire                                                     | 131 |
| `QuantumFoundations/Uhlhorn/GleasonExtend.lean` | U3a : extension d'une fonction-cadre sur les droites en `ProjMeasure` complet  | 268 |
| `QuantumFoundations/Uhlhorn/GleasonTwice.lean` | U3b : Â« Gleason appliquÃ© deux fois Â»                                            | 175 |
| `QuantumFoundations/Uhlhorn/Assembly.lean`  | U4 (assemblage) + U5 (rÃ©duction fini-dimensionnelle), thÃ©orÃ¨me `uhlhorn_finite_dim` | 111 |
| `QuantumFoundations/Uhlhorn/Nonvacuity.lean` | TÃ©moin Uhlhorn : `Ï† := id`                                                        | 53 |
| `QuantumFoundations/BornRule/Perspective.lean` | B1 : `Perspective`, `Refines`, `AxGrain`/`AxNorm`/`AxPos`/`AxNul`, `lemma4_noncontextual`, `basisPerspective`, `cellLines`, `refinePerspective` | 555 |
| `QuantumFoundations/BornRule/GleasonBridge.lean` | B2 : `g`, `g_isFrameFunctionOnLines`, `exists_rho` (remplace `axiom gleason`) | 115 |
| `QuantumFoundations/BornRule/Pinning.lean`   | B3 : `eq_projL_of_vanishes_on_orthogonal` (identification de `Ï` via U2)          | 83 |
| `QuantumFoundations/BornRule/Assembly.lean`  | B4 (assemblage), thÃ©orÃ¨me final `grainCoherenceTheorem`                          | 215 |
| `QuantumFoundations/BornRule/Nonvacuity.lean` | TÃ©moin BornRule : `Eâ‚€ v` (rÃ¨gle de Born) satisfait Grain+Norm+Pos+Null simultanÃ©ment | 177 |
| `QuantumFoundations/Nonvacuity.lean`         | TÃ©moin Naimark : POVM uniforme `n=2, m=2`                                         | 65 |
| `QuantumFoundations/HistoriesKent/Defs.lean`     | `History`, `IsHistoryOf`, `chainOp`, `decFunctional`, `IsConsistent`, `histProb`   | 162 |
| `QuantumFoundations/HistoriesKent/Nonvacuity.lean` | TÃ©moin HistoriesKent : toute `Perspective`, famille Ã  un Ã©tage, est cohÃ©rente        | 85 |
| `QuantumFoundations/HistoriesKent/Basic.lean`    | K1 : `decFunctional_last_stage_orthogonal`, `histProb_additivity_two_stage`       | 121 |
| `QuantumFoundations/HistoriesKent/Witness.lean`  | K2 : tÃ©moin explicite de Kent en `H 3`, `S_consistent`                            | 490 |
| `QuantumFoundations/HistoriesKent/ContraryInferences.lean` | K3 : `inference`, thÃ©orÃ¨me final `contrary_inferences`                  | 162 |
| `QuantumFoundations/BranchesRiedel/Defs.lean` | R0 : rÃ©solutions Ã©tiquetÃ©es, branches et records redondants | 234 |
| `QuantumFoundations/BranchesRiedel/Nonvacuity.lean` | R0 : tÃ©moin GHZ Ã  trois records | 210 |
| `QuantumFoundations/BranchesRiedel/Basic.lean` | R1 : identitÃ©s gÃ©nÃ©rales des projecteurs de records | 133 |
| `QuantumFoundations/BranchesRiedel/TwoObs.lean` | R2 : deux observables enregistrÃ©s | 207 |
| `QuantumFoundations/BranchesRiedel/Induction.lean` | R3 : induction multi-observables | 559 |
| `QuantumFoundations/BranchesRiedel/Local.lean` | R4 : localitÃ© spatiale et comptage `PairCovers` | 469 |
| `QuantumFoundations/BranchesRiedel/BornBridge/RecordChoice.lean` | C14a : invariance de choix de record redondant | 203 |
| `QuantumFoundations/BranchesRiedel/BornBridge/ActiveBranches.lean` | C14b : indice de branche active | 76 |
| `QuantumFoundations/BranchesRiedel/BornBridge/BranchCells.lean` | C14b/c : cellules de branche, identitÃ© de projection | 134 |
| `QuantumFoundations/BranchesRiedel/BornBridge/BranchPerspective.lean` | C14d/e : support, cellule rÃ©siduelle, perspective formelle | 218 |
| `QuantumFoundations/BranchesRiedel/BornBridge/BornWeights.lean` | C14f : poids de Born des branches induites par records | 151 |
| `QuantumFoundations/BranchesRiedel/BornBridge/Synthesis.lean` | C14g : thÃ©orÃ¨me de synthÃ¨se abstrait | 92 |
| `QuantumFoundations/BranchesRiedel/BornBridge/LocalRecords.lean` | C14h : corollaire local multi-sites | 49 |
| `QuantumFoundations/BranchesRiedel/BornBridge/GeneratedBranches.lean` | C14i/j : modÃ¨le unitaire exact C11, frontiÃ¨re du modÃ¨le bruitÃ© | 199 |
| `QuantumFoundations/BranchesRiedel/BornBridge/Evolution.lean` | C14k : prÃ©servation des poids sous Ã©volution norm-prÃ©servante | 129 |
| `QuantumFoundations/BranchesRiedel/BornBridge/ConcreteModel.lean` | C14l : instance concrÃ¨te (poids 9/25, 16/25) | 86 |
| `QuantumFoundations/BranchesRiedel/BornBridge/Nonvacuity.lean` | C14 : tÃ©moins de non-vacuitÃ© | 101 |
| `QuantumFoundations/Complexity/Defs.lean` | C0 : portes et circuits 2-locaux, Ã©valuation et support | 129 |
| `QuantumFoundations/Complexity/Nonvacuity.lean` | C0/C6/C7/C8/C9/C10/C11/C12/C13 : tÃ©moins Ã©lÃ©mentaires et modÃ¨les concrets | 389 |
| `QuantumFoundations/Complexity/CircuitLocality.lean` | C1 : commutation d'un circuit avec une rÃ©gion disjointe | 45 |
| `QuantumFoundations/Complexity/RecordInterference.lean` | C1 : records non touchÃ©s et amplitude croisÃ©e nulle | 122 |
| `QuantumFoundations/Complexity/Counting.lean` | C2 : comptage gÃ©nÃ©rique des rÃ©gions disjointes touchÃ©es | 35 |
| `QuantumFoundations/Complexity/Main.lean` | C2 : borne principale `R â‰¤ 2 * C.length` | 63 |
| `QuantumFoundations/Complexity/ProxyDefs.lean` | C3 : proxies exacts de distinguabilitÃ© et dâ€™interfÃ©rence | 82 |
| `QuantumFoundations/Complexity/NormalizedBranches.lean` | C3 : normalisation des branches enregistrÃ©es non nulles | 83 |
| `QuantumFoundations/Complexity/ProxyCertificates.lean` | C3 : certificats relationnels et `ceilHalf` | 96 |
| `QuantumFoundations/Complexity/RecordInterferenceBound.lean` | C4 : borne dâ€™interfÃ©rence Ã  deux orientations | 96 |
| `QuantumFoundations/Complexity/RecordDistinguishability.lean` | C5 : lecture par phase flip exact | 114 |
| `QuantumFoundations/Complexity/BranchGap.lean` | C6 : certificat de gap sans soustraction | 50 |
| `QuantumFoundations/Complexity/MinComplexity.lean` | C6 : minima `WithTop â„•` et gap effectif | 180 |
| `QuantumFoundations/Complexity/CircuitConjugation.lean` | C7a : Ã©volution rÃ©versible et circuits sandwich | 157 |
| `QuantumFoundations/Complexity/CircuitInverse.lean` | C7a : inverses locaux de portes et circuits | 207 |
| `QuantumFoundations/Complexity/ProxyTransport.lean` | C7b : transport exact des Ã©lÃ©ments de matrice et proxies | 180 |
| `QuantumFoundations/Complexity/Persistence.lean` | C7c : transport des certificats relationnels | 111 |
| `QuantumFoundations/Complexity/RecordPersistence.lean` | C7d : bornes de persistance par records | 104 |
| `QuantumFoundations/Complexity/PersistenceMinima.lean` | C7e : transport `WithTop â„•` sans atteinte du minimum | 117 |
| `QuantumFoundations/Complexity/ApproxRecordDefs.lean` | C8a : record approximatif Ã  erreur agrÃ©gÃ©e | 78 |
| `QuantumFoundations/Complexity/ApproxRecordBasic.lean` | C8a : paire enregistrÃ©e et pont exact | 64 |
| `QuantumFoundations/Complexity/ApproxRecordInterference.lean` | C8b : borne nette dâ€™amplitude croisÃ©e hors support | 132 |
| `QuantumFoundations/Complexity/ApproxRecordInterferenceBound.lean` | C8c : borne dâ€™interfÃ©rence robuste et minima | 123 |
| `QuantumFoundations/Complexity/ApproxRecordDistinguishability.lean` | C8d : lecture de phase approximative | 203 |
| `QuantumFoundations/Complexity/ApproxBranchGap.lean` | C8e : gap proxy robuste et rÃ©gression exacte | 152 |
| `QuantumFoundations/Complexity/ApproxRecordPersistence.lean` | C8f : persistance conditionnelle du gap robuste | 160 |
| `QuantumFoundations/Complexity/Models/Repetition/States.lean` | C9a : branches computationnelles zÃ©ro/un et Ã©tat cohÃ©rent | 106 |
| `QuantumFoundations/Complexity/Models/Repetition/Records.lean` | C9b : rÃ©solutions mono-site et records exacts | 278 |
| `QuantumFoundations/Complexity/Models/Repetition/Readout.lean` | C9c : rÃ©flexion de lecture en une porte | 161 |
| `QuantumFoundations/Complexity/Models/Repetition/Distinguishability.lean` | C9d : complexitÃ© de distinguabilitÃ© exactement un | 82 |
| `QuantumFoundations/Complexity/Models/Repetition/Interference.lean` | C9e : circuit fini de flips de tous les bits | 205 |
| `QuantumFoundations/Complexity/Models/Repetition/Complexities.lean` | C9f : bornes linÃ©aires et gap concret | 105 |
| `QuantumFoundations/Complexity/Models/Repetition/Persistence.lean` | C9g : budget concret de persistance par circuit | 57 |
| `QuantumFoundations/Complexity/Models/NoisyRepetition/Profiles.lean` | C10a : profils de bruit `keep`/`leak` normalisÃ©s | 76 |
| `QuantumFoundations/Complexity/Models/NoisyRepetition/States.lean` | C10b : quatre configurations et branches bruitÃ©es | 215 |
| `QuantumFoundations/Complexity/Models/NoisyRepetition/Records.lean` | C10c : erreurs de record exactes et paire approximative | 182 |
| `QuantumFoundations/Complexity/Models/NoisyRepetition/Readout.lean` | C10d : lecture exacte Ã  site de record arbitraire | 59 |
| `QuantumFoundations/Complexity/Models/NoisyRepetition/Complexities.lean` | C10e : sÃ©paration de complexitÃ© robuste Ã  `Î´ = 1/2` | 89 |
| `QuantumFoundations/Complexity/Models/NoisyRepetition/Interference.lean` | C10f : tÃ©moin fini d'interfÃ©rence bruitÃ©e | 151 |
| `QuantumFoundations/Complexity/Models/NoisyRepetition/Persistence.lean` | C10g : gap robuste et persistance conditionnelle | 123 |
| `QuantumFoundations/Complexity/Models/NoisyRepetition/ConcreteNoise.lean` | C10h : profil rationnel concret `(99/101, 20/101)` | 95 |
| `QuantumFoundations/Complexity/Gates/ControlledBitFlip.lean` | C11a : portes de bit-flip contrÃ´lÃ©, 2-locales | 229 |
| `QuantumFoundations/Complexity/Gates/AmplitudeRotation.lean` | C11e : rotation unitaire de mÃ©lange d'amplitude sur `N` sites | 415 |
| `QuantumFoundations/Complexity/Models/MeasurementGeneration/IdealFanout.lean` | C11b : fanout unitaire d'Ã©tiquette en base de calcul | 219 |
| `QuantumFoundations/Complexity/Models/MeasurementGeneration/Amplitudes.lean` | C11c : profil d'amplitude source normalisÃ© | 89 |
| `QuantumFoundations/Complexity/Models/MeasurementGeneration/BranchWeights.lean` | C11d/h : projecteurs source et prÃ©servation des poids de branche | 231 |
| `QuantumFoundations/Complexity/Models/MeasurementGeneration/ProfilePreparation.lean` | C11e : porte de prÃ©paration canonique par profil | 95 |
| `QuantumFoundations/Complexity/Models/MeasurementGeneration/NoisyGeneration.lean` | C11f/g : prÃ©paration corrÃ©lÃ©e des records et gÃ©nÃ©ration bruitÃ©e complÃ¨te | 493 |
| `QuantumFoundations/Complexity/Models/MeasurementGeneration/GeneratedComplexity.lean` | C11i : connexion gÃ©nÃ©ration unitaire / persistance du gap | 70 |
| `QuantumFoundations/Complexity/Models/MeasurementGeneration/ConcreteGeneration.lean` | C11j : tÃ©moin concret de gÃ©nÃ©ration unitaire | 89 |
| `QuantumFoundations/Complexity/OperatorNorm/FiniteDimensional.lean` | C12a : vue en application linÃ©aire continue, dimension finie | 115 |
| `QuantumFoundations/Complexity/OperatorNorm/Approximation.lean` | C12b : approximation gÃ©nÃ©rique en norme d'opÃ©rateur | 106 |
| `QuantumFoundations/Complexity/OperatorNorm/RecordReadout.lean` | C12c : pont erreur d'opÃ©rateur / erreur ponctuelle de lecture | 113 |
| `QuantumFoundations/Complexity/OperatorNorm/RecordGap.lean` | C12d/e : distinguabilitÃ© et gap proxy en norme d'opÃ©rateur | 207 |
| `QuantumFoundations/Complexity/OperatorNorm/NoisyRepetition.lean` | C12f : instanciation bruitÃ©e concrÃ¨te, budget `1/20` | 165 |
| `QuantumFoundations/Complexity/OperatorNorm/GeneratedBranches.lean` | C12g : connexion Ã  la gÃ©nÃ©ration unitaire C11 | 87 |
| `QuantumFoundations/Complexity/OperatorNorm/Composition.lean` | C12h : lois de composition (facultatif, pour C13) | 84 |
| `QuantumFoundations/Complexity/OperatorNorm/Nonvacuity.lean` | C12 : non-vacuitÃ© de l'API budget d'erreur | 83 |
| `QuantumFoundations/Complexity/SimulatedEvolution/NormPreserving.lean` | C13a : opÃ©rateurs prÃ©servant la norme | 92 |
| `QuantumFoundations/Complexity/SimulatedEvolution/MatrixElementStability.lean` | C13b : bornes de perturbation d'Ã©lÃ©ment de matrice | 132 |
| `QuantumFoundations/Complexity/SimulatedEvolution/ThresholdTransport.lean` | C13c : transport de seuil sous erreur d'opÃ©rateur | 127 |
| `QuantumFoundations/Complexity/SimulatedEvolution/MarginCertificate.lean` | C13d : certificat de gap Ã  marge de seuil | 88 |
| `QuantumFoundations/Complexity/SimulatedEvolution/CircuitPersistence.lean` | C13e : persistance de la marge sous circuit exact | 50 |
| `QuantumFoundations/Complexity/SimulatedEvolution/SimulationCertificate.lean` | C13f : persistance sous Ã©volution simulÃ©e | 142 |
| `QuantumFoundations/Complexity/SimulatedEvolution/NoisyRepetition.lean` | C13g : instanciation Ã  marge pour le modÃ¨le bruitÃ© | 92 |
| `QuantumFoundations/Complexity/SimulatedEvolution/GeneratedBranches.lean` | C13h : connexion aux branches engendrÃ©es C11 | 77 |
| `QuantumFoundations/Complexity/SimulatedEvolution/ConcreteModel.lean` | C13i : instance rationnelle concrÃ¨te `Î´=1/2, Î¼=1/10, Îµ=1/20` | 108 |
| `QuantumFoundations/Complexity/SimulatedEvolution/TimeEvolution.lean` | C13j : coÃ»t de simulation dÃ©pendant du temps | 85 |
| `QuantumFoundations/Complexity/SimulatedEvolution/HamiltonianEvolution.lean` | C13k : Ã©volution certifiÃ©e par gÃ©nÃ©rateur auto-adjoint | 117 |
| `QuantumFoundations/Complexity/SimulatedEvolution/Nonvacuity.lean` | C13 : non-vacuitÃ© de l'API d'Ã©volution simulÃ©e | 114 |
| `QuantumFoundations.lean`                    | AgrÃ©gateur d'imports racine                                                       | 69 |
| **Total recalculÃ©**                          | **119 fichiers**                                                                  | **19598** |

Documentation : `AGENTS.md` (rÃ¨gles pour l'agent IA, Ã  lire au dÃ©marrage),
`MILESTONES.md` (suivi dÃ©taillÃ© jalon par jalon), `ARCHITECTURE_NOTES.md` (mÃ©moire
consolidÃ©e de tous les Ã©carts vs les plans initiaux).

## Jalons â€” Naimark

| Jalon | Contenu                                                    | Ã‰tat |
|-------|------------------------------------------------------------|------|
| N0    | Squelette (POVM, DilSpace, Nonvacuity)                     | âœ… |
| N1    | `sqrtOp` (racine carrÃ©e positive spectrale)                | âœ… |
| N2    | Briques de l'espace dilatÃ© (`singleL`/`coordL`/`dilProj`)  | âœ… |
| N3    | Dilation (`dilV`, `naimark`, `naimark_born`)               | âœ… |
| N4    | ClÃ´ture (README, `#print axioms`, tag)                     | âœ… |
| N5    | *Optionnel* : version unitaire/ancilla (tag `v2.0-naimark`)| âœ… |

## Jalons â€” Wigner

| Jalon | Contenu                                                                    | Ã‰tat |
|-------|----------------------------------------------------------------------------|------|
| W0    | Squelette (Defs, Nonvacuity, 24 sorry)                                     | âœ… |
| W1    | Kit scalaire (`Scalar.lean` : rigiditÃ©, `scalar_dichotomy`)                | âœ… |
| W2    | IdentitÃ© de Bessel (Ã©galitÃ©), images orthonormÃ©es                          | âœ… |
| W3    | Construction `V` (colinÃ©aritÃ©, eqs 11â€“12a)                                 | âœ… |
| W4    | CÅ“ur : dichotomie de `chi`, additivitÃ©/homogÃ©nÃ©itÃ© de `V`                  | âœ… |
| W5    | Assemblage (`U`, bijectivitÃ©, compatibilitÃ©, `wigner`)                     | âœ… |
| W6    | *Optionnel* : exclusivitÃ© (A) + unicitÃ© restreinte (B) (tag `v2.0-wigner`) | âœ… |

## Jalons â€” Uhlhorn

| Jalon | Contenu                                                                        | Ã‰tat |
|-------|--------------------------------------------------------------------------------|------|
| U0    | Reconnaissance + squelette (`Defs.lean`, 6 sorry)                              | âœ… |
| U1    | Corollaire (B) de Wigner en langage de projections (`wigner_projection_form`)  | âœ… |
| U2    | Lemme spectral Ã©lÃ©mentaire (`eq_projL_of_positive_le_one_trace_one_inner_one`) | âœ… |
| U3a   | Extension d'une fonction-cadre sur les droites en `ProjMeasure` complet        | âœ… |
| U3b   | Â« Gleason appliquÃ© deux fois Â» (`traceProd_preserved_of_sendsONBToONB`)        | âœ… |
| U4    | Assemblage direct de U1 et U3b                                                 | âœ… |
| U5    | RÃ©duction fini-dimensionnelle, thÃ©orÃ¨me final (tag `v1.0-uhlhorn`)             | âœ… |

## Jalons â€” BornRule

| Jalon | Contenu                                                                        | Ã‰tat |
|-------|----------------------------------------------------------------------------------|------|
| B1    | Scaffolding : `Perspective`, axiomes, `lemma4_noncontextual`, `refinePerspective` | âœ… |
| B2    | Pont vers Gleason : `g`, `IsFrameFunctionOnLines`, `exists_rho`                | âœ… |
| B3    | Pinning : `eq_projL_of_vanishes_on_orthogonal` (identification de `Ï` via U2)  | âœ… |
| B4    | Assemblage final, thÃ©orÃ¨me `grainCoherenceTheorem`                             | âœ… |
| Nonvacuity | `Eâ‚€ v` (rÃ¨gle de Born) habite simultanÃ©ment Grain+Norm+Pos+Null            | âœ… |

## Jalons â€” BornRule/EffectPerspectives (extension qubit/Busch)

Voir aussi `QuantumFoundations/BornRule/EffectPerspectives/README.md` pour le
dÃ©tail complet (portÃ©e, dÃ©rivations, non-revendications interprÃ©tatives).

| Jalon | Contenu | Ã‰tat |
|-------|---------|------|
| QB1 | `Effect` (sous-type de `Gleason.IsEffect`), `zeroEffect`/`oneEffect`/`complementEffect`/`projectionEffect` | âœ… |
| QB2 | `EffectPerspective` (POVM finie Ã©tiquetÃ©e), `binaryPerspective`/`splitPerspective`/`duplicateZeroPerspective` | âœ… |
| QB3 | `Refines` (raffinement par `parent` + reconstruction par fibre) ; `Refines.trans` diffÃ©rÃ© (documentÃ©, non bloquant) | âœ… |
| QB4 | `EstimationRule` (poids/positivitÃ©/normalisation/`grain`), hypothÃ¨se strictement plus large que `AxGrain` projectif | âœ… |
| QB5 | IndÃ©pendance contextuelle, poids nul/unitÃ© et additivitÃ© binaire **dÃ©rivÃ©s** de `grain` seul (jamais des axiomes) | âœ… |
| QB6 | Construction de `Gleason.EffectMeasure` ; application directe de `Gleason.busch`/`Gleason.busch_born_rule` | âœ… |
| QB7 | `ContextualNullSupport` (Ã©tat-relatif) ; pinning de repli `density_bornValue_eq_pure_of_null` | âœ… |
| QB8 | `projectionEffect_weight_eq_born` : poids de Born pour les effets de projection, en dimension quelconque | âœ… |
| QB9 | Corollaire explicite en dimension deux (qubit), sans passer par `Gleason.gleason` | âœ… |
| QB10 | Non-vacuitÃ© : `pureStateEstimationRule` (preuve directe, sans Busch), tÃ©moins qubit exacts | âœ… |
| QB11 | Pont vers Naimark : `EffectPerspective.toPOVM`, rÃ©alisation projective dilatÃ©e (`naimark`/`naimark_born`/`naimark_projective_form`), simple couche d'intÃ©gration | âœ… |

## Jalons â€” HistoriesKent

| Jalon | Contenu                                                                        | Ã‰tat |
|-------|---------------------------------------------------------------------------------|------|
| K0    | Squelette (`History`, `chainOp`, `decFunctional`, `IsConsistent`, `Nonvacuity`)  | âœ… |
| K1    | Lemmes gÃ©nÃ©raux : `decFunctional_last_stage_orthogonal`, `histProb_additivity_two_stage` | âœ… |
| K2    | TÃ©moin explicite de Kent en `H 3` (`Witness.lean`), `S_consistent`               | âœ… |
| K3    | `inference`, thÃ©orÃ¨me final `contrary_inferences` (tag `v1.0-histories`)         | âœ… |

## Jalons â€” Complexity

| Jalon | Contenu | Ã‰tat |
|---|---|---|
| C0 | Circuits finis de portes unitaires supportÃ©es sur au plus deux sites | âœ… |
| C1 | Commutation hors support et annulation de lâ€™amplitude croisÃ©e | âœ… |
| C2 | Comptage indÃ©pendant et borne exacte `R â‰¤ 2 * C.length` | âœ… |
| C3 | Proxies exacts, branches normalisÃ©es et certificats relationnels | âœ… |
| C4 | Borne dâ€™interfÃ©rence `ceilHalf R` issue des records redondants | âœ… |
| C5 | Borne de distinguabilitÃ© issue dâ€™un phase flip de record explicite | âœ… |
| C6 | Gap sans soustraction et minima dans `WithTop â„•` | âœ… |
| C7 | Transport exact et persistance conditionnelle sous circuit rÃ©versible fini | âœ… |
| C8 | Records approximatifs, bornes quantitatives et persistance conditionnelle | âœ… |
| C9 | ModÃ¨le explicite de rÃ©pÃ©tition, circuits concrets et gap linÃ©aire | âœ… |
| C10 | ModÃ¨le explicite de rÃ©pÃ©tition **bruitÃ©e** (`leak â‰  0`), sÃ©paration robuste | âœ… |
| C11 | GÃ©nÃ©ration **unitaire** des branches source-record par circuit local explicite | âœ… |
| C12 | Pont fini-dimensionnel en **norme d'opÃ©rateur** vers les hypothÃ¨ses de lecture ponctuelles C8â€“C11 | âœ… |
| C13 | Persistance robuste du gap sous **Ã©volution simulÃ©e** norm-preservante, avec marge de seuil | âœ… |
| C14 | Pont **records redondants â†’ poids de Born** : dÃ©composition en branches de Riedel + ThÃ©orÃ¨me de CohÃ©rence de Grain | âœ… |
| C15 | UnicitÃ© `W = c â€–P_R Î¨â€–Â²` sur les situations de record admissibles sous stabilitÃ©, Ã©quivalence interne et saturation binaire | âœ… |
| C17 | PremiÃ¨re stabilitÃ© quantitative des poids C15 sous perturbation des composantes projetÃ©es, avec bornes ponctuelle, `LÂ¹` et uniforme | âœ… |
| C17b | Ponts de stabilitÃ© vers les secteurs fixes, la norme dâ€™opÃ©rateur C12, la simulation C13 et les poids de branches C14 explicitement appariÃ©es | âœ… |

## ThÃ©orÃ¨mes principaux â€” table de rÃ©fÃ©rence

| ThÃ©orÃ¨me | Ã‰noncÃ© informel | RÃ©fÃ©rence | Fichier (lignes) | Statut | Tag |
|---|---|---|---:|---|---|
| `naimark` | Toute POVM finie se dilate en une mesure projective sous une isomÃ©trie | Watrous Thm 2.42 | `Naimark/Main.lean` (157) | 0 sorry, 0 axiome | `v2.0-naimark` |
| `naimark_born` | La formule de Born est prÃ©servÃ©e par cette dilation | Watrous Thm 2.42 | `Naimark/Main.lean` (157) | 0 sorry, 0 axiome | `v2.0-naimark` |
| `exists_unitary_extension` / `naimark_projective_form` | L'isomÃ©trie de dilatation s'Ã©tend en un unitaire global (forme ancilla) | Paris Â§3.2 Thm 4 / Watrous Cor. 2.43 | `Naimark/Unitary.lean` (210) | 0 sorry, 0 axiome | `v2.0-naimark` |
| `wigner` | Toute transformation prÃ©servant `\|âŸ¨Ï†\|ÏˆâŸ©\|Â²` est induite par un unitaire ou un antiunitaire, sans hypothÃ¨se de bijectivitÃ© | Bargmann 1964 Â§1â€“Â§5 | `Wigner/Main.lean` (399) | 0 sorry, 0 axiome | `v1.0-wigner` |
| `exclusivity` | Un mÃªme `T` ne peut Ãªtre compatible Ã  la fois avec une Ã©quivalence unitaire et une antiunitaire (`n â‰¥ 2`) | Bargmann 1964 Â§1.5 | `Wigner/Uniqueness.lean` (439) | 0 sorry, 0 axiome | `v2.0-wigner` |
| `U_alt_eq_smul` | `U` est unique Ã  phase globale prÃ¨s relativement au choix du reprÃ©sentant de `eImg` (version restreinte) | Bargmann 1964 Â§6 (restreint) | `Wigner/Uniqueness.lean` (439) | 0 sorry, 0 axiome | `v2.0-wigner` |
| `uhlhorn_finite_dim` | En dimension `n â‰¥ 3`, prÃ©server l'orthogonalitÃ© dans un seul sens (ni injectivitÃ© ni surjectivitÃ©) suffit Ã  Ãªtre une symÃ©trie de Wigner | Å emrl 2021, arXiv:2106.06182, Cor. 1.2 | `Uhlhorn/Assembly.lean` (111) | 0 sorry, 0 axiome | `v1.0-uhlhorn` |
| `grainCoherenceTheorem` | Sous (Grain)+(Norm)+(Pos)+(Null), la valeur d'une rÃ¨gle d'estimation sur une cellule est la rÃ¨gle de Born (`âˆ‘áµ¢â€–âŸ¨v,fáµ¢âŸ©â€–Â²`) | Gleason 1957 (thÃ©orÃ¨me sous-jacent) | `BornRule/Assembly.lean` (215) | 0 sorry, 0 axiome | `v2.0-bornrule` |
| `grainCoherenceTheorem_projector` | Version en notation projecteur du thÃ©orÃ¨me prÃ©cÃ©dent (`Est D c = â€–projL c vâ€–Â²`), sans contenu mathÃ©matique indÃ©pendant supplÃ©mentaire | Corollaire de `grainCoherenceTheorem` | `BornRule/Assembly.lean` | 0 sorry, 0 axiome | â€” |
| `EffectPerspectives.projectionEffect_weight_eq_born` | Sous non-vacuitÃ© d'effets et support nul Ã©tat-relatif, le poids d'un effet de projection Ã©gale le poids de Born `â€–A.starProjection Ïˆâ€–Â²`, en dimension quelconque `n â‰¥ 1` | Busch 2003, PRL 91, 120403 | `BornRule/EffectPerspectives/Main.lean` | 0 sorry, 0 axiome | â€” |
| `EffectPerspectives.qubit_projectionEffect_weight_eq_born` | Corollaire explicite en dimension deux (qubit) du thÃ©orÃ¨me prÃ©cÃ©dent, sans invoquer `Gleason.gleason` | Busch 2003 (spÃ©cialisÃ© `n = 2`) | `BornRule/EffectPerspectives/Qubit.lean` | 0 sorry, 0 axiome | â€” |
| `contrary_inferences` | Deux ensembles cohÃ©rents d'histoires partageant prÃ©paration et post-sÃ©lection peuvent impliquer avec certitude deux propositions orthogonales | Kent 1997, PRL 78, 2874, arXiv:gr-qc/9604012 | `HistoriesKent/ContraryInferences.lean` (162) | 0 sorry, 0 axiome | `v1.0-histories` |
| `regions_card_le_two_mul_circuit_length_of_cross_amplitude_ne_zero` | `R` records exacts disjoints et une amplitude croisÃ©e non nulle imposent `R â‰¤ 2 * C.length` | Comptage fini + records de Riedel | `Complexity/Main.lean` (63) | 0 sorry, 0 axiome | â€” |
| `redundant_records_give_interference_lower_bound` | Tout circuit satisfaisant le proxy exact a longueur au moins `ceilHalf R` | Proxy exact + C2 dans les deux orientations | `Complexity/RecordInterferenceBound.lean` (96) | 0 sorry, 0 axiome | â€” |
| `record_phase_flip_gives_distinguishability_upper_bound` | Un circuit implÃ©mentant `2 P_j - I` distingue les branches normalisÃ©es Ã  seuil `Î´ â‰¤ 1` | Lecture exacte dâ€™un record | `Complexity/RecordDistinguishability.lean` (114) | 0 sorry, 0 axiome | â€” |
| `redundant_records_give_proxy_gap_certificate` | `D.length + g â‰¤ ceilHalf R` certifie un gap proxy dâ€™au moins `g` | Composition des certificats C4/C5 | `Complexity/BranchGap.lean` (50) | 0 sorry, 0 axiome | â€” |
| `redundant_records_complexity_gap` | Le mÃªme gap vaut pour les minima exacts dans `WithTop â„•` | Infimum des longueurs de circuits | `Complexity/MinComplexity.lean` (180) | 0 sorry, 0 axiome | â€” |
| `redundant_records_gap_persists_under_reversible_evolution` | Le gap de records persiste sous `D.length + 2 * overhead + g â‰¤ ceilHalf R` | Transport exact par paire de circuits inverses | `Complexity/RecordPersistence.lean` (104) | 0 sorry, 0 axiome | â€” |
| `redundant_records_gap_persists_under_circuit_evolution` | Pour l'inverse canonique, le budget devient `D.length + 4 * E.length + g â‰¤ ceilHalf R` | Inverse local canonique + thÃ©orÃ¨me prÃ©cÃ©dent | `Complexity/RecordPersistence.lean` (104) | 0 sorry, 0 axiome | â€” |
| `norm_cross_amplitude_le_of_untouched_approx_record` | Une rÃ©gion approximativement enregistrÃ©e et non touchÃ©e borne lâ€™amplitude croisÃ©e par `Î·` | DÃ©composition projecteur/dÃ©faut + Cauchyâ€“Schwarz | `Complexity/ApproxRecordInterference.lean` (132) | 0 sorry, 0 axiome | â€” |
| `approximate_records_give_interference_lower_bound` | `Î·i + Î·j < 2Î´` impose une longueur au moins `ceilHalf R` | Borne robuste + comptage C2 | `Complexity/ApproxRecordInterferenceBound.lean` (123) | 0 sorry, 0 axiome | â€” |
| `approx_record_phase_flip_gives_upper_bound` | `2Î´ + 2Î·j + Î¾ â‰¤ 2` fournit le tÃ©moin de distinguabilitÃ© | Lecture de phase approximative explicite | `Complexity/ApproxRecordDistinguishability.lean` (203) | 0 sorry, 0 axiome | â€” |
| `approximate_records_give_proxy_gap_certificate` | Les deux seuils robustes et `D.length + g â‰¤ ceilHalf R` certifient le gap | Composition C8c/C8d | `Complexity/ApproxBranchGap.lean` (152) | 0 sorry, 0 axiome | â€” |
| `approximate_records_gap_persists_under_circuit_evolution` | Le gap robuste persiste sous `D.length + 4 * E.length + g â‰¤ ceilHalf R` | Transport exact C7 du certificat C8 | `Complexity/ApproxRecordPersistence.lean` (160) | 0 sorry, 0 axiome | â€” |
| `repetition_distinguishabilityComplexity` | Le modÃ¨le explicite a `C_D = 1` | RÃ©flexion mono-site + exclusion du circuit vide | `Models/Repetition/Distinguishability.lean` (82) | 0 sorry, 0 axiome | â€” |
| `repetition_interferenceComplexity_bounds` | `ceilHalf R â‰¤ C_I â‰¤ R` et donc `C_I â‰  âŠ¤` | Records singletons + circuit de `R` flips | `Models/Repetition/Complexities.lean` (105) | 0 sorry, 0 axiome | â€” |
| `repetition_has_proxy_gap` | `1 + g â‰¤ ceilHalf R` certifie le gap explicite | Instanciation directe de C4â€“C6 | `Models/Repetition/Complexities.lean` (105) | 0 sorry, 0 axiome | â€” |
| `repetition_gap_persists_under_circuit` | `1 + 4 * E.length + g â‰¤ ceilHalf R` conserve le gap | Instanciation directe de C7 | `Models/Repetition/Persistence.lean` (57) | 0 sorry, 0 axiome | â€” |
| `noisy_repetition_approxRecordedPairOn` | Les records bruitÃ©s habitent `ApproxRecordedPairOn` avec erreur agrÃ©gÃ©e exacte `2 * â€–leakâ€–` | Actions exactes des projecteurs sur les quatre configurations | `Models/NoisyRepetition/Records.lean` (182) | 0 sorry, 0 axiome | â€” |
| `noisy_repetition_distinguishabilityComplexity` | Sous bruit robuste (`4â€–leakâ€– < 1`), `C_D = 1` Ã  `Î´ = 1/2` | Lecture exacte Ã  un site + seuil C8d | `Models/NoisyRepetition/Complexities.lean` (89) | 0 sorry, 0 axiome | â€” |
| `noisy_repetition_interference_bounds` | Sous bruit robuste, `ceilHalf R â‰¤ C_I â‰¤ R + 1` Ã  `Î´ = 1/2` | Records approximatifs C8c + tÃ©moin flip-tous-les-bits | `Models/NoisyRepetition/Interference.lean` (151) | 0 sorry, 0 axiome | â€” |
| `noisy_repetition_has_proxy_gap` | `1 + g â‰¤ ceilHalf R` certifie le gap robuste | Instanciation directe de C8e | `Models/NoisyRepetition/Persistence.lean` (123) | 0 sorry, 0 axiome | â€” |
| `noisy_repetition_gap_persists_under_circuit` | `1 + 4 * E.length + g â‰¤ ceilHalf R` conserve le gap robuste | Instanciation directe de C8f | `Models/NoisyRepetition/Persistence.lean` (123) | 0 sorry, 0 axiome | â€” |
| `rationalNoiseProfile_isRobust` | Le profil rationnel `(99/101, 20/101)` est robuste (`80/101 < 1`) | Triplet pythagoricien `99Â² + 20Â² = 101Â²` | `Models/NoisyRepetition/ConcreteNoise.lean` (95) | 0 sorry, 0 axiome | â€” |

Statut Â« 0 axiome Â» signifie : dÃ©pend uniquement de
`[propext, Classical.choice, Quot.sound]` (vÃ©rifiÃ© par `#print axioms` sur
chacun des thÃ©orÃ¨mes principaux, voir section prÃ©cÃ©dente et les sorties
`#print axioms` conservÃ©es dans les fichiers dâ€™assemblage).

## DÃ©pendances

Ce dÃ©pÃ´t Ã©pingle deux dÃ©pendances Lake sur des rÃ©visions fixes et rÃ©solvables
(`lakefile.toml`/`lake-manifest.json`), jamais sur une branche flottante :

- [`gleason-theorem-lean`](https://github.com/Bobart0/gleason-theorem-lean),
  `rev = "v1.0-gleason"` (rÃ©solu en `876aa7390b5d831cd81415d55493a1c0c3bae31e`,
  rÃ©vision fixe inchangÃ©e depuis Naimark). **Usage Ã©tendu depuis Uhlhorn, repris
  par BornRule** (contrairement Ã  Naimark, qui ne rÃ©utilise que
  `Gleason.IsPositiveOp`, un simple `Prop`) : Uhlhorn ET BornRule invoquent
  `Gleason.gleason` lui-mÃªme â€” le thÃ©orÃ¨me de Gleason complet, pas seulement
  une dÃ©finition â€” ainsi qu'une partie de sa machinerie interne
  (`Gleason.positive_inner_self_eq_zero`, `Gleason.cframe_sum_invariant`,
  `Gleason.ProjMeasure`/`bornValue`/`projL`,
  `Gleason.exists_orthonormalBasis_extension_complex`,
  `Submodule.starProjection_isSymmetric`/`re_inner_starProjection_nonneg`).
  C'est dÃ©libÃ©rÃ© et attendu : Uhlhorn (Corollaire 1.2 de Å emrl) et BornRule
  (`grainCoherenceTheorem`) **composent** Gleason (et, pour Uhlhorn, Wigner)
  par construction â€” ce ne sont pas des rÃ©sultats autonomes, voir les sections
  dÃ©diÃ©es plus haut. MalgrÃ© cette dÃ©pendance substantiellement plus large,
  **aucune fuite d'axiome par transitivitÃ©** : confirmÃ© directement par
  `#print axioms` sur chaque thÃ©orÃ¨me du prÃ©sent dÃ©pÃ´t, y compris
  `uhlhorn_finite_dim` (dÃ©pend Ã  la fois de `Gleason.gleason` externe et de
  `QuantumFoundations.Wigner.wigner` interne) et `grainCoherenceTheorem`
  (dÃ©pend Ã  la fois de `Gleason.gleason` externe et de l'infrastructure
  Uhlhorn interne U2/U3a) â€” dans les deux cas sans faire apparaÃ®tre un axiome
  supplÃ©mentaire. BornRule rÃ©utilise en outre directement, depuis Uhlhorn,
  `eq_projL_of_positive_le_one_trace_one_inner_one` (U2),
  `exists_projMeasure_of_frameFunctionOnLines` (U3a) et
  `isEffect_of_isDensityOperator` (relocalisÃ© de U3b vers `Uhlhorn/Defs.lean`
  lors de B3) â€” aucun contenu Gleason/Uhlhorn n'est reprouvÃ©. **HistoriesKent**
  n'invoque `Gleason.gleason` ni `Gleason.projL`/`Submodule.starProjection`
  directement, mais en hÃ©rite par transitivitÃ© via `BornRule.Perspective`
  (chaÃ®ne Ã  trois niveaux HistoriesKent â†’ BornRule â†’ Uhlhorn/Gleason externe) â€”
  mÃªme absence de fuite d'axiome, confirmÃ©e sur `contrary_inferences` et les
  35 autres dÃ©clarations publiques du bloc. **`BornRule/EffectPerspectives`**
  (extension qubit/Busch) rÃ©utilise, dans la mÃªme rÃ©vision Ã©pinglÃ©e dÃ©jÃ  en
  place, `Gleason.Busch.Effects`/`Gleason.Busch.Main` : `Gleason.IsEffect`,
  `Gleason.EffectMeasure`, et surtout `Gleason.busch`/`Gleason.busch_born_rule`
  (le thÃ©orÃ¨me de Busch complet, appliquÃ© directement en un seul point,
  `EffectMeasure.lean`, jamais reprouvÃ©). Contrairement Ã  `Gleason.gleason`
  (dimension `â‰¥ 3`), Busch s'applique dÃ¨s la dimension `1`, ce qui permet
  d'atteindre le qubit (`n = 2`) sans emprunter la voie projective. Aucune
  dÃ©claration de dÃ©pendance n'a Ã©tÃ© ajoutÃ©e ou modifiÃ©e : toutes ces
  dÃ©clarations existaient dÃ©jÃ  dans la rÃ©vision Ã©pinglÃ©e.
- `mathlib`, `rev = "8bba4200986270d3b30be2bb2f8840af47a7854f"`.

`./setup.sh` (`lake exe cache get` puis `lake build`) reproduit l'Ã©tat exact
du dÃ©pÃ´t sur un clone frais, sans intervention manuelle â€” testÃ© lors de
chaque passe de clÃ´ture (`lake clean` + `lake exe cache get` + `lake build`),
la plus rÃ©cente incluant `HistoriesKent` (2026-07-16).

## RÃ¨gles

Aucun `axiom`, aucun `native_decide` (CI bloquante, `scripts/guard.sh`). Toute nouvelle
structure d'hypothÃ¨ses reÃ§oit un habitant concret dans `Nonvacuity.lean`, dans le mÃªme
commit. Un `sorry` honnÃªte plutÃ´t qu'un Ã©noncÃ© affaibli en silence â€” voir `AGENTS.md`
pour l'ensemble des rÃ¨gles.

## Licence

[Apache License 2.0](LICENSE).

---

## English translation

# quantum-foundations-lean â€” Lean 4 formalizations: Naimark, Wigner, Uhlhorn, BornRule, HistoriesKent, BranchesRiedel, and Complexity

Status: Naimark v2 COMPLETE (v2.0-naimark, 2026-07-11), Wigner COMPLETE
with optional uniqueness/exclusivity (v2.0-wigner, 2026-07-13), Uhlhorn
COMPLETE (v1.0-uhlhorn, 2026-07-14), BornRule COMPLETE with Nonvacuity
(v2.0-bornrule, 2026-07-15), AND HistoriesKent COMPLETE
(v1.0-histories, 2026-07-16), plus the BranchesRiedel and Complexity C0â€“C13
blocks, and now the **C14 records-to-Born-weight bridge**. Seven mechanized
blocks,
without axioms in the sense of the project rules, apart from the three
standard Lean kernel axioms described below, in finite dimension over â„‚.

By the numbers (recomputed on 2026-07-23, project files excluding scratch):
119 `.lean` files, 19,598 lines, 663 public declarations (`theorem`), 0
`sorry`, and 0 project-specific axioms. The Complexity block contains 70
files and 9,490 lines, of which 12 files and 1,224 lines are the C13
simulated-evolution persistence milestone. The BranchesRiedel block
contains 17 files and 3,250 lines, of which 11 files and 1,438 lines are
the new `BornBridge/` subdirectory (the C14 milestone, bridging Riedel's
branch decomposition to the Born weight). The
main theorems of the Complexity and BornBridge blocks were checked with
`#print axioms` and depend on exactly `[propext, Classical.choice,
Quot.sound]`, the standard Lean/Mathlib trio.

**Current module names:** the Riedel block is
`QuantumFoundations.BranchesRiedel`, and Kent's contrary-inferences block is
`QuantumFoundations.HistoriesKent`. The former
`QuantumFoundations.Branches` and `QuantumFoundations.Histories` module paths
and namespaces are no longer exposed.

The Naimark dilation theorem for finite POVMs
(Watrous, The Theory of Quantum Information, Theorem 2.42): every POVM
E : Fin m â†’ (H n â†’â‚—[â„‚] H n) is realized as a projection-valued measure
(dilProj) under an isometry dilV, with preservation of the Born formula.

Wigner's theorem (Bargmann 1964, Note on Wigner's Theorem on Symmetry
Operations): every transformation on pure states preserving transition
probabilities |âŸ¨Ï†|ÏˆâŸ©|Â² is induced by a unitary or antiunitary operatorâ€”
formulation (A), without a bijectivity hypothesis on the initial
transformation (strictly stronger than Simonâ€“Mukundaâ€“Chaturvediâ€“Srinivasan
2008, Eq. 2.8, which assumes it). It is supplemented in optional W6 by
unitary/antiunitary exclusivity and uniqueness up to a global phase
in a restricted form, following Bargmann Â§1.5 and Â§6.

Å emrl's Corollary 1.2 (Å emrl 2021, Wigner symmetries and Gleason's
theorem, arXiv:2106.06182): in finite dimension n â‰¥ 3, every map on
rank-one projections that preserves orthogonality in one direction only
(with neither injectivity nor surjectivity assumed) is automatically a Wigner
symmetry. Unlike Naimark and Wigner, this is NOT a self-contained result: it
composes Gleason's theorem (gleason-theorem-lean, pinned external
dependency) with Wigner's theorem (the internal block above). See the
dedicated section below for details of this dual dependency and its axiom
audit.

The Grain Coherence Theorem (with Gleason 1957, Measures on the closed
subspaces of a Hilbert space, as the underlying theorem): for a
â€œperspective,â€ an orthogonal partition of H n into cells, and an estimation
rule satisfying four purely combinatorial axioms (Grain, Norm, Pos, Null),
the rule's value on every cell is EXACTLY the Born rule
(âˆ‘áµ¢ â€–âŸ¨v,fáµ¢âŸ©â€–Â² over an orthonormal basis of the cell), without ever assuming
a priori that the rule has trace form. Like Uhlhorn, this result composes
an internal block (Uhlhorn infrastructure U2 and U3a) with an external
dependency (Gleason.gleason, imported as an actual theorem rather than as
an axiom). See the dedicated section below.

The contrary-inferences theorem (Kent 1997, Quasiclassical Dynamics in a
Closed Quantum System, PRL 78, 2874, arXiv:gr-qc/9604012), in the
finite-dimensional consistent-histories framework: two consistent sets of
histories can share the same preparation and postselection while each
implying with CERTAINTY a different proposition, the two propositions being
mutually orthogonal. A temporal stage of a history set directly reuses
BornRule.Perspective, with no redefinition. As Uhlhorn and BornRule already
do for other components, HistoriesKent composes the repository's internal
infrastructure (BornRule â†’ Uhlhorn/Gleason) rather than starting over.
The generic profusion theorem of Dowkerâ€“Kent (1996), which would show that the
witness is not an isolated contrary-inference example, is explicitly outside
the scope of this block.

This repository relies on
gleason-theorem-lean
(tag v1.0-gleason). Naimark reuses only IsPositiveOp
(Gleason.Busch.Effects); Uhlhorn and BornRule, by contrast, invoke
Gleason.gleason itself as well as part of its internal machinery. HistoriesKent
does not invoke Gleason.gleason directly but inherits it transitively
through BornRule.Perspective/projL. See â€œDependenciesâ€ below for details
and verification that no additional axioms leak through the dependency
chain.

## Statements

lean
structure POVM (n m : â„•) where
 E : Fin m â†’ (H n â†’â‚—[â„‚] H n)
 pos : âˆ€ i, IsPositiveOp (E i)
 sum_eq_one : âˆ‘ i, E i = 1

theorem naimark (P : POVM n m) :
 âˆƒ V : H n â†’â‚—[â„‚] DilSpace n m, LinearMap.adjoint V âˆ˜â‚— V = LinearMap.id âˆ§
 âˆ€ i, LinearMap.adjoint V âˆ˜â‚— dilProj n m i âˆ˜â‚— V = P.E i

theorem naimark_born (P : POVM n m) (i : Fin m) (x : H n) :
 âŸªx, P.E i xâŸ«_â„‚ = âŸªdilV P x, dilProj n m i (dilV P x)âŸ«_â„‚


DilSpace n m := EuclideanSpace â„‚ (Fin m Ã— Fin n), and dilProj i is the
orthogonal projection onto the ith block.

N5 (optional, closed): dilV extends to a genuine unitary on
DilSpace n m, not merely an isometry, for every fixed ancilla index iâ‚€
(Watrous Cor. 2.43 / Paris Â§3.2 Thm 4):

lean
theorem exists_unitary_extension (P : POVM n m) (iâ‚€ : Fin m) :
 âˆƒ U : DilSpace n m â‰ƒâ‚—áµ¢[â„‚] DilSpace n m, U.toLinearMap âˆ˜â‚— singleL n m iâ‚€ = dilV P

theorem naimark_projective_form (P : POVM n m) (iâ‚€ : Fin m) :
 âˆƒ U : DilSpace n m â‰ƒâ‚—áµ¢[â„‚] DilSpace n m, âˆ€ (i : Fin m) (x : H n),
 âŸªx, P.E i xâŸ«_â„‚ = âŸªU (singleL n m iâ‚€ x), dilProj n m i (U (singleL n m iâ‚€ x))âŸ«_â„‚


## Documented deviation from Watrous

Watrous dilates in a tensor product X âŠ— â„‚^Î£. We dilate in the
Hilbert direct sum K := âŠ•_{i<m} H n, which is canonically isomorphic
(the Mathlib API for PiLp/EuclideanSpace was more mature at the time than
the Hilbert tensor-product API). Correspondence:
1_X âŠ— E_{a,a} becomes dilProj a; âˆšÎ¼(a) âŠ— e_a becomes
singleL a âˆ˜â‚— sqrtOp (E a). The mathematical content (isometry + Born formula) is identical; only the concrete realization of the dilation
space differs.

DilSpace n m := EuclideanSpace â„‚ (Fin m Ã— Fin n) was selected in step 0,
milestone N0, over PiLp 2 (fun _ : Fin m => H n) at equal proof-engineering
cost, because of its single flat index. See MILESTONES.md for details of the
two tested routes.

## Wigner's theorem

lean
def IsWignerMap (T : H n â†’ H n) : Prop :=
 âˆ€ x y : H n, â€–xâ€– = 1 â†’ â€–yâ€– = 1 â†’ â€–âŸªT x, T yâŸ«_â„‚â€– = â€–âŸªx, yâŸ«_â„‚â€–

theorem wigner (n : â„•) (T : H n â†’ H n) (hT : IsWignerMap T) :
 (âˆƒ U' : H n â‰ƒâ‚—áµ¢[â„‚] H n, âˆ€ x, â€–xâ€– = 1 â†’ âˆƒ c : â„‚, â€–câ€– = 1 âˆ§ T x = c â€¢ U' x)
 âˆ¨ (âˆƒ U' : H n â‰ƒâ‚›â‚—áµ¢[starRingEnd â„‚] H n, âˆ€ x, â€–xâ€– = 1 â†’ âˆƒ c : â„‚, â€–câ€– = 1 âˆ§ T x = c â€¢ U' x)


There is no bijectivity hypothesis on T: in finite dimension, the
constructed isometry U' is automatically bijective (U_bijective), and
injectivity at the ray level follows from hT alone. Mathematical blueprint:
Bargmann 1964, Â§1â€“Â§5, followed almost verbatim; Simonâ€“Mukundaâ€“Chaturvediâ€“
Srinivasan 2008 is used only as a cross-check and rejected as the primary
blueprint because of its trigonometric/Real.Angle approach.

Construction (Bargmann Â§3â€“Â§5): first Vâ€”definitional collinearity on
ð’« := eâŠ¥, W3â€”then Ï‡â€”the id/conj dichotomy established independently
on EACH direction and then globalized without an orthogonal-frame
hypothesis, W4â€”and finally
U := Ï‡âŸ¨e,Â·âŸ©â€¢e' + V(Â· âˆ’ âŸ¨e,Â·âŸ©â€¢e), extending V/Ï‡ to the whole space,
W5. No coordinates, no extension of an orthonormal basis, and no Submodule
for ð’«, which is represented by the simple Prop InPerp.

Documented deviations from the initial plan (see MILESTONES.md, sections
W3â€“W5, for full details):
- W3 (V_colinear): the initial skeleton asserted â€–Î´â€– = 1 for the
 collinearity coefficientâ€”FALSE in general, as refuted by T = id; corrected
 to â€–Î´â€– = â€–zâ€–.
- W4 (chi_eq_chidir): Bargmann's argument in Â§4.3â€“Â§4.5
 (w = fâ‚+fâ‚‚, orthogonal case only) is insufficient when n â‰¥ 3 and the
 second vector is neither collinear nor orthogonal to refVec. This was
 resolved by reduction to a single comparison point (i, where id and
 conj differ) rather than by proving the full functional identity.
- W5 (U_bijective): there is no direct Mathlib lemma for semilinear
 bijectivity in the antiunitary branch. The result was obtained by
 restriction to the real scalars (starRingEnd â„‚ is â„-linear), where
 LinearMap.injective_iff_surjective applies unchanged.

See ARCHITECTURE_NOTES.md for the consolidated list of all documented
deviations from N0â€“N5 and W0â€“W6.

## W6 (optional) â€” Exclusivity and uniqueness (Bargmann Â§1.5, restricted Â§6)

lean
def Delta (a b c : H n) : â„‚ := âŸªa, bâŸ«_â„‚ * âŸªb, câŸ«_â„‚ * âŸªc, aâŸ«_â„‚

theorem exclusivity (hT : IsWignerMap T) (hn : 2 â‰¤ n) :
 Â¬ ((âˆƒ U : H n â‰ƒâ‚—áµ¢[â„‚] H n, âˆ€ x, â€–xâ€– = 1 â†’ âˆƒ c : â„‚, â€–câ€– = 1 âˆ§ T x = c â€¢ U x)
 âˆ§ (âˆƒ U' : H n â‰ƒâ‚›â‚—áµ¢[starRingEnd â„‚] H n, âˆ€ x, â€–xâ€– = 1 â†’ âˆƒ c : â„‚, â€–câ€– = 1 âˆ§ T x = c â€¢ U' x))

theorem U_alt_eq_smul (T : H n â†’ H n) (lam : â„‚) (hlam : â€–lamâ€– = 1) (a : H n) :
 Up T (lam â€¢ eImg T) a = lam â€¢ U T a


**(A) Exclusivity** (Bargmann Â§1.5): the same T can never be compatible with
both a unitary and an antiunitary equivalence when n â‰¥ 2. The proof uses an
explicit witness: the triple
e, eâ‚‚ := (eâˆ’refVec)/âˆš2,
eâ‚ƒ := (e+refVec(1âˆ’i))/âˆš3 gives
Delta(e,eâ‚‚,eâ‚ƒ) = i/6 âˆ‰ â„
(bargmann_delta_witness, confirmed exactly by Lean). But Delta is
invariant in the unitary branch and conjugated in the antiunitary branch
(delta_transform_lin/delta_transform_conj), which would force
i/6 = -i/6.

**(B) Uniqueness up to a global phaseâ€”RESTRICTED version**: reconstructing
U after replacing, in the formulas of Defs.lean, the unit representative
eImg T := T(e n) with another unit representative Î» â€¢ eImg T of the same
class (â€–Î»â€– = 1) produces a new U exactly equal to Î» â€¢ U (U_alt_eq_smul). This is
strictly weaker than the full Bargmann Â§6 Theorem 2, which would cover a
completely arbitrary U', not merely freedom in the representative of
eImg, but it is sufficient for the repository's actual use case.
Defs.lean is unchanged: the parameterized reconstruction
(Vp, chidirp, chip, Up) is local to Uniqueness.lean and is connected
to V/chi/U by bridge lemmas proved by rfl.

## Å emrl's Corollary 1.2 (Uhlhorn)

lean
def PreservesOrthogonality (Ï† : Proj1 n â†’ Proj1 n) : Prop :=
 âˆ€ P Q : Proj1 n, (P : Submodule â„‚ (H n)) âŸ‚ (Q : Submodule â„‚ (H n)) â†’
 (Ï† P : Submodule â„‚ (H n)) âŸ‚ (Ï† Q : Submodule â„‚ (H n))

theorem uhlhorn_finite_dim (hn : 3 â‰¤ n) (Ï† : Proj1 n â†’ Proj1 n)
 (hÏ† : PreservesOrthogonality Ï†) : IsWignerSymmetryProj Ï†


Proj1 n := {A : Submodule â„‚ (H n) // Module.finrank â„‚ A = 1} represents a
rank-one projection, with no dedicated rankOne wrapper, in accordance with
gleason-theorem-lean. Every map on rank-one projections that preserves
orthogonality in one direction only
(PQ = 0 âŸ¹ Ï†(P)Ï†(Q) = 0, with neither injectivity nor surjectivity assumed)
is, in finite dimension n â‰¥ 3, a Wigner symmetryâ€”Å emrl 2021,
Wigner symmetries and Gleason's theorem (arXiv:2106.06182),
Corollary 1.2.

This result COMPOSES two theorems rather than introducing self-contained
mathematical content: the core proof applies Gleason.gleason, an external
dependency, TWICEâ€”first to construct, from a test density D and the
preservation hypothesis, a second density E; and a second time implicitly
by specializing D := projL(Ï†Q) to identify E = projL Q through the
elementary spectral lemma U2. It then concludes with wigner, the internal
block above, through Wigner's Corollary (B) in projection language (U1), which
had never been constructed before this milestone. The full decomposition
has six submilestones: U1, Wigner's corollary in projection language; U2,
the spectral lemma; U3a, extension of a frame function on lines to a full
ProjMeasure, absent from gleason-theorem-lean and therefore derived in
this repository; U3b, â€œGleason applied twiceâ€; U4, assembly; and U5, the
finite-dimensional cardinality-counting reduction. Full details are in
MILESTONES.md.

## Grain Coherence Theorem (BornRule)

lean
structure Perspective (n : â„•) where
 cells : Finset (Submodule â„‚ (H n))
 nz : âˆ€ c âˆˆ cells, c â‰  âŠ¥
 ortho : âˆ€ c âˆˆ cells, âˆ€ c' âˆˆ cells, c â‰  c' â†’ c â‰¤ c'á—®
 span : sSup (cells : Set (Submodule â„‚ (H n))) = âŠ¤

theorem grainCoherenceTheorem (hn3 : 3 â‰¤ n) (hA : AxGrain Est) (hN : AxNorm Est)
 (hPos : AxPos Est) {v : H n} (hv : â€–vâ€– = 1) (hNul : AxNul Est v)
 (D : Perspective n) {c : Submodule â„‚ (H n)} (hc : c âˆˆ D.cells) :
 Est D c = âˆ‘ i : Fin (Module.finrank â„‚ c),
 â€–âŸªv, ((stdOrthonormalBasis â„‚ c i : c) : H n)âŸ«_â„‚â€– ^ 2

theorem grainCoherenceTheorem_projector (hn3 : 3 â‰¤ n) (hA : AxGrain Est)
 (hN : AxNorm Est) (hPos : AxPos Est) {v : H n} (hv : â€–vâ€– = 1)
 (hNul : AxNul Est v) (D : Perspective n) {c : Submodule â„‚ (H n)}
 (hc : c âˆˆ D.cells) :
 Est D c = â€–projL c vâ€– ^ 2


For a perspective D, an orthogonal partition of H n into nonzero cells,
and a cell c of D, every estimation rule Est satisfying (Grain), (Norm),
(Pos), and, for a fixed unit vector v, (Null), satisfies
Est D c = âˆ‘áµ¢ â€–âŸ¨v,fáµ¢âŸ©â€–Â² over every orthonormal basis (fáµ¢) of c: the Born
rule in full generality, derived from the four coherence axioms alone, without
assuming a priori that Est has trace form. This covers the descriptive
route through Gleason's theorem. A second independent derivation route, using
a dynamic-stability axiom rather than grain coherence, the
existence/consistency of the four axioms themselves, and intersubjective
convergence between observers as a corollary are possible future extensions
and are not attempted here.

This result COMPOSES Gleason with the Uhlhorn infrastructure rather than
introducing self-contained mathematical content: B2 constructs a frame
function on lines directly from the estimation rule through
Perspective.binary, then invokes U3a + Gleason.gleason, an actual theorem
rather than an axiom, to obtain a density Ï; B3 reuses U2 to show that a
density operator vanishing on the orthogonal complement of a unit vector v
is exactly projL (â„‚âˆ™v); and B4 connects (Null) to this vanishing hypothesis
and assembles the result through
refinePerspective/refine_filter_eq_cellLines, already proved in B1. The
full decomposition has four milestones: B1, scaffoldingâ€”perspectives, axioms,
non-contextuality; B2, bridge to Gleason; B3, pinning; and B4, final assembly.
Full details and favorable deviations are in MILESTONES.md.

#print axioms grainCoherenceTheorem depends only on
[propext,
Classical.choice, Quot.sound]: Gleason's theorem is imported as an
actual theorem (Gleason.gleason), never postulated.

grainCoherenceTheorem_projector is only the projector-notation version of
the preceding theorem: Parseval's identity identifies its orthonormal-basis
sum with â€–projL c vâ€–Â². It is not a new independent mathematical result.

## Kent's contrary-inferences theorem (HistoriesKent)

lean
abbrev History (n L : â„•) := Fin L â†’ Submodule â„‚ (H n)

def IsConsistent (Ïˆ : H n) (Ps : Fin L â†’ Perspective n) : Prop :=
 âˆ€ h k : History n L, IsHistoryOf Ps h â†’ IsHistoryOf Ps k â†’ h â‰  k â†’
 decFunctional Ïˆ h k = 0

def histProb (Ïˆ : H n) (h : History n L) : â„ := â€–chainOp h Ïˆâ€– ^ 2

theorem contrary_inferences :
 âˆƒ (Ps Ps' : Fin 2 â†’ Perspective 3) (Ïˆ : H 3),
 P 0 âŸ‚ P 1 âˆ§
 IsConsistent Ïˆ Ps âˆ§ IsConsistent Ïˆ Ps' âˆ§
 (histProb Ïˆ (![(P 0)á—®, F] : History 3 2) = 0 âˆ§ histProb Ïˆ (![P 0, F] : History 3 2) â‰  0) âˆ§
 (histProb Ïˆ (![(P 1)á—®, F] : History 3 2) = 0 âˆ§ histProb Ïˆ (![P 1, F] : History 3 2) â‰  0)


In words: there exist two consistent families of two-stage histories on
H 3, sharing the same preparation Ïˆ and the same final postselection
stage F, such that the first implies proposition P 0 with certainty, the
second implies P 1 with certainty, and P 0 is orthogonal to P 1â€”Kent
1997, PRL 78, 2874, arXiv:gr-qc/9604012. A temporal stage of a history set
is a BornRule.Perspective, reused unchanged. The consistency notion is
Kent's â€œmedium/strongâ€ version (decFunctional Ïˆ h k = 0 for every pair of
distinct histories in the family, not merely vanishing of its real part).
The explicit witness is constructed in dimension 3:
Ïˆâ‚€ := eâ‚€+eâ‚+eâ‚‚, Ï†â‚€ := eâ‚€+eâ‚âˆ’eâ‚‚ (not normalized),
P i :=
â„‚âˆ™(e i), and F := â„‚âˆ™Ï†â‚€. The key cancellation is
âŸªÏ†â‚€, e iâŸ« = 1 for i âˆˆ {0,1} (= -1 for i = 2, outside the witness).

Neutrality note. The mathematical content aboveâ€”two consistent sets each
implying with certainty a proposition, with the two propositions
orthogonalâ€”is undisputed. Its interpretation as an objection to the
predictability of consistent histories is debated: the standard response
(Griffiths) invokes the â€œsingle-framework rule,â€ under which the two
inferences are valid only within their respective frameworks and may never
be combined in one argument. This repository fixes the mathematical
statement without adjudicating the interpretive debate.

The generic profusion theorem of Dowkerâ€“Kent
(J. Stat. Phys. 82, 1575 (1996), using parameter/dimension counting on
manifolds to show that contrary inferences are not isolated) is explicitly
outside the scope of this block. It remains a possible future extension; see
MILESTONES.md.

## Redundant-record interference-circuit bound (Complexity)

`QuantumFoundations.Complexity` connects Riedel's exact or approximate spatial records to
exact 2-local quantum circuits. A circuit is a finite list of unitary gates,
each local to a `Finset (Fin N)` of cardinality at most two. The evaluation
convention is chronological: for `[Gâ‚, Gâ‚‚, Gâ‚ƒ]`,
`eval C x = Gâ‚ƒ (Gâ‚‚ (Gâ‚ x))`.

Its main theorem has the exact type:

```lean
theorem regions_card_le_two_mul_circuit_length_of_cross_amplitude_ne_zero
    {N d K R : â„•} [NeZero R]
    (e : H (d ^ N) â‰ƒâ‚—áµ¢[â„‚] Sites N d) (C : Circuit N d)
    (regions : Fin R â†’ Finset (Fin N))
    (recs : Fin R â†’ LabeledResolution (d ^ N) K) (Ïˆ : H (d ^ N))
    (hrec : IsRecordedOn Ïˆ recs) (i j : Fin K) (hij : i â‰  j)
    (hlocal : âˆ€ r, IsLocalTo (transportedRecordProj e (recs r) j) (regions r))
    (hpairwise : âˆ€ r r', r â‰  r' â†’ Disjoint (regions r) (regions r'))
    (hcross : âŸªbranch recs Ïˆ j, Circuit.evalOnH C e (branch recs Ïˆ i)âŸ«_â„‚ â‰  0) :
    R â‰¤ 2 * Circuit.length C
```

Thus an exact nonzero cross amplitude between distinct recorded branches
forces the circuit to touch every record region. Pairwise disjointness and
the two-site support bound then give `R â‰¤ 2 * C.length`.

C3â€“C6 add the exact division-free `DistinguishesAt` and `InterferesAt`
predicates displayed in the French section above. For distinct nonzero
normalized recorded branches and `0 < Î´ â‰¤ 1`, redundant pairwise-disjoint
records imply the per-circuit interference bound `ceilHalf R â‰¤ C.length`.
An explicitly supplied circuit implementing `2 P_j - I` provides the
distinguishability upper bound. These combine first as a relational,
subtraction-free proxy-gap certificate and then as
`distinguishabilityComplexity + g â‰¤ interferenceComplexity` in `WithTop â„•`.
Both target-label locality hypotheses are required because either orientation
of the two-term interference proxy may be nonzero.

C7 proves conditional persistence under an explicit finite reversible
circuit evolution. A `ReversibleCircuitEvolution` stores forward and backward
circuits whose evaluations are mutual inverses, with overhead
`forward.length + backward.length`. The append convention implies that
`backward ++ C ++ forward` implements `forward âˆ˜ C âˆ˜ backward`, while
`forward ++ C ++ backward` implements the pullback. Exact matrix elements and
both proxies are invariant under these conjugations. Distinguishability can
gain one overhead, interference can lose one, and the certified gap can
therefore lose at most twice the overhead.

A canonical inverse circuit was constructed by reversing the gate list and
inverting every gate while preserving its local support. Consequently
`ofCircuit E` has overhead `2 * E.length`, and the record theorem derives the
budget `D.length + 4 * E.length + g â‰¤ ceilHalf R`. The `WithTop â„•` transport
theorems work directly under the infimum, including `âŠ¤`, without attainment
or subtraction.

C8 replaces the exact record identities by the aggregated predicate
`â€–P target - targetâ€– + â€–P otherâ€– â‰¤ Î·`. The projector/defect decomposition
gives the sharp untouched cross-amplitude bound `Î·`; the two proxy
orientations therefore require `Î·i + Î·j < 2 * Î´`. A supplied readout circuit
may have aggregate pointwise error `Î¾`; its diagonal separation loses exactly
`2 * Î·j + Î¾`, giving the sufficient threshold
`2 * Î´ + 2 * Î·j + Î¾ â‰¤ 2`. The robust certificates and `WithTop â„•` bounds then
reuse C6. Exact C7 conjugation adds no analytic error, only the existing
twice-overhead circuit budget. Setting all errors to zero recovers C4â€“C7.

C9 instantiates this architecture in the explicit binary repetition model.
`zeroBranch R` and `oneBranch R` are the transported constant-zero and
constant-one computational basis vectors; their coherent sum
`repetitionState R` is deliberately unnormalized. Every singleton site is an
independent exact binary record. Reflection in the bit-one cell at the first
site gives an exact one-gate readout, while an ordered list of `R` Pauli-X
gates exchanges the two branches. Consequently
`C_D = 1`, `ceilHalf R â‰¤ C_I â‰¤ R`, the interference minimum is finite,
every `1 + g â‰¤ ceilHalf R` gives a proxy gap, and the concrete persistence
budget is `1 + 4 * E.length + g â‰¤ ceilHalf R`. Paired-flip sharpness is not
claimed; the closed interference result is the stated pair of linear bounds.

C10 finally shows this robust C8 theory is inhabited by a genuinely
**nonzero-noise** explicit family, on `R + 1` sites: one source qubit (site
`0`) plus `R` record qubits (`recordSite r := Fin.succ r`). A normalized
`NoiseProfile` (`keep`, `leak`, with `â€–keepâ€–Â² + â€–leakâ€–Â² = 1`) mixes two
same-source-bit configurations,
`noisyZeroBranch := keep â€¢ basis00 + leak â€¢ basis01` and
`noisyOneBranch := leak â€¢ basis10 + keep â€¢ basis11`, which stay **exactly
orthogonal for every `leak`** because their source qubits differ. Every
record projector has an exact computed error â€” it fixes the aligned
configuration exactly and leaks exactly `â€–leakâ€–` into the other one â€” giving
the exact aggregate `ApproxRecordedPairOn` budget `2 * â€–leakâ€–` per label, a
genuine (not merely zero-error) inhabitant of the C8 approximate-record
predicate. At threshold `Î´ = 1/2` the robust condition
`NoiseProfile.IsRobust p := 4 * â€–p.leakâ€– < 1` gives exactly the same
qualitative bounds as C9:

```lean
distinguishabilityComplexity (sitesEquivR (R+1)) (noisyZeroBranch p R) (noisyOneBranch p R) (1/2) = 1
ceilHalf R â‰¤ interferenceComplexity (sitesEquivR (R+1)) (noisyZeroBranch p R) (noisyOneBranch p R) (1/2)
interferenceComplexity (sitesEquivR (R+1)) (noisyZeroBranch p R) (noisyOneBranch p R) (1/2) â‰¤ R + 1
```

together with the robust proxy gap and its conditional persistence under the
same budget `1 + 4 * E.length + g â‰¤ ceilHalf R`. The Pythagorean triple
`99Â² + 20Â² = 101Â²` gives a fully concrete rational witness
`(keep, leak) = (99/101, 20/101)` with `4 * (20/101) = 80/101 < 1`, to which
every C10aâ€“C10g theorem applies unconditionally. Three generalizations were
added additively to C9 (at a generality C9 itself never needed, and without
changing any existing public type): a basis vector at an arbitrary
configuration (`configurationBranch`), a reflection readout at an arbitrary
site (`recordReadoutGateAt`/`recordReadoutCircuitAt`), and the all-bit-flip
action on an arbitrary configuration
(`allBitFlipCircuit_maps_configurationBranch`).

C11 closes precisely the gap noted at the end of C10: an explicit finite
circuit of 1- and 2-local unitary gates **dynamically generates** the
source-record branching from an uncorrelated source qubit `Î±|0âŸ© + Î²|1âŸ©` and
`R` blank record qubits, rather than assuming the branched state as given.
`controlledBitFlipGate` (C11a) is a genuine 2-local permutation gate;
`idealFanoutCircuit R` (C11b) copies the source qubit's classical label onto
every record â€” computational-basis label fanout, never cloning of an
arbitrary quantum state (no-cloning is not violated: only the classical
`0`/`1` label is fanned out, never the source qubit's own amplitudes). The
hardest construction (C11e) is a genuine single-qubit amplitude-mixing
unitary lifted to all `N` sites through the flat `Sites N d` representation
(no tensor-factor infrastructure existed in the repository for this):
`prepLinearMap p t := keep â€¢ Pâ‚€ + leak â€¢ (F âˆ˜ Pâ‚€) - conj(leak) â€¢ (F âˆ˜ Pâ‚) +
conj(keep) â€¢ Pâ‚`, proved unitary by a direct 16-term inner-product
expansion. This construction succeeds **unconditionally** for every
`NoiseProfile` â€” no supplied-gate fallback was needed. `noisyMeasurementCircuit
p R` (C11fâ€“g, length `2R`) turns `Î± â€¢ basis00 + Î² â€¢ basis10` into exactly
`Î± â€¢ noisyZeroBranch p R + Î² â€¢ noisyOneBranch p R` â€” the *same* states as
C10's, so C10's robust proxy gap and its conditional persistence under any
further circuit transport immediately (C11i), with no new distinguishability
argument. The Pythagorean triple `3Â² + 4Â² = 5Â²` gives a fully concrete
rational source-amplitude witness `(amp0, amp1) = (3/5, 4/5)` (C11j), to
which â€” paired with C10h's rational noise profile `(99/101, 20/101)` â€” the
full C11 chain applies unconditionally.

C12 closes the optional operator-norm bridge left open since C8:
`toContinuousLinearMapFD` (C12a) is the canonical continuous-linear-map view
of a linear map out of a finite-dimensional complex normed space
(Mathlib's `LinearMap.toContinuousLinearMap`) â€” `Circuit.evalOnH`,
`recordPhaseFlip`, and every existing `LinearMap` API are left entirely
unchanged; this is an additional view, not a replacement.
`ApproximatesOperator A B Îµ := â€–A - Bâ€– â‰¤ Îµ` (C12b) is a generic operator-norm
error budget mentioning no records or circuits; the central estimate
`â€–A x - B xâ€– â‰¤ Îµâ€–xâ€–` gives, on two unit states `a, b`, the accumulation
`â€–A a - B aâ€– + â€–A b - B bâ€– â‰¤ 2Îµ` â€” the factor `2` derived by plain
arithmetic, never postulated. `ApproximatesRecordPhaseFlipOp` (C12c)
specializes this bridge to `recordPhaseFlip`: an operator-norm error budget
`Îµ` implies the C8 pointwise budget `Î¾ = 2Îµ`, which directly recovers
(C12d) the readout threshold `2Î´ + 2Î·j + 2Îµ â‰¤ 2` and (C12e) the robust
proxy gap and its conditional persistence, reusing C8's own analytic
estimate unchanged â€” no new estimate is introduced. At C10's noisy model
(C12f) this threshold becomes exactly `4â€–leakâ€– + 2Îµ â‰¤ 1`; the hypothesis
`p.IsRobust` (`4â€–leakâ€– < 1`, strict) is still required alongside it â€” not
redundant, since `hreadout` alone (with `Îµ â‰¥ 0`) gives only the non-strict
`4â€–leakâ€– â‰¤ 1`, insufficient for the strict interference argument. At C11's
dynamically generated branches (C12g), the same threshold applies directly
to the generated branch pair. The concrete rational witness `Îµ = 1/20`
checks exactly `80/101 + 2Â·(1/20) â‰¤ 1` by exact rational arithmetic.
Generic composition laws (C12h, optional) prepare C13's simulation-error
accumulation.

C13 establishes robust gap persistence under an actual norm-preserving
evolution `U` (not necessarily a circuit), as long as an exact circuit `E`
approximates it in operator norm to error `Îµ`. The central mathematical
point is that same-threshold persistence at `Î´` with **no** margin is
generally **not** justified: perturbing two unit states by `Îµ` each moves
the diagonal difference by at most `4Îµ` and the cross sum by at most `4Îµ`
(C13b), shifting the proxy threshold by `2Îµ` (since the definitions use
`2 Â· threshold`). C13 therefore introduces a margin `Î¼`: a certificate at
the widened thresholds `Î´ - Î¼` (interference) and `Î´ + Î¼`
(distinguishability) â€” `HasProxyGapMarginAtLeast` (C13d) â€” persists under an
exact circuit (C13e) and then transports to the central threshold `Î´` for
the `U`-evolved states, whenever `2Îµ â‰¤ Î¼` (C13f, the main theorem). The
simulation certificates `CircuitSimulatesEvolutionAt`/`HasCircuitSimulationAt`
(C13f) and their time-dependent extension `HasCircuitSimulationBound` (C13j)
make this directly reusable. Instantiated at C10's noisy model (C13g) and
then at C11's generated branches (C13h), with the concrete rational witness
`Î´=1/2, Î¼=1/10, Îµ=1/20` (C13i, `80/101 < 4/5`, `6/5+80/101 â‰¤ 2`,
`2Â·(1/20) â‰¤ 1/10`). An optional layer (C13k) constructs an evolution
*genuinely* generated by a self-adjoint generator `H` â€” `evolve t :=
exp(-itH)`, via Mathlib's existing operator exponential for bounded Câ‹†-
algebras, with no extra assumption â€” leaving only the additive group law
unproved (a precisely documented Mathlib instance-resolution obstruction,
not a mathematical gap).

**C14** connects two already-established theorems rather than deriving one
from the other: Riedel's unique orthogonal joint-branch decomposition
(`Induction.riedel`, BranchesRiedel) and the Born weight
`grainCoherenceTheorem_projector` (BornRule), which assigns `â€–projL c vâ€–Â²`
to any cell `c` of a perspective under (Pos), (Norm), (Grain), (Null).
`BranchesRiedel/BornBridge/` distinguishes four objects: a branch vector
`B f`, its active cell `span â„‚ {B f}` (defined only when `B f â‰  0` â€” a
zero vector has no formal cell), the support `branchSupport` (the supremum
of the active cells, not necessarily the whole space), and the residual
orthogonal cell `residualCell` (which may be `âŠ¥`). The central projection
identity, `starProjection_branchCell_apply_state : (branchCell B
f).starProjection Ïˆ = activeBranchVector B f` (C14c), is a pure
linear-algebra fact â€” via `Submodule.eq_starProjection_of_mem_orthogonal'`
â€” independent of any weighting. `BranchPerspectivePackage` (C14e) builds a
genuine `Perspective` from the active cells, adding the residual cell only
when it is nonzero (`Perspective` forbids `âŠ¥` cells).
`recordBranch_weight_eq_norm_sq` (C14f) then chains
`grainCoherenceTheorem_projector` with the projection identity: the Born
weight of each active cell is exactly `â€–B fâ€–Â²`, the residual weight is
zero, and the active weights sum to `1`. Record-choice invariance (C14a) â€”
`chainProj_choice_invariant`, proved by replacing one observable's record
at a time via `Induction.tunneling`, never composing two different records
of the same observable â€” gives weight invariance under the chosen record
(C14f.5) at the vector level, not merely the norm level.
`record_induced_Born_decomposition` (C14g) assembles all of this into one
abstract theorem, specialized to the local multisite model (C14h) and then
to C11's exact unitary generation (C14i) â€” two branches `q.amp0 â€¢ basis00
R`/`q.amp1 â€¢ basis11 R`, weights `â€–amp0â€–Â²`/`â€–amp1â€–Â²` â€” concretely at
`(3/5, 4/5)` giving the exact rational weights `9/25` and `16/25` (C14l).
C10's noisy model satisfies only approximate redundancy
(`ApproxRecordedPairOn`), not exact `IsRecordedOn`: exact branch uniqueness
is therefore not concluded for it, only exact source-component extraction
(C14j). Finally, the Born weights of evolved branches under a
norm-preserving evolution (C13) retain their squared norm â€” via the
norm-based polarization identity `inner_eq_sum_norm_sq_div_four` â€” without
the evolved branch still being selected by the original record projectors
(C14k).

The result is
limited to finitely many sites, finite local dimension, supplied exact or
approximate records,
pairwise disjoint regions, exact 2-local gates, and an exact nonzero cross
amplitude/proxy above the explicit threshold. It does not
address generic formation of approximate records from decoherence (distinct
from C11's explicit unitary construction), establish efficient synthesis of
arbitrary local record projectors, complete the operator-norm view of every
repository API (C12 covers only the record-readout bridge), the full
physical Taylorâ€“McCulloch
criterion, a Trotter/product-formula or Liebâ€“Robinson simulation bound,
linear or polynomial simulation-cost growth in time (C13 formalizes no
`O(t)` notation), generic or
Brownâ€“Susskind complexity growth, macroscopic irreversibility, equivalence
with Weingarten, or any interpretive claim about quantum mechanics. C14
connects redundant records to Born weights for a given model, under (Pos),
(Norm), (Grain), (Null) â€” it does not claim that records alone imply the
Born rule, that (Grain) need only hold on physically realized
perspectives, or approximate/generic many-body branch-decomposition
uniqueness.

**C15** is the Lean formalization and repository integration of Theorem 3
and Corollary 2 of Marko Lela, â€œThe Born Rule as the Unique
Refinement-Stable Induced Weight on Robust Record Sectorsâ€
(arXiv:2603.24619v1). It concerns induced weights on admissible record
situations, not a measure on the full projector lattice. Internal
equivalence initially means equality of binary refinement profiles; exact
binary saturation then proves that projected magnitude classifies those
profiles. The resulting functional equation forces
`W = c â€–P_R Î¨â€–Â²`, and finite normalization fixes `c = 1`. Additivity may be
inherited from an extensive valuation on disjoint continuation bundles. No
Gleason, Busch, decision-theoretic, or envariance theorem is used. Binary
saturation is assumed rather than derived from C14 dynamics; dense
saturation plus continuity, the physical C14/C15 bridge, and C16 are
explicitly deferred.

**C17** is the first quantitative stability theorem within this
development. It assumes that both weights already obey the exact quadratic
law supplied by C15 and measures perturbations by the distance between
projected components `u = P_(Râ‚)x Î¨â‚x` and `v = P_(Râ‚‚)x Î¨â‚‚x`. It proves
`|Wâ‚-Wâ‚‚| â‰¤ (â€–uâ€–+â€–vâ€–)â€–u-vâ€–`, the unit-ball estimate
`|Wâ‚-Wâ‚‚| â‰¤ 2â€–u-vâ€–`, and explicit finite-`LÂ¹`, `2Â·card(s)Â·Îµ`, and half-`LÂ¹`
bounds. It does not address approximate C15 hypotheses, approximate branch
uniqueness, or a dynamical derivation of component proximity. No historical
priority claim is made.

**C17b** is an integration milestone, not a strengthening of the already
completed reduced C17 core. On the unit ball, a fixed sector satisfies
`|w_R(Ïˆ)-w_R(Ï†)| â‰¤ 2â€–Ïˆ-Ï†â€–`; projectors within operator-norm error `Îµ` satisfy
`|w_R(Ïˆ)-w_S(Ïˆ)| â‰¤ 2Îµ`. A C13 simulation certificate therefore gives
`|w_R(U(t)Ïˆ)-w_R(CÏˆ)| â‰¤ 2Îµ` for every fixed sector. C14 branch weights also
inherit the generic branch-vector bound when the caller supplies an explicit
branch correspondence. These bridges do not establish approximate branch
matching or uniqueness, approximate saturation, or physical persistence of
record selection.

## AI assistance

This developmentâ€”skeleton, proofs, and architectural choicesâ€”was carried out
with assistance from Claude (Anthropic), under human supervision at every
stage: every uncertain Mathlib API was checked through stdin before use
(lake env lean --stdin), every milestone began with a validated skeleton
containing sorry before being filled, and lake build +
./scripts/guard.sh were run after every closed proof. See AGENTS.md for
the exact rules followed and the commit history for milestone-by-milestone
details.

## Getting started

bash
./setup.sh # toolchain + mathlib + cache + build (~10 min avec cache)
./scripts/guard.sh # audit : 0 axiome, 0 native_decide, compte des sorry


## Verifying the proofs

bash
lake build # doit terminer vert
./scripts/guard.sh # 0 axiome, 0 native_decide, 0 sorry (seven blocks)


#print axioms for the chapter-level theorems (the exhaustive list of 155
content-bearing public declarations is in ARCHITECTURE_NOTES.md/the closing
report; all depend on the same trio):


'QuantumFoundations.naimark' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.naimark_born' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.exists_unitary_extension' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.naimark_projective_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Wigner.wigner' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Wigner.exclusivity' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Wigner.bargmann_delta_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Wigner.U_alt_eq_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Uhlhorn.uhlhorn_finite_dim' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Uhlhorn.wignerSymmetryProj_of_sendsONBToONB' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Uhlhorn.traceProd_preserved_of_sendsONBToONB' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.Uhlhorn.exists_projMeasure_of_frameFunctionOnLines' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.grainCoherenceTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.grainCoherenceTheorem_projector' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.full_rho_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.hker_derivation' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.exists_rho' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.eq_projL_of_vanishes_on_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.Eâ‚€_satisfies_axioms' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.BornRule.refine_filter_sup_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.HistoriesKent.contrary_inferences' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.HistoriesKent.inference' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.HistoriesKent.S_consistent' depends on axioms: [propext, Classical.choice, Quot.sound]
'QuantumFoundations.HistoriesKent.isConsistent_single_stage' depends on axioms: [propext, Classical.choice, Quot.sound]


These are the three standard axioms accepted by Lean/Mathlib itself:
propositional extensionality, choice, and quotient soundness. There is no
sorryAx and no project-specific axiom. Points checked specifically:
uhlhorn_finite_dim is the first theorem in the repository to depend both on
Gleason.gleason, an external dependency, AND on
QuantumFoundations.Wigner.wigner, an internal block;
grainCoherenceTheorem depends both on Gleason.gleason AND on the internal
Uhlhorn infrastructure U2/U3a. In both cases, the dual dependency chain leaks
no additional axioms, as confirmed above. contrary_inferences depends
transitively on a THREE-level chain
(HistoriesKent â†’ BornRule.Perspective â†’ external Uhlhorn/Gleason); the
same trio was confirmed when HistoriesKent was closed on 2026-07-16, as was the
absence of any BornRule axiom regression following the relocation of
norm_sq_sum_of_pairwise_orthogonal/sum_sq_projL_of_pairwise_isOrtho
(from private in Nonvacuity.lean to public declarations in
Perspective.lean). The 34 PUBLIC BornRule declarationsâ€”the previous 32 +
the two relocated, now public lemmasâ€”were rechecked individually; none
was affected.

## Repository map

| File | Content | Lines |
|---|---|---:|
| QuantumFoundations/Naimark/Defs.lean | POVM n m (reuses Gleason.IsPositiveOp) | 46 |
| QuantumFoundations/Naimark/SqrtOp.lean | Positive square root (spectral construction) | 191 |
| QuantumFoundations/Naimark/DilSpace.lean | Dilation space K, singleL/coordL/dilProj | 194 |
| QuantumFoundations/Naimark/Main.lean | dilV, isometry, Naimark theorem, Born corollary | 157 |
| QuantumFoundations/Naimark/Unitary.lean | N5 (optional): unitary extension, ancilla form | 210 |
| QuantumFoundations/Wigner/Defs.lean | e, eImg, InPerp, V, refVec, chidir, chi, U, IsWignerMap | 119 |
| QuantumFoundations/Wigner/Scalar.lean | Scalar toolkit over â„‚ (rigidity, id/conj dichotomy) | 117 |
| QuantumFoundations/Wigner/Bessel.lean | Bessel identity (equality); orthonormal images | 126 |
| QuantumFoundations/Wigner/VConstruction.lean | Bargmann's Construction B: V, collinearity, (11)â€“(12a) | 449 |
| QuantumFoundations/Wigner/Core.lean | Core: dichotomy of chi, additivity/homogeneity of V | 833 |
| QuantumFoundations/Wigner/Main.lean | U, bijectivity, compatibility with T, theorem wigner | 399 |
| QuantumFoundations/Wigner/Uniqueness.lean | W6 (optional): exclusivity (A), restricted uniqueness (B) | 439 |
| QuantumFoundations/Wigner/Nonvacuity.lean | Wigner witnesses: id (unitary branch), conjCoords (antiunitary branch) | 112 |
| QuantumFoundations/Uhlhorn/Defs.lean | Proj1, TraceProd, PreservesOrthogonality, IsWignerSymmetryProj, IsFrameFunctionOnLines, SendsONBToONB | 278 |
| QuantumFoundations/Uhlhorn/WignerProjectionForm.lean | U1: Wigner's Corollary (B) in projection language | 117 |
| QuantumFoundations/Uhlhorn/Spectral.lean | U2: elementary spectral lemma | 131 |
| QuantumFoundations/Uhlhorn/GleasonExtend.lean | U3a: extension of a frame function on lines to a full ProjMeasure | 268 |
| QuantumFoundations/Uhlhorn/GleasonTwice.lean | U3b: â€œGleason applied twiceâ€ | 175 |
| QuantumFoundations/Uhlhorn/Assembly.lean | U4 (assembly) + U5 (finite-dimensional reduction), theorem uhlhorn_finite_dim | 111 |
| QuantumFoundations/Uhlhorn/Nonvacuity.lean | Uhlhorn witness: Ï† := id | 53 |
| QuantumFoundations/BornRule/Perspective.lean | B1: Perspective, Refines, AxGrain/AxNorm/AxPos/AxNul, lemma4_noncontextual, basisPerspective, cellLines, refinePerspective | 555 |
| QuantumFoundations/BornRule/GleasonBridge.lean | B2: g, g_isFrameFunctionOnLines, exists_rho (replaces axiom gleason) | 115 |
| QuantumFoundations/BornRule/Pinning.lean | B3: eq_projL_of_vanishes_on_orthogonal (identification of Ï via U2) | 83 |
| QuantumFoundations/BornRule/Assembly.lean | B4 (assembly), final theorem grainCoherenceTheorem | 215 |
| QuantumFoundations/BornRule/Nonvacuity.lean | BornRule witness: Eâ‚€ v (Born rule) satisfies Grain+Norm+Pos+Null simultaneously | 177 |
| QuantumFoundations/Nonvacuity.lean | Naimark witness: uniform POVM with n=2, m=2 | 65 |
| QuantumFoundations/HistoriesKent/Defs.lean | History, IsHistoryOf, chainOp, decFunctional, IsConsistent, histProb | 162 |
| QuantumFoundations/HistoriesKent/Nonvacuity.lean | HistoriesKent witness: every one-stage Perspective is consistent | 85 |
| QuantumFoundations/HistoriesKent/Basic.lean | K1: decFunctional_last_stage_orthogonal, histProb_additivity_two_stage | 121 |
| QuantumFoundations/HistoriesKent/Witness.lean | K2: explicit Kent witness in H 3, S_consistent | 490 |
| QuantumFoundations/HistoriesKent/ContraryInferences.lean | K3: inference, final theorem contrary_inferences | 162 |
| QuantumFoundations/BranchesRiedel/Defs.lean | R0: labeled resolutions, branches, and redundant records | 234 |
| QuantumFoundations/BranchesRiedel/Nonvacuity.lean | R0: three-record GHZ witness | 210 |
| QuantumFoundations/BranchesRiedel/Basic.lean | R1: general record-projector identities | 133 |
| QuantumFoundations/BranchesRiedel/TwoObs.lean | R2: two recorded observables | 207 |
| QuantumFoundations/BranchesRiedel/Induction.lean | R3: multi-observable induction | 559 |
| QuantumFoundations/BranchesRiedel/Local.lean | R4: spatial locality and `PairCovers` counting | 469 |
| QuantumFoundations/BranchesRiedel/BornBridge/RecordChoice.lean | C14a: redundant record-choice invariance | 203 |
| QuantumFoundations/BranchesRiedel/BornBridge/ActiveBranches.lean | C14b: active branch index | 76 |
| QuantumFoundations/BranchesRiedel/BornBridge/BranchCells.lean | C14b/c: branch cells, projection identity | 134 |
| QuantumFoundations/BranchesRiedel/BornBridge/BranchPerspective.lean | C14d/e: support, residual cell, formal perspective | 218 |
| QuantumFoundations/BranchesRiedel/BornBridge/BornWeights.lean | C14f: Born weights of record-induced branches | 151 |
| QuantumFoundations/BranchesRiedel/BornBridge/Synthesis.lean | C14g: abstract synthesis theorem | 92 |
| QuantumFoundations/BranchesRiedel/BornBridge/LocalRecords.lean | C14h: local multisite corollary | 49 |
| QuantumFoundations/BranchesRiedel/BornBridge/GeneratedBranches.lean | C14i/j: C11 exact unitary model, noisy-model boundary | 199 |
| QuantumFoundations/BranchesRiedel/BornBridge/Evolution.lean | C14k: weight preservation under norm-preserving evolution | 129 |
| QuantumFoundations/BranchesRiedel/BornBridge/ConcreteModel.lean | C14l: concrete instance (weights 9/25, 16/25) | 86 |
| QuantumFoundations/BranchesRiedel/BornBridge/Nonvacuity.lean | C14: non-vacuity witnesses | 101 |
| QuantumFoundations/Complexity/Defs.lean | C0: exact 2-local gates and circuits, evaluation and support | 129 |
| QuantumFoundations/Complexity/Nonvacuity.lean | C0/C6/C7/C8/C9/C10/C11/C12/C13: elementary witnesses and concrete models | 389 |
| QuantumFoundations/Complexity/CircuitLocality.lean | C1: circuit commutation away from its support | 45 |
| QuantumFoundations/Complexity/RecordInterference.lean | C1: untouched records force zero cross amplitude | 122 |
| QuantumFoundations/Complexity/Counting.lean | C2: generic counting of touched disjoint regions | 35 |
| QuantumFoundations/Complexity/Main.lean | C2: main bound `R â‰¤ 2 * C.length` | 63 |
| QuantumFoundations/Complexity/ProxyDefs.lean | C3: exact distinguishability and interference proxies | 82 |
| QuantumFoundations/Complexity/NormalizedBranches.lean | C3: normalization of nonzero recorded branches | 83 |
| QuantumFoundations/Complexity/ProxyCertificates.lean | C3: relational certificates and `ceilHalf` | 96 |
| QuantumFoundations/Complexity/RecordInterferenceBound.lean | C4: two-orientation interference bound | 96 |
| QuantumFoundations/Complexity/RecordDistinguishability.lean | C5: exact phase-flip readout | 114 |
| QuantumFoundations/Complexity/BranchGap.lean | C6: subtraction-free gap certificate | 50 |
| QuantumFoundations/Complexity/MinComplexity.lean | C6: `WithTop â„•` minima and actual gap | 180 |
| QuantumFoundations/Complexity/CircuitConjugation.lean | C7a: reversible evolution certificates and sandwich circuits | 157 |
| QuantumFoundations/Complexity/CircuitInverse.lean | C7a: local gate inverses and canonical inverse circuits | 207 |
| QuantumFoundations/Complexity/ProxyTransport.lean | C7b: exact matrix-element and proxy transport | 180 |
| QuantumFoundations/Complexity/Persistence.lean | C7c: relational certificate transport | 111 |
| QuantumFoundations/Complexity/RecordPersistence.lean | C7d: redundant-record persistence bounds | 104 |
| QuantumFoundations/Complexity/PersistenceMinima.lean | C7e: `WithTop â„•` transport without attainment | 117 |
| QuantumFoundations/Complexity/ApproxRecordDefs.lean | C8a: aggregated approximate-record predicate | 78 |
| QuantumFoundations/Complexity/ApproxRecordBasic.lean | C8a: recorded pairs and exact bridge | 64 |
| QuantumFoundations/Complexity/ApproxRecordInterference.lean | C8b: sharp untouched cross-amplitude bound | 132 |
| QuantumFoundations/Complexity/ApproxRecordInterferenceBound.lean | C8c: robust interference bound and minima | 123 |
| QuantumFoundations/Complexity/ApproxRecordDistinguishability.lean | C8d: approximate phase readout | 203 |
| QuantumFoundations/Complexity/ApproxBranchGap.lean | C8e: robust proxy gap and exact regression | 152 |
| QuantumFoundations/Complexity/ApproxRecordPersistence.lean | C8f: conditional robust-gap persistence | 160 |
| QuantumFoundations/Complexity/Models/Repetition/States.lean | C9a: zero/one computational branches and coherent state | 106 |
| QuantumFoundations/Complexity/Models/Repetition/Records.lean | C9b: single-site resolutions and exact records | 278 |
| QuantumFoundations/Complexity/Models/Repetition/Readout.lean | C9c: one-gate reflection readout | 161 |
| QuantumFoundations/Complexity/Models/Repetition/Distinguishability.lean | C9d: distinguishability complexity exactly one | 82 |
| QuantumFoundations/Complexity/Models/Repetition/Interference.lean | C9e: finite all-bit-flip circuit | 205 |
| QuantumFoundations/Complexity/Models/Repetition/Complexities.lean | C9f: linear bounds and concrete gap | 105 |
| QuantumFoundations/Complexity/Models/Repetition/Persistence.lean | C9g: concrete circuit-persistence budget | 57 |
| QuantumFoundations/Complexity/Models/NoisyRepetition/Profiles.lean | C10a: normalized `keep`/`leak` noise profiles | 76 |
| QuantumFoundations/Complexity/Models/NoisyRepetition/States.lean | C10b: four configurations and noisy branches | 215 |
| QuantumFoundations/Complexity/Models/NoisyRepetition/Records.lean | C10c: exact record errors and approximate pair | 182 |
| QuantumFoundations/Complexity/Models/NoisyRepetition/Readout.lean | C10d: exact readout at an arbitrary record site | 59 |
| QuantumFoundations/Complexity/Models/NoisyRepetition/Complexities.lean | C10e: robust complexity separation at `Î´ = 1/2` | 89 |
| QuantumFoundations/Complexity/Models/NoisyRepetition/Interference.lean | C10f: finite noisy interference witness | 151 |
| QuantumFoundations/Complexity/Models/NoisyRepetition/Persistence.lean | C10g: robust gap and conditional persistence | 123 |
| QuantumFoundations/Complexity/Models/NoisyRepetition/ConcreteNoise.lean | C10h: concrete rational profile `(99/101, 20/101)` | 95 |
| QuantumFoundations/Complexity/Gates/ControlledBitFlip.lean | C11a: 2-local controlled-bit-flip gates | 229 |
| QuantumFoundations/Complexity/Gates/AmplitudeRotation.lean | C11e: amplitude-mixing unitary lifted to `N` sites | 415 |
| QuantumFoundations/Complexity/Models/MeasurementGeneration/IdealFanout.lean | C11b: unitary computational-basis label fanout | 219 |
| QuantumFoundations/Complexity/Models/MeasurementGeneration/Amplitudes.lean | C11c: normalized source-amplitude profile | 89 |
| QuantumFoundations/Complexity/Models/MeasurementGeneration/BranchWeights.lean | C11d/h: source projectors and branch-weight preservation | 231 |
| QuantumFoundations/Complexity/Models/MeasurementGeneration/ProfilePreparation.lean | C11e: canonical profile-preparation gate | 95 |
| QuantumFoundations/Complexity/Models/MeasurementGeneration/NoisyGeneration.lean | C11f/g: correlated record preparation and full noisy generation | 493 |
| QuantumFoundations/Complexity/Models/MeasurementGeneration/GeneratedComplexity.lean | C11i: unitary generation meets branch persistence | 70 |
| QuantumFoundations/Complexity/Models/MeasurementGeneration/ConcreteGeneration.lean | C11j: concrete unitary generation witness | 89 |
| QuantumFoundations/Complexity/OperatorNorm/FiniteDimensional.lean | C12a: finite-dimensional continuous-linear-map view | 115 |
| QuantumFoundations/Complexity/OperatorNorm/Approximation.lean | C12b: generic operator-norm approximation | 106 |
| QuantumFoundations/Complexity/OperatorNorm/RecordReadout.lean | C12c: operator-norm/pointwise readout-error bridge | 113 |
| QuantumFoundations/Complexity/OperatorNorm/RecordGap.lean | C12d/e: distinguishability and proxy gap from operator norm | 207 |
| QuantumFoundations/Complexity/OperatorNorm/NoisyRepetition.lean | C12f: concrete noisy instantiation, `1/20` budget | 165 |
| QuantumFoundations/Complexity/OperatorNorm/GeneratedBranches.lean | C12g: connection to C11 unitary generation | 87 |
| QuantumFoundations/Complexity/OperatorNorm/Composition.lean | C12h: composition laws (optional, for C13) | 84 |
| QuantumFoundations/Complexity/OperatorNorm/Nonvacuity.lean | C12: non-vacuity of the error-budget API | 83 |
| QuantumFoundations/Complexity/SimulatedEvolution/NormPreserving.lean | C13a: norm-preserving operators | 92 |
| QuantumFoundations/Complexity/SimulatedEvolution/MatrixElementStability.lean | C13b: matrix-element perturbation bounds | 132 |
| QuantumFoundations/Complexity/SimulatedEvolution/ThresholdTransport.lean | C13c: threshold transport under operator error | 127 |
| QuantumFoundations/Complexity/SimulatedEvolution/MarginCertificate.lean | C13d: threshold-margin gap certificate | 88 |
| QuantumFoundations/Complexity/SimulatedEvolution/CircuitPersistence.lean | C13e: margin persistence under an exact circuit | 50 |
| QuantumFoundations/Complexity/SimulatedEvolution/SimulationCertificate.lean | C13f: persistence under simulated evolution | 142 |
| QuantumFoundations/Complexity/SimulatedEvolution/NoisyRepetition.lean | C13g: margin instantiation for the noisy model | 92 |
| QuantumFoundations/Complexity/SimulatedEvolution/GeneratedBranches.lean | C13h: connection to C11 generated branches | 77 |
| QuantumFoundations/Complexity/SimulatedEvolution/ConcreteModel.lean | C13i: concrete rational instance `Î´=1/2, Î¼=1/10, Îµ=1/20` | 108 |
| QuantumFoundations/Complexity/SimulatedEvolution/TimeEvolution.lean | C13j: time-dependent simulation cost | 85 |
| QuantumFoundations/Complexity/SimulatedEvolution/HamiltonianEvolution.lean | C13k: certified self-adjoint-generated evolution | 117 |
| QuantumFoundations/Complexity/SimulatedEvolution/Nonvacuity.lean | C13: non-vacuity of the simulated-evolution API | 114 |
| QuantumFoundations.lean | Root import aggregator | 69 |
| Recomputed total | 119 files | 19598 |

Documentation: AGENTS.md (rules for the AI agent, to be read at startup),
MILESTONES.md (detailed milestone-by-milestone tracking), and
ARCHITECTURE_NOTES.md (consolidated record of all deviations from the
initial plans).

## Milestones â€” Naimark

| Milestone | Content | Status |
|-----------|------------------------------------------------------------|--------|
| N0 | Skeleton (POVM, DilSpace, Nonvacuity) | âœ… |
| N1 | sqrtOp (spectral positive square root) | âœ… |
| N2 | Dilation-space components (singleL/coordL/dilProj) | âœ… |
| N3 | Dilation (dilV, naimark, naimark_born) | âœ… |
| N4 | Closure (README, #print axioms, tag) | âœ… |
| N5 | Optional: unitary/ancilla version (tag v2.0-naimark) | âœ… |

## Milestones â€” Wigner

| Milestone | Content | Status |
|-----------|----------------------------------------------------------------------------|--------|
| W0 | Skeleton (Defs, Nonvacuity, 24 sorry) | âœ… |
| W1 | Scalar toolkit (Scalar.lean: rigidity, scalar_dichotomy) | âœ… |
| W2 | Bessel identity (equality), orthonormal images | âœ… |
| W3 | Construction of V (collinearity, Eqs. 11â€“12a) | âœ… |
| W4 | Core: dichotomy of chi, additivity/homogeneity of V | âœ… |
| W5 | Assembly (U, bijectivity, compatibility, wigner) | âœ… |
| W6 | Optional: exclusivity (A) + restricted uniqueness (B) (tag v2.0-wigner) | âœ… |

## Milestones â€” Uhlhorn

| Milestone | Content | Status |
|-----------|--------------------------------------------------------------------------------|--------|
| U0 | Reconnaissance + skeleton (Defs.lean, 6 sorry) | âœ… |
| U1 | Wigner's Corollary (B) in projection language (wigner_projection_form) | âœ… |
| U2 | Elementary spectral lemma (eq_projL_of_positive_le_one_trace_one_inner_one) | âœ… |
| U3a | Extension of a frame function on lines to a full ProjMeasure | âœ… |
| U3b | â€œGleason applied twiceâ€ (traceProd_preserved_of_sendsONBToONB) | âœ… |
| U4 | Direct assembly of U1 and U3b | âœ… |
| U5 | Finite-dimensional reduction, final theorem (tag v1.0-uhlhorn) | âœ… |

## Milestones â€” BornRule

| Milestone | Content | Status |
|-----------|----------------------------------------------------------------------------------|--------|
| B1 | Scaffolding: Perspective, axioms, lemma4_noncontextual, refinePerspective | âœ… |
| B2 | Bridge to Gleason: g, IsFrameFunctionOnLines, exists_rho | âœ… |
| B3 | Pinning: eq_projL_of_vanishes_on_orthogonal (identification of Ï via U2) | âœ… |
| B4 | Final assembly, theorem grainCoherenceTheorem | âœ… |
| Nonvacuity | Eâ‚€ v (Born rule) simultaneously inhabits Grain+Norm+Pos+Null | âœ… |

## Milestones â€” BornRule/EffectPerspectives (qubit/Busch extension)

See also `QuantumFoundations/BornRule/EffectPerspectives/README.md` for the
full detail (scope, derivations, interpretive non-claims).

| Milestone | Content | Status |
|-----------|---------|--------|
| QB1 | `Effect` (subtype of `Gleason.IsEffect`), `zeroEffect`/`oneEffect`/`complementEffect`/`projectionEffect` | âœ… |
| QB2 | `EffectPerspective` (finite labelled POVM-like family), `binaryPerspective`/`splitPerspective`/`duplicateZeroPerspective` | âœ… |
| QB3 | `Refines` (refinement via `parent` + fiber-sum reconstruction); `Refines.trans` deferred (documented, non-blocking) | âœ… |
| QB4 | `EstimationRule` (weight/non-negativity/normalization/`grain`), a strictly larger hypothesis domain than the projective `AxGrain` | âœ… |
| QB5 | Context independence, zero/unit-effect weight, and binary additivity **derived** from `grain` alone (never axioms) | âœ… |
| QB6 | Construction of `Gleason.EffectMeasure`; direct application of `Gleason.busch`/`Gleason.busch_born_rule` | âœ… |
| QB7 | `ContextualNullSupport` (state-relative); fallback pinning theorem `density_bornValue_eq_pure_of_null` | âœ… |
| QB8 | `projectionEffect_weight_eq_born`: Born weight for projection effects, in arbitrary finite dimension | âœ… |
| QB9 | Explicit dimension-two (qubit) corollary, without invoking `Gleason.gleason` | âœ… |
| QB10 | Nonvacuity: `pureStateEstimationRule` (proved directly, without Busch), exact qubit witnesses | âœ… |
| QB11 | Bridge to Naimark: `EffectPerspective.toPOVM`, dilated projective realization (`naimark`/`naimark_born`/`naimark_projective_form`), a pure integration layer | âœ… |

## Milestones â€” HistoriesKent

| Milestone | Content | Status |
|-----------|--------------------------------------------------------------------------------------------------|--------|
| K0 | Skeleton (History, chainOp, decFunctional, IsConsistent, Nonvacuity) | âœ… |
| K1 | General lemmas: decFunctional_last_stage_orthogonal, histProb_additivity_two_stage | âœ… |
| K2 | Explicit Kent witness in H 3 (Witness.lean), S_consistent | âœ… |
| K3 | inference, final theorem contrary_inferences (tag v1.0-histories) | âœ… |

## Milestones â€” Complexity

| Milestone | Content | Status |
|---|---|---|
| C0 | Finite circuits of unitary gates supported on at most two sites | âœ… |
| C1 | Commutation away from the support and zero cross amplitude | âœ… |
| C2 | Independent counting and exact bound `R â‰¤ 2 * C.length` | âœ… |
| C3 | Exact proxy predicates, normalized branches, and relational certificates | âœ… |
| C4 | Interference lower bound `ceilHalf R` from redundant records | âœ… |
| C5 | Distinguishability upper bound from a supplied exact record phase flip | âœ… |
| C6 | Subtraction-free proxy gap and `WithTop â„•` minima | âœ… |
| C7 | Exact transport and conditional persistence under finite reversible circuits | âœ… |
| C8 | Approximate records, quantitative bounds, and conditional persistence | âœ… |
| C9 | Explicit repetition model, concrete circuits, and linear proxy gap | âœ… |
| C10 | Explicit **noisy** repetition model (`leak â‰  0`), robust separation | âœ… |
| C11 | **Unitary** local-circuit generation of source-record branches | âœ… |
| C12 | Finite-dimensional **operator-norm** bridge to the C8â€“C11 pointwise readout hypotheses | âœ… |
| C13 | Robust gap persistence under **simulated evolution**, with a mandatory threshold margin | âœ… |
| C14 | **Record-induced Born bridge**: Riedel's branch decomposition + the Grain Coherence Theorem | âœ… |
| C15 | Uniqueness `W = c â€–P_R Î¨â€–Â²` on admissible record situations under stability, internal equivalence, and binary saturation | âœ… |
| C17 | First quantitative stability theorem for C15 weights under projected-component perturbations, with pointwise, `LÂ¹`, and uniform bounds | âœ… |
| C17b | Stability bridges to fixed sectors, C12 operator norm, C13 simulation, and explicitly matched C14 branch weights | âœ… |

## Main theorems â€” reference table

| Theorem | Informal statement | Reference | File (lines) | Status | Tag |
|---|---|---|---:|---|---|
| naimark | Every finite POVM dilates to a projection-valued measure under an isometry | Watrous Thm 2.42 | Naimark/Main.lean (157) | 0 sorry, 0 axioms | v2.0-naimark |
| naimark_born | The Born formula is preserved by this dilation | Watrous Thm 2.42 | Naimark/Main.lean (157) | 0 sorry, 0 axioms | v2.0-naimark |
| exists_unitary_extension / naimark_projective_form | The dilation isometry extends to a global unitary (ancilla form) | Paris Â§3.2 Thm 4 / Watrous Cor. 2.43 | Naimark/Unitary.lean (210) | 0 sorry, 0 axioms | v2.0-naimark |
| wigner | Every transformation preserving \|âŸ¨Ï†\|ÏˆâŸ©\|Â² is induced by a unitary or antiunitary, without a bijectivity hypothesis | Bargmann 1964 Â§1â€“Â§5 | Wigner/Main.lean (399) | 0 sorry, 0 axioms | v1.0-wigner |
| exclusivity | The same T cannot be compatible with both a unitary and an antiunitary equivalence (n â‰¥ 2) | Bargmann 1964 Â§1.5 | Wigner/Uniqueness.lean (439) | 0 sorry, 0 axioms | v2.0-wigner |
| U_alt_eq_smul | U is unique up to a global phase relative to the choice of representative of eImg (restricted version) | Bargmann 1964 Â§6 (restricted) | Wigner/Uniqueness.lean (439) | 0 sorry, 0 axioms | v2.0-wigner |
| uhlhorn_finite_dim | In dimension n â‰¥ 3, preserving orthogonality in one direction only (neither injectivity nor surjectivity) suffices to be a Wigner symmetry | Å emrl 2021, arXiv:2106.06182, Cor. 1.2 | Uhlhorn/Assembly.lean (111) | 0 sorry, 0 axioms | v1.0-uhlhorn |
| grainCoherenceTheorem | Under (Grain)+(Norm)+(Pos)+(Null), the value of an estimation rule on a cell is the Born rule (âˆ‘áµ¢â€–âŸ¨v,fáµ¢âŸ©â€–Â²) | Gleason 1957 (underlying theorem) | BornRule/Assembly.lean (215) | 0 sorry, 0 axioms | v2.0-bornrule |
| grainCoherenceTheorem_projector | Projector-notation version of the preceding theorem (Est D c = â€–projL c vâ€–Â²), with no additional independent mathematical content | Corollary of grainCoherenceTheorem | BornRule/Assembly.lean | 0 sorry, 0 axioms | â€” |
| EffectPerspectives.projectionEffect_weight_eq_born | Under effect nonvacuity and state-relative null support, the weight of a projection effect equals the Born weight â€–A.starProjection Ïˆâ€–Â², in arbitrary finite dimension n â‰¥ 1 | Busch 2003, PRL 91, 120403 | BornRule/EffectPerspectives/Main.lean | 0 sorry, 0 axioms | â€” |
| EffectPerspectives.qubit_projectionEffect_weight_eq_born | Explicit dimension-two (qubit) corollary of the preceding theorem, without invoking Gleason.gleason | Busch 2003 (specialized n = 2) | BornRule/EffectPerspectives/Qubit.lean | 0 sorry, 0 axioms | â€” |
| contrary_inferences | Two consistent history sets sharing preparation and postselection can imply two orthogonal propositions with certainty | Kent 1997, PRL 78, 2874, arXiv:gr-qc/9604012 | HistoriesKent/ContraryInferences.lean (162) | 0 sorry, 0 axioms | v1.0-histories |
| regions_card_le_two_mul_circuit_length_of_cross_amplitude_ne_zero | `R` exact disjoint records and a nonzero cross amplitude imply `R â‰¤ 2 * C.length` | Finite counting + Riedel records | Complexity/Main.lean (63) | 0 sorry, 0 axioms | â€” |
| redundant_records_give_interference_lower_bound | Every circuit satisfying the exact proxy has length at least `ceilHalf R` | Exact proxy + C2 in both orientations | Complexity/RecordInterferenceBound.lean (96) | 0 sorry, 0 axioms | â€” |
| record_phase_flip_gives_distinguishability_upper_bound | A circuit implementing `2 P_j - I` distinguishes normalized branches at threshold `Î´ â‰¤ 1` | Exact record readout | Complexity/RecordDistinguishability.lean (114) | 0 sorry, 0 axioms | â€” |
| redundant_records_give_proxy_gap_certificate | `D.length + g â‰¤ ceilHalf R` certifies a proxy gap of at least `g` | Composition of C4/C5 certificates | Complexity/BranchGap.lean (50) | 0 sorry, 0 axioms | â€” |
| redundant_records_complexity_gap | The same gap holds for exact `WithTop â„•` minima | Infimum of circuit lengths | Complexity/MinComplexity.lean (180) | 0 sorry, 0 axioms | â€” |
| redundant_records_gap_persists_under_reversible_evolution | The record gap persists under `D.length + 2 * overhead + g â‰¤ ceilHalf R` | Exact transport by an inverse circuit pair | Complexity/RecordPersistence.lean (104) | 0 sorry, 0 axioms | â€” |
| redundant_records_gap_persists_under_circuit_evolution | The canonical inverse specializes the budget to `D.length + 4 * E.length + g â‰¤ ceilHalf R` | Canonical local inverse + preceding theorem | Complexity/RecordPersistence.lean (104) | 0 sorry, 0 axioms | â€” |
| norm_cross_amplitude_le_of_untouched_approx_record | An untouched approximate record bounds its cross amplitude by `Î·` | Projector/defect split + Cauchyâ€“Schwarz | Complexity/ApproxRecordInterference.lean (132) | 0 sorry, 0 axioms | â€” |
| approximate_records_give_interference_lower_bound | `Î·i + Î·j < 2Î´` forces length at least `ceilHalf R` | Robust bound + C2 counting | Complexity/ApproxRecordInterferenceBound.lean (123) | 0 sorry, 0 axioms | â€” |
| approx_record_phase_flip_gives_upper_bound | `2Î´ + 2Î·j + Î¾ â‰¤ 2` supplies a distinguishability witness | Explicit approximate phase readout | Complexity/ApproxRecordDistinguishability.lean (203) | 0 sorry, 0 axioms | â€” |
| approximate_records_give_proxy_gap_certificate | The robust thresholds and `D.length + g â‰¤ ceilHalf R` certify the proxy gap | C8c/C8d composition | Complexity/ApproxBranchGap.lean (152) | 0 sorry, 0 axioms | â€” |
| approximate_records_gap_persists_under_circuit_evolution | The robust gap persists under `D.length + 4 * E.length + g â‰¤ ceilHalf R` | Exact C7 transport of the C8 certificate | Complexity/ApproxRecordPersistence.lean (160) | 0 sorry, 0 axioms | â€” |
| repetition_distinguishabilityComplexity | The explicit model has `C_D = 1` | One-site reflection + exclusion of the empty circuit | Models/Repetition/Distinguishability.lean (82) | 0 sorry, 0 axioms | â€” |
| repetition_interferenceComplexity_bounds | `ceilHalf R â‰¤ C_I â‰¤ R`, hence `C_I â‰  âŠ¤` | Singleton records + explicit `R`-flip circuit | Models/Repetition/Complexities.lean (105) | 0 sorry, 0 axioms | â€” |
| repetition_has_proxy_gap | `1 + g â‰¤ ceilHalf R` certifies the explicit gap | Direct C4â€“C6 instantiation | Models/Repetition/Complexities.lean (105) | 0 sorry, 0 axioms | â€” |
| repetition_gap_persists_under_circuit | `1 + 4 * E.length + g â‰¤ ceilHalf R` preserves the gap | Direct C7 instantiation | Models/Repetition/Persistence.lean (57) | 0 sorry, 0 axioms | â€” |
| noisy_repetition_approxRecordedPairOn | Noisy records inhabit `ApproxRecordedPairOn` with exact aggregate error `2 * â€–leakâ€–` | Exact projector actions on the four configurations | Models/NoisyRepetition/Records.lean (182) | 0 sorry, 0 axioms | â€” |
| noisy_repetition_distinguishabilityComplexity | Under robust noise (`4â€–leakâ€– < 1`), `C_D = 1` at `Î´ = 1/2` | One-site exact readout + C8d threshold | Models/NoisyRepetition/Complexities.lean (89) | 0 sorry, 0 axioms | â€” |
| noisy_repetition_interference_bounds | Under robust noise, `ceilHalf R â‰¤ C_I â‰¤ R + 1` at `Î´ = 1/2` | C8c approximate records + all-bit-flip witness | Models/NoisyRepetition/Interference.lean (151) | 0 sorry, 0 axioms | â€” |
| noisy_repetition_has_proxy_gap | `1 + g â‰¤ ceilHalf R` certifies the robust gap | Direct C8e instantiation | Models/NoisyRepetition/Persistence.lean (123) | 0 sorry, 0 axioms | â€” |
| noisy_repetition_gap_persists_under_circuit | `1 + 4 * E.length + g â‰¤ ceilHalf R` preserves the robust gap | Direct C8f instantiation | Models/NoisyRepetition/Persistence.lean (123) | 0 sorry, 0 axioms | â€” |
| rationalNoiseProfile_isRobust | The rational profile `(99/101, 20/101)` is robust (`80/101 < 1`) | Pythagorean triple `99Â² + 20Â² = 101Â²` | Models/NoisyRepetition/ConcreteNoise.lean (95) | 0 sorry, 0 axioms | â€” |

â€œ0 axiomsâ€ means dependence only on
[propext, Classical.choice, Quot.sound], verified by #print axioms for
each main theorem; see the preceding section and the `#print axioms` output
kept in the assembly files.

## Dependencies

This repository pins two Lake dependencies to fixed, resolvable revisions
(lakefile.toml/lake-manifest.json), never to a floating branch:

- gleason-theorem-lean,
 rev = "v1.0-gleason" (resolved to
 876aa7390b5d831cd81415d55493a1c0c3bae31e, a fixed revision unchanged
 since Naimark). Usage expanded from Uhlhorn and reused by BornRule
 (unlike Naimark, which reuses only Gleason.IsPositiveOp, a simple Prop):
 Uhlhorn AND BornRule invoke Gleason.gleason itselfâ€”the full Gleason
 theorem, not merely a definitionâ€”as well as part of its internal machinery
 (Gleason.positive_inner_self_eq_zero, Gleason.cframe_sum_invariant,
 Gleason.ProjMeasure/bornValue/projL,
 Gleason.exists_orthonormalBasis_extension_complex,
 Submodule.starProjection_isSymmetric/re_inner_starProjection_nonneg).
 This is deliberate and expected: Uhlhorn (Å emrl's Corollary 1.2) and
 BornRule (grainCoherenceTheorem) compose Gleasonâ€”and, for Uhlhorn,
 Wignerâ€”by construction; they are not self-contained results, as explained
 in the dedicated sections above. Despite this substantially broader
 dependency, there is no transitive axiom leakage: this was confirmed
 directly by #print axioms for every theorem in this repository, including
 uhlhorn_finite_dim, which depends both on external
 Gleason.gleason and internal QuantumFoundations.Wigner.wigner, and
 grainCoherenceTheorem, which depends both on external
 Gleason.gleason and internal Uhlhorn infrastructure U2/U3a. Neither case
 introduces an additional axiom. BornRule also reuses directly from Uhlhorn
 eq_projL_of_positive_le_one_trace_one_inner_one (U2),
 exists_projMeasure_of_frameFunctionOnLines (U3a), and
 isEffect_of_isDensityOperator (moved from U3b to Uhlhorn/Defs.lean
 during B3); no Gleason/Uhlhorn content is reproved. HistoriesKent does not
 invoke Gleason.gleason or
 Gleason.projL/Submodule.starProjection directly, but inherits them
 transitively through BornRule.Perspective (the three-level chain
 HistoriesKent â†’ BornRule â†’ external Uhlhorn/Gleason). The same absence of axiom
 leakage was confirmed for contrary_inferences and the other 35 public
 declarations in the block. **BornRule/EffectPerspectives** (the qubit/Busch
 extension) reuses, within the same already-pinned revision,
 Gleason.Busch.Effects/Gleason.Busch.Main: Gleason.IsEffect,
 Gleason.EffectMeasure, and above all Gleason.busch/Gleason.busch_born_rule
 (the full Busch theorem, applied directly at a single point,
 EffectMeasure.lean, never reproved). Unlike Gleason.gleason (dimension
 â‰¥ 3), Busch applies from dimension 1 onward, which is what makes the qubit
 case (n = 2) reachable without the projective route. No dependency
 declaration was added or changed: every one of these declarations already
 existed in the pinned revision.
- mathlib, rev = "8bba4200986270d3b30be2bb2f8840af47a7854f".

./setup.sh (lake exe cache get, then lake build) reproduces the exact
repository state on a fresh clone without manual intervention. This was
tested during every closing pass (lake clean + lake exe cache get +
lake build), most recently including HistoriesKent on 2026-07-16.

## Rules

No axiom, no native_decide (blocking CI, scripts/guard.sh). Every new
hypothesis structure receives a concrete inhabitant in Nonvacuity.lean in
the same commit. Use an honest sorry rather than silently weakening a
statement; see AGENTS.md for the complete rules.

## License

Apache License 2.0.

## Module D â€” selector bridges with explicit costs

Module D formalizes bridges between the selector family and a supplied finite
tensor decomposition `D : TensorDecomposition n a`. Generic coordinate
transport remains in `QuantumFoundations.FiniteTensor.Transport`; the
selector corollaries are layered above it, so `FiniteTensor/Main.lean`
does not import selector bridges.

For the isotropic selector, the reduced system state is

`Tr_A[rho_t^(na)(psi tensor eta)] =
  t P_psi + (1-t)/(na-1) (a I - P_psi)`.

Tensor multiplicativity is tested with the composite parameter `t*u`.
Its three scalar equations classify all admissible pairs as either
`(t,u)=(1,1)` (Born/pure) or `(t,u)=(1/n,1/a)` (maximally mixed).
For equal dimensions this gives `t in {1,1/d}`. If the composite uses
the same parameter `t`, the diagnostic theorem strengthens this to
`t=1`.

The maximally mixed branch is multiplicative and covariant but fails NSNC1,
so multiplicativity does not by itself select Born. Ancilla neutrality of
the isotropic family pins `t=1`, relative to the supplied decomposition
`D`. It is not identified with Module C residual neutrality, no preferred
factorization is derived, and no unproved equivalence with NSNC1 is claimed.
