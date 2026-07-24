# Release Notes — v1.0-fop-companion

**Release title:** One State, Many Perspectives — Lean formal companion
**Tag:** `v1.0-fop-companion`
**Release branch:** `release/fop-companion-v1`, merged into local `master`

## Release scope

This release integrates every completed, manuscript-relevant Lean 4 /
Mathlib development in this repository into a single, reproducible,
publication-facing artifact: the formal companion to the manuscript *One
State, Many Perspectives: Branch Structure and Born Weights in Everettian
Quantum Mechanics*, submitted to *Foundations of Physics*.

It is an integration and editorial release. No theorem statement,
definition, proof body, or mathematical assumption of any previously
validated milestone was changed; only documentation, citation and
archival metadata, a consolidated axiom-audit module, and repository
presentation were added or revised.

## Integrated milestones

Ancestry analysis (`git merge-base --is-ancestor`) confirmed that every
completed local branch except the explicitly archived experiment
`effect-perspectives-qubit-antigravity` was already a linear ancestor of
`quantitative-stability-bridges-c17b`. Consequently, integration required
a single non-fast-forward merge of that branch into a release branch cut
from local `master`, rather than separate merges per line of work. The
integrated milestone chain, in dependency order:

- **Naimark** (N0–N5): finite-dimensional Naimark dilation, its Born-rule
  corollary, and the optional unitary/ancilla form.
- **Wigner** (W0–W6-partial): Wigner's theorem without a bijectivity
  hypothesis, and the exclusivity/uniqueness corollaries.
- **Uhlhorn** (U0–U5): Uhlhorn-type uniqueness (Šemrl's Corollary 1.2).
- **BornRule** (B1–B4 and Nonvacuity): the Grain Coherence Theorem,
  connecting Gleason's theorem to a Born-weight representation.
- **HistoriesKent** (K0–K3): Kent's contrary-inferences construction, a
  conceptual contrast to the branch-theoretic development.
- **BranchesRiedel** (R0–R5) and **Complexity** (C0–C13): Riedel's
  branch-decomposition theorem, redundant-record interference-complexity
  lower bounds, and their robust (noisy-record) and dynamical
  (simulated-evolution) persistence extensions.
- **BranchesRiedel.BornBridge** (C14): the record-induced Born-weight
  connection theorem.
- **BornRule.EffectPerspectives** (QB1–QB11): an independent, effect-based
  route to the Born rule via Busch's theorem, reaching the qubit case
  (`n = 2`), and its Naimark projective realization.
- **BornRule.RestrictedRecordSectors** (C15, C17, C17b): restricted-sector
  quadratic uniqueness (formalizing Lela's theorem), its first
  quantitative weight-stability extension, and state/operator-norm/
  simulated-evolution/branch stability bridges.

See `docs/FOP_THEOREM_MAP.md` for the exact per-theorem correspondence and
`MILESTONES.md`/`ARCHITECTURE_NOTES.md` for the full milestone-by-milestone
development history.

## Principal theorem groups

- **Grain coherence → context independence → Born representation**
  (`BornRule`).
- **Unitary record formation → Riedel branch uniqueness → record-induced
  branch cells → C14 Born weights** (`BranchesRiedel`).
- **Redundant records → complexity separation → robust and dynamical
  persistence** (`Complexity`).
- **Restricted record sectors → C15 quadratic uniqueness → C17
  quantitative weight stability → C17b state/operator/simulation/branch
  bridges** (`BornRule.RestrictedRecordSectors`).
- **Effect perspectives → context independence → effect additivity →
  Busch qubit representation → Naimark projective realization**
  (`BornRule.EffectPerspectives`).

## Known-result formalizations (attribution)

Gleason's theorem, Busch's generalized-measurement representation
theorem, and the Naimark dilation theorem are formalized as reused
dependencies or direct formalizations, not claimed as original results of
this program. Riedel's branch-decomposition theorem, Kent's
contrary-inferences construction, Wigner's theorem, and Uhlhorn-type
uniqueness (Šemrl's Corollary 1.2) are likewise formalizations of known
results, integrated into this repository's dependency graph. See
`docs/FOP_THEOREM_MAP.md` for the exact status of each.

## Connection theorems

`grainCoherenceTheorem` (composing Gleason's theorem with internal Uhlhorn
infrastructure), `record_induced_Born_decomposition` (composing Riedel's
decomposition with the Grain Coherence Theorem), the
`BornRule.EffectPerspectives` construction of Busch's required effect
measure from effect-perspective refinement coherence, and the C17b
stability bridges (composing C17 with the `Complexity` operator-norm and
simulated-evolution infrastructure) are connection theorems: each composes
previously separate developments without reproving either side.

## C15 attribution

**EN.** The C15 development formalizes and integrates the restricted-sector
uniqueness theorem of Lela. No independent priority claim is made for the
underlying uniqueness theorem.

**FR.** Le développement C15 formalise et intègre le théorème d'unicité
sur les secteurs restreints de Lela. Aucune revendication de priorité
indépendante n'est formulée pour le théorème d'unicité sous-jacent.

## Reduced C17 scope

C17 (`restricted_record_sector_weight_uniform_stability`) establishes that
projected-component proximity implies quantitative Born-weight proximity
on a restricted record sector. It is presented as the first quantitative
weight-stability result *within this formal development*, without an
unrestricted historical priority claim. It does not establish stability of
the C15 uniqueness conclusion under approximate versions of the C15
hypotheses, approximate branch uniqueness, or a physical derivation of
component proximity. See `docs/SCOPE_AND_LIMITATIONS.md`.

## C17b integration scope

C17b extends C17 with an explicit state-level stability bridge, an
operator-norm bridge, a simulated-circuit-evolution bridge
(`sector_weight_stability_under_circuit_simulation`), and a connection to
record-induced branch weights
(`recordBranch_weight_pointwise_stability`). It remains subject to the
same scope limitations as C17.

## Deferred C16

C16, as referenced in `MILESTONES.md`, is not part of this release and
remains open. See `docs/SCOPE_AND_LIMITATIONS.md`.

## Build and audit summary

Recorded at the release commit (see also `docs/REPRODUCIBILITY.md` for
exact reproduction commands):

- `lake build QuantumFoundations`: **success**.
- `lake env lean QuantumFoundations/Audit/FoP.lean`: **success**; all 17
  audited declarations depend only on `[propext, Classical.choice,
  Quot.sound]` (the standard Lean/Mathlib kernel trio; no project-specific
  axioms).
- Source guard (both the shell script and its PowerShell reproduction):
  zero project-specific axiom declarations, zero `sorry`, zero
  `native_decide` across the entire `QuantumFoundations/` tree.
- `git diff --check`: clean.

## Generated repository statistics (at the release commit)

Computed via the reproducible commands in `docs/REPRODUCIBILITY.md`
(`find QuantumFoundations -name "*.lean" | wc -l`, and analogous `grep`
counts for declarations):

- Lean source files under `QuantumFoundations/`: 142
- Total lines across those files: 22,113
- `theorem`/`lemma` declarations: 740
- `def`/`abbrev` declarations: 233
- `structure` declarations: 20
- Tracked top-level Markdown documents: `README.md`, `ARCHITECTURE_NOTES.md`,
  `MILESTONES.md`, `AGENTS.md`, plus the new `docs/FOP_THEOREM_MAP.md`,
  `docs/REPRODUCIBILITY.md`, `docs/SCOPE_AND_LIMITATIONS.md`,
  `docs/IMPLEMENTATION_NOTES.md`, `docs/AI_ASSISTANCE.md`, and this file.

## Exact release tag

`v1.0-fop-companion`, an annotated tag on the final `master` commit
produced by merging `release/fop-companion-v1`.

## Exact dependency revisions

- Lean toolchain: `leanprover/lean4:v4.32.0-rc1`
- `mathlib`: `8bba4200986270d3b30be2bb2f8840af47a7854f`
- `gleason` (`gleason-theorem-lean`): `876aa7390b5d831cd81415d55493a1c0c3bae31e`
  (tag `v1.0-gleason`)

No dependency revision was changed as part of this release.

## Résumé en français

Cette version intègre l'ensemble des développements Lean 4 / Mathlib
achevés et pertinents pour le manuscrit dans une seule version
reproductible : le compagnon formel du manuscrit *One State, Many
Perspectives: Branch Structure and Born Weights in Everettian Quantum
Mechanics*, soumis à *Foundations of Physics*. Il s'agit d'une version
d'intégration et de révision éditoriale : aucun énoncé de théorème,
aucune définition, aucun corps de preuve et aucune hypothèse mathématique
d'un jalon déjà validé n'a été modifié ; seules la documentation, les
métadonnées de citation et d'archivage, un module d'audit des axiomes
consolidé, et la présentation du dépôt ont été ajoutés ou révisés. Voir
`docs/FOP_THEOREM_MAP.md`, `docs/SCOPE_AND_LIMITATIONS.md` et
`docs/REPRODUCIBILITY.md` pour le détail complet, en anglais avec des
résumés français synchronisés.
