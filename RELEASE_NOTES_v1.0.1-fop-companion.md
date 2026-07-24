# Release Notes — v1.0.1-fop-companion

**Release title:** One State, Many Perspectives — Lean formal companion v1.0.1
**Tag:** `v1.0.1-fop-companion`
**Relative to:** `v1.0-fop-companion`

## Release scope

**v1.0.1 is a corrective release.** It contains **no mathematical
changes** relative to `v1.0-fop-companion`: no theorem statement, no
definition, no proof body, no mathematical assumption, no dependency
revision, and no Lean version changed. It is limited to documentation,
citation/archival metadata, the source guard script, the theorem-map
scope wording, and continuous-integration tooling.

## What changed

- **Removed inaccurate editorial-status wording from permanent metadata
  and publication-facing documents.** `CITATION.cff`, `.zenodo.json`,
  `README.md`, and `RELEASE_NOTES_v1.0-fop-companion.md` (the historical
  v1.0 notes) stated that the manuscript *One State, Many Perspectives:
  Branch Structure and Born Weights in Everettian Quantum Mechanics* had
  been "submitted to *Foundations of Physics*". That was not accurate at
  the time it was written, and remains not accurate now. All occurrences
  were corrected to neutral, stable wording (the repository is the formal
  companion to the manuscript, prepared for that journal) with no
  journal-workflow status claimed in permanent citation metadata.
- **Synchronized `CITATION.cff` and `.zenodo.json` at version 1.0.1**,
  with a consistent title, creator (Bertrand Dalimier, Independent
  Researcher, ORCID 0009-0000-2457-375X), repository URL, license
  (Apache-2.0), and keyword list. No DOI was inserted in either file; none
  exists yet, and none will until Zenodo mints one from the published
  GitHub Release.
- **Corrected `scripts/guard.sh`** to report `AXIOM_HITS`,
  `NATIVE_DECIDE_HITS`, and `SORRY_COUNT` explicitly and to emit
  `GUARD_RESULT=PASS`/`FAIL`, matching the existing PowerShell-equivalent
  guard's output format exactly, so the two implementations are directly
  comparable. The script's scan targets (`QuantumFoundations` and
  `QuantumFoundations.lean`) were re-verified against the current
  integrated source tree and found already correct; only the reporting
  format needed correction. `set -euo pipefail` robustness against the
  historical no-match/pipefail early-exit bug was re-verified and
  preserved.
- **Corrected the C15/C17 scope wording in `docs/FOP_THEOREM_MAP.md`.**
  The C15 entry previously contained a parenthetical ("does not establish
  stability under approximate versions of those hypotheses — that is C17,
  below") that could be misread as implying C17 *does* establish
  stability of the C15 uniqueness conclusion under approximate hypotheses.
  It does not. The C15, C17, C17b, and record-branch-bridge entries now
  state explicitly and consistently that these theorems prove *projected-
  component proximity implies quantitative weight proximity*, and do not
  prove: approximate refinement stability implying an approximately
  quadratic law; approximate binary saturation implying approximate
  uniqueness; approximate matching or uniqueness of branch decompositions;
  a physical derivation of projected-component proximity; or persistence
  of record selection under arbitrary dynamics.
- **Added a reproducible GitHub Actions workflow**
  (`.github/workflows/lean.yml`) running on push to `master`, on pull
  requests targeting `master`, and on manual dispatch: checkout,
  `leanprover/lean-action@v1`, `lake build QuantumFoundations`, the
  consolidated axiom audit, the source guard, and `git diff --check`. It
  relies exclusively on the toolchain and dependency revisions already
  pinned in `lean-toolchain` and `lake-manifest.json` and never updates
  them.
- **Small consistency updates strictly required by the above:**
  `README.md` and `docs/REPRODUCIBILITY.md` now recommend
  `v1.0.1-fop-companion` as the immutable release to build from, and
  reference `RELEASE_NOTES_v1.0.1-fop-companion.md` for the recorded audit
  output; the citation version string was updated from 1.0.0 to 1.0.1 in
  both places it appeared in `README.md`; `docs/REPRODUCIBILITY.md`'s
  description of the shell guard's expected output was updated to match
  its corrected reporting format.

## Explicitly unchanged

- No theorem statement changed.
- No definition changed.
- No proof body changed.
- No mathematical assumption changed.
- No dependency revision changed (`mathlib`
  `8bba4200986270d3b30be2bb2f8840af47a7854f`; `gleason-theorem-lean`
  `876aa7390b5d831cd81415d55493a1c0c3bae31e`, tag `v1.0-gleason`).
- No Lean version changed (`leanprover/lean4:v4.32.0-rc1`).
- No public declaration name, namespace, or import structure changed.

## Historical record preserved

The `v1.0-fop-companion` tag and `RELEASE_NOTES_v1.0-fop-companion.md` are
preserved unchanged in git history; the corrective release adds a visible
editorial note to the latter rather than silently altering the historical
record. No git history was rewritten, and no existing tag was moved,
deleted, or recreated.

## Build and audit summary

Recorded at the release commit:

- `lake build QuantumFoundations`: **success**, 8803 jobs.
- `lake env lean QuantumFoundations/Audit/FoP.lean`: **success**; all 17
  audited declarations depend only on `[propext, Classical.choice,
  Quot.sound]`.
- Source guard (`scripts/guard.sh`, corrected) and its PowerShell
  reproduction: both report `AXIOM_HITS=0`, `NATIVE_DECIDE_HITS=0`,
  `SORRY_COUNT=0`, `GUARD_RESULT=PASS`.
- `git diff --check`: clean.

## Exact dependency revisions

- Lean toolchain: `leanprover/lean4:v4.32.0-rc1`
- `mathlib`: `8bba4200986270d3b30be2bb2f8840af47a7854f`
- `gleason` (`gleason-theorem-lean`): `876aa7390b5d831cd81415d55493a1c0c3bae31e`
  (tag `v1.0-gleason`)

No dependency revision was changed as part of this corrective release.

## Résumé en français

La version 1.0.1 est une **version corrective** : elle ne contient
**aucun changement mathématique** par rapport à `v1.0-fop-companion`.
Elle corrige une mention inexacte du statut éditorial du manuscrit
(« soumis à *Foundations of Physics* », inexact) dans les métadonnées
permanentes et les documents de publication ; synchronise `CITATION.cff`
et `.zenodo.json` à la version 1.0.1, sans DOI (aucun n'existe encore) ;
corrige le format de sortie de `scripts/guard.sh` pour qu'il corresponde
exactement à la garde PowerShell équivalente ; corrige la formulation de
portée de C15/C17 dans `docs/FOP_THEOREM_MAP.md`, qui pouvait laisser
entendre à tort que C17 établit la stabilité de la conclusion d'unicité de
C15 sous hypothèses approximatives (ce n'est pas le cas) ; et ajoute un
workflow GitHub Actions reproductible. Aucun énoncé de théorème, aucune
définition, aucun corps de preuve, aucune hypothèse mathématique, aucune
révision de dépendance et aucune version de Lean n'a été modifié. L'étiquette
historique `v1.0-fop-companion` et ses notes de version restent inchangées.
