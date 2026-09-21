# Release notes — v1.4.1-afm-audit

This is the publication-facing audit release for the Annals of Formalized
Mathematics manuscript on finite-dimensional quantum probability, symmetry,
refinement, and dimension-two boundaries.

## Scientific tree

No theorem body is changed relative to `v1.4.0-journal-audit`. The audited
scientific/documentation head is commit
`406e248ac3e77d438eaa5cb4c9459b4489f20b0a`.

The mathematical additions of v1.4.0 (binary refinement generation, the
elementary-split Born calibration theorem, and its relative sharpness
witnesses) remain byte-identical.

## AFM reviewer surface

This release adds:

- `QuantumFoundations/Audit/AFM.lean`: exact `#check` / `#print axioms`
  coverage for the principal Gleason/Busch and QuantumFoundations
  declarations used by the AFM manuscript, including
  `projectionEffect_weight_eq_born` and
  `strictIso_iff_residualDims_eq`;
- `AFM_ARTIFACT.md`: reviewer-facing paper-to-declaration and
  cross-repository map;
- `scripts/verify_afm.sh`: one-command build, AFM audit, source guard, and
  diff-hygiene check;
- CI coverage for the AFM audit;
- refreshed README and reproducibility documentation that no longer identify
  the repository as the companion of the abandoned Foundations of Physics
  manuscript.

The downstream dimension-two/deletion witnesses remain in the pinned
`everettian-probability-lean` v2.4.0 artifact and are audited there by
`EverettianProbability/Audit/JournalCore.lean`.

## Trust boundary

The expected axiom report for every theorem in the AFM QF-side audit is:

```
[propext, Classical.choice, Quot.sound]
```

The source guard separately rejects project-specific `axiom` declarations,
unresolved `sorry`, and `native_decide`.

## Dependency pins

- Lean: `leanprover/lean4:v4.32.0-rc1`
- Mathlib: `8bba4200986270d3b30be2bb2f8840af47a7854f`
- Gleason dependency: `v1.1.0-journal-audit`, commit
  `5c5bc40d2e4a31a0d1b3112fcc9a3e92b2000ec5`

## Release / Zenodo

The GitHub release tag is `v1.4.1-afm-audit`. The repository is connected
to Zenodo; publishing this GitHub release is intended to create/update the
corresponding archived software version. The immutable Git commit remains
the exact source identity used by the manuscript.
