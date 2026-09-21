# Release notes — v1.4.2-afm-final

This is the final AFM-facing publication release of the Quantum Foundations
library.

## Scientific tree

No Lean theorem body is changed relative to `v1.4.1-afm-audit`. The
pre-release documentation head `483e0269f433ab6f39a2aa1fa21fc1bce1180913` passed both the Lean and CI
workflows before this release.

The mathematical surface remains the one audited by
`QuantumFoundations/Audit/AFM.lean`, including Wigner, one-directional
Uhlhorn--Semrl, the projective and effect-perspective Born routes, binary
refinement generation and sharpness witnesses, Naimark dilation, and the
strict residual-dimension classification.

## Final publication packaging

This release freezes:

- the cleaned AFM-facing README;
- `AFM_ARTIFACT.md` with the final Gleason AFM release
  `v1.1.1-afm-final` at commit
  `cd88c1d658eab2a8c47e950025547ae79c8852ce`;
- the exact AFM audit and one-command verification path;
- final reproducibility and citation metadata;
- Zenodo metadata for software version 1.4.2.

## Dependency pins

- Lean: `leanprover/lean4:v4.32.0-rc1`
- Mathlib: `8bba4200986270d3b30be2bb2f8840af47a7854f`
- direct Gleason code dependency: `v1.1.0-journal-audit`, commit
  `5c5bc40d2e4a31a0d1b3112fcc9a3e92b2000ec5`

The version-specific Zenodo DOI is minted by the connected Zenodo integration
after publication of this GitHub Release and is recorded in the AFM article.
