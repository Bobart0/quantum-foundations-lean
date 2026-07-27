# Release Notes — v1.0.2-fop-companion

**Release title:** One State, Many Perspectives — Lean formal companion v1.0.2  
**Tag:** `v1.0.2-fop-companion`  
**Base:** `v1.0.1-fop-companion`  
**Release date:** 2026-07-27  
**Release commit:** resolved by the annotated tag `v1.0.2-fop-companion`

## Release scope

This is a corrective documentation and metadata release relative to
`v1.0.1-fop-companion`. No proof, definition, theorem signature, or
mathematical hypothesis has changed.

## Corrections

- `BornRule.Perspective.lemma4_noncontextual` is documented precisely:
  `AxGrain` establishes context independence for proper nonzero cells, while
  `AxNorm` fixes the exceptional top cell. Context independence is derived,
  rather than postulated separately.
- The theorem-map entry gives exactly those dependencies and does not claim
  that `AxPos` or `AxNul` is required by `lemma4_noncontextual` itself. It
  also records that this lemma does not by itself derive the numerical Born
  weight.
- The documentation of `BranchesRiedel.riedel` now distinguishes the
  theorem's canonical record-`0` diagonal and uniqueness clauses from the
  separately proved invariance of constructed branch vectors under admissible
  redundant-record choices.

## Files modified relative to the base

- `QuantumFoundations/BornRule/Perspective.lean`
- `QuantumFoundations/BranchesRiedel/Induction.lean`
- `docs/FOP_THEOREM_MAP.md`
- `CITATION.cff`
- `.zenodo.json`
- `README.md`
- `docs/REPRODUCIBILITY.md`
- `RELEASE_NOTES_v1.0.2-fop-companion.md`

## Validation

- `lake build QuantumFoundations`: success.
- `lake env lean QuantumFoundations/Audit/FoP.lean`: success; audited
  declarations use only `[propext, Classical.choice, Quot.sound]`.
- Source guard: `AXIOM_HITS=0`, `NATIVE_DECIDE_HITS=0`, `SORRY_COUNT=0`.
  The repository's documented PowerShell-equivalent guard reported pass;
  its Bash wrapper was unavailable in the release environment.
- `git diff --check`: clean.

There are no unresolved `sorry` occurrences, no `native_decide` calls, and
no project-specific `axiom` declarations in the guarded source tree.

## Dependencies unchanged

- Lean toolchain: `leanprover/lean4:v4.32.0-rc1`
- `mathlib`: `8bba4200986270d3b30be2bb2f8840af47a7854f`
- `gleason` (`gleason-theorem-lean`):
  `876aa7390b5d831cd81415d55493a1c0c3bae31e` (tag `v1.0-gleason`)

No dependency revision or toolchain version changed.
