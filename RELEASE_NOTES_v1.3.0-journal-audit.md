# Release notes — v1.3.0-journal-audit

**EN.** Release notes for the coordinated pre-journal audit release, the
second (middle) link of the `gleason-theorem-lean →
quantum-foundations-lean → everettian-probability-lean` chain.

## Identification

- Selected release tag: `v1.3.0-journal-audit`
- Starting commit SHA (before this release's changes):
  `cbeb10ccdea2269b35e8d2d23faaf8e1459b71cf`
- Upstream `gleason` dependency: tag `v1.1.0-journal-audit`, resolved commit
  `5c5bc40d2e4a31a0d1b3112fcc9a3e92b2000ec5` (both the requested `rev` in
  `lakefile.toml` and the resolved `rev` in `lake-manifest.json` match this
  commit exactly)
- Lean toolchain: `leanprover/lean4:v4.32.0-rc1`
- Mathlib commit: `8bba4200986270d3b30be2bb2f8840af47a7854f` (unchanged by
  this release)

The final tagged commit's own SHA is intentionally not recorded here, since
this file is itself part of the commit that produces it; see the execution
report for that value.

## Corrected claim scope: proper-cell vs. full non-contextuality

This section records the historical split audited by v1.3.0. The corrective
release v1.3.1 supersedes its former premise analysis: Grain coherence alone
now proves full context independence, including the degenerate whole-space
cell. The c = ⊤ branch identifies both perspectives as the same singleton
perspective using Perspective.eq_of_cells.

The public declarations are now:

- lemma4_noncontextual_of_ne_top: the original proper-cell geometric proof
  through a binary perspective, from AxGrain alone;
- lemma4_noncontextual_grain_only: the full theorem, from AxGrain alone;
- lemma4_noncontextual: a compatibility wrapper retaining the historical
  AxNorm argument, which is not used by the context-independence proof.

Normalization remains required downstream to obtain normalized projective
weights and the condition μ ⊤ = 1.

## New focused publication audit

`QuantumFoundations/Audit/JournalCore.lean`: `#check`s the public contract
and runs `#print axioms` on `lemma4_noncontextual_of_ne_top`,
`lemma4_noncontextual`, `E₀_satisfies_axioms`, `grainCoherenceTheorem`, and
`grainCoherenceTheorem_projector`. Added to `.github/workflows/lean.yml`
alongside the existing `FoP.lean` and `DownstreamAPI.lean` audits (neither
removed nor weakened).

## Trust boundary

Expected for the five declarations above and for the pre-existing `FoP.lean`
/ `DownstreamAPI.lean` audits:

```
[propext, Classical.choice, Quot.sound]
```

No project-specific axiom, no `sorry`, no `native_decide`.

## Verification commands

```bash
lake exe cache get
lake build QuantumFoundations
bash scripts/guard.sh
lake env lean QuantumFoundations/Audit/JournalCore.lean
lake env lean QuantumFoundations/Audit/FoP.lean
lake env lean QuantumFoundations/Audit/DownstreamAPI.lean
git diff --check
```
