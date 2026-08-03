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

**EN.** The public theorem `QuantumFoundations.BornRule.lemma4_noncontextual`
establishes non-contextuality of the estimation rule on *every* cell,
including the degenerate whole-space cell `⊤`, and for that it needs both
`AxGrain` (Grain) and `AxNorm` (Norm). Prior documentation (notably
`docs/FOP_THEOREM_MAP.md`) stated that this full result followed from
`AxGrain` alone, which is imprecise: inspection of the existing proof shows
the `c = ⊤` branch uses `AxNorm`, while the `c ≠ ⊤` branch never uses it.

This release makes that split explicit and public:

- **New theorem** `QuantumFoundations.BornRule.lemma4_noncontextual_of_ne_top`
  (`QuantumFoundations/BornRule/Perspective.lean`): non-contextuality of a
  **proper** cell (`c ≠ ⊤`), derived from `AxGrain` **alone** — it does not
  take `AxNorm`. This is exactly the argument already present in the
  `c ≠ ⊤` branch of the previous proof, extracted as its own public
  declaration.
- **Refactored** `QuantumFoundations.BornRule.lemma4_noncontextual`: same
  public signature as before (`hA : AxGrain Est`, `hN : AxNorm Est`, same
  implicit/explicit arguments); the `c = ⊤` case still uses `hN`, and the
  `c ≠ ⊤` case is now delegated entirely to
  `lemma4_noncontextual_of_ne_top`. No existing caller's type changes
  (`BornRule.Assembly.grainCoherenceTheorem`,
  `BornRule.GleasonBridge.g_isFrameFunctionOnLines`).

Authorized wording (used verbatim in the corrected documentation):

> Grain coherence alone yields context independence for proper cells. Full
> context independence, including the degenerate whole-space cell, follows
> from Grain together with normalization.

Corrected in `docs/FOP_THEOREM_MAP.md` (split into two theorem-map entries)
and `MILESTONES.md` (B1 milestone bullet). No other tracked overstatement of
this scope was found by a repository-wide search for the relevant phrasing.

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
