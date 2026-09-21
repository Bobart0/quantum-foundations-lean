# AFM reviewer artifact guide

This file is the reviewer-facing entry point for the manuscript

> *Finite-dimensional quantum probability and symmetry in Lean 4:
> representation, rigidity, and dimension-two boundaries*.

The article is a focused study of the representation / rigidity / refinement
core of a larger three-repository library.  It is not a duplicate of the
broader August 2026 preprint *A Layered Lean 4 Library for Finite-Dimensional
Quantum Foundations with Typed Premise Auditing* (DOI
`10.21203/rs.3.rs-10617850/v1`), which surveys additional record,
complexity, selector, decision-theoretic, and premise-audit material that is
outside the AFM manuscript.

## Frozen artifacts used by the manuscript

| Layer | Release | Commit | Role in the AFM article |
| --- | --- | --- | --- |
| `gleason-theorem-lean` | `v1.1.1-afm-final` | `cd88c1d658eab2a8c47e950025547ae79c8852ce` | Busch and Gleason representation theorems; documentation-only finalization relative to v1.1.0 |
| `quantum-foundations-lean` | `v1.4.2-afm-final` | immutable tag target; full SHA recorded in the article | Wigner, Uhlhorn--Semrl, perspective/effect routes, binary refinements, Naimark |
| `everettian-probability-lean` | `v2.4.0-journal-audit` | `b027ee9cd310514ddb33b9c8af8b35a24cbe5d7f` | dimension-two and deletion witnesses |

The QF AFM release line changes no theorem body relative to
`v1.4.0-journal-audit`. Version `v1.4.2-afm-final` freezes the final reviewer
guide, exact AFM audit surface, reproduction entry point, and publication
metadata. The article records the version-specific Zenodo DOI once minted.

## Exact QF-side audit

Run from a clean checkout of the AFM release:

```sh
bash scripts/verify_afm.sh
```

The script builds `QuantumFoundations`, runs
`QuantumFoundations/Audit/AFM.lean`, executes the no-axiom/no-sorry source
guard, and performs diff hygiene checks.

`QuantumFoundations/Audit/AFM.lean` includes `#print axioms` for the exact
principal Gleason/Busch and QF declarations used by the article, including
the two interfaces that were not covered by the older manuscript audits:

- `QuantumFoundations.BornRule.EffectPerspectives.projectionEffect_weight_eq_born`;
- `QuantumFoundations.Naimark.BinaryImpl.strictIso_iff_residualDims_eq`.

The expected output for every audited theorem contains only the ordinary
Lean/Mathlib logical dependencies `propext`, `Classical.choice`, and
`Quot.sound`.

## Downstream witnesses

The EP repository cannot be imported by QF without creating a dependency
cycle.  Its AFM-relevant declarations are already part of the consolidated
audit

```sh
lake env lean EverettianProbability/Audit/JournalCore.lean
```

including:

- `grain_does_not_imply_born_at_two`;
- `skewProjMeasure_not_representable`;
- `dimensionTwo_orthogonality_not_injective`;
- `w1_remove_axNorm`, `w2_remove_axNul`, `w3_remove_unit_norm`,
  `w4_remove_axGrain`, and `w5_remove_axPos`;
- `axNorm_iff_singletonTop_of_axGrain`.

## Manuscript-to-declaration map

The manuscript itself contains a declaration index with immutable GitHub
permalinks.  The principal QF declarations audited here are:

| Manuscript role | Lean declaration |
| --- | --- |
| Wigner theorem | `QuantumFoundations.Wigner.wigner` |
| Projective Wigner bridge | `QuantumFoundations.Uhlhorn.wigner_projection_form` |
| One-directional Uhlhorn--Semrl | `QuantumFoundations.Uhlhorn.uhlhorn_finite_dim` |
| Context independence from Grain | `QuantumFoundations.BornRule.lemma4_noncontextual_grain_only` |
| Projective Born representation | `QuantumFoundations.BornRule.grainCoherenceTheorem_projector` |
| Binary generation of refinements | `QuantumFoundations.BornRule.refinement_binaryGenerated` |
| Binary-split Born calibration | `QuantumFoundations.BornRule.splitRCBornCalibration_projector` |
| Effect-route Born value | `QuantumFoundations.BornRule.EffectPerspectives.projectionEffect_weight_eq_born` |
| Qubit specialization | `QuantumFoundations.BornRule.EffectPerspectives.qubit_contextual_projection_weight_eq_born` |
| Naimark dilation | `QuantumFoundations.naimark` |
| Strict binary-implementation classification | `QuantumFoundations.Naimark.BinaryImpl.strictIso_iff_residualDims_eq` |

## Scope of the release

This release is publication-facing packaging and audit infrastructure.  It
does not strengthen or alter the mathematical statements in the v1.4.0
scientific tree.  In particular, it should not be read as a new priority
claim for Wigner or Naimark; the AFM manuscript explicitly compares the
independent Lean developments known at the article's release date.
