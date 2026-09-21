# Publication artifact guide

This is the reviewer-facing entry point for the article

> *Gleason's theorem along the Cooke--Keane--Moran route in Lean 4:
> Uhlhorn--Semrl and dimension-two boundaries*.

The article studies the representation / rigidity / refinement part of a
larger three-repository Lean 4 library.

## Frozen artifacts

| Layer | Release | Role |
| --- | --- | --- |
| `gleason-theorem-lean` | `v1.1.2` | Busch and Gleason representation theorems |
| `quantum-foundations-lean` | `v1.4.3` | Wigner, Uhlhorn--Semrl, perspective/effect routes, binary refinements, Naimark |
| `everettian-probability-lean` | `v2.4.1` | dimension-two and deletion witnesses |

The article records the exact tag targets, commit hashes, and Zenodo DOIs.

## Verification

```sh
bash scripts/verify_publication.sh
```

This builds `QuantumFoundations`, runs
`QuantumFoundations/Audit/PublicationCore.lean`, executes the source guard,
and checks diff hygiene. The expected trust base for the audited declarations
is `[propext, Classical.choice, Quot.sound]`.

The downstream dimension-two countermodels and deletion witnesses remain
audited by `EverettianProbability/Audit/JournalCore.lean`; that historical
filename is retained for source compatibility, while the current releases and
citation metadata are journal-neutral.

## Principal declaration map

| Mathematical role | Lean declaration |
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

Release `v1.4.3` changes no pre-existing theorem body relative to the
preceding publication snapshot. It repins the byte-identical Gleason source
through neutral tag `v1.1.2` and refreshes publication-facing audit names,
documentation, and metadata.
