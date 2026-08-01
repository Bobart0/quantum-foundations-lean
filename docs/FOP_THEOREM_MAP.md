# FoP Theorem Map

This document records, for every theorem used substantively in the
manuscript *One State, Many Perspectives: Branch Structure and Born
Weights in Everettian Quantum Mechanics*, its exact Lean declaration,
module, mathematical status, principal dependencies, dimension
assumptions, exactness, axiom-audit status, and scope limitation.

Status categories used below:

- **original result** — a theorem whose statement and proof are original
  to this formal development (not necessarily to the mathematical
  literature; see the attribution notes under each entry).
- **connection theorem** — a theorem that connects two previously
  separate developments without reproving either.
- **new reduction to a known theorem** — a theorem that reduces a new
  hypothesis or setting to an already-formalized theorem, without
  reproving that theorem.
- **formalization of a known theorem** — a direct Lean formalization of a
  theorem already established in the literature.
- **auxiliary operational theorem** — a supporting result establishing an
  operational realization, not itself a representation or weight theorem.
- **conceptual contrast** — a formalization presented to contrast with the
  branch-theoretic development, not as a premise of it.
- **nonvacuity witness** — a concrete inhabitant establishing that a
  hypothesis structure is not vacuous.

All axiom-audit statuses below were verified by `#print axioms` on the
stated declaration and read `[propext, Classical.choice, Quot.sound]`
unless otherwise noted; this is the standard Lean/Mathlib kernel trio,
not a project-specific axiom. See `docs/REPRODUCIBILITY.md` for the exact
commands and `QuantumFoundations/Audit/FoP.lean` for the consolidated
audit module.

## Grain coherence, context independence, Born representation (BornRule)

| Field | Value |
|---|---|
| Manuscript role | Context independence derived from refinement coherence; Born-rule weight representation |
| Lean declaration | `QuantumFoundations.BornRule.lemma4_noncontextual` |
| Module | `QuantumFoundations/BornRule/Perspective.lean` |
| Status | original result (context independence derived from `AxGrain` alone, not assumed) |
| Dependencies | `BornRule.Perspective`, `AxGrain`/`AxNorm`/`AxPos`/`AxNul` |
| Dimension | generic `n` |
| Exactness | exact |
| Axiom audit | standard trio |
| Scope limitation | establishes non-contextuality of the estimation rule under (Grain); does not by itself derive the numerical Born weight |

| Field | Value |
|---|---|
| Manuscript role | The Grain Coherence Theorem: Born-rule weights from (Grain)+(Norm)+(Pos)+(Null) |
| Lean declaration | `QuantumFoundations.BornRule.grainCoherenceTheorem` (and the projector-notation corollary `grainCoherenceTheorem_projector`, not an independent result) |
| Module | `QuantumFoundations/BornRule/Assembly.lean` |
| Status | original result (this development's central connection theorem), composing Gleason's theorem (external dependency) with the Uhlhorn infrastructure formalized in this repository |
| Dependencies | `Gleason.gleason` (pinned `gleason-theorem-lean` dependency), internal Uhlhorn infrastructure (U2, U3a) |
| Dimension | `n ≥ 3` (inherited from Gleason's theorem) |
| Exactness | exact |
| Axiom audit | standard trio (confirmed despite the dual external/internal dependency chain) |
| Scope limitation | requires `n ≥ 3`; does not apply to the qubit. The qubit case is reached separately, via Busch, in `BornRule.EffectPerspectives` (below) |

## Effect perspectives: context independence, effect additivity, Busch qubit representation, Naimark realization

| Field | Value |
|---|---|
| Manuscript role | Context independence and effect additivity derived from effect-perspective refinement coherence |
| Lean declaration | `QuantumFoundations.BornRule.EffectPerspectives.contextual_weight_eq_effectWeight`, `effectWeight_zero`, `effectWeight_one`, `effectWeight_add` |
| Module | `QuantumFoundations/BornRule/EffectPerspectives/ContextIndependence.lean` |
| Status | original result; derived theorems, never assumed as structure fields or axioms |
| Dependencies | `EstimationRule.grain` alone |
| Dimension | generic `n` |
| Exactness | exact |
| Axiom audit | standard trio |
| Scope limitation | derives properties of the estimation rule; does not by itself supply a numerical representation |

| Field | Value |
|---|---|
| Manuscript role | Construction of the effect measure required by Busch's representation theorem |
| Lean declaration | `QuantumFoundations.BornRule.EffectPerspectives.EstimationRule.toEffectMeasure`, `existsUnique_densityOperator`, `exists_densityOperator_projective` |
| Module | `QuantumFoundations/BornRule/EffectPerspectives/EffectMeasure.lean` |
| Status | new reduction to a known theorem (packages a contextual estimation rule into `Gleason.EffectMeasure`, then applies Busch's theorem directly, without reproving it) |
| Dependencies | `Gleason.busch`, `Gleason.busch_born_rule` (pinned dependency) |
| Dimension | `n ≥ 1` |
| Exactness | exact |
| Axiom audit | standard trio |
| Scope limitation | none beyond `n ≥ 1` |

| Field | Value |
|---|---|
| Manuscript role | The qubit Born-weight theorem |
| Lean declaration | `QuantumFoundations.BornRule.EffectPerspectives.qubit_projectionEffect_weight_eq_born` (general-dimension form: `projectionEffect_weight_eq_born`) |
| Module | `QuantumFoundations/BornRule/EffectPerspectives/Qubit.lean` (general form in `Main.lean`) |
| Status | original result (in the sense that its derivation route, through Busch's theorem and state-relative null support, is original to this development); reaches `n = 2`, where the Gleason-based `grainCoherenceTheorem` above does not apply |
| Dependencies | `Gleason.busch_born_rule`; `ContextualNullSupport`; the fallback pinning theorem `density_bornValue_eq_pure_of_null` |
| Dimension | `n = 2` (specialization of the general-dimension theorem, valid for all `n ≥ 1`) |
| Exactness | exact |
| Axiom audit | standard trio |
| Scope limitation | requires a state-relative null-support hypothesis on the estimation rule; does not invoke `Gleason.gleason` or `grainCoherenceTheorem_projector` |

| Field | Value |
|---|---|
| Manuscript role | Effect-perspective / Naimark bridge |
| Lean declaration | `QuantumFoundations.BornRule.EffectPerspectives.effectPerspective_naimark_realization`, `effectPerspective_born_preserved_under_dilation`, `effectPerspective_projective_ancilla_realization` |
| Module | `QuantumFoundations/BornRule/EffectPerspectives/NaimarkBridge.lean` |
| Status | connection theorem (a pure integration layer: every finite effect perspective is canonically a `QuantumFoundations.POVM`, then the existing Naimark dilation theorem is applied directly; no Naimark, Busch, Gleason, or effect-perspective theorem is reproved) |
| Dependencies | `QuantumFoundations.naimark`, `naimark_born`, `naimark_projective_form` |
| Dimension | generic `n` and outcome count |
| Exactness | exact (holds for every vector, not only unit vectors, in the Born-preservation statement) |
| Axiom audit | standard trio |
| Scope limitation | supplies an operational realization, not the Born rule or contextual independence; does not claim that the dilated projective measurement is the unique or physically realized implementation |

## Riedel branch decomposition and record-induced Born weights (BranchesRiedel)

| Field | Value |
|---|---|
| Manuscript role | Riedel's branch-decomposition theorem: unitary record formation induces an orthogonal branch decomposition |
| Lean declaration | `QuantumFoundations.BranchesRiedel.riedel` |
| Module | `QuantumFoundations/BranchesRiedel/Induction.lean` |
| Status | formalization of a known theorem (Riedel's branch-decomposition theorem); the formalization and its integration into this repository are the contribution of this development, not authorship of the original theorem |
| Dependencies | finite induction on redundant, commuting record resolutions |
| Dimension | generic `n` |
| Exactness | exact |
| Axiom audit | standard trio |
| Scope limitation | establishes the branch decomposition under redundancy and a commutation witness; does not establish approximate uniqueness or physical persistence of a record selection |

| Field | Value |
|---|---|
| Manuscript role | The C14 connection: record-induced branch cells carry Born weights |
| Lean declaration | `QuantumFoundations.BranchesRiedel.BornBridge.record_induced_Born_decomposition` (component lemma: `recordBranch_weight_eq_norm_sq`) |
| Module | `QuantumFoundations/BranchesRiedel/BornBridge/Synthesis.lean` (`BornWeights.lean`) |
| Status | connection theorem, composing Riedel's decomposition with the Grain Coherence Theorem; explicitly does not claim that redundant records alone determine Born weights, since (Pos)/(Norm)/(Grain)/(Null) remain visible hypotheses |
| Dependencies | `riedel`, `grainCoherenceTheorem` infrastructure |
| Dimension | `n ≥ 3` |
| Exactness | exact |
| Axiom audit | standard trio |
| Scope limitation | requires `n ≥ 3` (inherited from the Grain Coherence Theorem); does not derive record persistence or approximate branch uniqueness |

## Redundant-record complexity separation and persistence (Complexity)

| Field | Value |
|---|---|
| Manuscript role | Explicit lower bound on interference complexity from spatially disjoint redundant records |
| Lean declaration | `QuantumFoundations.Complexity.redundant_records_give_interference_lower_bound` |
| Module | `QuantumFoundations/Complexity/RecordInterferenceBound.lean` |
| Status | original result within this integrated program |
| Dependencies | finite counting (`C0`–`C2`), the exact proxy predicates of `C3` |
| Dimension | generic, finite multi-site model |
| Exactness | exact |
| Axiom audit | standard trio |
| Scope limitation | a complexity lower bound under an exact-record-readout proxy, not a physical-availability claim |

| Field | Value |
|---|---|
| Manuscript role | Robust (noisy-record) persistence of the complexity gap under circuit evolution |
| Lean declaration | `QuantumFoundations.Complexity.approximate_records_gap_persists_under_circuit_evolution` |
| Module | `QuantumFoundations/Complexity/ApproxRecordPersistence.lean` |
| Status | original result |
| Dependencies | approximate-record readout bounds (`C8`), exact transport under reversible circuits (`C7`) |
| Dimension | generic, finite multi-site model |
| Exactness | approximate (quantitative thresholds) |
| Axiom audit | standard trio |
| Scope limitation | persistence under a modeled circuit evolution and a stated noise threshold, not a universal robustness claim |

| Field | Value |
|---|---|
| Manuscript role | Dynamical (simulated-evolution) persistence of the complexity gap |
| Lean declaration | `QuantumFoundations.Complexity.SimulatedEvolution.margin_gap_persists_under_simulated_evolution` |
| Module | `QuantumFoundations/Complexity/SimulatedEvolution/SimulationCertificate.lean` |
| Status | original result |
| Dependencies | norm-preserving simulated evolutions (`C13a`), operator-norm bridge (`C12`) |
| Dimension | generic, finite multi-site model |
| Exactness | approximate (explicit threshold margin) |
| Axiom audit | standard trio |
| Scope limitation | persistence under a specific simulated-evolution model with an explicit threshold margin, not a claim about arbitrary physical dynamics |

## Restricted record sectors: C15, C17, C17b (BornRule.RestrictedRecordSectors)

| Field | Value |
|---|---|
| Manuscript role | C15: restricted-sector quadratic uniqueness |
| Lean declaration | `QuantumFoundations.BornRule.RestrictedRecordSectors.restricted_record_sector_born` (real-valued form: `restricted_record_sector_born_real`) |
| Module | `QuantumFoundations/BornRule/RestrictedRecordSectors/Hilbert.lean` |
| Status | formalization and integration of Lela's restricted-sector uniqueness theorem; no independent priority claim is made for the underlying uniqueness theorem |
| Dependencies | the restricted-sector profile structure of `Profiles.lean`, `Additive.lean` |
| Dimension | as required by the restricted-sector construction |
| Exactness | exact |
| Axiom audit | standard trio |
| Scope limitation | establishes exact uniqueness on the restricted sector under the stated exact saturation hypotheses. C17 (below) controls perturbations of this already-established exact quadratic law; it does not establish that the C15 uniqueness conclusion itself remains valid, even approximately, when the C15 hypotheses hold only approximately — see the C17 entry for the precise statement of what is and is not proved. |

| Field | Value |
|---|---|
| Manuscript role | C17: quantitative weight stability — the first quantitative stability result in this formal development |
| Lean declaration | `QuantumFoundations.BornRule.RestrictedRecordSectors.restricted_record_sector_weight_uniform_stability` |
| Module | `QuantumFoundations/BornRule/RestrictedRecordSectors/Stability.lean` |
| Status | original result within this integrated program; no unrestricted historical priority claim is made |
| Dependencies | `restricted_record_sector_born`, an explicit projected-component proximity hypothesis |
| Dimension | as required by the restricted-sector construction |
| Exactness | approximate (explicit quantitative bound) |
| Axiom audit | standard trio |
| Scope limitation | **Proves:** projected-component proximity implies quantitative weight proximity — i.e. C17 controls perturbations of the already-established exact quadratic law (C15) around the exact hypotheses, quantitatively. **Does not prove:** (i) that approximate refinement stability implies an approximately quadratic law; (ii) that approximate binary saturation implies approximate uniqueness; (iii) approximate matching or uniqueness of branch decompositions; (iv) a physical derivation of projected-component proximity itself; (v) persistence of record selection under arbitrary dynamics. In particular, C17 does not establish stability of the C15 uniqueness conclusion under approximate versions of the C15 assumptions. |

| Field | Value |
|---|---|
| Manuscript role | C17b: state, operator-norm, and simulated-evolution stability bridges |
| Lean declaration | `QuantumFoundations.BornRule.RestrictedRecordSectors.sector_weight_stability_under_circuit_simulation` |
| Module | `QuantumFoundations/BornRule/RestrictedRecordSectors/StabilitySimulatedEvolution.lean` |
| Status | original result (connection theorem, integrating C17's stability bound with the `Complexity.SimulatedEvolution` machinery) |
| Dependencies | `restricted_record_sector_weight_uniform_stability`, the operator-norm and simulated-evolution infrastructure of `Complexity/` |
| Dimension | as required by the restricted-sector construction |
| Exactness | approximate (explicit quantitative bound) |
| Axiom audit | standard trio |
| Scope limitation | Proves the same projected-component-proximity-implies-weight-proximity statement as C17, specialized to a simulated-circuit evolution model. Does not prove any of the five items listed under C17's scope limitation, and does not establish persistence of record selection under arbitrary physical dynamics. |

| Field | Value |
|---|---|
| Manuscript role | Pointwise stability of record-induced branch weights (C17b branch bridge) |
| Lean declaration | `QuantumFoundations.BranchesRiedel.BornBridge.recordBranch_weight_pointwise_stability` |
| Module | `QuantumFoundations/BranchesRiedel/BornBridge/Stability.lean` |
| Status | connection theorem, linking the C14 record-induced branch-weight theorem to the C17 quantitative stability bound |
| Dependencies | `recordBranch_weight_eq_norm_sq` (C14), the C17 stability bound |
| Dimension | `n ≥ 3` (inherited from C14) |
| Exactness | approximate (explicit quantitative bound) |
| Axiom audit | standard trio |
| Scope limitation | Proves the same projected-component-proximity-implies-weight-proximity statement as C17/C17b, specialized to record-induced branch cells. Does not prove any of the five items listed under C17's scope limitation. |

## Auxiliary operational theorem: Naimark dilation

| Field | Value |
|---|---|
| Manuscript role | Auxiliary operational theorem: every finite POVM is realized as a projective measurement on a dilated space |
| Lean declaration | `QuantumFoundations.naimark` (statistical corollary: `naimark_born`; ancilla/unitary form: `naimark_projective_form`) |
| Module | `QuantumFoundations/Naimark/Main.lean` (`Unitary.lean`) |
| Status | formalization of a known theorem (Naimark dilation, following Watrous, *The Theory of Quantum Information*, Theorem 2.42) |
| Dependencies | none beyond finite-dimensional linear algebra and Mathlib |
| Dimension | generic `n`, `m` |
| Exactness | exact |
| Axiom audit | standard trio |
| Scope limitation | supplies a projective operational realization of a given POVM; does not itself derive a probability rule, and does not establish minimality or uniqueness of the dilation |

## Conceptual contrast: HistoriesKent

| Field | Value |
|---|---|
| Manuscript role | Conceptual contrast: Kent's contrary-inferences construction |
| Lean declaration | `QuantumFoundations.HistoriesKent.contrary_inferences` |
| Module | `QuantumFoundations/HistoriesKent/ContraryInferences.lean` |
| Status | formalization of a known construction (Kent, *Quasiclassical Dynamics in a Closed Quantum System*, PRL 78, 2874, 1997), presented as a conceptual contrast to the branch-theoretic development, not as a premise of it |
| Dependencies | `BornRule.Perspective` (inherited transitively, hence also transitively from `Gleason.gleason`) |
| Dimension | `H 3` (explicit witness) |
| Exactness | exact |
| Axiom audit | standard trio |
| Scope limitation | illustrates a limitation of naive consistent-histories reasoning; is not used as a premise anywhere in the branch-theoretic (BranchesRiedel/BornRule) chain |

## Infrastructural results reused only through specific lemmas: Wigner and Uhlhorn

| Field | Value |
|---|---|
| Manuscript role | Infrastructural (not a substantive premise of the manuscript's central argument) |
| Lean declaration | `QuantumFoundations.Wigner.wigner` |
| Module | `QuantumFoundations/Wigner/Main.lean` |
| Status | formalization of a known theorem (Bargmann 1964; a strengthened formulation without a bijectivity hypothesis, compared explicitly to Simon–Mukunda–Chaturvedi–Srinivasan) |
| Dependencies | none beyond Mathlib |
| Dimension | generic `n` |
| Exactness | exact |
| Axiom audit | standard trio |
| Scope limitation | not invoked as a premise of the Born-weight or complexity chains; reused only where explicitly noted (e.g. via specific Uhlhorn lemmas) |

| Field | Value |
|---|---|
| Manuscript role | Infrastructural (not a substantive premise of the manuscript's central argument) |
| Lean declaration | `QuantumFoundations.Uhlhorn.uhlhorn_finite_dim` |
| Module | `QuantumFoundations/Uhlhorn/Assembly.lean` |
| Status | formalization of a known theorem (Uhlhorn-type uniqueness, Šemrl 2021, arXiv:2106.06182, Corollary 1.2) |
| Dependencies | `Gleason.gleason`, `Wigner.wigner` |
| Dimension | `n ≥ 3` |
| Exactness | exact |
| Axiom audit | standard trio |
| Scope limitation | the full theorem is not invoked as a substantive premise of the Born-weight chain; `BornRule` reuses specific internal lemmas (`eq_projL_of_positive_le_one_trace_one_inner_one`, `exists_projMeasure_of_frameFunctionOnLines`, `isEffect_of_isDensityOperator`), not the assembled theorem itself |

## Nonvacuity witnesses

Every hypothesis structure introduced in this repository carries a
concrete nonvacuity witness in the same commit as the structure (an
explicit-instantiation discipline documented in `AGENTS.md`). Representative
witnesses include `QuantumFoundations.BornRule.Nonvacuity` (the Born rule
satisfies (Grain)/(Norm)/(Pos)/(Null)),
`QuantumFoundations.BornRule.EffectPerspectives.pureStateEstimationRule`
(QB10), and
`QuantumFoundations.BornRule.RestrictedRecordSectors.Nonvacuity`'s saturated
scalar model (C15). These are not listed exhaustively here; see each
subsystem's own `README.md` and `Nonvacuity.lean` file.

## Downstream-facing API (no manuscript role)

The declarations below were added to support downstream developments
(currently `Bobart0/everettian-probability-lean`, a Born-weight decision-
theory layer). **None of them plays any role in the manuscript's
argument.** Each is an auxiliary API wrapper with no independent
mathematical content: a reformulation or an immediate consequence of an
already-validated declaration. No existing theorem statement, definition,
proof body, or public declaration name was changed to add them.

| Lean declaration | Module | Status | Immediate consequence of |
|---|---|---|---|
| `QuantumFoundations.BornRule.Refines.refl` | `BornRule/RefinementAPI.lean` | auxiliary API wrapper | reflexivity of `≤`; no independent mathematical content |
| `QuantumFoundations.BornRule.Refines.trans` | `BornRule/RefinementAPI.lean` | auxiliary API wrapper | transitivity of `≤`; no independent mathematical content |
| `QuantumFoundations.BornRule.parentOf` | `BornRule/RefinementAPI.lean` | auxiliary API wrapper | a total parent map built by `Classical.choice` on the existence witness `Refines` already supplies; no independent mathematical content |
| `QuantumFoundations.BornRule.parentOf_mem` | `BornRule/RefinementAPI.lean` | auxiliary API wrapper | immediate consequence of `parentOf`'s defining choice; no independent mathematical content |
| `QuantumFoundations.BornRule.parentOf_le` | `BornRule/RefinementAPI.lean` | auxiliary API wrapper | immediate consequence of `parentOf`'s defining choice; no independent mathematical content |
| `QuantumFoundations.BornRule.parentOf_eq_of_le` | `BornRule/RefinementAPI.lean` | auxiliary API wrapper | immediate consequence of `Perspective.unique_parent`; no independent mathematical content |
| `QuantumFoundations.BornRule.coarseCells` | `BornRule/RefinementAPI.lean` | auxiliary API wrapper | a stabilized presentation of `AxGrain`'s existing `Finset.filter (· ≤ c)` under a named, fixed decidability instance; no independent mathematical content |
| `QuantumFoundations.BornRule.mem_coarseCells_iff` | `BornRule/RefinementAPI.lean` | auxiliary API wrapper | `Finset.mem_filter`; no independent mathematical content |
| `QuantumFoundations.BornRule.axGrain_iff_coarseCells` | `BornRule/RefinementAPI.lean` | auxiliary API wrapper | restatement of `AxGrain` via `coarseCells`; the two sides coincide definitionally; no independent mathematical content |
| `QuantumFoundations.BornRule.coarseCells_eq_fiber_parentOf` | `BornRule/RefinementAPI.lean` | auxiliary API wrapper | immediate consequence of `parentOf_eq_of_le`/`parentOf_le`; no independent mathematical content |
| `QuantumFoundations.BornRule.EffectPerspectives.Refines.trans` | `BornRule/EffectPerspectives/Refinement.lean` | auxiliary API wrapper | composition of two existing refinements via `parent := parent₂ ∘ parent₁`, reindexing a double finite sum; no independent mathematical content; deferred through QB1–QB11, added here once a downstream consumer needs it |
| `QuantumFoundations.ProbabilityAPI` (module) | `ProbabilityAPI.lean` | auxiliary API wrapper | a pure re-export surface; imports and re-exports existing declarations only, adds none |
| `QuantumFoundations.ProbabilityAPI.BornRule.{refine_filter_sup_eq, E₀, E₀_isPos, E₀_isNul, E₀_isNorm, E₀_isGrain, E₀_satisfies_axioms}` | `BornRule/Nonvacuity.lean` via `ProbabilityAPI.lean` | auxiliary API wrapper | **FR :** aucun contenu mathématique indépendant ; réexport de témoins de non-vacuité existants pour construire les témoins aval. **EN:** no independent mathematical content; re-export of existing nonvacuity witnesses for downstream witness construction |
| `QuantumFoundations.ProbabilityAPI.EffectPerspectives.{pureStateEstimationRule, pureStateEstimationRule_nullSupport, pureStateEstimationRule_weight, qubitZeroState, qubitOneState, qubitZeroState_norm, qubitOneState_norm, qubitZeroState_inner_qubitOneState, nonempty_estimationRule_two}` | `BornRule/EffectPerspectives/Nonvacuity.lean` via `ProbabilityAPI.lean` | auxiliary API wrapper | **FR :** aucun contenu mathématique indépendant ; réexport de la route de non-vacuité qubit existante. **EN:** no independent mathematical content; re-export of the existing qubit nonvacuity route |
| `QuantumFoundations.ProbabilityAPI.BornBridge.{concrete_activeBranchIndex_nonempty, concrete_exists_branchPerspectivePackage, concrete_branch0_weight_ne_zero, concrete_branch1_weight_ne_zero, concrete_recordChoice_distinct, concrete_recordChoice_weight_invariant_nonvacuous}` | `BranchesRiedel/BornBridge/Nonvacuity.lean` via `ProbabilityAPI.lean` | auxiliary API wrapper | **FR :** aucun contenu mathématique indépendant ; réexport des témoins de branches induites par records existants. **EN:** no independent mathematical content; re-export of existing record-induced-branch nonvacuity witnesses |
| `QuantumFoundations.ProbabilityAPI.EffectPerspectives.{projectionEffect, ContextualNullSupport}` | `BornRule/EffectPerspectives/{Basic,PureStatePinning}.lean` via `ProbabilityAPI.lean` | auxiliary API wrapper | no independent mathematical content; re-export of two existing declarations that already appeared, unnamably, in the signature of the already-exported `qubit_` theorems and of the two general theorems below — closing the signature-closure gap left open in `v1.1.1` |
| `QuantumFoundations.ProbabilityAPI.EffectPerspectives.{projectionEffect_weight_eq_born, contextual_projection_weight_eq_born}` | `BornRule/EffectPerspectives/Main.lean` via `ProbabilityAPI.lean` | auxiliary API wrapper | no independent mathematical content beyond what `qubit_projectionEffect_weight_eq_born`/`qubit_contextual_projection_weight_eq_born` (already exported in `v1.1.1`) already exposed at `n := 2`; these are the same theorems at their originally proved generality, `1 ≤ n` |
| `QuantumFoundations.ProbabilityAPI.Repetition.{Sites, configurationEquiv, sitesEquivR, configurationBasis, sitesCell, siteCell, siteResolution, sitesCell_ortho, sitesCell_covers, sitesCell_iSup}` | `BranchesRiedel/Local.lean`, `Complexity/Models/Repetition/{States,Records}.lean` via `ProbabilityAPI.lean` | auxiliary API wrapper | no independent mathematical content; re-export of the existing configuration-space scaffolding for `R` binary trials (flat space, reindexing isometry, per-site cells with their orthogonality/covering lemmas, already wired to `LabeledResolution`); does not include the i.i.d. product-state construction, which upstream does not supply (see `ARCHITECTURE_NOTES.md`) |

Every declaration above depends only on the standard trio
`[propext, Classical.choice, Quot.sound]`, verified by
`QuantumFoundations/Audit/DownstreamAPI.lean` (not imported by the
repository root, run separately in CI, mirroring `Audit/FoP.lean`).

## Selectors (interpretively neutral, no manuscript role)

`QuantumFoundations/Selectors/` is an independent, interpretively neutral
development — nothing Everettian enters it, and no manuscript-facing
theorem elsewhere in this repository depends on it. It is not part of the
manuscript's argument chain and is not audited by `Audit/FoP.lean` (see
that module's own scope note); see `Selectors/README.md` for the full
architecture. It studies **selectors** (pure-state ↦ density-operator
maps) from two independent angles: unitary covariance plus a bridge
premise (`NSNC1`), and a general classification of single-effect
constraints (Proposition 2).

| Field | Value |
|---|---|
| Manuscript role | none — interpretively neutral, independent development |
| Lean declaration | `QuantumFoundations.Selector.covariant_iff_tSelector` |
| Module | `Selectors/Classification.lean` |
| Status | original result (this development's classification, via an elementary vector-stabilizer argument; no Schur's lemma or representation theory) |
| Dependencies | `Selector`, `IsCovariant`, `tDensity`; the sign-reflection/transposition toolbox in `Selectors/Unitaries.lean` |
| Dimension | `n ≥ 2` |
| Exactness | exact |
| Axiom audit | standard trio |
| Scope limitation | the `tDensity` family itself is the well-known isotropic/depolarizing family in quantum information, not original; the classification (this theorem) shows covariance alone cannot select the Born member of that family |

| Field | Value |
|---|---|
| Manuscript role | none — interpretively neutral, independent development |
| Lean declaration | `QuantumFoundations.Selector.covariant_and_nsnc1_iff_born` (assembling `nsnc1_iff_born`, `tSelector_nsnc1_iff_t_eq_one`) |
| Module | `Selectors/Pinning.lean` |
| Status | original result (this development's assembly); `nsnc1_iff_born` itself does not use covariance and reuses the existing `QuantumFoundations.BornRule.eq_projL_of_vanishes_on_orthogonal` for the operator identification |
| Dependencies | `covariant_iff_tSelector`, `NSNC1`, `apply_eq_zero_of_quadratic_eq_zero` (a positive-operator quadratic-vanishing lemma proved here via `sqrtOp`, not reused from elsewhere) |
| Dimension | `n ≥ 2` |
| Exactness | exact |
| Axiom audit | standard trio |
| Scope limitation | `NSNC1` ("no successor, no chance") is a bridge premise studied as a hypothesis, not derived from anything more primitive; no claim is made that it must be accepted as a principle of chance |

| Field | Value |
|---|---|
| Manuscript role | none — interpretively neutral, independent development |
| Lean declaration | `QuantumFoundations.Selector.single_effect_selector_iff` (Proposition 2) |
| Module | `Selectors/SingleEffect.lean` |
| Status | original result (this development's convex/spectral classification) |
| Dependencies | `density_supported_on_kernel_of_extremal_trace` (a general spectral-support lemma via `LinearMap.IsSymmetric.eigenvectorBasis`, proved here); `apply_eq_zero_of_quadratic_eq_zero` (reused from `Selectors/Pinning.lean`, not reproved); `QuantumFoundations.BornRule.eq_projL_of_vanishes_on_orthogonal` (reused, not reproved) |
| Dimension | generic `n` |
| Exactness | exact |
| Axiom audit | standard trio |
| Scope limitation | a convex/spectral geometry statement about which single-effect constraints *would* select a pure state; it takes no position on whether any specific effect/value pair is physically realized or should be adopted as a probability postulate. `NSNC1` (above) is recovered as the special case `E₀ = P_{ψ⊥}`, `c = 0` (`nsnc1_iff_born_from_proposition_two`) — a proved corollary, not a re-derivation of one classification from the other |

| Field | Value |
|---|---|
| Manuscript role | none — interpretively neutral, independent development |
| Lean declaration | `QuantumFoundations.Selector.{cellwiseInvariant_density_iff_blockScalar, setwiseInvariant_density_iff_blockScalar_orbitConstant}` |
| Module | `Selectors/PerspectiveClassification.lean` |
| Status | original result (this development's classification of density operators invariant under a perspective's cellwise/setwise stabilizer; no Schur's lemma or representation theory) |
| Dependencies | `PerspectiveCellwiseStabilizer`/`PerspectiveSetwiseStabilizer` (`Selectors/PerspectiveStabilizer.lean`); `reflIso`/`swapIso` (`Selectors/Unitaries.lean`, reused as-is, not extended); `sum_projL_cells_eq_id` (resolution of the identity, proved here from `Gleason.projL_sup_of_pairwise_isOrtho`) |
| Dimension | generic `n` (setwise orbit-constancy witness needs `n ≥ 2` inside a two-cell orbit) |
| Exactness | exact |
| Axiom audit | standard trio |
| Scope limitation | a pure classification of a FIXED operator's invariance under a subgroup (`IsInvariantUnder`, `Selectors/SubgroupCovariance.lean`); distinct from selector covariance (`IsCovariantUnder`) — `Selectors/StructureMain.lean` documents the distinction. `PerspectiveCellwiseStabilizer_mono_of_refines` (`Selectors/Monotonicity.lean`) shows the classification is monotone under perspective refinement; nonvacuity and strict-hierarchy witnesses are in `Selectors/StructureNonvacuity.lean`/`StructureNontriviality.lean` |

Every declaration in `Selectors/` depends only on the standard trio
`[propext, Classical.choice, Quot.sound]` (verified individually via
`#print axioms` on each public declaration; there is no dedicated audit
module for this interpretively neutral subsystem, matching its exclusion
from `Audit/FoP.lean`; `Audit/SelectorStructure.lean` runs the same
`#check`/`#print axioms` sweep specifically over Module B's public API).

## Naimark/BinaryImpl (interpretively neutral, no manuscript role)

`QuantumFoundations/Naimark/BinaryImpl/` is an independent, interpretively
neutral development — nothing Everettian enters it, and no
manuscript-facing theorem elsewhere in this repository depends on it. It
is not part of the manuscript's argument chain and is not audited by
`Audit/FoP.lean`; see `Naimark/README.md` for the full architecture. It
classifies the exact structure of concrete binary implementations of a
fixed effect, on top of the auxiliary Naimark dilation theorem above,
without ever re-proving it.

| Field | Value |
|---|---|
| Manuscript role | none — interpretively neutral, independent development |
| Lean declaration | `QuantumFoundations.Naimark.BinaryImpl.minimal_strictIso` |
| Module | `Naimark/BinaryImpl/MinimalUniqueness.lean` |
| Status | original result (this development's central theorem: two minimal implementations of the same effect are always strictly isomorphic) |
| Dependencies | `BinaryImpl`, `StrictIso` (`Defs.lean`); `IsMinimal`, `minimalSubspace` (`Minimal.lean`); `exists_isometryEquiv_of_adjoint_comp_self_eq_of_surjective` (`GramRange.lean`, a general Gram-equality-implies-canonical-isometry lemma proved here) |
| Dimension | generic `n` |
| Exactness | exact |
| Axiom audit | standard trio |
| Scope limitation | `StrictIso` is deliberately stronger than mere equality of induced effects (automatic by construction); the theorem says nothing about non-minimal implementations, which `Residual.lean`/`StrictClassification.lean` address separately (necessity direction only — see next entry) |

| Field | Value |
|---|---|
| Manuscript role | none — interpretively neutral, independent development |
| Lean declaration | `QuantumFoundations.Naimark.BinaryImpl.StrictIso.{excessEventDim_eq, excessComplementDim_eq}` |
| Module | `Naimark/BinaryImpl/StrictClassification.lean` |
| Status | original result (necessity direction only): a strict isomorphism forces equality of the two residual dilation multiplicities `excessEventDim`/`excessComplementDim` (`Residual.lean`) |
| Dependencies | `StrictIso.projectorRange_finrank_eq`/`projectorKernel_finrank_eq` (`Defs.lean`); the additive decompositions `projectorRank_decomposition`/`projectorNullity_decomposition` (`Residual.lean`) |
| Dimension | generic `n` |
| Exactness | exact |
| Axiom audit | standard trio |
| Scope limitation | **the converse (sufficient) direction, and hence the full equivalence `strictIso_iff_residualDims_eq` envisioned for this module, is NOT proved.** Its construction would require gluing three orthogonal isometries (the minimal part plus two residual sectors with no natural common domain) into one ambient isometry; no statement here uses it, weakens it to a single implication, or otherwise substitutes for it. `ResidualExtension`/`minimalCore` and the residual-neutral valuation equivalence (`Valuation.lean`) are correspondingly not built — see `Naimark/README.md`, "What is not claimed" |

| Field | Value |
|---|---|
| Manuscript role | none — interpretively neutral, independent development |
| Lean declaration | `QuantumFoundations.Naimark.BinaryImpl.canonicalBinaryImpl_canonicalTernaryImpl_not_strictIso_replicatedAncilla` |
| Module | `Naimark/BinaryImpl/TernaryFusion.lean` |
| Status | original result: the canonical binary and ternary implementations of the same effect (ambient rank ratios `1/2` vs `1/3`) are never strictly isomorphic, even after adjoining an arbitrarily large replicated ancilla on either side |
| Dependencies | `rankRatio`, `rankRatio_replicatedAncilla`, `replicatedAncillaImpl` (`ReplicatedAncilla.lean`); `StrictIso.rankRatio_eq` (a strict isomorphism forces equal rank ratio, since it forces equal `ambientDim` and equal `projectorRank` separately) |
| Dimension | `n ≥ 1` |
| Exactness | exact |
| Axiom audit | standard trio |
| Scope limitation | `rankRatio` is a computable numeric invariant, not a claim about physical distinguishability of ancilla-augmented implementations; `Valuation.lean`'s `ambientDimValuation` shows `StrictIsoInvariant` does not by itself entail `ReplicatedAncillaNeutral` |

Every declaration in `Naimark/BinaryImpl/` depends only on the standard
trio `[propext, Classical.choice, Quot.sound]`, verified by
`QuantumFoundations/Audit/NaimarkOmega.lean` (not imported by the
repository root, run separately in CI, mirroring `Audit/SelectorStructure.lean`).
