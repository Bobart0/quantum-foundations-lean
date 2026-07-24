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
| Scope limitation | establishes uniqueness on the restricted sector under the stated saturation hypotheses; does not establish stability under approximate versions of those hypotheses (that is C17, below) |

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
| Scope limitation | states that projected-component proximity implies quantitative weight proximity; does not state stability under approximate versions of the C15 hypotheses themselves, approximate branch uniqueness, or a physical derivation of component proximity |

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
| Scope limitation | as for C17, specialized to a simulated-circuit evolution model; does not establish persistence of record selection under arbitrary physical dynamics |

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
| Scope limitation | as for C17/C17b, specialized to record-induced branch cells |

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
