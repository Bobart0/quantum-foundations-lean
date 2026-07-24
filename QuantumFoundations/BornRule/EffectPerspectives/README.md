# BornRule/EffectPerspectives — the qubit/Busch extension (QB1–QB10)

This directory formalizes a second, independent route to the Born rule,
built on **effects** (`0 ≤ T ≤ 1` in the Loewner order) rather than on
pairwise-orthogonal projective subspaces. It reuses Busch's 2003 theorem
(`Gleason.busch`/`Gleason.busch_born_rule`, pinned in the
`gleason-theorem-lean` dependency) as an unmodified black box, and connects
it to a finite, POVM-like refinement-coherence structure analogous in
spirit to — but not interchangeable with — the existing projective
`BornRule.Perspective`/`BornRule.AxGrain` development.

## Why a second route

Gleason's theorem needs dimension `n ≥ 3`. Busch's theorem, because its
additivity hypothesis ranges over the strictly larger class of effects
rather than only orthogonal projections, holds from dimension `1` onward
— in particular at `n = 2`, the qubit, where the projective route in
`BornRule/` is silent. This directory exists to reach the qubit case, not
to re-derive or replace the projective development.

## Effect-domain assumptions are stronger than the projective `Grain`

`EstimationRule.grain` (QB4, `Estimation.lean`) is refinement coherence
stated over `EffectPerspective`, a finite labelled family of effects
summing to the identity — with **no** nonzero, injectivity, or
commutativity constraint on its members. This is a materially larger
hypothesis domain than the existing projective `BornRule.AxGrain`, whose
carrier `BornRule.Perspective` consists of pairwise-orthogonal *nonzero*
subspaces. The two `grain` predicates are stated on different carriers and
are not interchangeable; neither is derived from the other anywhere in
this directory.

## File-by-file map

| File | Milestone | Content |
|---|---|---|
| `Basic.lean` | QB1 | `Effect n` (subtype wrapper around `Gleason.IsEffect`, reusing — not recreating — Busch's positivity notion); `zeroEffect`, `oneEffect`, `complementEffect`, `projectionEffect` |
| `Perspective.lean` | QB2 | `EffectPerspective` (a finite labelled family of effects summing to `1`); `binaryPerspective`, `splitPerspective`, `duplicateZeroPerspective` |
| `Refinement.lean` | QB3 | `Refines` (a `parent` map plus fiber-sum reconstruction of every coarse effect); `Refines.refl`, `collapseToChosen`, `splitRefinesBinary`, `duplicateZeroRefinesBinary`. **`Refines.trans` is deferred** (documented in-file): the double finite-sum reindexing it needs proved disproportionately brittle, and no mandatory milestone QB4–QB10 requires composing two refinements. |
| `Estimation.lean` | QB4 | `EstimationRule` (weight, non-negativity, per-perspective normalization, and `grain` refinement coherence) |
| `ContextIndependence.lean` | QB5 | Context independence, zero-effect weight, unit-effect weight, and binary effect additivity — all **derived theorems** from `grain` alone, never structure fields or axioms |
| `EffectMeasure.lean` | QB6 | `EstimationRule.toEffectMeasure : Gleason.EffectMeasure n`; direct application of `Gleason.busch` and `Gleason.busch_born_rule` (the Busch proof itself is never reproduced) |
| `PureStatePinning.lean` | QB7 | `ContextualNullSupport` (state-relative null support stated directly on effect occurrences); the fallback pinning theorem `density_bornValue_eq_pure_of_null`, reusing `QuantumFoundations.BornRule.eq_projL_of_vanishes_on_orthogonal` and `Gleason.bornValue_span_singleton` |
| `Main.lean` | QB8 | `projectionEffect_weight_eq_born` and `contextual_projection_weight_eq_born`: the Born-rule weight formula for projection effects, under a state-relative null-support hypothesis, in arbitrary finite dimension |
| `Qubit.lean` | QB9 | `qubit_projectionEffect_weight_eq_born` and `qubit_contextual_projection_weight_eq_born`: pure specializations of QB8 at `n := 2`, with no proof repetition |
| `Nonvacuity.lean` | QB10 | `pureStateEstimationRule` (proved directly, never via `Gleason.busch`); concrete qubit witnesses (`qubitZeroState`, `qubitOneState`) and exact weight-one/weight-zero examples |

## What is derived, never assumed

Context independence, zero-effect weight, unit-effect weight, and binary
effect additivity (QB5) are **theorems** proved from `EstimationRule.grain`
alone. They are not fields of `EstimationRule` and are not introduced as
axioms anywhere in this directory.

## Null-support pinning (QB7)

`ContextualNullSupport E ψ` says: any effect occurrence that annihilates a
fixed unit vector `ψ` carries zero weight. From this hypothesis alone (plus
the Busch representation from QB6), `density_bornValue_eq_pure_of_null`
pins the represented density operator to the rank-one projector onto `ψ`
and gives the Born-value formula `bornValue ρ A = ‖A.starProjection ψ‖ ^ 2`
for *every* subspace `A` — not merely the one `A` that was used to witness
the null support.

## The qubit theorem does not depend on projective Gleason

`qubit_projectionEffect_weight_eq_born` (QB9, `Qubit.lean`) is a
specialization of the general-dimension `projectionEffect_weight_eq_born`
(QB8), whose only route to a Busch/Gleason-type representation theorem is
`Gleason.busch`/`Gleason.busch_born_rule` (invoked once, in
`EffectMeasure.lean`). Neither the qubit theorem nor any theorem in this
directory invokes `Gleason.gleason` or
`BornRule.grainCoherenceTheorem_projector` — confirmed by direct search
(`rg 'Gleason\.gleason|grainCoherenceTheorem_projector'` over this
directory returns no code occurrence, only prose mentions of what is *not*
used). This is the entire point of reusing Busch rather than Gleason: the
qubit case is reachable precisely because the effect-domain hypothesis does
not need dimension `≥ 3`.

## Scope: what this development does *not* claim

This directory is a formal statement about a mathematical structure
(effects, refinement coherence, and the Busch representation theorem) and
its consequence for projection weights. It makes no claim that:

- every effect occurring in the refinement hierarchy is *physically
  available* to an observer or experiment;
- the derived weights constitute *rational credences* in any decision-
  theoretic or Bayesian sense;
- the construction supports, motivates, or otherwise bears on an Everettian
  (many-worlds) reading of quantum mechanics.

These are all interpretive questions outside the scope of a Lean
formalization of a representation theorem.

## Relationship to C0–C14 and C15

No file in `QuantumFoundations/BornRule/` outside this directory was
modified, and no existing C0–C14 theorem statement was changed. No file
under the C15 development (`restricted-record-born-c15` / the C15
directory) was read, touched, or referenced. This directory is additive
only: it introduces a new namespace
(`QuantumFoundations.BornRule.EffectPerspectives`) and new files, integrated
into `QuantumFoundations.lean` purely by adding ten import lines.

## Dependency

The pinned `gleason-theorem-lean` revision was not changed. This directory
reuses declarations that already existed in that pinned revision
(`Gleason.IsEffect`, `Gleason.EffectMeasure`, `Gleason.busch`,
`Gleason.busch_born_rule`, `Gleason.projL`, `Gleason.bornValue`,
`Gleason.IsDensityOperator`, `Gleason.positive_inner_self_eq_zero`,
`Gleason.bornValue_span_singleton`) — no new dependency declaration was
required, and none was added.

## Axiom audit

Every public declaration in this directory (verified via `#print axioms`
on 16 representative theorems spanning QB5–QB10, including the two
headline theorems `projectionEffect_weight_eq_born` and
`qubit_projectionEffect_weight_eq_born`) depends only on
`[propext, Classical.choice, Quot.sound]` — the standard Mathlib trio, with
no additional or leaked axiom.

## Deferred / optional work

- `Refines.trans` (QB3.2) is deferred; see `Refinement.lean`'s module
  docstring for the precise reason.
- `effectWeight_eq_pure_expectation` (an optional strengthening of QB8 to
  arbitrary effects, not only projection effects) is deferred; see
  `Main.lean`'s QB8.3 section for exactly what would be needed to complete
  it.
- The optional `ProjectiveBridge.lean` adapter (connecting
  `projectionEffect` back to the projective `BornRule.Perspective` carrier)
  was not attempted in this pass.

None of these deferrals affects any mandatory QB1–QB10 milestone.
