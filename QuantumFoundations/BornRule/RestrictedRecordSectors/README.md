# C15 — Restricted record-sector quadratic-weight uniqueness

This directory is the Lean formalization and repository integration of
Theorem 3 and Corollary 2 of Marko Lela, “The Born Rule as the Unique
Refinement-Stable Induced Weight on Robust Record Sectors,”
arXiv:2603.24619v1.

## Scope and statement

C15 concerns an induced weight on an abstract carrier of admissible record
situations. A situation may encode a state, a sector, a context, record data,
or other admissibility metadata. It is not a measure on the full projector
lattice.

The generic layer assumes:

- a non-negative magnitude;
- an admissible binary-refinement relation with Pythagorean magnitudes;
- exact realization of all magnitudes;
- exact binary saturation;
- refinement stability of the weight;
- internal equivalence expressed initially as equality of binary refinement
  profiles.

Internal equivalence is deliberately not defined as equality of weights at
equal norms. Binary saturation first proves that binary profiles are
classified by magnitude. Only then does profile invariance reduce the weight
to a one-variable function.

The resulting Pythagorean functional equation becomes additive after the
reparameterization `f u = g (NNReal.sqrt u)`. Additivity and non-negativity
force

```text
W x = c * magnitude(x)^2.
```

The Hilbert adapter sets

```text
magnitude(x) = ‖(sector x).starProjection (state x)‖₊
```

and therefore obtains

```text
W x = c ‖P_R Ψ‖².
```

Matching finite normalizations of the weight and squared magnitudes fix
`c = 1` globally.

## Additivity and continuations

The main theorem consumes the reusable predicate `RefinementStable`. The
separate continuation adapter records one logical source of that predicate:
an extensive valuation on sets of continuations is finitely additive on
disjoint unions, and a binary refinement partitions the parent bundle into
two disjoint child bundles. No sigma-algebra, countable additivity, or
probability measure is introduced.

## Dependencies and boundaries

The generic core (`Additive`, `Basic`, `Profiles`, and `Main`) is independent
of the repository’s global Born-rule assembly, C14 Born-weight declarations,
and the Gleason and Busch theorem routes. No Gleason, Busch,
decision-theoretic, or envariance theorem is used.

Binary saturation is an exact assumption. C15 does not derive it from C14
dynamics or claim that physical robust record sectors satisfy it. Dense
saturation plus continuity, approximate profiles, a C14/C15 physical
saturation bridge, and C16 remain future work.

## C17 — First quantitative stability theorem

C17 is the first non-trivial quantitative stability theorem within the
present formal development. It assumes that both weights already satisfy the
exact normalized quadratic law supplied by C15. For projected components

```text
u = P_(R₁ x) Ψ₁ x,    v = P_(R₂ x) Ψ₂ x,
```

it proves

```text
|W₁ x - W₂ x| ≤ (‖u‖ + ‖v‖) ‖u - v‖.
```

Thus the perturbation may simultaneously change the state, the record
sector, or both; no metric on subspaces is introduced. On the unit ball the
bound becomes

```text
|W₁ x - W₂ x| ≤ 2 ‖u - v‖.
```

For a finite family `s`, C17 gives the corresponding `L¹` bound. If every
component distance is at most `ε`, then

```text
∑ x ∈ s, |W₁ x - W₂ x| ≤ 2 * card(s) * ε
```

and the half-`L¹` expression is at most `card(s) * ε`. For weights normalized
on `s`, the latter may be read as a finite total-variation-type estimate;
no general probability-distribution framework is added.

The result shows that once restricted-sector weights are fixed by C15,
perturbations of the projected branch components produce linearly controlled
perturbations of the corresponding weights.

C17 does not prove stability under approximate C15 hypotheses, approximate
uniqueness of branch decompositions, or a dynamical derivation of the
projected-component distance. It does not address C16 or claim optimality of
the constant two. No historical priority claim is made.

## C17b — Low-cost integration bridges

C17b does not strengthen the reduced C17 theorem. It connects that theorem
to already completed APIs. For a fixed sector `R`, states in the unit ball
satisfy

```text
|w_R(ψ) - w_R(φ)| ≤ 2 ‖ψ - φ‖.
```

If two orthogonal projections are within operator-norm error `ε`, their
quadratic weights on a normalized state satisfy

```text
|w_R(ψ) - w_S(ψ)| ≤ 2 ε.
```

A C13 circuit-simulation certificate with error `ε` consequently gives this
same `2 ε` bound for every fixed sector evaluated on the exact and simulated
states. This compares the same supplied sector on both states; it does not
assert that the sector remains selected by the evolved record dynamics.

Finally, C14 active-branch weights inherit the generic
`(‖u‖ + ‖v‖) ‖u - v‖` estimate, and its unit-ball constant-two form, when the
caller explicitly supplies the correspondence between the two branches.
C17b derives neither approximate branch matching or uniqueness, approximate
saturation, physical persistence of record selection, nor any stronger C17
stability statement. No historical priority claim is made.

## Files

- `Additive.lean`: additive maps `ℝ≥0 → ℝ≥0` are scalar multiplication,
  without a continuity hypothesis.
- `Basic.lean`: abstract refinement system, realization, saturation, and
  optional positive-scaling closure.
- `Profiles.lean`: binary profiles, profile classification, scalar profile
  function, and functional equation.
- `Main.lean`: unnormalized quadratic uniqueness, null corollary, and
  normalized theorem.
- `Hilbert.lean`: projected-component norm adapter and paper-facing theorems.
- `Continuation.lean`: finite disjoint-bundle additivity adapter.
- `Nonvacuity.lean`: non-trivial saturated scalar model plus Hilbert and
  finite continuation witnesses.
- `Stability.lean`: generic norm-square estimate, exact-law adapter,
  pointwise, finite-`L¹`, uniform-error, and normalized-state C17 bounds.
- `StabilityNonvacuity.lean`: nonzero-distance scalar witnesses.
- `StabilityOperatorNorm.lean`: fixed-sector state, C12 operator-norm,
  projection, and combined state-sector bridges.
- `StabilitySimulatedEvolution.lean`: C13 circuit-simulation, bounded-cost,
  and finite-family fixed-sector bridges.
- `BranchesRiedel/BornBridge/Stability.lean`: C14 active-branch weight
  stability under an explicitly supplied branch correspondence.
