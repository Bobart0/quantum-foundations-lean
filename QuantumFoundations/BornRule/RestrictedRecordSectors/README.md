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
saturation bridge, C16, and C17 remain future work.

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
