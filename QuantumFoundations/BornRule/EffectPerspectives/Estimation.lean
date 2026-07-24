import QuantumFoundations.BornRule.EffectPerspectives.Refinement

/-!
# QB4 — Contextual estimation rule

A **contextual estimation rule** assigns a non-negative real weight to every
outcome of every effect perspective, normalized on each perspective, and
coherent under refinement (`grain`). This is *effect-perspective* refinement
coherence, on the finite POVM-like carrier `EffectPerspective` defined in
this directory — it is a genuinely different predicate from the existing
projective `BornRule.AxGrain` (whose carrier is the projective
`BornRule.Perspective`, a family of pairwise-orthogonal nonzero subspaces).
The two are not interchangeable and neither is reused for the other.

Context independence, zero-effect weight, unit-effect weight, and binary
effect additivity are deliberately *not* structure fields: they are derived
theorems, proved in `ContextIndependence.lean` (QB5) from `grain` alone.
-/

namespace QuantumFoundations.BornRule.EffectPerspectives

noncomputable section

/-- A contextual estimation rule: a non-negative, normalized, refinement-
coherent weight on every outcome of every finite effect perspective. -/
structure EstimationRule (n : ℕ) where
  /-- The weight assigned to an outcome of a perspective. -/
  weight : (D : EffectPerspective n) → Fin D.outcomes → ℝ
  /-- Non-negativity. -/
  nonneg : ∀ (D : EffectPerspective n) (i : Fin D.outcomes), 0 ≤ weight D i
  /-- Normalization on every perspective. -/
  normalized : ∀ D : EffectPerspective n, ∑ i, weight D i = 1
  /-- Refinement coherence: the weight of a coarse outcome equals the sum
  of the weights of its fine preimage. This is effect-perspective
  refinement coherence, not the existing projective `AxGrain`. -/
  grain :
    ∀ {fine coarse : EffectPerspective n} (r : Refines fine coarse)
      (j : Fin coarse.outcomes),
      weight coarse j = ∑ i : Fin fine.outcomes, if r.parent i = j then weight fine i else 0

end

end QuantumFoundations.BornRule.EffectPerspectives
