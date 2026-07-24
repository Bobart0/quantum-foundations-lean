import QuantumFoundations.BornRule.EffectPerspectives.PureStatePinning

/-!
# QB8 — Born weights from effect-perspective refinement

The headline theorem: under a state-relative null-support hypothesis, the
weight a contextual estimation rule assigns to a projection effect equals
the Born value `‖A.starProjection ψ‖ ^ 2`. The proof passes through
`Gleason.busch_born_rule` (via `exists_densityOperator_projective`, QB6)
and the fallback pinning theorem (`density_bornValue_eq_pure_of_null`,
QB7); it never invokes `Gleason.gleason` or
`grainCoherenceTheorem_projector`.
-/

namespace QuantumFoundations.BornRule.EffectPerspectives

noncomputable section

variable {n : ℕ}

/-! ## QB8.1 — Born weights for projection effects -/

/-- **Main theorem.** The weight a contextual estimation rule assigns to a
projection effect `projectionEffect A`, under a state-relative null-support
hypothesis at `ψ`, equals the Born value of `A`. -/
theorem projectionEffect_weight_eq_born {n : ℕ} (hn : 1 ≤ n) (ψ : Gleason.H n)
    (hψ : ‖ψ‖ = 1) (E : EstimationRule n) (hNull : ContextualNullSupport E ψ)
    (A : Submodule ℂ (Gleason.H n)) :
    E.effectWeight (projectionEffect A) = ‖A.starProjection ψ‖ ^ 2 := by
  obtain ⟨ρ, hρ, hRep⟩ := exists_densityOperator_projective E hn
  have hNullProj : ∀ A : Submodule ℂ (Gleason.H n),
      A.starProjection ψ = 0 → Gleason.bornValue ρ A = 0 := by
    intro A hA
    rw [← hRep A]
    exact projectionEffect_weight_zero E ψ hNull A hA
  rw [hRep A]
  exact density_bornValue_eq_pure_of_null hn ψ hψ ρ hρ hNullProj A

/-! ## QB8.2 — Contextual specialization -/

/-- The same theorem restated for an arbitrary occurrence of a projection
effect inside any effect perspective, using context independence
(`contextual_weight_eq_effectWeight`, QB5) to reduce to the canonical
form. -/
theorem contextual_projection_weight_eq_born {n : ℕ} (hn : 1 ≤ n) (ψ : Gleason.H n)
    (hψ : ‖ψ‖ = 1) (E : EstimationRule n) (hNull : ContextualNullSupport E ψ)
    (D : EffectPerspective n) (i : Fin D.outcomes) (A : Submodule ℂ (Gleason.H n))
    (hAi : (D.effects i : Gleason.H n →ₗ[ℂ] Gleason.H n) = Gleason.projL A) :
    E.weight D i = ‖A.starProjection ψ‖ ^ 2 := by
  rw [contextual_weight_eq_effectWeight E D i,
    show D.effects i = projectionEffect A from Subtype.ext hAi]
  exact projectionEffect_weight_eq_born hn ψ hψ E hNull A

/-! ## QB8.3 — Deferred: expectation-value form (optional, not blocking)

An optional strengthening would restate the Born formula for an *arbitrary*
effect `T` (not only projection effects) as the expectation value
`⟪T.1 ψ, ψ⟫.re`. This is not attempted here: `density_bornValue_eq_pure_of_null`
(QB7) exposes only the Born-value formula on subspaces, not the full
operator identity `ρ = Gleason.projL (ℂ ∙ ψ)` it derives internally, and the
`rankOne`/`trace_rankOne` computation in `bornValue_projL_singleton` is
specific to `T = Gleason.projL A`. Generalizing it to an arbitrary effect
`T` would require exposing the operator identity publicly and a separate
trace computation `(trace (Gleason.projL (ℂ ∙ ψ) ∘ₗ T)).re = (⟪T.1 ψ, ψ⟫_ℂ).re`
for arbitrary `T`, neither of which the mandatory milestones require.
Deferred, not silently dropped; QB8's two mandatory theorems above do not
depend on it. -/

end

end QuantumFoundations.BornRule.EffectPerspectives
