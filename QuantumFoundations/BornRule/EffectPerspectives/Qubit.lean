import QuantumFoundations.BornRule.EffectPerspectives.Main

/-!
# QB9 — The dimension-two Busch corollary

Busch's theorem, unlike Gleason's, applies from dimension one onward. These
are pure specializations of `projectionEffect_weight_eq_born` and
`contextual_projection_weight_eq_born` (QB8) at `n := 2`, with no proof
repetition: the qubit case is not derived from the projective
`Gleason.gleason` theorem (which requires dimension `≥ 3`), but from the
effect-domain Busch route already established in general dimension.
-/

namespace QuantumFoundations.BornRule.EffectPerspectives

noncomputable section

/-! ## QB9.1 — Qubit Born weights for projection effects -/

theorem qubit_projectionEffect_weight_eq_born (ψ : Gleason.H 2) (hψ : ‖ψ‖ = 1)
    (E : EstimationRule 2) (hNull : ContextualNullSupport E ψ)
    (A : Submodule ℂ (Gleason.H 2)) :
    E.effectWeight (projectionEffect A) = ‖A.starProjection ψ‖ ^ 2 :=
  projectionEffect_weight_eq_born (by norm_num) ψ hψ E hNull A

/-! ## QB9.2 — Qubit contextual specialization -/

theorem qubit_contextual_projection_weight_eq_born (ψ : Gleason.H 2) (hψ : ‖ψ‖ = 1)
    (E : EstimationRule 2) (hNull : ContextualNullSupport E ψ)
    (D : EffectPerspective 2) (i : Fin D.outcomes) (A : Submodule ℂ (Gleason.H 2))
    (hAi : (D.effects i : Gleason.H 2 →ₗ[ℂ] Gleason.H 2) = Gleason.projL A) :
    E.weight D i = ‖A.starProjection ψ‖ ^ 2 :=
  contextual_projection_weight_eq_born (by norm_num) ψ hψ E hNull D i A hAi

end

end QuantumFoundations.BornRule.EffectPerspectives
