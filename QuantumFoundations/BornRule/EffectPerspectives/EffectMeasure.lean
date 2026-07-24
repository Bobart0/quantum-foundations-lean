import QuantumFoundations.BornRule.EffectPerspectives.ContextIndependence
import Gleason.Busch.Main

/-!
# QB6 — Construct `Gleason.EffectMeasure`

Packages an `EstimationRule` into the pinned dependency's own
`Gleason.EffectMeasure` (positive, normalized to `1`, finitely additive on
effects), then applies `Gleason.busch`/`Gleason.busch_born_rule` directly —
the difficult Busch theorem itself is reused, never reproved.
-/

namespace QuantumFoundations.BornRule.EffectPerspectives

open scoped Classical

noncomputable section

variable {n : ℕ}

/-! ## QB6 — The effect measure -/

/-- An estimation rule packages into a `Gleason.EffectMeasure`: the
underlying function is zero away from effects (no arbitrary classical
choice on non-effects). -/
noncomputable def EstimationRule.toEffectMeasure (E : EstimationRule n) : Gleason.EffectMeasure n where
  f T := if hT : Gleason.IsEffect T then E.effectWeight ⟨T, hT⟩ else 0
  nonneg T hT := by
    rw [dif_pos hT]
    exact effectWeight_nonneg E ⟨T, hT⟩
  map_one := by
    have h1 : Gleason.IsEffect (1 : Gleason.H n →ₗ[ℂ] Gleason.H n) := oneEffect_coe n ▸ (oneEffect n).2
    rw [dif_pos h1,
      show (⟨(1 : Gleason.H n →ₗ[ℂ] Gleason.H n), h1⟩ : Effect n) = oneEffect n from
        Subtype.ext (oneEffect_coe n).symm]
    exact effectWeight_one E
  additive S T hS hT hSum := by
    rw [dif_pos hS, dif_pos hT, dif_pos hSum]
    exact effectWeight_add E ⟨S, hS⟩ ⟨T, hT⟩ hSum

/-! ## QB6.4 — Application specification -/

theorem toEffectMeasure_apply (E : EstimationRule n) (T : Gleason.H n →ₗ[ℂ] Gleason.H n)
    (hT : Gleason.IsEffect T) :
    E.toEffectMeasure.f T = E.effectWeight ⟨T, hT⟩ := by
  show (if h : Gleason.IsEffect T then E.effectWeight ⟨T, h⟩ else 0) = E.effectWeight ⟨T, hT⟩
  rw [dif_pos hT]

theorem toEffectMeasure_apply_context (E : EstimationRule n) (D : EffectPerspective n)
    (i : Fin D.outcomes) :
    E.toEffectMeasure.f (D.effects i).1 = E.weight D i := by
  rw [toEffectMeasure_apply E (D.effects i).1 (D.effects i).2]
  exact (contextual_weight_eq_effectWeight E D i).symm

/-! ## QB6.5 — Busch representation -/

/-- **Direct application of Busch's theorem.** No part of the Busch proof
itself is reproduced here. -/
theorem existsUnique_densityOperator (E : EstimationRule n) (hn : 1 ≤ n) :
    ∃! ρ : Gleason.H n →ₗ[ℂ] Gleason.H n,
      Gleason.IsDensityOperator ρ
        ∧ ∀ T, Gleason.IsEffect T →
            E.toEffectMeasure.f T = (LinearMap.trace ℂ (Gleason.H n) (ρ ∘ₗ T)).re :=
  Gleason.busch hn E.toEffectMeasure

/-! ## QB6.6 — Projective representation wrapper -/

theorem exists_densityOperator_projective (E : EstimationRule n) (hn : 1 ≤ n) :
    ∃ ρ : Gleason.H n →ₗ[ℂ] Gleason.H n,
      Gleason.IsDensityOperator ρ
        ∧ ∀ A : Submodule ℂ (Gleason.H n),
            E.effectWeight (projectionEffect A) = Gleason.bornValue ρ A := by
  obtain ⟨ρ, hρ, hrep⟩ := Gleason.busch_born_rule hn E.toEffectMeasure
  refine ⟨ρ, hρ, fun A => ?_⟩
  rw [← hrep A]
  show E.effectWeight (projectionEffect A) = E.toEffectMeasure.f (Gleason.projL A)
  rw [toEffectMeasure_apply E (Gleason.projL A) (Gleason.EffectMeasure.isEffect_projL A)]
  rfl

end

end QuantumFoundations.BornRule.EffectPerspectives
