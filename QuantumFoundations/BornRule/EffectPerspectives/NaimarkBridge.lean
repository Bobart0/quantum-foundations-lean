import QuantumFoundations.BornRule.EffectPerspectives.Nonvacuity
import QuantumFoundations.Naimark.Unitary

/-!
# QB11 — Effect-perspective / Naimark bridge

A pure integration layer: every finite `EffectPerspective` is canonically a
`QuantumFoundations.POVM` (its effects are already positive, by
`Gleason.IsEffect T = Gleason.IsPositiveOp T ∧ Gleason.IsPositiveOp (1 - T)`,
and `EffectPerspective.sum_eq_one` already supplies POVM completeness), so
the existing finite-dimensional Naimark dilation
(`QuantumFoundations.naimark`/`naimark_born`/`naimark_projective_form`)
applies to it directly. Nothing about Naimark, Busch, Gleason, or QB1–QB10
is reproved or modified here; every theorem below is a thin wrapper
obtained by `simpa` from an existing theorem in `QuantumFoundations.Naimark`.
-/

namespace QuantumFoundations.BornRule.EffectPerspectives

open scoped InnerProductSpace

noncomputable section

variable {n : ℕ}

/-! ## QB11.1 — Canonical POVM conversion -/

/-- Every finite effect perspective is canonically a `QuantumFoundations.POVM`:
its effects are already positive, and `sum_eq_one` already supplies
completeness. No new hypothesis is needed. -/
def EffectPerspective.toPOVM (D : EffectPerspective n) :
    QuantumFoundations.POVM n D.outcomes where
  E i := (D.effects i : Gleason.H n →ₗ[ℂ] Gleason.H n)
  pos i := (D.effects i).2.1
  sum_eq_one := D.sum_eq_one

@[simp] theorem EffectPerspective.toPOVM_E (D : EffectPerspective n) (i : Fin D.outcomes) :
    D.toPOVM.E i = (D.effects i : Gleason.H n →ₗ[ℂ] Gleason.H n) := rfl

/-! ## QB11.2 — Isometric Naimark realization -/

/-- Every finite effect perspective is realized, via the Naimark dilation
isometry, as a projection-valued measure on `DilSpace n D.outcomes`. Direct
application of `QuantumFoundations.naimark`; the dilation proof itself is
not reproduced. -/
theorem effectPerspective_naimark_realization (D : EffectPerspective n) :
    ∃ V : Gleason.H n →ₗ[ℂ] QuantumFoundations.DilSpace n D.outcomes,
      LinearMap.adjoint V ∘ₗ V = LinearMap.id ∧
      ∀ i : Fin D.outcomes,
        LinearMap.adjoint V ∘ₗ QuantumFoundations.dilProj n D.outcomes i ∘ₗ V
          = (D.effects i : Gleason.H n →ₗ[ℂ] Gleason.H n) := by
  simpa using QuantumFoundations.naimark D.toPOVM

/-! ## QB11.3 — Preservation of effect expectation values -/

/-- Effect expectation values are preserved exactly under the Naimark
dilation. Direct application of `QuantumFoundations.naimark_born`; holds for
every vector `ψ`, with no normalization hypothesis. -/
theorem effectPerspective_born_preserved_under_dilation (D : EffectPerspective n)
    (i : Fin D.outcomes) (ψ : Gleason.H n) :
    ⟪ψ, (D.effects i : Gleason.H n →ₗ[ℂ] Gleason.H n) ψ⟫_ℂ
      = ⟪QuantumFoundations.dilV D.toPOVM ψ,
          QuantumFoundations.dilProj n D.outcomes i
            (QuantumFoundations.dilV D.toPOVM ψ)⟫_ℂ := by
  simpa using QuantumFoundations.naimark_born D.toPOVM i ψ

/-! ## QB11.4 — Full unitary/ancilla realization -/

/-- With an explicit ancilla index `i₀`, the effect perspective is realized
by preparing the ancilla in block `i₀`, applying a single global unitary on
`DilSpace n D.outcomes`, and measuring the dilated projection-valued
measure. Direct application of `QuantumFoundations.naimark_projective_form`;
`i₀` is kept explicit, with no chosen default. -/
theorem effectPerspective_projective_ancilla_realization (D : EffectPerspective n)
    (i₀ : Fin D.outcomes) :
    ∃ U : QuantumFoundations.DilSpace n D.outcomes ≃ₗᵢ[ℂ] QuantumFoundations.DilSpace n D.outcomes,
      ∀ (i : Fin D.outcomes) (ψ : Gleason.H n),
        ⟪ψ, (D.effects i : Gleason.H n →ₗ[ℂ] Gleason.H n) ψ⟫_ℂ
          = ⟪U (QuantumFoundations.singleL n D.outcomes i₀ ψ),
              QuantumFoundations.dilProj n D.outcomes i
                (U (QuantumFoundations.singleL n D.outcomes i₀ ψ))⟫_ℂ := by
  simpa using QuantumFoundations.naimark_projective_form D.toPOVM i₀

/-! ## QB11.5 — Optional corollary: pure-state weight under dilation

`pureStateEstimationRule_weight` (QB10) already gives the contextual weight
of an outcome as `Re ⟪T ψ, ψ⟫` with no new mathematics; composing it with
the effect's own symmetry (already part of `Gleason.IsPositiveOp`, not new)
and `effectPerspective_born_preserved_under_dilation` above identifies that
weight with the real part of the dilated projective expectation, purely by
existing-theorem composition. -/
theorem pureStateEstimationRule_weight_eq_dilated_expectation
    (ψ : Gleason.H n) (hψ : ‖ψ‖ = 1) (D : EffectPerspective n) (i : Fin D.outcomes) :
    (pureStateEstimationRule ψ hψ).weight D i
      = (⟪QuantumFoundations.dilV D.toPOVM ψ,
            QuantumFoundations.dilProj n D.outcomes i
              (QuantumFoundations.dilV D.toPOVM ψ)⟫_ℂ).re := by
  rw [pureStateEstimationRule_weight ψ hψ D i,
    (D.effects i).2.1.1 ψ ψ,
    effectPerspective_born_preserved_under_dilation D i ψ]

end

end QuantumFoundations.BornRule.EffectPerspectives
