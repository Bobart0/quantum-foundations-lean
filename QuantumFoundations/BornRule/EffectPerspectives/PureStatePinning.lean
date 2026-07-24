import QuantumFoundations.BornRule.EffectPerspectives.EffectMeasure
import QuantumFoundations.BornRule.Pinning

/-!
# QB7 — State-relative null support and pure-state pinning

`ContextualNullSupport` is *state-relative* and stated directly on effect
occurrences (`(D.effects i).1 ψ = 0 → weight D i = 0`) — a stronger-carrier
analogue of the existing projective `BornRule.AxNul`, not the same
predicate, and not a field of `EstimationRule`.

No existing theorem in the repository or the pinned dependency directly
gives the *general* pinning formula `∀ A, bornValue ρ A = ‖A.starProjection
ψ‖ ^ 2` from a projective null-support hypothesis (confirmed by the searches
required in the task). The closest reusable result is
`QuantumFoundations.BornRule.eq_projL_of_vanishes_on_orthogonal`, which
already does the hard work of pinning `ρ` to the *exact* rank-one operator
`projL (ℂ ∙ ψ)` from the *stronger* hypothesis `hker : ∀ w, ⟪ψ,w⟫ = 0 → ρ w
= 0`. The fallback theorem below (1) derives `hker` from the weaker
projective null-support hypothesis via `Gleason.bornValue_span_singleton`
and `Gleason.positive_inner_self_eq_zero` (the same architecture as
`BornRule.Assembly.hker_derivation`), then (2) computes the Born value of
`projL (ℂ ∙ ψ)` on an *arbitrary* subspace `A` directly via
`InnerProductSpace.rankOne`/`InnerProductSpace.trace_rankOne` (the same
technique `Gleason.bornValue_span_singleton` itself uses, generalized from
singleton `A` to arbitrary `A`).
-/

namespace QuantumFoundations.BornRule.EffectPerspectives

open scoped InnerProductSpace

noncomputable section

variable {n : ℕ}

/-! ## QB7.1 — Contextual null support -/

/-- **State-relative** null support: an effect occurrence that annihilates
`ψ` carries no weight. Stated directly on effect occurrences, not as a
field of `EstimationRule`; stronger in carrier than the existing projective
`BornRule.AxNul` (a different predicate, not reused as-is). -/
def ContextualNullSupport (E : EstimationRule n) (ψ : Gleason.H n) : Prop :=
  ∀ (D : EffectPerspective n) (i : Fin D.outcomes),
    (D.effects i).1 ψ = 0 → E.weight D i = 0

/-! ## QB7.2 — Canonical effect form -/

theorem effectWeight_eq_zero_of_apply_eq_zero (E : EstimationRule n) (ψ : Gleason.H n)
    (hNull : ContextualNullSupport E ψ) (T : Effect n) (hTψ : T.1 ψ = 0) :
    E.effectWeight T = 0 := by
  apply hNull (binaryPerspective T) (0 : Fin 2)
  show ((binaryPerspective T).effects (0 : Fin 2)).1 ψ = 0
  rw [binaryPerspective_effect_zero]
  exact hTψ

/-! ## QB7.3 — Projection form -/

theorem projectionEffect_weight_zero (E : EstimationRule n) (ψ : Gleason.H n)
    (hNull : ContextualNullSupport E ψ) (A : Submodule ℂ (Gleason.H n))
    (hAψ : A.starProjection ψ = 0) :
    E.effectWeight (projectionEffect A) = 0 := by
  apply effectWeight_eq_zero_of_apply_eq_zero E ψ hNull
  show Gleason.projL A ψ = 0
  exact hAψ

/-! ## QB7.5 — Fallback pinning theorem -/

/-- The Born value, under a rank-one pure-state density operator `projL (ℂ
∙ ψ)`, of an *arbitrary* subspace `A`: the general form of
`Gleason.bornValue_span_singleton`, generalized from a singleton `A` to
arbitrary `A`, by the same `rankOne`/`trace_rankOne` computation. -/
private theorem bornValue_projL_singleton (ψ : Gleason.H n) (hψ : ‖ψ‖ = 1)
    (A : Submodule ℂ (Gleason.H n)) :
    Gleason.bornValue (Gleason.projL (ℂ ∙ ψ)) A = ‖A.starProjection ψ‖ ^ 2 := by
  unfold Gleason.bornValue
  set w : Gleason.H n := A.starProjection ψ with hw_def
  have hcomp : (Gleason.projL (ℂ ∙ ψ) : Gleason.H n →ₗ[ℂ] Gleason.H n) ∘ₗ Gleason.projL A
      = (InnerProductSpace.rankOne ℂ ψ w : Gleason.H n →ₗ[ℂ] Gleason.H n) := by
    ext1 x
    simp only [LinearMap.comp_apply, Gleason.projL, ContinuousLinearMap.coe_coe,
      Submodule.starProjection_unit_singleton ℂ hψ, InnerProductSpace.rankOne_apply]
    congr 1
    rw [hw_def]
    exact (Submodule.starProjection_isSymmetric (K := A) ψ x).symm
  rw [hcomp, InnerProductSpace.trace_rankOne]
  have hzero : ⟪ψ - w, w⟫_ℂ = 0 :=
    Submodule.starProjection_inner_eq_zero ψ w (Submodule.starProjection_apply_mem A ψ)
  rw [inner_sub_left, sub_eq_zero] at hzero
  have hzero' : ⟪w, ψ⟫_ℂ = ⟪w, w⟫_ℂ := by
    rw [← inner_conj_symm w ψ, hzero]
    exact inner_conj_symm w w
  rw [hzero', inner_self_eq_norm_sq_to_K]
  norm_cast

/-- **Fallback pure-state pinning theorem.** No existing theorem in the
repository or the pinned dependency directly supplies this general
statement (confirmed by the required searches), so it is proved here,
reusing `BornRule.eq_projL_of_vanishes_on_orthogonal` for the hard operator
identification and the `rankOne`/`trace_rankOne` computation above for the
general Born-value formula. -/
theorem density_bornValue_eq_pure_of_null {n : ℕ} (hn : 1 ≤ n) (ψ : Gleason.H n)
    (hψ : ‖ψ‖ = 1) (ρ : Gleason.H n →ₗ[ℂ] Gleason.H n) (hρ : Gleason.IsDensityOperator ρ)
    (hNullProj : ∀ A : Submodule ℂ (Gleason.H n),
      A.starProjection ψ = 0 → Gleason.bornValue ρ A = 0) :
    ∀ A : Submodule ℂ (Gleason.H n), Gleason.bornValue ρ A = ‖A.starProjection ψ‖ ^ 2 := by
  have hker : ∀ w : Gleason.H n, ⟪ψ, w⟫_ℂ = 0 → ρ w = 0 := by
    intro w hw
    rcases eq_or_ne w 0 with hw0 | hw0
    · simp [hw0]
    · set u : Gleason.H n := (‖w‖⁻¹ : ℂ) • w with hu_def
      have hwnorm_ne : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw0
      have hwu : w = (‖w‖ : ℂ) • u := by
        rw [hu_def, smul_smul, mul_inv_cancel₀ hwnorm_ne, one_smul]
      have hu_norm : ‖u‖ = 1 := by
        rw [hu_def, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg w), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)]
      have hline_eq : (ℂ ∙ w : Submodule ℂ (Gleason.H n)) = ℂ ∙ u := by
        rw [hwu]; exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hwnorm_ne) u
      have hwψ0 : ⟪w, ψ⟫_ℂ = 0 := by
        rw [← inner_conj_symm w ψ, hw]
        simp
      have hprojzero : (ℂ ∙ w : Submodule ℂ (Gleason.H n)).starProjection ψ = 0 := by
        rw [Submodule.starProjection_singleton, hwψ0]
        simp
      have hbv0 : Gleason.bornValue ρ (ℂ ∙ w) = 0 := hNullProj _ hprojzero
      rw [hline_eq] at hbv0
      rw [Gleason.bornValue_span_singleton ρ u hu_norm] at hbv0
      have him0 : (⟪ρ u, u⟫_ℂ).im = 0 := by
        apply Complex.conj_eq_iff_im.mp
        rw [inner_conj_symm u (ρ u)]
        exact (hρ.symmetric u u).symm
      have hzero_cplx : ⟪ρ u, u⟫_ℂ = 0 := Complex.ext hbv0 (by rw [him0]; simp)
      have hρu0 : ρ u = 0 := Gleason.positive_inner_self_eq_zero hρ.symmetric hρ.nonneg hzero_cplx
      rw [hwu, map_smul, hρu0, smul_zero]
  have hρeq : ρ = Gleason.projL (ℂ ∙ ψ) :=
    QuantumFoundations.BornRule.eq_projL_of_vanishes_on_orthogonal hρ hψ hker
  intro A
  rw [hρeq]
  exact bornValue_projL_singleton ψ hψ A

end

end QuantumFoundations.BornRule.EffectPerspectives
