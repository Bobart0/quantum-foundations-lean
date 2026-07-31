import QuantumFoundations.Selectors.Defs
import QuantumFoundations.Naimark.SqrtOp

/-!
**FR.** # Selectors — S4/S5 : NSNC-1 ⟺ Born, et le pont fixe exactement `t`

**Théorème 1**, sans covariance : un sélecteur satisfait NSNC-1 si et
seulement s'il coïncide avec le sélecteur de Born sur tout vecteur unitaire.
Route : un opérateur positif s'annule sur tout vecteur isotrope de sa forme
quadratique (via `sqrtOp`) ; la valeur de Born nulle sur `ψᗮ` force, terme à
terme sur une base adaptée, l'annulation de `σ(ψ)` sur `ψᗮ` ; on conclut par
`BornRule.eq_projL_of_vanishes_on_orthogonal`, déjà présent dans le dépôt.

Ce théorème n'utilise **pas** la covariance : c'est le point du module, visible
dans sa signature.

**S5** : sur la famille candidate, NSNC-1 équivaut exactement à `t = 1`.
Assemblage de clôture : covariance + NSNC-1 équivaut à la règle de Born.

**EN.** # Selectors — S4/S5: NSNC-1 ⟺ Born, and the bridge exactly pins `t`

**Theorem 1**, without covariance: a selector satisfies NSNC-1 if and only if
it coincides with the Born selector on every unit vector. Route: a positive
operator vanishes on every isotropic vector of its quadratic form (via
`sqrtOp`); a vanishing Born value on `ψᗮ` forces, term by term on an adapted
basis, the vanishing of `σ(ψ)` on `ψᗮ`; conclude via
`BornRule.eq_projL_of_vanishes_on_orthogonal`, already present in this
repository.

This theorem does **not** use covariance: that is the point of the module,
visible in its signature.

**S5**: on the candidate family, NSNC-1 is exactly equivalent to `t = 1`.
Closing assembly: covariance + NSNC-1 is equivalent to the Born rule.
-/

namespace QuantumFoundations.Selector

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ}

/--
**FR.** Un opérateur positif annule tout vecteur isotrope de sa forme
quadratique. Route : `sqrtOp`. `⟪ρ w, w⟫ = ⟪√ρ w, √ρ w⟫ = ‖√ρ w‖²` par symétrie
de `√ρ` et `sqrtOp_mul_self` ; d'où `√ρ w = 0` puis `ρ w = 0`.

**EN.** A positive operator vanishes on every isotropic vector of its
quadratic form. Route: `sqrtOp`. `⟪ρ w, w⟫ = ⟪√ρ w, √ρ w⟫ = ‖√ρ w‖²` by
symmetry of `√ρ` and `sqrtOp_mul_self`; hence `√ρ w = 0` then `ρ w = 0`.
-/
private theorem apply_eq_zero_of_quadratic_eq_zero {ρ : H n →ₗ[ℂ] H n}
    (hρ : IsPositiveOp ρ) {w : H n} (h : ⟪ρ w, w⟫_ℂ = 0) : ρ w = 0 := by
  sorry

private theorem vanishes_on_orthogonal_of_bornValue_eq_zero {ρ : H n →ₗ[ℂ] H n}
    (hρ : IsDensityOperator ρ) {ψ : H n} (hψ : ‖ψ‖ = 1)
    (h : bornValue ρ ((ℂ ∙ ψ)ᗮ) = 0) : ∀ w : H n, ⟪ψ, w⟫_ℂ = 0 → ρ w = 0 := by
  sorry

/--
**FR.** **Théorème 1** : NSNC-1 équivaut exactement à la règle de Born, sans
hypothèse de covariance.

**EN.** **Theorem 1**: NSNC-1 is exactly equivalent to the Born rule, without
a covariance hypothesis.
-/
theorem nsnc1_iff_born (σ : Selector n) :
    NSNC1 σ ↔ ∀ ψ : H n, ‖ψ‖ = 1 → σ.ρ ψ = projL (ℂ ∙ ψ) := by
  sorry

/--
**FR.** Sur la famille candidate, NSNC-1 fixe exactement `t = 1`.

**EN.** On the candidate family, NSNC-1 exactly pins `t = 1`.
-/
theorem tSelector_nsnc1_iff_t_eq_one (hn : 2 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    NSNC1 (tSelector n hn t ht0 ht1) ↔ t = 1 := by
  sorry

/--
**FR.** Assemblage de clôture : covariance et NSNC-1 ensemble équivalent
exactement à la règle de Born.

**EN.** Closing assembly: covariance and NSNC-1 together are exactly
equivalent to the Born rule.
-/
theorem covariant_and_nsnc1_iff_born (hn : 2 ≤ n) (σ : Selector n) :
    (IsCovariant σ ∧ NSNC1 σ) ↔ ∀ ψ : H n, ‖ψ‖ = 1 → σ.ρ ψ = projL (ℂ ∙ ψ) := by
  sorry

end
end QuantumFoundations.Selector
