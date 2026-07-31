import QuantumFoundations.Selectors.Classification
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
open QuantumFoundations.Uhlhorn (projL_singleton_unit one_le_of_norm_eq_one)

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
  have hsym : LinearMap.IsSymmetric (QuantumFoundations.sqrtOp ρ) :=
    (QuantumFoundations.sqrtOp_isPositive hρ).1
  have hmul : QuantumFoundations.sqrtOp ρ ∘ₗ QuantumFoundations.sqrtOp ρ = ρ :=
    QuantumFoundations.sqrtOp_mul_self hρ
  have heq : ⟪ρ w, w⟫_ℂ = ⟪QuantumFoundations.sqrtOp ρ w, QuantumFoundations.sqrtOp ρ w⟫_ℂ := by
    conv_lhs => rw [← hmul]
    rw [LinearMap.comp_apply]
    exact hsym (QuantumFoundations.sqrtOp ρ w) w
  rw [heq] at h
  have hself := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (QuantumFoundations.sqrtOp ρ w)
  rw [h] at hself
  have hzero_c : (‖QuantumFoundations.sqrtOp ρ w‖ : ℂ) = 0 := sq_eq_zero_iff.mp hself.symm
  have hnorm : ‖QuantumFoundations.sqrtOp ρ w‖ = 0 := by exact_mod_cast hzero_c
  have hzero : QuantumFoundations.sqrtOp ρ w = 0 := by rwa [norm_eq_zero] at hnorm
  rw [← hmul, LinearMap.comp_apply, hzero, map_zero]

/-- **FR.** Étend `ψ` en base orthonormée `b` (`b i₀ = ψ`) ; développe
`bornValue ρ (ℂ∙ψ)ᗮ` en somme, sur `b`, de termes réels non négatifs
(positivité de `ρ`) ; la somme nulle force chaque terme à zéro ; le terme
en `i₀` est trivialement nul (`projL Aᗮ ψ = 0`), et pour `k ≠ i₀` le terme
donne `⟪b k, ρ (b k)⟫_ℂ = 0`, d'où `ρ (b k) = 0` par
`apply_eq_zero_of_quadratic_eq_zero`. Un `w ⊥ ψ` arbitraire se développe sur
`b` avec un coefficient nul en `i₀`, donc `ρ w = 0` par linéarité.

**EN.** Extends `ψ` to an orthonormal basis `b` (`b i₀ = ψ`); expands
`bornValue ρ (ℂ∙ψ)ᗮ` as a sum, over `b`, of nonnegative real terms
(positivity of `ρ`); the vanishing sum forces every term to vanish; the
`i₀` term is trivially zero (`projL Aᗮ ψ = 0`), and for `k ≠ i₀` the term
gives `⟪b k, ρ (b k)⟫_ℂ = 0`, hence `ρ (b k) = 0` by
`apply_eq_zero_of_quadratic_eq_zero`. An arbitrary `w ⊥ ψ` expands on `b`
with a vanishing `i₀` coefficient, hence `ρ w = 0` by linearity. -/
private theorem vanishes_on_orthogonal_of_bornValue_eq_zero {ρ : H n →ₗ[ℂ] H n}
    (hρ : IsDensityOperator ρ) {ψ : H n} (hψ : ‖ψ‖ = 1)
    (h : bornValue ρ ((ℂ ∙ ψ)ᗮ) = 0) : ∀ w : H n, ⟪ψ, w⟫_ℂ = 0 → ρ w = 0 := by
  have hn1 : 1 ≤ n := one_le_of_norm_eq_one hψ
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_extension_complex hn1 (fun _ : Fin 1 => ψ)
    (by rw [orthonormal_iff_ite]; intro i j; fin_cases i; fin_cases j; simp [hψ])
  set i₀ : Fin n := Fin.castLE hn1 (0 : Fin 1) with hi0_def
  have hbi₀ : b i₀ = ψ := hb 0
  have hp_i0 : projL (ℂ ∙ ψ)ᗮ (b i₀) = 0 := by
    have hp1 : projL (ℂ ∙ ψ) ψ = ψ := by
      rw [projL_singleton_unit ψ ψ hψ, inner_self_eq_norm_sq_to_K, hψ]; norm_num
    have hp2 : projL (ℂ ∙ ψ) ψ + projL (ℂ ∙ ψ)ᗮ ψ = ψ :=
      congrArg (· ψ) (projL_add_projL_compl (ℂ ∙ ψ))
    rw [hbi₀]
    rw [hp1] at hp2
    exact add_left_cancel (hp2.trans (add_zero ψ).symm)
  have hp_ne : ∀ k : Fin n, k ≠ i₀ → projL (ℂ ∙ ψ)ᗮ (b k) = b k := by
    intro k hk
    have hbk_perp : ⟪ψ, b k⟫_ℂ = 0 := by
      rw [← hbi₀]
      exact b.inner_eq_ite i₀ k ▸ (if_neg (Ne.symm hk))
    have hp1 : projL (ℂ ∙ ψ) (b k) = 0 := by
      rw [projL_singleton_unit ψ (b k) hψ, hbk_perp, zero_smul]
    have hp2 : projL (ℂ ∙ ψ) (b k) + projL (ℂ ∙ ψ)ᗮ (b k) = b k :=
      congrArg (· (b k)) (projL_add_projL_compl (ℂ ∙ ψ))
    rw [hp1, zero_add] at hp2
    exact hp2
  have hborn_sum : bornValue ρ ((ℂ ∙ ψ)ᗮ) = ∑ k, (⟪b k, ρ (projL (ℂ ∙ ψ)ᗮ (b k))⟫_ℂ).re := by
    show (LinearMap.trace ℂ (H n) (ρ ∘ₗ projL (ℂ ∙ ψ)ᗮ)).re = _
    rw [LinearMap.trace_eq_sum_inner (ρ ∘ₗ projL (ℂ ∙ ψ)ᗮ) b, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [LinearMap.comp_apply]
  have hterm_nonneg : ∀ k : Fin n, 0 ≤ (⟪b k, ρ (projL (ℂ ∙ ψ)ᗮ (b k))⟫_ℂ).re := by
    intro k
    by_cases hk : k = i₀
    · rw [hk, hp_i0, map_zero, inner_zero_right]; simp
    · rw [hp_ne k hk, ← hρ.symmetric (b k) (b k)]
      exact hρ.nonneg (b k)
  have hterm_zero : ∀ k : Fin n, (⟪b k, ρ (projL (ℂ ∙ ψ)ᗮ (b k))⟫_ℂ).re = 0 := by
    intro k
    have hsum0 : ∑ k, (⟪b k, ρ (projL (ℂ ∙ ψ)ᗮ (b k))⟫_ℂ).re = 0 := hborn_sum ▸ h
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hterm_nonneg k)).mp hsum0
    exact hall k (Finset.mem_univ k)
  have hρbk_zero : ∀ k : Fin n, k ≠ i₀ → ρ (b k) = 0 := by
    intro k hk
    have hre0 : (⟪b k, ρ (b k)⟫_ℂ).re = 0 := by
      have ht := hterm_zero k; rwa [hp_ne k hk] at ht
    have hsymmk : ⟪ρ (b k), b k⟫_ℂ = ⟪b k, ρ (b k)⟫_ℂ := hρ.symmetric (b k) (b k)
    have hreal : ⟪b k, ρ (b k)⟫_ℂ = ((⟪b k, ρ (b k)⟫_ℂ).re : ℂ) := by
      have hconjeq : (starRingEnd ℂ) ⟪b k, ρ (b k)⟫_ℂ = ⟪b k, ρ (b k)⟫_ℂ := by
        rw [inner_conj_symm, hsymmk]
      exact (Complex.conj_eq_iff_re.mp hconjeq).symm
    have hzero_c : ⟪b k, ρ (b k)⟫_ℂ = 0 := by rw [hreal, hre0]; norm_num
    apply apply_eq_zero_of_quadratic_eq_zero ⟨hρ.symmetric, hρ.nonneg⟩
    rw [hsymmk, hzero_c]
  intro w hw
  conv_lhs => rw [← OrthonormalBasis.sum_repr b w]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro k _
  rw [map_smul]
  by_cases hk : k = i₀
  · have hc : (b.repr w).ofLp i₀ = 0 := by
      rw [OrthonormalBasis.repr_apply_apply, hbi₀]; exact hw
    rw [hk, hc, zero_smul]
  · rw [hρbk_zero k hk, smul_zero]

/--
**FR.** **Théorème 1** : NSNC-1 équivaut exactement à la règle de Born, sans
hypothèse de covariance.

**EN.** **Theorem 1**: NSNC-1 is exactly equivalent to the Born rule, without
a covariance hypothesis.
-/
theorem nsnc1_iff_born (σ : Selector n) :
    NSNC1 σ ↔ ∀ ψ : H n, ‖ψ‖ = 1 → σ.ρ ψ = projL (ℂ ∙ ψ) := by
  constructor
  · intro hnsnc ψ hψ
    have hden := σ.isDensity ψ hψ
    exact QuantumFoundations.BornRule.eq_projL_of_vanishes_on_orthogonal hden hψ
      (vanishes_on_orthogonal_of_bornValue_eq_zero hden hψ (hnsnc ψ hψ))
  · intro heq ψ hψ
    show bornValue (σ.ρ ψ) ((ℂ ∙ ψ)ᗮ) = 0
    rw [heq ψ hψ]
    have hadd := bornValue_add_bornValue_compl (projL (ℂ ∙ ψ)) (ℂ ∙ ψ)
    rw [trace_projL_singleton hψ] at hadd
    have hA : bornValue (projL (ℂ ∙ ψ)) (ℂ ∙ ψ) = 1 := by
      have hp1 : projL (ℂ ∙ ψ) ψ = ψ := by
        rw [projL_singleton_unit ψ ψ hψ, inner_self_eq_norm_sq_to_K, hψ]; norm_num
      rw [Gleason.bornValue_span_singleton (projL (ℂ ∙ ψ)) ψ hψ, hp1,
        inner_self_eq_norm_sq_to_K, hψ]
      norm_num
    rw [hA] at hadd
    norm_num at hadd
    linarith

/--
**FR.** Sur la famille candidate, NSNC-1 fixe exactement `t = 1`. Route :
`bornValue_add_bornValue_compl` + `trace_one` donnent
`bornValue (tDensity n t ψ) (ℂ∙ψ) + bornValue (tDensity n t ψ) (ℂ∙ψ)ᗮ = 1` ;
`Gleason.bornValue_span_singleton` + `tDensity_apply_self` identifient le
premier terme à `t`, d'où le second vaut `1 − t`.

**EN.** On the candidate family, NSNC-1 exactly pins `t = 1`. Route:
`bornValue_add_bornValue_compl` + `trace_one` give
`bornValue (tDensity n t ψ) (ℂ∙ψ) + bornValue (tDensity n t ψ) (ℂ∙ψ)ᗮ = 1`;
`Gleason.bornValue_span_singleton` + `tDensity_apply_self` identify the
first term with `t`, hence the second equals `1 − t`.
-/
theorem tSelector_nsnc1_iff_t_eq_one (hn : 2 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    NSNC1 (tSelector n hn t ht0 ht1) ↔ t = 1 := by
  have hborn : ∀ ψ : H n, ‖ψ‖ = 1 →
      bornValue ((tSelector n hn t ht0 ht1).ρ ψ) ((ℂ ∙ ψ)ᗮ) = 1 - t := by
    intro ψ hψ
    show bornValue (tDensity n t ψ) ((ℂ ∙ ψ)ᗮ) = 1 - t
    have htrace : LinearMap.trace ℂ (H n) (tDensity n t ψ) = 1 :=
      (tDensity_isDensity hn ht0 ht1 hψ).trace_one
    have hadd := bornValue_add_bornValue_compl (tDensity n t ψ) (ℂ ∙ ψ)
    rw [htrace] at hadd
    have hA : bornValue (tDensity n t ψ) (ℂ ∙ ψ) = t := by
      rw [Gleason.bornValue_span_singleton (tDensity n t ψ) ψ hψ, tDensity_apply_self hψ,
        inner_smul_left]
      have hself : ⟪ψ, ψ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
      rw [hself, mul_one, Complex.conj_ofReal]
      norm_num
    rw [hA] at hadd
    norm_num at hadd
    linarith
  constructor
  · intro hnsnc
    have hψ₀ : ‖(EuclideanSpace.single (⟨0, by omega⟩ : Fin n) (1 : ℂ) : H n)‖ = 1 := by
      rw [PiLp.norm_single]; norm_num
    have h1 := hnsnc _ hψ₀
    rw [hborn _ hψ₀] at h1
    linarith
  · intro ht
    subst ht
    intro ψ hψ
    rw [hborn ψ hψ]
    norm_num

/--
**FR.** Assemblage de clôture : covariance et NSNC-1 ensemble équivalent
exactement à la règle de Born. Le sens direct est déjà `nsnc1_iff_born` (la
covariance n'y sert pas) ; le sens réciproque construit le témoin `t = 1` via
`covariant_iff_tSelector` et `bornSelector_eq_tDensity_one`.

**EN.** Closing assembly: covariance and NSNC-1 together are exactly
equivalent to the Born rule. The forward direction is already
`nsnc1_iff_born` (covariance plays no role there); the converse builds the
`t = 1` witness via `covariant_iff_tSelector` and
`bornSelector_eq_tDensity_one`.
-/
theorem covariant_and_nsnc1_iff_born (hn : 2 ≤ n) (σ : Selector n) :
    (IsCovariant σ ∧ NSNC1 σ) ↔ ∀ ψ : H n, ‖ψ‖ = 1 → σ.ρ ψ = projL (ℂ ∙ ψ) := by
  constructor
  · rintro ⟨_, hnsnc⟩
    exact (nsnc1_iff_born σ).mp hnsnc
  · intro heq
    refine ⟨?_, (nsnc1_iff_born σ).mpr heq⟩
    rw [covariant_iff_tSelector hn σ]
    refine ⟨1, by norm_num, by norm_num, fun ψ hψ => ?_⟩
    rw [heq ψ hψ]
    exact bornSelector_eq_tDensity_one hψ

end
end QuantumFoundations.Selector
