import QuantumFoundations.Wigner.VConstruction
import QuantumFoundations.Wigner.Scalar

/-!
# W4 — LE cœur : analyse de `V` (Bargmann §4, l'analogue de `sqrtOp` pour N1)

Seul contenu mathématique réellement neuf du dépôt Wigner (le reste est de la
plomberie disciplinée, comme N2-N3-N5 l'étaient pour Naimark).

Le case split de la construction du repère adapté (`V_additive` etc.) porte sur la
**dépendance linéaire** de la paire de vecteurs, PAS sur `n` : `n = 2` est absorbé
automatiquement (la dépendance y est forcée), aucune disjonction `n = 2` vs `n ≥ 3`
n'apparaît dans le cœur — contrairement à Gleason.
-/

namespace QuantumFoundations.Wigner

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ} {T : H n → H n}

/-- Étape 1 de Bargmann §4.2 : si `T` préserve les probabilités de transition, une
rotation de phase `c • f` sur un vecteur unitaire `f` induit une rotation de phase
sur `T f` — cas d'égalité de Cauchy-Schwarz appliqué à `T f, T(c•f)` (tous deux
unitaires, produit scalaire de module 1). -/
private theorem T_phase (hT : IsWignerMap T) {f : H n} (hf : ‖f‖ = 1) {c : ℂ} (hc : ‖c‖ = 1) :
    ∃ lam : ℂ, ‖lam‖ = 1 ∧ T (c • f) = lam • T f := by
  have hcf : ‖c • f‖ = 1 := by rw [norm_smul, hc, hf, mul_one]
  have hTf : ‖T f‖ = 1 := norm_T_unit hT hf
  have hTcf : ‖T (c • f)‖ = 1 := norm_T_unit hT hcf
  have hff : ⟪f, f⟫_ℂ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hf]; norm_num
  have hinner : ⟪f, c • f⟫_ℂ = c := by rw [inner_smul_right, hff, mul_one]
  have hnorm : ‖⟪T f, T (c • f)⟫_ℂ‖ = ‖T f‖ * ‖T (c • f)‖ := by
    rw [hT f (c • f) hf hcf, hinner, hc, hTf, hTcf, mul_one]
  have hTfne : T f ≠ 0 := by
    intro h; rw [h, norm_zero] at hTf; exact one_ne_zero hTf.symm
  have hor := (norm_inner_eq_norm_tfae ℂ (T f) (T (c • f))).out 0 2
  rcases hor.mp hnorm with h0 | ⟨r, hr⟩
  · exact absurd h0 hTfne
  · refine ⟨r, ?_, hr⟩
    have hrnorm : ‖T (c • f)‖ = ‖r‖ * ‖T f‖ := by rw [hr, norm_smul]
    rw [hTcf, hTf, mul_one] at hrnorm
    exact hrnorm.symm

/-- Étape 2 de Bargmann §4.2, généralisée à un `f` unitaire QUELCONQUE de `𝒫` (pas
seulement `refVec`) : `V` restreinte à la direction de `f` est colinéaire à `V f`,
avec le coefficient IDENTIFIÉ comme `chidir T f α` (unicité du coefficient de
colinéarité contre `V f ≠ 0`, cf. `norm_V`). -/
private theorem V_dir_colinear (hT : IsWignerMap T) (hn : 2 ≤ n) {f : H n} (hf : InPerp f)
    (hfu : ‖f‖ = 1) (α : ℂ) : V T (α • f) = chidir T f α • V T f := by
  by_cases hα0 : α = 0
  · subst hα0
    have hV0 : V T (0 : H n) = 0 := by
      have h := norm_V hT hn 0 (by show ⟪e n, (0 : H n)⟫_ℂ = 0; simp)
      rw [norm_zero] at h
      exact norm_eq_zero.mp h
    rw [zero_smul, hV0]
    show (0 : H n) = ⟪V T f, V T ((0 : ℂ) • f)⟫_ℂ • V T f
    rw [zero_smul, hV0, inner_zero_right, zero_smul]
  · have hf0 : f ≠ 0 := by intro h; rw [h, norm_zero] at hfu; exact one_ne_zero hfu.symm
    have hz0 : α • f ≠ 0 := smul_ne_zero hα0 hf0
    have hzf : InPerp (α • f) := by
      show ⟪e n, α • f⟫_ℂ = 0
      rw [inner_smul_right, hf]; ring
    obtain ⟨δ, hδnorm, hVz⟩ := V_colinear hT hn (α • f) hzf hz0
    have hnormaf : ‖α • f‖ = ‖α‖ := by rw [norm_smul, hfu, mul_one]
    have hc : (‖α • f‖⁻¹ : ℂ) • (α • f) = (α * (‖α‖ : ℂ)⁻¹) • f := by
      rw [hnormaf, smul_smul]; congr 1; ring
    rw [hc] at hVz
    set c : ℂ := α * (‖α‖ : ℂ)⁻¹ with hc_def
    have hαne : ‖α‖ ≠ 0 := norm_ne_zero_iff.mpr hα0
    have hcnorm : ‖c‖ = 1 := by
      rw [hc_def, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        mul_inv_cancel₀ hαne]
    obtain ⟨lam, _, hTcf⟩ := T_phase hT hfu hcnorm
    rw [hTcf, smul_smul] at hVz
    obtain ⟨δf, hδfnorm, hVf⟩ := V_colinear hT hn f hf hf0
    rw [hfu, Complex.ofReal_one, inv_one, one_smul] at hVf
    have hδfne : δf ≠ 0 := by
      intro h; rw [h, norm_zero, hfu] at hδfnorm; exact zero_ne_one hδfnorm
    have hTf_eq : T f = δf⁻¹ • V T f := by
      rw [hVf, smul_smul, inv_mul_cancel₀ hδfne, one_smul]
    rw [hTf_eq, smul_smul] at hVz
    set c0 : ℂ := δ * lam * δf⁻¹ with hc0_def
    have hchidir : chidir T f α = c0 := by
      show ⟪V T f, V T (α • f)⟫_ℂ = c0
      rw [hVz, inner_smul_right]
      have hVfVf : ⟪V T f, V T f⟫_ℂ = (1 : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K, norm_V hT hn f hf, hfu]; norm_num
      rw [hVfVf, mul_one]
    rw [hVz, hchidir]

/-- (14)(15)(15a)(15b) : `chidir T f` est une fonction scalaire qui vérifie les
hypothèses de `scalar_dichotomy` pour tout `f` unitaire de `𝒫`. -/
theorem chidir_dichotomy (hT : IsWignerMap T) (hn : 2 ≤ n) (f : H n) (hf : InPerp f)
    (hfu : ‖f‖ = 1) :
    (fun α => chidir T f α) = id ∨ (fun α => chidir T f α) = starRingEnd ℂ := by
  have hInPerp : ∀ β : ℂ, InPerp (β • f) := by
    intro β; show ⟪e n, β • f⟫_ℂ = 0; rw [inner_smul_right, hf]; ring
  have hff : ⟪f, f⟫_ℂ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hfu]; norm_num
  have hnorm : ∀ α : ℂ, ‖chidir T f α‖ = ‖α‖ := by
    intro α
    show ‖⟪V T f, V T (α • f)⟫_ℂ‖ = ‖α‖
    rw [norm_inner_V hT hn f (α • f) hf (hInPerp α), inner_smul_right, hff, mul_one]
  have hone : chidir T f 1 = 1 := by
    show ⟪V T f, V T ((1 : ℂ) • f)⟫_ℂ = 1
    rw [one_smul, inner_self_eq_norm_sq_to_K, norm_V hT hn f hf, hfu]; norm_num
  have hre : ∀ α β : ℂ, (starRingEnd ℂ (chidir T f α) * chidir T f β).re =
      (starRingEnd ℂ α * β).re := by
    intro α β
    have hVfVf : ⟪V T f, V T f⟫_ℂ = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, norm_V hT hn f hf, hfu]; norm_num
    have hkey : (starRingEnd ℂ (chidir T f α) * chidir T f β) = ⟪V T (α • f), V T (β • f)⟫_ℂ := by
      rw [V_dir_colinear hT hn hf hfu α, V_dir_colinear hT hn hf hfu β, inner_smul_left,
        inner_smul_right, hVfVf, mul_one]
    rw [hkey, re_inner_V hT hn (α • f) (β • f) (hInPerp α) (hInPerp β), inner_smul_left,
      inner_smul_right, hff, mul_one]
  exact scalar_dichotomy hnorm hone hre

private theorem refVec_norm (hn : 2 ≤ n) : ‖refVec n‖ = 1 := by
  simp only [refVec, dif_pos hn, PiLp.norm_single]
  norm_num

private theorem refVec_InPerp (hn : 2 ≤ n) : InPerp (refVec n) := by
  have h0 : 0 < n := by omega
  show ⟪e n, refVec n⟫_ℂ = 0
  simp only [e, refVec, dif_pos h0, dif_pos hn, EuclideanSpace.inner_single_left,
    PiLp.single_apply]
  simp

/-- `chi` (calculé le long de `refVec`) coïncide avec `chidir` le long de
n'importe quel autre vecteur unitaire de `𝒫` : globalisation de la dichotomie
directionnelle (Bargmann §4, `w = f₁ + f₂`). -/
theorem chi_eq_chidir (hT : IsWignerMap T) (hn : 2 ≤ n) (f : H n) (hf : InPerp f)
    (hfu : ‖f‖ = 1) (α : ℂ) : chi T α = chidir T f α := by
  sorry

/-- `chi` est globalement l'identité ou la conjugaison (conséquence directe de
`chidir_dichotomy` appliqué à `refVec`). -/
theorem chi_dichotomy (hT : IsWignerMap T) (hn : 2 ≤ n) :
    (fun α => chi T α) = id ∨ (fun α => chi T α) = starRingEnd ℂ :=
  chidir_dichotomy hT hn (refVec n) (refVec_InPerp hn) (refVec_norm hn)

/-- (18a) `V` est additive sur `𝒫`. -/
theorem V_additive (hT : IsWignerMap T) (hn : 2 ≤ n) (y z : H n) (hy : InPerp y)
    (hz : InPerp z) : V T (y + z) = V T y + V T z := by
  sorry

/-- (18b) `V` est `χ`-homogène sur `𝒫`. -/
theorem V_chi_homogeneous (hT : IsWignerMap T) (hn : 2 ≤ n) (c : ℂ) (z : H n)
    (hz : InPerp z) : V T (c • z) = chi T c • V T z := by
  sorry

/-- (18c) `V` transporte le produit scalaire via `χ` sur `𝒫`. -/
theorem inner_V_eq_chi_inner (hT : IsWignerMap T) (hn : 2 ≤ n) (y z : H n)
    (hy : InPerp y) (hz : InPerp z) : ⟪V T y, V T z⟫_ℂ = chi T ⟪y, z⟫_ℂ := by
  sorry

end
end QuantumFoundations.Wigner
