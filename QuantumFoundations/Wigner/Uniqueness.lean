import QuantumFoundations.Wigner.Main

/-!
# W6 (optionnel) — Unicité et exclusivité (Bargmann §1.5, §6 restreint)

Deux livrables indépendants, de priorité basse :
(A) Exclusivité unitaire/antiunitaire (Bargmann §1.5, témoin `Delta = i/6`).
(B) Unicité de `U` à phase globale près relativement au choix du représentant
`eImg` (version RESTREINTE : pas la généralité complète du Théorème 2 de
Bargmann, qui demanderait de rederiver l'homogénéité réelle depuis
l'additivité + l'isométrie pour un `U'` complètement arbitraire — non
nécessaire ici, puisque toute la liberté de `wigner` provient du choix de
`eImg`).
-/

namespace QuantumFoundations.Wigner

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ} {T : H n → H n}

/-! ## (A) Exclusivité unitaire/antiunitaire (Bargmann §1.5) -/

/-- Produit cyclique de rayons, témoin de non-réalité (Bargmann §1.5). -/
def Delta (a b c : H n) : ℂ := ⟪a, b⟫_ℂ * ⟪b, c⟫_ℂ * ⟪c, a⟫_ℂ

private theorem conj_mul_self_eq_one {z : ℂ} (h : ‖z‖ = 1) : (starRingEnd ℂ) z * z = 1 := by
  rw [mul_comm, Complex.mul_conj]
  norm_cast
  rw [← Complex.sq_norm, h]
  norm_num

/-- Analogue semilinéaire de `LinearIsometryEquiv.inner_map_map`, absent de
Mathlib pour `σ ≠ id` — dérivé à la main par polarisation. -/
private theorem conj_isometry_inner {U' : H n → H n}
    (hadd : ∀ a b, U' (a + b) = U' a + U' b)
    (hsmul : ∀ (c : ℂ) a, U' (c • a) = (starRingEnd ℂ) c • U' a)
    (hiso : ∀ a, ‖U' a‖ = ‖a‖) (a b : H n) :
    ⟪U' a, U' b⟫_ℂ = (starRingEnd ℂ) ⟪a, b⟫_ℂ := by
  have hRe : (⟪U' a, U' b⟫_ℂ).re = (⟪a, b⟫_ℂ).re := by
    have h1 : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * RCLike.re ⟪a, b⟫_ℂ + ‖b‖ ^ 2 := norm_add_sq (𝕜 := ℂ) a b
    have h2 : ‖U' a + U' b‖ ^ 2
        = ‖U' a‖ ^ 2 + 2 * RCLike.re ⟪U' a, U' b⟫_ℂ + ‖U' b‖ ^ 2 := norm_add_sq (𝕜 := ℂ) (U' a) (U' b)
    rw [← hadd, hiso, hiso, hiso] at h2
    have hfin : RCLike.re ⟪a, b⟫_ℂ = RCLike.re ⟪U' a, U' b⟫_ℂ := by linarith [h1, h2]
    exact hfin.symm
  have hIm : (⟪U' a, U' b⟫_ℂ).im = -(⟪a, b⟫_ℂ).im := by
    have h1 : ‖a + Complex.I • b‖ ^ 2
        = ‖a‖ ^ 2 + 2 * RCLike.re ⟪a, Complex.I • b⟫_ℂ + ‖Complex.I • b‖ ^ 2 :=
      norm_add_sq (𝕜 := ℂ) a (Complex.I • b)
    have h2 : ‖U' a - Complex.I • U' b‖ ^ 2
        = ‖U' a‖ ^ 2 - 2 * RCLike.re ⟪U' a, Complex.I • U' b⟫_ℂ + ‖Complex.I • U' b‖ ^ 2 :=
      norm_sub_sq (𝕜 := ℂ) (U' a) (Complex.I • U' b)
    have hUab : U' (a + Complex.I • b) = U' a - Complex.I • U' b := by
      rw [hadd, hsmul, sub_eq_add_neg]
      congr 1
      simp
    rw [← hUab, hiso, hiso] at h2
    have hrw1 : RCLike.re ⟪a, Complex.I • b⟫_ℂ = -(⟪a, b⟫_ℂ).im := by
      rw [inner_smul_right]
      show (Complex.I * ⟪a, b⟫_ℂ).re = -(⟪a, b⟫_ℂ).im
      simp [Complex.mul_re]
    have hrw2 : RCLike.re ⟪U' a, Complex.I • U' b⟫_ℂ = -(⟪U' a, U' b⟫_ℂ).im := by
      rw [inner_smul_right]
      show (Complex.I * ⟪U' a, U' b⟫_ℂ).re = -(⟪U' a, U' b⟫_ℂ).im
      simp [Complex.mul_re]
    rw [hrw1] at h1
    rw [hrw2] at h2
    have hnI : ‖Complex.I • b‖ = ‖b‖ := by rw [norm_smul]; simp
    have hnI' : ‖Complex.I • U' b‖ = ‖U' b‖ := by rw [norm_smul]; simp
    rw [hnI] at h1
    rw [hnI', hiso] at h2
    nlinarith [h1, h2]
  exact Complex.ext hRe (by rw [Complex.conj_im]; exact hIm)

/-- Étape 1, branche linéaire (`chi = id`) : `Delta` est invariant sous `T`. -/
theorem delta_transform_lin (_hT : IsWignerMap T) (_hn : 2 ≤ n) (U : H n ≃ₗᵢ[ℂ] H n)
    (hcompat : ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U x)
    (a b c : H n) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    Delta (T a) (T b) (T c) = Delta a b c := by
  obtain ⟨ca, hcanorm, hTa⟩ := hcompat a ha
  obtain ⟨cb, hcbnorm, hTb⟩ := hcompat b hb
  obtain ⟨cc, hccnorm, hTc⟩ := hcompat c hc
  show ⟪T a, T b⟫_ℂ * ⟪T b, T c⟫_ℂ * ⟪T c, T a⟫_ℂ = Delta a b c
  rw [hTa, hTb, hTc]
  show ⟪ca • U a, cb • U b⟫_ℂ * ⟪cb • U b, cc • U c⟫_ℂ * ⟪cc • U c, ca • U a⟫_ℂ
      = ⟪a, b⟫_ℂ * ⟪b, c⟫_ℂ * ⟪c, a⟫_ℂ
  simp only [inner_smul_left, inner_smul_right, LinearIsometryEquiv.inner_map_map]
  have h1 := conj_mul_self_eq_one hcanorm
  have h2 := conj_mul_self_eq_one hcbnorm
  have h3 := conj_mul_self_eq_one hccnorm
  linear_combination
    (⟪a, b⟫_ℂ * ⟪b, c⟫_ℂ * ⟪c, a⟫_ℂ * cb * (starRingEnd ℂ) cb * cc * (starRingEnd ℂ) cc) * h1
    + (⟪a, b⟫_ℂ * ⟪b, c⟫_ℂ * ⟪c, a⟫_ℂ * (starRingEnd ℂ) cc * cc) * h2
    + (⟪a, b⟫_ℂ * ⟪b, c⟫_ℂ * ⟪c, a⟫_ℂ) * h3

/-- Étape 1, branche antiunitaire (`chi = conj`) : `Delta` est envoyé sur son
conjugué sous `T`. -/
theorem delta_transform_conj (_hT : IsWignerMap T) (_hn : 2 ≤ n)
    (U' : H n ≃ₛₗᵢ[starRingEnd ℂ] H n)
    (hcompat : ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U' x)
    (a b c : H n) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    Delta (T a) (T b) (T c) = (starRingEnd ℂ) (Delta a b c) := by
  obtain ⟨ca, hcanorm, hTa⟩ := hcompat a ha
  obtain ⟨cb, hcbnorm, hTb⟩ := hcompat b hb
  obtain ⟨cc, hccnorm, hTc⟩ := hcompat c hc
  have hUadd : ∀ x y : H n, U' (x + y) = U' x + U' y := fun x y => U'.map_add x y
  have hUsmul : ∀ (z : ℂ) (x : H n), U' (z • x) = (starRingEnd ℂ) z • U' x := fun z x =>
    U'.map_smulₛₗ z x
  have hUiso : ∀ x : H n, ‖U' x‖ = ‖x‖ := fun x => U'.norm_map x
  show ⟪T a, T b⟫_ℂ * ⟪T b, T c⟫_ℂ * ⟪T c, T a⟫_ℂ = (starRingEnd ℂ) (Delta a b c)
  rw [hTa, hTb, hTc]
  show ⟪ca • U' a, cb • U' b⟫_ℂ * ⟪cb • U' b, cc • U' c⟫_ℂ * ⟪cc • U' c, ca • U' a⟫_ℂ
      = (starRingEnd ℂ) (⟪a, b⟫_ℂ * ⟪b, c⟫_ℂ * ⟪c, a⟫_ℂ)
  simp only [inner_smul_left, inner_smul_right, conj_isometry_inner hUadd hUsmul hUiso, map_mul]
  have h1 := conj_mul_self_eq_one hcanorm
  have h2 := conj_mul_self_eq_one hcbnorm
  have h3 := conj_mul_self_eq_one hccnorm
  linear_combination
    ((starRingEnd ℂ) ⟪a, b⟫_ℂ * (starRingEnd ℂ) ⟪b, c⟫_ℂ * (starRingEnd ℂ) ⟪c, a⟫_ℂ
      * cb * (starRingEnd ℂ) cb * cc * (starRingEnd ℂ) cc) * h1
    + ((starRingEnd ℂ) ⟪a, b⟫_ℂ * (starRingEnd ℂ) ⟪b, c⟫_ℂ * (starRingEnd ℂ) ⟪c, a⟫_ℂ
      * (starRingEnd ℂ) cc * cc) * h2
    + ((starRingEnd ℂ) ⟪a, b⟫_ℂ * (starRingEnd ℂ) ⟪b, c⟫_ℂ * (starRingEnd ℂ) ⟪c, a⟫_ℂ) * h3

private theorem he_self' (hn : 2 ≤ n) : ⟪e n, e n⟫_ℂ = (1 : ℂ) := by
  have h0 : 0 < n := by omega
  simp only [e, dif_pos h0, EuclideanSpace.inner_single_left, PiLp.single_apply]
  simp

private theorem he_norm' (hn : 2 ≤ n) : ‖e n‖ = 1 := by
  have h0 : 0 < n := by omega
  simp only [e, dif_pos h0, PiLp.norm_single]
  norm_num

private theorem refVec_norm' (hn : 2 ≤ n) : ‖refVec n‖ = 1 := by
  simp only [refVec, dif_pos hn, PiLp.norm_single]
  norm_num

private theorem refVec_InPerp' (hn : 2 ≤ n) : InPerp (refVec n) := by
  have h0 : 0 < n := by omega
  show ⟪e n, refVec n⟫_ℂ = 0
  simp only [e, refVec, dif_pos h0, dif_pos hn, EuclideanSpace.inner_single_left,
    PiLp.single_apply]
  simp

/-- Témoins de non-réalité de Bargmann §1.5 : deux vecteurs unitaires formant,
avec `e`, un triplet dont `Delta` n'est pas réel. -/
private noncomputable def e2 (n : ℕ) : H n := ((Real.sqrt 2)⁻¹ : ℂ) • (e n - refVec n)

private noncomputable def e3 (n : ℕ) : H n :=
  ((Real.sqrt 3)⁻¹ : ℂ) • (e n + (1 - Complex.I) • refVec n)

private theorem e2_norm (hn : 2 ≤ n) : ‖e2 n‖ = 1 := by
  have hef : ⟪e n, refVec n⟫_ℂ = 0 := refVec_InPerp' hn
  have hsub2 : ‖e n - refVec n‖ ^ 2 = 2 := by
    rw [norm_sub_sq (𝕜 := ℂ), he_norm' hn, refVec_norm' hn, hef]
    norm_num
  have hc2sq : (Real.sqrt 2)⁻¹ ^ 2 = (1 / 2 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]; norm_num
  show ‖((Real.sqrt 2)⁻¹ : ℂ) • (e n - refVec n)‖ = 1
  have hsq : ‖((Real.sqrt 2)⁻¹ : ℂ) • (e n - refVec n)‖ ^ 2 = 1 := by
    rw [norm_smul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2), hc2sq, hsub2]
    norm_num
  nlinarith [hsq, norm_nonneg (((Real.sqrt 2)⁻¹ : ℂ) • (e n - refVec n)),
    sq_nonneg (‖((Real.sqrt 2)⁻¹ : ℂ) • (e n - refVec n)‖ - 1)]

private theorem e3_norm (hn : 2 ≤ n) : ‖e3 n‖ = 1 := by
  have hef : ⟪e n, refVec n⟫_ℂ = 0 := refVec_InPerp' hn
  have hnormI : ‖(1 - Complex.I) • refVec n‖ ^ 2 = 2 := by
    rw [norm_smul, mul_pow, refVec_norm' hn, Complex.sq_norm, Complex.normSq_apply]
    norm_num
  have hcross : (⟪e n, (1 - Complex.I) • refVec n⟫_ℂ).re = 0 := by
    rw [inner_smul_right, hef]; simp
  have hadd3 : ‖e n + (1 - Complex.I) • refVec n‖ ^ 2 = 3 := by
    rw [norm_add_sq (𝕜 := ℂ), he_norm' hn]
    rw [show RCLike.re ⟪e n, (1 - Complex.I) • refVec n⟫_ℂ
        = (⟪e n, (1 - Complex.I) • refVec n⟫_ℂ).re from rfl, hcross, hnormI]
    norm_num
  have hc3sq : (Real.sqrt 3)⁻¹ ^ 2 = (1 / 3 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)]; norm_num
  show ‖((Real.sqrt 3)⁻¹ : ℂ) • (e n + (1 - Complex.I) • refVec n)‖ = 1
  have hsq : ‖((Real.sqrt 3)⁻¹ : ℂ) • (e n + (1 - Complex.I) • refVec n)‖ ^ 2 = 1 := by
    rw [norm_smul, mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 3), hc3sq, hadd3]
    norm_num
  nlinarith [hsq, norm_nonneg (((Real.sqrt 3)⁻¹ : ℂ) • (e n + (1 - Complex.I) • refVec n)),
    sq_nonneg (‖((Real.sqrt 3)⁻¹ : ℂ) • (e n + (1 - Complex.I) • refVec n)‖ - 1)]

/-- Étape 2 : calcul explicite `Delta(e, e2, e3) = i/6` (Bargmann §1.5). -/
theorem bargmann_delta_witness (hn : 2 ≤ n) : Delta (e n) (e2 n) (e3 n) = Complex.I / 6 := by
  have hself := he_self' hn
  have hfself : ⟪refVec n, refVec n⟫_ℂ = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, refVec_norm' hn]; norm_num
  have hef : ⟪e n, refVec n⟫_ℂ = 0 := refVec_InPerp' hn
  have hfe : ⟪refVec n, e n⟫_ℂ = 0 := by
    have h : (starRingEnd ℂ) ⟪refVec n, e n⟫_ℂ = 0 := by
      rw [inner_conj_symm (e n) (refVec n)]; exact hef
    have h2 := congrArg (starRingEnd ℂ) h
    simpa using h2
  show ⟪e n, ((Real.sqrt 2)⁻¹ : ℂ) • (e n - refVec n)⟫_ℂ *
      ⟪((Real.sqrt 2)⁻¹ : ℂ) • (e n - refVec n),
        ((Real.sqrt 3)⁻¹ : ℂ) • (e n + (1 - Complex.I) • refVec n)⟫_ℂ *
      ⟪((Real.sqrt 3)⁻¹ : ℂ) • (e n + (1 - Complex.I) • refVec n), e n⟫_ℂ = Complex.I / 6
  simp only [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, inner_add_left,
    inner_add_right, hself, hfself, hef, hfe, Complex.conj_ofReal, map_sub, map_one, map_inv₀,
    Complex.conj_I]
  have hc2sq : ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) ^ 2 = (1 / 2 : ℂ) := by
    have h : (Real.sqrt 2)⁻¹ ^ 2 = (1 / 2 : ℝ) := by
      rw [inv_pow, Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]; norm_num
    have h2 : ((Real.sqrt 2 : ℝ)⁻¹ : ℂ) ^ 2 = ((1 / 2 : ℝ) : ℂ) := by exact_mod_cast h
    rw [h2]; norm_num
  have hc3sq : ((Real.sqrt 3 : ℝ)⁻¹ : ℂ) ^ 2 = (1 / 3 : ℂ) := by
    have h : (Real.sqrt 3)⁻¹ ^ 2 = (1 / 3 : ℝ) := by
      rw [inv_pow, Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)]; norm_num
    have h2 : ((Real.sqrt 3 : ℝ)⁻¹ : ℂ) ^ 2 = ((1 / 3 : ℝ) : ℂ) := by exact_mod_cast h
    rw [h2]; norm_num
  linear_combination
    (((Real.sqrt 3 : ℝ)⁻¹ : ℂ)) ^ 2 * Complex.I * hc2sq + ((1 : ℂ) / 2) * Complex.I * hc3sq

/-- Étape 3 : un même `T` ne peut être compatible simultanément avec une
équivalence unitaire ET une équivalence antiunitaire (Bargmann §1.5). -/
theorem exclusivity (hT : IsWignerMap T) (hn : 2 ≤ n) :
    ¬ ((∃ U : H n ≃ₗᵢ[ℂ] H n, ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U x)
     ∧ (∃ U' : H n ≃ₛₗᵢ[starRingEnd ℂ] H n, ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U' x)) := by
  rintro ⟨⟨U, hU⟩, ⟨U', hU'⟩⟩
  have ha : ‖e n‖ = 1 := he_norm' hn
  have hb : ‖e2 n‖ = 1 := e2_norm hn
  have hc : ‖e3 n‖ = 1 := e3_norm hn
  have hlin := delta_transform_lin hT hn U hU (e n) (e2 n) (e3 n) ha hb hc
  have hconj := delta_transform_conj hT hn U' hU' (e n) (e2 n) (e3 n) ha hb hc
  rw [bargmann_delta_witness hn] at hlin
  rw [bargmann_delta_witness hn] at hconj
  rw [hlin] at hconj
  have hconjI : (starRingEnd ℂ) (Complex.I / 6) = -(Complex.I / 6) := by
    rw [map_div₀, Complex.conj_I, map_ofNat]
    ring
  rw [hconjI] at hconj
  have hI0 : Complex.I = 0 := by linear_combination 3 * hconj
  exact Complex.I_ne_zero hI0

/-! ## (B) Unicité de `U` à phase globale près (version restreinte)

`eImg T := T (e n)` est un `def` FIXE dans `Defs.lean` (pas de paramètre pour
choisir un autre représentant unitaire de la même classe). Pour énoncer
l'unicité, on introduit ici une version paramétrée LOCALE `Vp`/`chidirp`/`chip`/
`Up`, obtenue en substituant, dans les formules mêmes de `Defs.lean`, `eImg T`
par un représentant explicite `eImg0`. `Defs.lean` n'est pas modifié : les
lemmes `V_eq_Vp`/`chi_eq_chip`/`U_eq_Up` ci-dessous montrent (par `rfl`) que ces
versions paramétrées, évaluées en `eImg T`, redonnent exactement `V`/`chi`/`U`.

Portée : ceci est strictement plus faible que le Théorème 2 de Bargmann §6 (qui
couvrirait un `U'` complètement arbitraire) -- seule la liberté effectivement
exploitée par `wigner`, le choix du représentant de `eImg`, est traitée. -/

/-- Version paramétrée localement de `V` : `eImg` explicite plutôt que fixé à
`eImg T := T (e n)`. -/
private noncomputable def Vp (T : H n → H n) (eImg0 : H n) (z : H n) : H n :=
  (⟪eImg0, T ((‖e n + z‖⁻¹ : ℂ) • (e n + z))⟫_ℂ)⁻¹ • T ((‖e n + z‖⁻¹ : ℂ) • (e n + z)) - eImg0

private def chidirp (T : H n → H n) (eImg0 f : H n) (α : ℂ) : ℂ :=
  ⟪Vp T eImg0 f, Vp T eImg0 (α • f)⟫_ℂ

private noncomputable def chip (T : H n → H n) (eImg0 : H n) (α : ℂ) : ℂ :=
  chidirp T eImg0 (refVec n) α

private noncomputable def Up (T : H n → H n) (eImg0 : H n) (a : H n) : H n :=
  chip T eImg0 ⟪e n, a⟫_ℂ • eImg0 + Vp T eImg0 (a - ⟪e n, a⟫_ℂ • e n)

/-- Pont vers `Defs.lean` : `Vp`/`chidirp`/`chip`/`Up` évalués au représentant
canonique `eImg T` redonnent exactement `V`/`chidir`/`chi`/`U`. -/
private theorem V_eq_Vp (T : H n → H n) (z : H n) : V T z = Vp T (eImg T) z := rfl

private theorem chidir_eq_chidirp (T : H n → H n) (f : H n) (α : ℂ) :
    chidir T f α = chidirp T (eImg T) f α := rfl

private theorem chi_eq_chip (T : H n → H n) (α : ℂ) : chi T α = chip T (eImg T) α := rfl

private theorem U_eq_Up (T : H n → H n) (a : H n) : U T a = Up T (eImg T) a := rfl

/-- Étapes (i)+(ii) : `V` calculé au représentant `λ • eImg` vaut `λ • V` calculé
au représentant `eImg`, pour tout `‖λ‖ = 1`. -/
theorem Vp_smul_eImg (T : H n → H n) (eImg0 : H n) (lam : ℂ) (hlam : ‖lam‖ = 1) (z : H n) :
    Vp T (lam • eImg0) z = lam • Vp T eImg0 z := by
  set w := (‖e n + z‖⁻¹ : ℂ) • (e n + z)
  show (⟪lam • eImg0, T w⟫_ℂ)⁻¹ • T w - lam • eImg0
      = lam • ((⟪eImg0, T w⟫_ℂ)⁻¹ • T w - eImg0)
  rw [inner_smul_left]
  have hconjlam : (starRingEnd ℂ) lam * lam = 1 := conj_mul_self_eq_one hlam
  have hinv2 : ((starRingEnd ℂ) lam)⁻¹ = lam := inv_eq_of_mul_eq_one_right hconjlam
  have hinv : ((starRingEnd ℂ) lam * ⟪eImg0, T w⟫_ℂ)⁻¹ = lam * (⟪eImg0, T w⟫_ℂ)⁻¹ := by
    rw [mul_inv, hinv2]
  rw [hinv]
  module

/-- Étape (iii) : `χ` ne dépend PAS du choix du représentant `eImg` -- pas
seulement sa branche `id`/`conj`, la fonction entière. -/
theorem chip_smul_eImg (T : H n → H n) (eImg0 : H n) (lam : ℂ) (hlam : ‖lam‖ = 1) (α : ℂ) :
    chip T (lam • eImg0) α = chip T eImg0 α := by
  show chidirp T (lam • eImg0) (refVec n) α = chidirp T eImg0 (refVec n) α
  show ⟪Vp T (lam • eImg0) (refVec n), Vp T (lam • eImg0) (α • refVec n)⟫_ℂ
      = ⟪Vp T eImg0 (refVec n), Vp T eImg0 (α • refVec n)⟫_ℂ
  rw [Vp_smul_eImg T eImg0 lam hlam, Vp_smul_eImg T eImg0 lam hlam]
  rw [inner_smul_left, inner_smul_right]
  have hconjlam : (starRingEnd ℂ) lam * lam = 1 := conj_mul_self_eq_one hlam
  rw [← mul_assoc, hconjlam, one_mul]

/-- Étape (iv) : `U` calculé au représentant `λ • eImg` vaut `λ • U` calculé au
représentant `eImg`. -/
theorem Up_smul_eImg (T : H n → H n) (eImg0 : H n) (lam : ℂ) (hlam : ‖lam‖ = 1) (a : H n) :
    Up T (lam • eImg0) a = lam • Up T eImg0 a := by
  show chip T (lam • eImg0) ⟪e n, a⟫_ℂ • (lam • eImg0)
      + Vp T (lam • eImg0) (a - ⟪e n, a⟫_ℂ • e n)
      = lam • (chip T eImg0 ⟪e n, a⟫_ℂ • eImg0 + Vp T eImg0 (a - ⟪e n, a⟫_ℂ • e n))
  rw [chip_smul_eImg T eImg0 lam hlam, Vp_smul_eImg T eImg0 lam hlam, smul_add, smul_smul,
    smul_smul, mul_comm lam]

/-- **Unicité de `U` à phase globale près (version restreinte)** : si l'on
reconstruit `V'`, `χ'`, `U'` en substituant, dans les formules de `Defs.lean`, le
représentant unitaire `eImg T := T (e n)` par un autre représentant unitaire
`λ • eImg T` de la même classe (`‖λ‖ = 1`), alors `U'` et `U` diffèrent
exactement d'une phase globale `λ`. Version RESTREINTE du Théorème 2 de Bargmann
§6 : ne couvre que la liberté effectivement exploitée par `wigner` (le choix du
représentant de `eImg`), pas un `U'` complètement arbitraire. -/
theorem U_alt_eq_smul (T : H n → H n) (lam : ℂ) (hlam : ‖lam‖ = 1) (a : H n) :
    Up T (lam • eImg T) a = lam • U T a := by
  rw [U_eq_Up]
  exact Up_smul_eImg T (eImg T) lam hlam a

end
end QuantumFoundations.Wigner
