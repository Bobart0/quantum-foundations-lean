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

/-- Rigidité générale (généralise `eq_one_of_norm_one_re_one`, W1, au cas `M`
quelconque) : un scalaire dont le module ET la partie réelle valent tous deux `M`
(réel) est EXACTEMENT `M` — aucune ambiguïté de signe sur la partie imaginaire. -/
private theorem eq_of_norm_eq_re_eq {z : ℂ} {M : ℝ} (h1 : ‖z‖ = M) (h2 : z.re = M) :
    z = (M : ℂ) := by
  have hns : Complex.normSq z = M ^ 2 := by rw [← Complex.sq_norm, h1]
  rw [Complex.normSq_apply, h2] at hns
  have him : z.im = 0 := by nlinarith [sq_nonneg z.im]
  exact Complex.ext h2 (by rw [him]; simp)

/-- Isolé en lemme `ℂ` pur (contexte minimal) pour éviter le timeout `whnf` documenté
règle 12 : appliqué inline à `chi T b` (une expression énorme, `chidir` déplié via
`V`/`⟪·,·⟫`), `norm_cast` explore le terme et dépasse `maxHeartbeats`. -/
private theorem sq_norm_eq_mul_conj {b c : ℂ} (h : ‖c‖ = ‖b‖) :
    (‖b‖ : ℂ) ^ 2 = c * (starRingEnd ℂ) c := by
  rw [← h, Complex.mul_conj]
  norm_cast
  exact Complex.sq_norm c

private theorem inner_I_smul_eq_norm {a : ℂ} (ha : a ≠ 0) :
    (starRingEnd ℂ) (Complex.I * a * (‖a‖ : ℂ)⁻¹) * Complex.I * a = (‖a‖ : ℂ) := by
  have hane : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr ha
  rw [map_mul, map_mul, Complex.conj_I, map_inv₀, Complex.conj_ofReal]
  have hconj : (starRingEnd ℂ) a * a = (‖a‖ : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj]; norm_cast; exact (Complex.sq_norm a).symm
  field_simp
  rw [Complex.I_sq, show -((-1 : ℂ) * (starRingEnd ℂ) a * a) = (starRingEnd ℂ) a * a from by
    ring, hconj]

private theorem inner_smul_eq_norm {a : ℂ} (ha : a ≠ 0) :
    (starRingEnd ℂ) (a * (‖a‖ : ℂ)⁻¹) * a = (‖a‖ : ℂ) := by
  have hane : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr ha
  rw [map_mul, map_inv₀, Complex.conj_ofReal]
  have hconj : (starRingEnd ℂ) a * a = (‖a‖ : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj]; norm_cast; exact (Complex.sq_norm a).symm
  field_simp
  rw [hconj]

/-- Le point-clé de la généralisation aux repères non orthogonaux (Bargmann §4,
écart signalé dans le plan initial) : pour DEUX vecteurs unitaires `f1,f2 ∈ 𝒫`
avec `⟪f1,f2⟫ ≠ 0` (PAS besoin d'orthogonalité), les fonctions `chidir T f1` et
`chidir T f2` coïncident au point `i` — ce qui, combiné à `chidir_dichotomy` de
chaque côté (chacune vaut GLOBALEMENT `id` ou `conj`, et `id i ≠ conj i`), force
l'égalité FONCTIONNELLE complète. Coup de pouce : `c1 := i·a/‖a‖`, `c1' := a/‖a‖`
(`a := ⟪f1,f2⟫`) sont choisis pour que `⟪c1•f1, i•f2⟫` et `⟪c1'•f1, f2⟫` soient
TOUS DEUX exactement `‖a‖` (réel positif, par construction algébrique — AUCUNE
disjonction réel/non-réel sur `a` n'est nécessaire, contrairement à l'approche
initialement envisagée). -/
private theorem chidir_branch_transfer (hT : IsWignerMap T) (hn : 2 ≤ n) {f1 f2 : H n}
    (hf1 : InPerp f1) (hf1u : ‖f1‖ = 1) (hf2 : InPerp f2) (hf2u : ‖f2‖ = 1)
    (ha : ⟪f1, f2⟫_ℂ ≠ 0) : chidir T f2 Complex.I = chidir T f1 Complex.I := by
  set a : ℂ := ⟪f1, f2⟫_ℂ with ha_def
  have hane : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  set c1 : ℂ := Complex.I * a * (‖a‖ : ℂ)⁻¹ with hc1_def
  set c1' : ℂ := a * (‖a‖ : ℂ)⁻¹ with hc1'_def
  have hc1_eq : c1 = Complex.I * c1' := by rw [hc1_def, hc1'_def]; ring
  have hInPerp1 : ∀ β : ℂ, InPerp (β • f1) := by
    intro β; show ⟪e n, β • f1⟫_ℂ = 0; rw [inner_smul_right, hf1]; ring
  have hInPerp2 : ∀ β : ℂ, InPerp (β • f2) := by
    intro β; show ⟪e n, β • f2⟫_ℂ = 0; rw [inner_smul_right, hf2]; ring
  have hVpq : ⟪V T (c1 • f1), V T (Complex.I • f2)⟫_ℂ = (‖a‖ : ℂ) := by
    have hpq : ⟪c1 • f1, Complex.I • f2⟫_ℂ = (‖a‖ : ℂ) := by
      rw [inner_smul_left, inner_smul_right, ← ha_def, hc1_def, ← mul_assoc]
      exact inner_I_smul_eq_norm ha
    have hnorm : ‖⟪V T (c1 • f1), V T (Complex.I • f2)⟫_ℂ‖ = ‖a‖ := by
      rw [norm_inner_V hT hn _ _ (hInPerp1 c1) (hInPerp2 Complex.I), hpq]; simp
    have hre : (⟪V T (c1 • f1), V T (Complex.I • f2)⟫_ℂ).re = ‖a‖ := by
      rw [re_inner_V hT hn _ _ (hInPerp1 c1) (hInPerp2 Complex.I), hpq]; simp
    exact eq_of_norm_eq_re_eq hnorm hre
  have hVp'q' : ⟪V T (c1' • f1), V T f2⟫_ℂ = (‖a‖ : ℂ) := by
    have hp'q' : ⟪c1' • f1, f2⟫_ℂ = (‖a‖ : ℂ) := by
      rw [inner_smul_left, ← ha_def, hc1'_def]
      exact inner_smul_eq_norm ha
    have hnorm : ‖⟪V T (c1' • f1), V T f2⟫_ℂ‖ = ‖a‖ := by
      rw [norm_inner_V hT hn _ _ (hInPerp1 c1') hf2, hp'q']; simp
    have hre : (⟪V T (c1' • f1), V T f2⟫_ℂ).re = ‖a‖ := by
      rw [re_inner_V hT hn _ _ (hInPerp1 c1') hf2, hp'q']; simp
    exact eq_of_norm_eq_re_eq hnorm hre
  rw [V_dir_colinear hT hn hf1 hf1u c1, V_dir_colinear hT hn hf2 hf2u Complex.I,
    inner_smul_left, inner_smul_right] at hVpq
  rw [V_dir_colinear hT hn hf1 hf1u c1'] at hVp'q'
  rw [inner_smul_left] at hVp'q'
  have hVf1f2ne : ⟪V T f1, V T f2⟫_ℂ ≠ 0 := by
    have : ‖⟪V T f1, V T f2⟫_ℂ‖ = ‖a‖ := by rw [norm_inner_V hT hn f1 f2 hf1 hf2]
    intro h; rw [h, norm_zero] at this; exact hane this.symm
  have hcancel : (starRingEnd ℂ) (chidir T f1 c1) * chidir T f2 Complex.I
      = (starRingEnd ℂ) (chidir T f1 c1') := by
    have e1 : (starRingEnd ℂ) (chidir T f1 c1) * chidir T f2 Complex.I *
        ⟪V T f1, V T f2⟫_ℂ = (starRingEnd ℂ) (chidir T f1 c1') * ⟪V T f1, V T f2⟫_ℂ := by
      rw [mul_assoc]; exact hVpq.trans hVp'q'.symm
    exact mul_right_cancel₀ hVf1f2ne e1
  have hc1'ne : c1' ≠ 0 := by
    rw [hc1'_def]; exact mul_ne_zero ha (inv_ne_zero (by exact_mod_cast hane))
  have hIcancel : Complex.I * (-Complex.I) = (1 : ℂ) := by linear_combination -Complex.I_sq
  rcases chidir_dichotomy hT hn f1 hf1 hf1u with hid | hconjb
  · have e1 : chidir T f1 c1 = c1 := congrFun hid c1
    have e2 : chidir T f1 c1' = c1' := congrFun hid c1'
    rw [e1, e2, hc1_eq, map_mul, Complex.conj_I] at hcancel
    have hxne : (starRingEnd ℂ) c1' ≠ 0 := by simpa using hc1'ne
    have h2 : (starRingEnd ℂ) c1' * ((-Complex.I) * chidir T f2 Complex.I)
        = (starRingEnd ℂ) c1' * 1 := by rw [mul_one]; linear_combination hcancel
    have h3 := mul_left_cancel₀ hxne h2
    have h4 : Complex.I * ((-Complex.I) * chidir T f2 Complex.I) = Complex.I * 1 := by rw [h3]
    rw [← mul_assoc, hIcancel, one_mul, mul_one] at h4
    rw [h4, congrFun hid Complex.I]; rfl
  · have e1 : chidir T f1 c1 = (starRingEnd ℂ) c1 := congrFun hconjb c1
    have e2 : chidir T f1 c1' = (starRingEnd ℂ) c1' := congrFun hconjb c1'
    rw [e1, e2, Complex.conj_conj, Complex.conj_conj, hc1_eq] at hcancel
    have h2 : c1' * (Complex.I * chidir T f2 Complex.I) = c1' * 1 := by
      rw [mul_one]; linear_combination hcancel
    have h3 := mul_left_cancel₀ hc1'ne h2
    have h4 : (-Complex.I) * (Complex.I * chidir T f2 Complex.I) = (-Complex.I) * 1 := by
      rw [h3]
    rw [← mul_assoc, show (-Complex.I) * Complex.I = (1 : ℂ) from by
      linear_combination -Complex.I_sq, one_mul, mul_one] at h4
    rw [h4, congrFun hconjb Complex.I, Complex.conj_I]

/-- Cas dégénéré de la généralisation aux repères non orthogonaux : quand `f` est
COLINÉAIRE à `refVec` (`f = c • refVec`, `c` unitaire), `chidir T f` coïncide avec
`chi` au point `i` directement (sans avoir besoin de `chidir_branch_transfer`, qui
exige `⟪refVec,f⟫ ≠ 0` — colinéaire couvre en particulier `f = -refVec`, le seul
point où le pont `f_w := (refVec+f)/‖refVec+f‖` de `chi_eq_chidir` dégénère). -/
private theorem chidir_colinear_refVec (hT : IsWignerMap T) (hn : 2 ≤ n) {c : ℂ}
    (hc : ‖c‖ = 1) : chidir T (c • refVec n) Complex.I = chi T Complex.I := by
  have hrefu := refVec_norm hn
  have hrefp := refVec_InPerp hn
  have hcu : ‖c • refVec n‖ = 1 := by rw [norm_smul, hc, hrefu, mul_one]
  show ⟪V T (c • refVec n), V T (Complex.I • (c • refVec n))⟫_ℂ = chi T Complex.I
  rw [smul_smul, V_dir_colinear hT hn hrefp hrefu c,
    V_dir_colinear hT hn hrefp hrefu (Complex.I * c), inner_smul_left, inner_smul_right]
  have hVrefVref : ⟪V T (refVec n), V T (refVec n)⟫_ℂ = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, norm_V hT hn (refVec n) hrefp, hrefu]; norm_num
  rw [hVrefVref, mul_one]
  show (starRingEnd ℂ) (chi T c) * chi T (Complex.I * c) = chi T Complex.I
  rcases chidir_dichotomy hT hn (refVec n) hrefp hrefu with hid | hconjb
  · have e1 : chi T c = c := congrFun hid c
    have e2 : chi T (Complex.I * c) = Complex.I * c := congrFun hid (Complex.I * c)
    have e3 : chi T Complex.I = Complex.I := congrFun hid Complex.I
    have hcc : (starRingEnd ℂ) c * c = (1 : ℂ) := by
      rw [mul_comm, Complex.mul_conj]; norm_cast; rw [← Complex.sq_norm, hc]; norm_num
    rw [e1, e2, e3]; linear_combination Complex.I * hcc
  · have e1 : chi T c = (starRingEnd ℂ) c := congrFun hconjb c
    have e2 : chi T (Complex.I * c) = (starRingEnd ℂ) (Complex.I * c) :=
      congrFun hconjb (Complex.I * c)
    have e3 : chi T Complex.I = (starRingEnd ℂ) Complex.I := congrFun hconjb Complex.I
    have hcc : c * (starRingEnd ℂ) c = (1 : ℂ) := by
      rw [Complex.mul_conj]; norm_cast; rw [← Complex.sq_norm, hc]; norm_num
    rw [e1, e2, e3, Complex.conj_I, map_mul, Complex.conj_I, Complex.conj_conj]
    linear_combination (-Complex.I) * hcc

/-- Deux fonctions GLOBALEMENT `id` ou `conj` (chacune, indépendamment) qui
coïncident en `i` (le point où `id` et `conj` se distinguent) coïncident
partout — c'est ce qui permet de réduire `chi_eq_chidir` à une seule valeur
comparée plutôt qu'à une identité fonctionnelle complète. -/
private theorem eq_branch_of_eq_at_I {g h : ℂ → ℂ} (hg : g = id ∨ g = starRingEnd ℂ)
    (hh : h = id ∨ h = starRingEnd ℂ) (hI : g Complex.I = h Complex.I) : g = h := by
  rcases hg with hg | hg <;> rcases hh with hh | hh <;> subst hg <;> subst hh
  · rfl
  · exfalso; norm_num [Complex.ext_iff] at hI
  · exfalso; norm_num [Complex.ext_iff] at hI
  · rfl

/-- `chi` (calculé le long de `refVec`) coïncide avec `chidir` le long de
n'importe quel autre vecteur unitaire de `𝒫` — GÉNÉRALISATION aux repères non
orthogonaux (écart signalé dans le plan initial, résolu via `chidir_branch_transfer`
+ `chidir_colinear_refVec` plutôt que par l'argument `w = f₁ + f₂` de Bargmann
§4.3-4.5, qui n'est PAS nécessaire ici). -/
theorem chi_eq_chidir (hT : IsWignerMap T) (hn : 2 ≤ n) (f : H n) (hf : InPerp f)
    (hfu : ‖f‖ = 1) (α : ℂ) : chi T α = chidir T f α := by
  have hrefu := refVec_norm hn
  have hrefp := refVec_InPerp hn
  have hffself : ⟪f, f⟫_ℂ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hfu]; norm_num
  have hrefself : ⟪refVec n, refVec n⟫_ℂ = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hrefu]; norm_num
  have hkeyI : chidir T f Complex.I = chi T Complex.I := by
    by_cases hedge : ⟪refVec n, f⟫_ℂ = -1
    · have hCS : ‖⟪refVec n, f⟫_ℂ‖ = ‖refVec n‖ * ‖f‖ := by rw [hedge, hrefu, hfu]; norm_num
      have hor := (norm_inner_eq_norm_tfae ℂ (refVec n) f).out 0 2
      rcases hor.mp hCS with h0 | ⟨r, hr⟩
      · exfalso; rw [h0, norm_zero] at hrefu; exact zero_ne_one hrefu
      · have hr1 : r = -1 := by
          rw [hr, inner_smul_right, hrefself, mul_one] at hedge; exact hedge
        rw [hr, hr1]
        exact chidir_colinear_refVec hT hn (by norm_num : ‖(-1 : ℂ)‖ = 1)
    · set w := refVec n + f with hw_def
      have haR : ⟪refVec n, w⟫_ℂ ≠ 0 := by
        rw [hw_def, inner_add_right, hrefself]
        intro hc; apply hedge; linear_combination hc
      have haR' : ⟪w, f⟫_ℂ ≠ 0 := by
        rw [hw_def, inner_add_left, hffself]
        intro hc; apply hedge; linear_combination hc
      have hwne : w ≠ 0 := by
        intro h0; apply haR; rw [h0, inner_zero_right]
      set fw : H n := (‖w‖⁻¹ : ℂ) • w with hfw_def
      have hfwu : ‖fw‖ = 1 := by
        rw [hfw_def, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hwne)]
      have hfwp : InPerp fw := by
        show ⟪e n, fw⟫_ℂ = 0
        rw [hfw_def, inner_smul_right, hw_def, inner_add_right, hrefp, hf]; ring
      have hRefFwNe : ⟪refVec n, fw⟫_ℂ ≠ 0 := by
        rw [hfw_def, inner_smul_right]
        exact mul_ne_zero (inv_ne_zero (by exact_mod_cast norm_ne_zero_iff.mpr hwne)) haR
      have hFwFNe : ⟪fw, f⟫_ℂ ≠ 0 := by
        rw [hfw_def, inner_smul_left, map_inv₀, Complex.conj_ofReal]
        exact mul_ne_zero (inv_ne_zero (by exact_mod_cast norm_ne_zero_iff.mpr hwne)) haR'
      have step1 : chidir T fw Complex.I = chidir T (refVec n) Complex.I :=
        chidir_branch_transfer hT hn hrefp hrefu hfwp hfwu hRefFwNe
      have step2 : chidir T f Complex.I = chidir T fw Complex.I :=
        chidir_branch_transfer hT hn hfwp hfwu hf hfu hFwFNe
      rw [step2, step1]; rfl
  have hbranchEq : (fun β => chidir T (refVec n) β) = (fun β => chidir T f β) :=
    eq_branch_of_eq_at_I (chidir_dichotomy hT hn (refVec n) hrefp hrefu)
      (chidir_dichotomy hT hn f hf hfu) hkeyI.symm
  show chidir T (refVec n) α = chidir T f α
  exact congrFun hbranchEq α

/-- `chi` est globalement l'identité ou la conjugaison (conséquence directe de
`chidir_dichotomy` appliqué à `refVec`). -/
theorem chi_dichotomy (hT : IsWignerMap T) (hn : 2 ≤ n) :
    (fun α => chi T α) = id ∨ (fun α => chi T α) = starRingEnd ℂ :=
  chidir_dichotomy hT hn (refVec n) (refVec_InPerp hn) (refVec_norm hn)

/-- `chi` fixe les réels dans les DEUX branches (`id r = r` ; `conj r = r` pour
`r` réel) — outil réutilisé pour l'homogénéité de `V` et la formule à deux
directions. -/
private theorem chi_real (hT : IsWignerMap T) (hn : 2 ≤ n) (r : ℝ) :
    chi T (r : ℂ) = (r : ℂ) := by
  rcases chi_dichotomy hT hn with h | h
  · rw [congrFun h]; rfl
  · rw [congrFun h]; exact Complex.conj_ofReal r

/-- (18b) `V` est `χ`-homogène sur `𝒫` (généralise `V_dir_colinear`/`chi_eq_chidir`
d'un `f` unitaire à un `z` quelconque de `𝒫`, via `z = ‖z‖ • (‖z‖⁻¹•z)` et
`chi_real`, puisque `‖z‖` est réel). -/
theorem V_chi_homogeneous (hT : IsWignerMap T) (hn : 2 ≤ n) (c : ℂ) (z : H n)
    (hz : InPerp z) : V T (c • z) = chi T c • V T z := by
  by_cases hz0 : z = 0
  · subst hz0
    have hV0 : V T (0 : H n) = 0 := by
      have h := norm_V hT hn 0 (by show ⟪e n, (0 : H n)⟫_ℂ = 0; simp)
      rw [norm_zero] at h; exact norm_eq_zero.mp h
    rw [smul_zero, hV0, smul_zero]
  · set f : H n := (‖z‖⁻¹ : ℂ) • z with hf_def
    have hfu : ‖f‖ = 1 := by
      rw [hf_def, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)]
    have hfp : InPerp f := by
      show ⟪e n, f⟫_ℂ = 0; rw [hf_def, inner_smul_right, hz]; ring
    have hzf : z = (‖z‖ : ℂ) • f := by
      rw [hf_def, smul_smul, mul_inv_cancel₀ (by exact_mod_cast norm_ne_zero_iff.mpr hz0 :
        (‖z‖ : ℂ) ≠ 0), one_smul]
    have hVz : V T z = (‖z‖ : ℂ) • V T f := by
      conv_lhs => rw [hzf]
      rw [V_dir_colinear hT hn hfp hfu, ← chi_eq_chidir hT hn f hfp hfu, chi_real hT hn]
    have hVcz : V T (c • z) = chi T (c * (‖z‖ : ℂ)) • V T f := by
      conv_lhs => rw [hzf]
      rw [smul_smul, V_dir_colinear hT hn hfp hfu, chi_eq_chidir hT hn f hfp hfu]
    rw [hVcz, hVz, smul_smul]
    congr 1
    rcases chi_dichotomy hT hn with h | h
    · rw [congrFun h, congrFun h]; rfl
    · rw [congrFun h, congrFun h, map_mul, Complex.conj_ofReal]

/-- Formule de décomposition à deux directions ORTHOGONALES (Bargmann §4.6-4.7,
préliminaire à l'additivité). Preuve DIRECTE (pas de Bessel/`orthonormal_image`
nécessaire) : le candidat `chi a1 • V f1 + chi a2 • V f2` a même norme que `V x`
(Pythagore + `‖chi c‖ = ‖c‖`) et la partie réelle de leur produit scalaire croisé
vaut EXACTEMENT cette norme commune — rigidité `eq_of_norm_eq_re_eq` appliquée à
`⟪V(a_p f_p), V x⟫`, qui isole `⟪V f_p, V x⟫ = chi a_p` pour chaque `p`. -/
private theorem V_two_dir (hT : IsWignerMap T) (hn : 2 ≤ n) {f1 f2 : H n} (hf1 : InPerp f1)
    (hf1u : ‖f1‖ = 1) (hf2 : InPerp f2) (hf2u : ‖f2‖ = 1) (horth : ⟪f1, f2⟫_ℂ = 0)
    (a1 a2 : ℂ) : V T (a1 • f1 + a2 • f2) = chi T a1 • V T f1 + chi T a2 • V T f2 := by
  have hf1self : ⟪f1, f1⟫_ℂ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hf1u]; norm_num
  have hf2self : ⟪f2, f2⟫_ℂ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hf2u]; norm_num
  set x := a1 • f1 + a2 • f2 with hx_def
  have hxp : InPerp x := by
    show ⟪e n, x⟫_ℂ = 0
    rw [hx_def, inner_add_right, inner_smul_right, inner_smul_right, hf1, hf2]; ring
  have hVf1f2 : ⟪V T f1, V T f2⟫_ℂ = 0 := by
    have h := norm_inner_V hT hn f1 f2 hf1 hf2
    rw [horth, norm_zero] at h; exact norm_eq_zero.mp h
  have key : ∀ (g : H n) (b : ℂ), InPerp g → ‖g‖ = 1 → ⟪g, x⟫_ℂ = b →
      ⟪V T g, V T x⟫_ℂ = chi T b := by
    intro g b hg hgu hgx
    by_cases hb0 : b = 0
    · have hgVx : ⟪V T g, V T x⟫_ℂ = 0 := by
        have hmod : ‖⟪V T g, V T x⟫_ℂ‖ = ‖b‖ := by
          rw [norm_inner_V hT hn g x hg hxp, hgx]
        rw [hb0, norm_zero] at hmod; exact norm_eq_zero.mp hmod
      have hchib : chi T b = 0 := by
        rw [hb0, chi_eq_chidir hT hn g hg hgu]
        show ⟪V T g, V T ((0 : ℂ) • g)⟫_ℂ = 0
        rw [zero_smul]
        have hV0 : V T (0 : H n) = 0 := by
          have h := norm_V hT hn 0 (by show ⟪e n, (0 : H n)⟫_ℂ = 0; simp)
          rw [norm_zero] at h; exact norm_eq_zero.mp h
        rw [hV0, inner_zero_right]
      rw [hgVx, hchib]
    · have hgb : ⟪g, b • g⟫_ℂ = b := by
        rw [inner_smul_right]
        have hgself : ⟪g, g⟫_ℂ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hgu]; norm_num
        rw [hgself, mul_one]
      have hgbp : InPerp (b • g) := by
        show ⟪e n, b • g⟫_ℂ = 0; rw [inner_smul_right, hg]; ring
      have e1 : (starRingEnd ℂ) (chi T b) * ⟪V T g, V T x⟫_ℂ = (‖b‖ : ℂ) ^ 2 := by
        have hmod : ‖⟪V T (b • g), V T x⟫_ℂ‖ = ‖b‖ ^ 2 := by
          rw [norm_inner_V hT hn (b • g) x hgbp hxp, inner_smul_left, hgx, mul_comm,
            Complex.mul_conj]
          norm_cast
          rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg b)]
          exact (Complex.sq_norm b).symm
        have hre : (⟪V T (b • g), V T x⟫_ℂ).re = ‖b‖ ^ 2 := by
          rw [re_inner_V hT hn (b • g) x hgbp hxp, inner_smul_left, hgx, mul_comm,
            Complex.mul_conj, Complex.ofReal_re]
          exact (Complex.sq_norm b).symm
        have hexact := eq_of_norm_eq_re_eq hmod hre
        rw [V_dir_colinear hT hn hg hgu b, inner_smul_left,
          ← chi_eq_chidir hT hn g hg hgu] at hexact
        push_cast at hexact
        exact hexact
      have hmodb : ‖chi T b‖ = ‖b‖ := by
        rw [chi_eq_chidir hT hn g hg hgu]
        show ‖⟪V T g, V T (b • g)⟫_ℂ‖ = ‖b‖
        rw [norm_inner_V hT hn g (b • g) hg hgbp, hgb]
      have hchibne : chi T b ≠ 0 := by
        intro hc; rw [hc, norm_zero] at hmodb; exact hb0 (norm_eq_zero.mp hmodb.symm)
      have hconjne : (starRingEnd ℂ) (chi T b) ≠ 0 := by simpa using hchibne
      have hsq : (‖b‖ : ℂ) ^ 2 = chi T b * (starRingEnd ℂ) (chi T b) :=
        sq_norm_eq_mul_conj hmodb
      generalize hc_def : chi T b = c at e1 hsq hconjne ⊢
      rw [hsq, mul_comm c] at e1
      exact mul_left_cancel₀ hconjne e1
  have hβ1 : ⟪V T f1, V T x⟫_ℂ = chi T a1 := by
    apply key f1 a1 hf1 hf1u
    rw [hx_def, inner_add_right, inner_smul_right, inner_smul_right, horth, hf1self]; ring
  have hβ2 : ⟪V T f2, V T x⟫_ℂ = chi T a2 := by
    apply key f2 a2 hf2 hf2u
    rw [hx_def, inner_add_right, inner_smul_right, inner_smul_right, hf2self]
    have : ⟪f2, f1⟫_ℂ = 0 := by rw [← inner_conj_symm f2 f1, horth]; simp
    rw [this]; ring
  set x' := chi T a1 • V T f1 + chi T a2 • V T f2 with hx'_def
  have hnormVx : ‖V T x‖ ^ 2 = ‖a1‖ ^ 2 + ‖a2‖ ^ 2 := by
    rw [norm_V hT hn x hxp, hx_def, norm_add_sq (𝕜 := ℂ), norm_smul, norm_smul, hf1u, hf2u,
      mul_one, mul_one]
    have : ⟪a1 • f1, a2 • f2⟫_ℂ = 0 := by rw [inner_smul_left, inner_smul_right, horth]; ring
    rw [this]; simp
  have hchia1 : ‖chi T a1‖ = ‖a1‖ := by
    rw [chi_eq_chidir hT hn f1 hf1 hf1u]
    show ‖⟪V T f1, V T (a1 • f1)⟫_ℂ‖ = ‖a1‖
    rw [norm_inner_V hT hn f1 (a1 • f1) hf1
      (by show ⟪e n, a1 • f1⟫_ℂ = 0; rw [inner_smul_right, hf1]; ring),
      inner_smul_right, hf1self, mul_one]
  have hchia2 : ‖chi T a2‖ = ‖a2‖ := by
    rw [chi_eq_chidir hT hn f2 hf2 hf2u]
    show ‖⟪V T f2, V T (a2 • f2)⟫_ℂ‖ = ‖a2‖
    rw [norm_inner_V hT hn f2 (a2 • f2) hf2
      (by show ⟪e n, a2 • f2⟫_ℂ = 0; rw [inner_smul_right, hf2]; ring),
      inner_smul_right, hf2self, mul_one]
  have hcross : ⟪chi T a1 • V T f1, chi T a2 • V T f2⟫_ℂ = 0 := by
    rw [inner_smul_left, inner_smul_right, hVf1f2]; ring
  have hVf1u : ‖V T f1‖ = 1 := by rw [norm_V hT hn f1 hf1, hf1u]
  have hVf2u : ‖V T f2‖ = 1 := by rw [norm_V hT hn f2 hf2, hf2u]
  have hnormx' : ‖x'‖ ^ 2 = ‖a1‖ ^ 2 + ‖a2‖ ^ 2 := by
    rw [hx'_def, norm_add_sq (𝕜 := ℂ), norm_smul, norm_smul, hchia1, hchia2, hcross,
      hVf1u, hVf2u]
    simp
  have hre : (⟪V T x, x'⟫_ℂ).re = ‖a1‖ ^ 2 + ‖a2‖ ^ 2 := by
    rw [hx'_def, inner_add_right, inner_smul_right, inner_smul_right,
      ← inner_conj_symm (V T x) (V T f1), ← inner_conj_symm (V T x) (V T f2), hβ1, hβ2,
      ← sq_norm_eq_mul_conj hchia1, ← sq_norm_eq_mul_conj hchia2]
    norm_cast
  have hnormsub : ‖V T x - x'‖ ^ 2 = 0 := by
    rw [norm_sub_sq (𝕜 := ℂ), hnormVx, hnormx', show RCLike.re ⟪V T x, x'⟫_ℂ
      = (⟪V T x, x'⟫_ℂ).re from rfl, hre]
    ring
  have hsub : V T x - x' = 0 := by
    have h0 : ‖V T x - x'‖ = 0 := by
      nlinarith [sq_nonneg ‖V T x - x'‖, hnormsub, norm_nonneg (V T x - x')]
    exact norm_eq_zero.mp h0
  exact sub_eq_zero.mp hsub

/-- `chi` fixe les réels ADDITIVEMENT décalés : `chi (r + a) = r + chi a` pour `r`
réel, dans les deux branches (`id` trivial ; `conj` additive + fixe les réels). -/
private theorem chi_add_real (hT : IsWignerMap T) (hn : 2 ≤ n) (r : ℝ) (a : ℂ) :
    chi T ((r : ℂ) + a) = (r : ℂ) + chi T a := by
  rcases chi_dichotomy hT hn with h | h
  · rw [congrFun h, congrFun h]; rfl
  · rw [congrFun h, congrFun h, map_add, Complex.conj_ofReal]

/-- (18a) `V` est additive sur `𝒫`. Preuve : cas colinéaire (`z = a•f1`) direct via
`chi_add_real` ; cas général via Gram-Schmidt (`f2` := composante de `z`
orthogonale à `f1 := y/‖y‖`, normalisée) puis `V_two_dir`. -/
theorem V_additive (hT : IsWignerMap T) (hn : 2 ≤ n) (y z : H n) (hy : InPerp y)
    (hz : InPerp z) : V T (y + z) = V T y + V T z := by
  by_cases hy0 : y = 0
  · subst hy0
    have hV0 : V T (0 : H n) = 0 := by
      have h := norm_V hT hn 0 (by show ⟪e n, (0 : H n)⟫_ℂ = 0; simp)
      rw [norm_zero] at h; exact norm_eq_zero.mp h
    rw [zero_add, hV0, zero_add]
  set f1 : H n := (‖y‖⁻¹ : ℂ) • y with hf1_def
  have hf1u : ‖f1‖ = 1 := by
    rw [hf1_def, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy0)]
  have hf1p : InPerp f1 := by
    show ⟪e n, f1⟫_ℂ = 0; rw [hf1_def, inner_smul_right, hy]; ring
  have hf1self : ⟪f1, f1⟫_ℂ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hf1u]; norm_num
  have hyf1 : y = (‖y‖ : ℂ) • f1 := by
    rw [hf1_def, smul_smul, mul_inv_cancel₀ (by exact_mod_cast norm_ne_zero_iff.mpr hy0 :
      (‖y‖ : ℂ) ≠ 0), one_smul]
  set a : ℂ := ⟪f1, z⟫_ℂ with ha_def
  set g : H n := z - a • f1 with hg_def
  by_cases hg0 : g = 0
  · have hz_eq : z = a • f1 := sub_eq_zero.mp (hg_def ▸ hg0)
    have hsum : y + z = ((‖y‖ : ℂ) + a) • f1 := by
      conv_lhs => rw [hyf1, hz_eq]
      rw [add_smul]
    have hVsum : V T (y + z) = chi T ((‖y‖ : ℂ) + a) • V T f1 := by
      rw [hsum, V_dir_colinear hT hn hf1p hf1u, chi_eq_chidir hT hn f1 hf1p hf1u]
    have hVy : V T y = (‖y‖ : ℂ) • V T f1 := by
      conv_lhs => rw [hyf1]
      rw [V_dir_colinear hT hn hf1p hf1u, ← chi_eq_chidir hT hn f1 hf1p hf1u, chi_real hT hn]
    have hVz : V T z = chi T a • V T f1 := by
      rw [hz_eq, V_dir_colinear hT hn hf1p hf1u, chi_eq_chidir hT hn f1 hf1p hf1u]
    rw [hVsum, hVy, hVz, chi_add_real hT hn, add_smul]
  · have hgp : InPerp g := by
      show ⟪e n, g⟫_ℂ = 0
      rw [hg_def, inner_sub_right, inner_smul_right, hz, hf1p]; ring
    set f2 : H n := (‖g‖⁻¹ : ℂ) • g with hf2_def
    have hf2u : ‖f2‖ = 1 := by
      rw [hf2_def, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hg0)]
    have hf2p : InPerp f2 := by
      show ⟪e n, f2⟫_ℂ = 0; rw [hf2_def, inner_smul_right, hgp]; ring
    have hf1g : ⟪f1, g⟫_ℂ = 0 := by
      rw [hg_def, inner_sub_right, inner_smul_right, hf1self, mul_one, ha_def, sub_self]
    have horth : ⟪f1, f2⟫_ℂ = 0 := by
      rw [hf2_def, inner_smul_right, hf1g, mul_zero]
    have hgf2 : g = (‖g‖ : ℂ) • f2 := by
      rw [hf2_def, smul_smul, mul_inv_cancel₀ (by exact_mod_cast norm_ne_zero_iff.mpr hg0 :
        (‖g‖ : ℂ) ≠ 0), one_smul]
    have hzf12 : z = a • f1 + (‖g‖ : ℂ) • f2 := by
      rw [← hgf2, hg_def]; abel
    have hyf12 : y = (‖y‖ : ℂ) • f1 + (0 : ℂ) • f2 := by
      conv_lhs => rw [hyf1]
      rw [zero_smul, add_zero]
    have hsum : y + z = ((‖y‖ : ℂ) + a) • f1 + (‖g‖ : ℂ) • f2 := by
      conv_lhs => rw [hyf1, hzf12]
      rw [add_smul]; abel
    have hVsum : V T (y + z) = chi T ((‖y‖ : ℂ) + a) • V T f1 + chi T (‖g‖ : ℂ) • V T f2 := by
      rw [hsum, V_two_dir hT hn hf1p hf1u hf2p hf2u horth]
    have hVy : V T y = chi T (‖y‖ : ℂ) • V T f1 + chi T (0 : ℂ) • V T f2 := by
      conv_lhs => rw [hyf12]
      rw [V_two_dir hT hn hf1p hf1u hf2p hf2u horth]
    have hVz : V T z = chi T a • V T f1 + chi T (‖g‖ : ℂ) • V T f2 := by
      rw [hzf12, V_two_dir hT hn hf1p hf1u hf2p hf2u horth]
    have hchi0 : chi T (0 : ℂ) = 0 := by
      have h := chi_real hT hn 0; simpa using h
    have hchiy : chi T (‖y‖ : ℂ) = (‖y‖ : ℂ) := chi_real hT hn ‖y‖
    rw [hVsum, hVy, hVz, hchi0, hchiy, chi_add_real hT hn, zero_smul, add_zero, add_smul]
    abel

/-- `chi` fixe les réels MULTIPLICATIVEMENT : `chi (r * w) = r * chi w` pour `r`
réel (`id` trivial ; `conj` multiplicative + fixe les réels). -/
private theorem chi_mul_real (hT : IsWignerMap T) (hn : 2 ≤ n) (r : ℝ) (w : ℂ) :
    chi T ((r : ℂ) * w) = (r : ℂ) * chi T w := by
  rcases chi_dichotomy hT hn with h | h
  · rw [congrFun h, congrFun h]; rfl
  · rw [congrFun h, congrFun h, map_mul, Complex.conj_ofReal]

/-- Cas particulier de (18c) avec `g` unitaire — même argument de rigidité que
`V_two_dir`, mais sans besoin d'une seconde direction orthogonale : `z`
quelconque de `𝒫` joue directement le rôle de `x`. -/
private theorem V_inner_eq_chi_of_unit (hT : IsWignerMap T) (hn : 2 ≤ n) {g : H n}
    (hg : InPerp g) (hgu : ‖g‖ = 1) {z : H n} (hz : InPerp z) :
    ⟪V T g, V T z⟫_ℂ = chi T ⟪g, z⟫_ℂ := by
  set b : ℂ := ⟪g, z⟫_ℂ with hb_def
  by_cases hb0 : b = 0
  · have hmod : ‖⟪V T g, V T z⟫_ℂ‖ = ‖b‖ := norm_inner_V hT hn g z hg hz
    rw [hb0, norm_zero] at hmod
    have hVz0 : ⟪V T g, V T z⟫_ℂ = 0 := norm_eq_zero.mp hmod
    have hchib : chi T b = 0 := by
      rw [hb0, chi_eq_chidir hT hn g hg hgu]
      show ⟪V T g, V T ((0 : ℂ) • g)⟫_ℂ = 0
      rw [zero_smul]
      have hV0 : V T (0 : H n) = 0 := by
        have h := norm_V hT hn 0 (by show ⟪e n, (0 : H n)⟫_ℂ = 0; simp)
        rw [norm_zero] at h; exact norm_eq_zero.mp h
      rw [hV0, inner_zero_right]
    rw [hVz0, hchib]
  · have hgb : ⟪g, b • g⟫_ℂ = b := by
      rw [inner_smul_right]
      have hgself : ⟪g, g⟫_ℂ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hgu]; norm_num
      rw [hgself, mul_one]
    have hgbp : InPerp (b • g) := by
      show ⟪e n, b • g⟫_ℂ = 0; rw [inner_smul_right, hg]; ring
    have e1 : (starRingEnd ℂ) (chi T b) * ⟪V T g, V T z⟫_ℂ = (‖b‖ : ℂ) ^ 2 := by
      have hmod : ‖⟪V T (b • g), V T z⟫_ℂ‖ = ‖b‖ ^ 2 := by
        rw [norm_inner_V hT hn (b • g) z hgbp hz, inner_smul_left, ← hb_def, mul_comm,
          Complex.mul_conj]
        norm_cast
        rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg b)]
        exact (Complex.sq_norm b).symm
      have hre : (⟪V T (b • g), V T z⟫_ℂ).re = ‖b‖ ^ 2 := by
        rw [re_inner_V hT hn (b • g) z hgbp hz, inner_smul_left, ← hb_def, mul_comm,
          Complex.mul_conj, Complex.ofReal_re]
        exact (Complex.sq_norm b).symm
      have hexact := eq_of_norm_eq_re_eq hmod hre
      rw [V_dir_colinear hT hn hg hgu b, inner_smul_left,
        ← chi_eq_chidir hT hn g hg hgu] at hexact
      push_cast at hexact
      exact hexact
    have hmodb : ‖chi T b‖ = ‖b‖ := by
      rw [chi_eq_chidir hT hn g hg hgu]
      show ‖⟪V T g, V T (b • g)⟫_ℂ‖ = ‖b‖
      rw [norm_inner_V hT hn g (b • g) hg hgbp, hgb]
    have hchibne : chi T b ≠ 0 := by
      intro hc; rw [hc, norm_zero] at hmodb; exact hb0 (norm_eq_zero.mp hmodb.symm)
    have hconjne : (starRingEnd ℂ) (chi T b) ≠ 0 := by simpa using hchibne
    have hsq : (‖b‖ : ℂ) ^ 2 = chi T b * (starRingEnd ℂ) (chi T b) := sq_norm_eq_mul_conj hmodb
    rw [hsq, mul_comm (chi T b)] at e1
    exact mul_left_cancel₀ hconjne e1

/-- (18c) `V` transporte le produit scalaire via `χ` sur `𝒫`. Réduction au cas
unitaire (`V_inner_eq_chi_of_unit`) via `y = ‖y‖ • f1`, `V_chi_homogeneous` et
`chi_mul_real`. -/
theorem inner_V_eq_chi_inner (hT : IsWignerMap T) (hn : 2 ≤ n) (y z : H n)
    (hy : InPerp y) (hz : InPerp z) : ⟪V T y, V T z⟫_ℂ = chi T ⟪y, z⟫_ℂ := by
  by_cases hy0 : y = 0
  · subst hy0
    have hV0 : V T (0 : H n) = 0 := by
      have h := norm_V hT hn 0 (by show ⟪e n, (0 : H n)⟫_ℂ = 0; simp)
      rw [norm_zero] at h; exact norm_eq_zero.mp h
    have hchi0 : chi T (0 : ℂ) = 0 := by have h := chi_real hT hn 0; simpa using h
    rw [hV0, inner_zero_left, inner_zero_left, hchi0]
  · set f1 : H n := (‖y‖⁻¹ : ℂ) • y with hf1_def
    have hf1u : ‖f1‖ = 1 := by
      rw [hf1_def, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy0)]
    have hf1p : InPerp f1 := by
      show ⟪e n, f1⟫_ℂ = 0; rw [hf1_def, inner_smul_right, hy]; ring
    have hyf1 : y = (‖y‖ : ℂ) • f1 := by
      rw [hf1_def, smul_smul, mul_inv_cancel₀ (by exact_mod_cast norm_ne_zero_iff.mpr hy0 :
        (‖y‖ : ℂ) ≠ 0), one_smul]
    have hVy : V T y = (‖y‖ : ℂ) • V T f1 := by
      conv_lhs => rw [hyf1]
      rw [V_chi_homogeneous hT hn (‖y‖ : ℂ) f1 hf1p, chi_real hT hn]
    have hinner_yz : ⟪y, z⟫_ℂ = (‖y‖ : ℂ) * ⟪f1, z⟫_ℂ := by
      conv_lhs => rw [hyf1]
      rw [inner_smul_left, Complex.conj_ofReal]
    rw [hVy, inner_smul_left, Complex.conj_ofReal, hinner_yz, chi_mul_real hT hn,
      V_inner_eq_chi_of_unit hT hn hf1p hf1u hz]

end
end QuantumFoundations.Wigner
