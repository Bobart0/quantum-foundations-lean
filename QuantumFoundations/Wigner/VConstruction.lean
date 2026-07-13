import QuantumFoundations.Wigner.Bessel

/-!
# W3 — Construction de `V` et propriétés de base (Bargmann §3, eqs 11-12a)

Préférer systématiquement les formes multiplicatives croisées dans les hypothèses
des lemmes (`γ • V z = T w − γ • e'` plutôt que des `⁻¹` dans les buts) — même
discipline que `sqrtOp`/`dilProj` côté Naimark pour éviter la casse `WithLp`/`⁻¹`.

**Écart signalé (2026-07-13)** : les 6 théorèmes de ce fichier reçoivent tous
`hn : 2 ≤ n` (absent des énoncés-squelettes de W0). Nécessaire : pour `n = 0`, `e n = 0`
(valeur poubelle) et `eImg T = T 0` peut être nul, auquel cas `γ` peut s'annuler
et la division `γ⁻¹ • T w` dégénère — les identités algébriques de ce fichier
(`γ⁻¹ * γ = 1`, etc.) supposent `γ ≠ 0`, qui n'est garanti que par `‖e n‖ = 1`
(donc `n ≥ 1`). Choix de `2 ≤ n` (plutôt que `0 < n`, techniquement suffisant
pour W3 seul) pour cohérence avec `Core.lean` (W4), qui appellera ces lemmes
exactement sous cette hypothèse.

**Piège Lean rencontré** (règle 12 CLAUDE.md, généralisé au-delà des `obtain`) :
déballer `e n` via `unfold e; rw [dif_pos h0]` (ou `show` explicite de la valeur
dépliée) déclenche un timeout déterministe au `whnf` — la présence d'une
instance `NeZero n` construite localement dans la branche `dite` semble coûteuse
à unifier lors d'une réécriture directe. Remède : `simp only [e, dif_pos h0, ...]`
referme la même égalité sans jamais timeout (`simp` gère la réduction du `dite`
plus robustement qu'un `rw`/`show` manuel).
-/

namespace QuantumFoundations.Wigner

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ} {T : H n → H n}

/-! ## Préliminaires privés (réutilisés par les 6 théorèmes publics) -/

private theorem he_norm (hn : 2 ≤ n) : ‖e n‖ = 1 := by
  have h0 : 0 < n := by omega
  simp only [e, dif_pos h0, PiLp.norm_single]
  norm_num

private theorem he_inner_self (hn : 2 ≤ n) : ⟪e n, e n⟫_ℂ = 1 := by
  have h0 : 0 < n := by omega
  simp only [e, dif_pos h0, EuclideanSpace.inner_single_left, PiLp.single_apply]
  simp

/-- Pythagore : `e ⊥ z` donne `‖e+z‖² = ‖e‖²+‖z‖² = 1+‖z‖²`. -/
private theorem norm_add_e_sq (hn : 2 ≤ n) {z : H n} (hz : InPerp z) :
    ‖e n + z‖ ^ 2 = 1 + ‖z‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), he_norm hn, hz]
  simp

private theorem he_add_ne_zero (hn : 2 ≤ n) {z : H n} (hz : InPerp z) : e n + z ≠ 0 := by
  intro h
  have hnz : ‖e n + z‖ ^ 2 = 0 := by rw [h]; simp
  rw [norm_add_e_sq hn hz] at hnz
  nlinarith [sq_nonneg ‖z‖]

private theorem norm_w (hn : 2 ≤ n) {z : H n} (hz : InPerp z) :
    ‖(‖e n + z‖⁻¹ : ℂ) • (e n + z)‖ = 1 := by
  have hne := he_add_ne_zero hn hz
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)]

private theorem heImg_norm (hT : IsWignerMap T) (hn : 2 ≤ n) : ‖eImg T‖ = 1 := by
  have h1 : ‖⟪eImg T, eImg T⟫_ℂ‖ = ‖⟪e n, e n⟫_ℂ‖ := hT (e n) (e n) (he_norm hn) (he_norm hn)
  rw [he_inner_self hn, norm_one, inner_self_eq_norm_sq_to_K] at h1
  have h2 : ‖eImg T‖ ^ 2 = 1 := by simpa using h1
  nlinarith [h2, norm_nonneg (eImg T), sq_nonneg (‖eImg T‖ - 1)]

private theorem heImg_inner_self (hT : IsWignerMap T) (hn : 2 ≤ n) :
    ⟪eImg T, eImg T⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, heImg_norm hT hn]
  norm_num

private theorem inner_e_w (hn : 2 ≤ n) {z : H n} (hz : InPerp z) :
    ⟪e n, ((‖e n + z‖⁻¹ : ℂ) • (e n + z))⟫_ℂ = (‖e n + z‖⁻¹ : ℂ) := by
  rw [inner_smul_right, inner_add_right, he_inner_self hn, hz]
  ring

private theorem norm_gamma (hT : IsWignerMap T) (hn : 2 ≤ n) {z : H n} (hz : InPerp z) :
    ‖⟪eImg T, T ((‖e n + z‖⁻¹ : ℂ) • (e n + z))⟫_ℂ‖ = ‖e n + z‖⁻¹ := by
  show ‖⟪T (e n), T ((‖e n + z‖⁻¹ : ℂ) • (e n + z))⟫_ℂ‖ = ‖e n + z‖⁻¹
  rw [hT (e n) _ (he_norm hn) (norm_w hn hz), inner_e_w hn hz, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr (he_add_ne_zero hn hz))]

private theorem gamma_ne_zero (hT : IsWignerMap T) (hn : 2 ≤ n) {z : H n} (hz : InPerp z) :
    ⟪eImg T, T ((‖e n + z‖⁻¹ : ℂ) • (e n + z))⟫_ℂ ≠ 0 := by
  intro h
  have h1 := norm_gamma hT hn hz
  rw [h, norm_zero] at h1
  exact (inv_ne_zero (norm_ne_zero_iff.mpr (he_add_ne_zero hn hz))) h1.symm

theorem inner_eImg_V (hT : IsWignerMap T) (hn : 2 ≤ n) (z : H n) (hz : InPerp z) :
    ⟪eImg T, V T z⟫_ℂ = 0 := by
  show ⟪eImg T,
    (⟪eImg T, T ((‖e n + z‖⁻¹ : ℂ) • (e n + z))⟫_ℂ)⁻¹ • T ((‖e n + z‖⁻¹ : ℂ) • (e n + z))
      - eImg T⟫_ℂ = 0
  rw [inner_sub_right, inner_smul_right, heImg_inner_self hT hn,
    inv_mul_cancel₀ (gamma_ne_zero hT hn hz)]
  ring

private theorem norm_T_unit (hT : IsWignerMap T) {v : H n} (hv : ‖v‖ = 1) : ‖T v‖ = 1 := by
  have h1 : ‖⟪T v, T v⟫_ℂ‖ = ‖⟪v, v⟫_ℂ‖ := hT v v hv hv
  have hvv : ⟪v, v⟫_ℂ = (1 : ℂ) := by rw [inner_self_eq_norm_sq_to_K, hv]; norm_num
  rw [hvv, norm_one, inner_self_eq_norm_sq_to_K] at h1
  have h2 : ‖T v‖ ^ 2 = 1 := by simpa using h1
  nlinarith [h2, norm_nonneg (T v), sq_nonneg (‖T v‖ - 1)]

private theorem hfz_norm {z : H n} (hz0 : z ≠ 0) : ‖(‖z‖⁻¹ : ℂ) • z‖ = 1 := by
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)]

private theorem inner_e_fz (hn : 2 ≤ n) {z : H n} (hz : InPerp z) :
    ⟪e n, (‖z‖⁻¹ : ℂ) • z⟫_ℂ = 0 := by
  rw [inner_smul_right, hz]; ring

private theorem inner_z_e {z : H n} (hz : InPerp z) : ⟪z, e n⟫_ℂ = 0 := by
  have h : (starRingEnd ℂ) ⟪z, e n⟫_ℂ = ⟪e n, z⟫_ℂ := inner_conj_symm (e n) z
  rw [hz] at h
  have h2 := congrArg (starRingEnd ℂ) h
  simpa using h2

private theorem inner_fz_e (hn : 2 ≤ n) {z : H n} (hz : InPerp z) :
    ⟪(‖z‖⁻¹ : ℂ) • z, e n⟫_ℂ = 0 := by
  rw [inner_smul_left, inner_z_e hz]
  simp

/-- `{e, f_z}` (avec `f_z` le représentant unitaire de `z`) est orthonormée dès que
`z ⊥ e` et `z ≠ 0` — le pivot pour appliquer Bessel (9) à `T w` sur cette base. -/
private theorem orthonormal_e_fz (hn : 2 ≤ n) {z : H n} (hz : InPerp z) (hz0 : z ≠ 0) :
    Orthonormal ℂ ![e n, (‖z‖⁻¹ : ℂ) • z] := by
  constructor
  · intro i
    fin_cases i
    · exact he_norm hn
    · exact hfz_norm hz0
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | exact inner_e_fz hn hz
      | exact inner_fz_e hn hz

private theorem inner_fz_w (hn : 2 ≤ n) {z : H n} (hz : InPerp z) (hz0 : z ≠ 0) :
    ⟪(‖z‖⁻¹ : ℂ) • z, (‖e n + z‖⁻¹ : ℂ) • (e n + z)⟫_ℂ
      = (‖z‖ * ‖e n + z‖⁻¹ : ℝ) := by
  have hzR : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  have hzC : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hzR
  have hzz : (⟪z, z⟫_ℂ : ℂ) = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have hsq : (‖z‖ : ℂ)⁻¹ * (‖z‖ : ℂ) ^ 2 = (‖z‖ : ℂ) := by
    rw [sq, ← mul_assoc, inv_mul_cancel₀ hzC, one_mul]
  rw [inner_smul_left, inner_smul_right, inner_add_right, inner_z_e hz, zero_add, hzz,
    map_inv₀, Complex.conj_ofReal]
  push_cast
  rw [mul_left_comm, hsq, mul_comm]

private theorem norm_mu (hT : IsWignerMap T) (hn : 2 ≤ n) {z : H n} (hz : InPerp z)
    (hz0 : z ≠ 0) :
    ‖⟪T ((‖z‖⁻¹ : ℂ) • z), T ((‖e n + z‖⁻¹ : ℂ) • (e n + z))⟫_ℂ‖ = ‖z‖ * ‖e n + z‖⁻¹ := by
  rw [hT _ _ (hfz_norm hz0) (norm_w hn hz), inner_fz_w hn hz hz0, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]

private theorem ab_sq_one (hn : 2 ≤ n) {z : H n} (hz : InPerp z) :
    (‖e n + z‖⁻¹) ^ 2 + (‖z‖ * ‖e n + z‖⁻¹) ^ 2 = 1 := by
  have hne : ‖e n + z‖ ≠ 0 := norm_ne_zero_iff.mpr (he_add_ne_zero hn hz)
  have h := norm_add_e_sq hn hz
  field_simp
  linarith [h]

/-- Colinéarité définitionnelle : `V z` est un multiple scalaire de `T` appliqué au
représentant unitaire de `z` (Bargmann §3.2 : « Clearly, `Vz = f'β' ∈ (Tf)‖z‖ = Tz` » —
`β'` a pour MODULE `‖z‖`, pas nécessairement 1). Rend la compatibilité `⟪e,x⟫ = 0` de
W5 GRATUITE, sans Cauchy-Schwarz. -/
theorem V_colinear (hT : IsWignerMap T) (hn : 2 ≤ n) (z : H n) (hz : InPerp z) (hz0 : z ≠ 0) :
    ∃ δ : ℂ, ‖δ‖ = ‖z‖ ∧ V T z = δ • T ((‖z‖⁻¹ : ℂ) • z) := by
  set w := (‖e n + z‖⁻¹ : ℂ) • (e n + z) with hw_def
  set g2 : Fin 2 → H n := ![e n, (‖z‖⁻¹ : ℂ) • z] with hg2_def
  have hg2orth : Orthonormal ℂ g2 := orthonormal_e_fz hn hz hz0
  have hTg2orth : Orthonormal ℂ (fun p => T (g2 p)) := orthonormal_image hT hg2orth
  have hbessel : ‖T w‖ ^ 2 = ∑ p, ‖⟪(fun p => T (g2 p)) p, T w⟫_ℂ‖ ^ 2 := by
    rw [Fin.sum_univ_two]
    show ‖T w‖ ^ 2 = ‖⟪T (g2 0), T w⟫_ℂ‖ ^ 2 + ‖⟪T (g2 1), T w⟫_ℂ‖ ^ 2
    have hg20 : g2 0 = e n := rfl
    have hg21 : g2 1 = (‖z‖⁻¹ : ℂ) • z := rfl
    rw [hg20, hg21, norm_T_unit hT (norm_w hn hz)]
    show (1 : ℝ) ^ 2 = ‖⟪eImg T, T w⟫_ℂ‖ ^ 2 + ‖⟪T ((‖z‖⁻¹ : ℂ) • z), T w⟫_ℂ‖ ^ 2
    rw [norm_gamma hT hn hz, norm_mu hT hn hz hz0]
    rw [one_pow]
    exact (ab_sq_one hn hz).symm
  have hTw_eq : T w = ∑ p, ⟪(fun p => T (g2 p)) p, T w⟫_ℂ • (fun p => T (g2 p)) p :=
    bessel_eq_of_norm_sq_eq hTg2orth (T w) hbessel
  rw [Fin.sum_univ_two] at hTw_eq
  simp only [] at hTw_eq
  have hg20 : g2 0 = e n := rfl
  have hg21 : g2 1 = (‖z‖⁻¹ : ℂ) • z := rfl
  rw [hg20, hg21] at hTw_eq
  have heImg_eq : T (e n) = eImg T := rfl
  rw [heImg_eq] at hTw_eq
  set γ := ⟪eImg T, T w⟫_ℂ with hγ_def
  set μ := ⟪T ((‖z‖⁻¹ : ℂ) • z), T w⟫_ℂ with hμ_def
  have hγne : γ ≠ 0 := gamma_ne_zero hT hn hz
  refine ⟨γ⁻¹ * μ, ?_, ?_⟩
  · have h1 : ‖γ‖ = ‖e n + z‖⁻¹ := norm_gamma hT hn hz
    have h2 : ‖μ‖ = ‖z‖ * ‖e n + z‖⁻¹ := norm_mu hT hn hz hz0
    have hne : ‖e n + z‖ ≠ 0 := norm_ne_zero_iff.mpr (he_add_ne_zero hn hz)
    rw [norm_mul, norm_inv, h1, h2, inv_inv]
    field_simp
  · show γ⁻¹ • T w - eImg T = (γ⁻¹ * μ) • T ((‖z‖⁻¹ : ℂ) • z)
    rw [hTw_eq, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hγne, one_smul,
      add_sub_cancel_left]

theorem norm_V (hT : IsWignerMap T) (hn : 2 ≤ n) (z : H n) (hz : InPerp z) :
    ‖V T z‖ = ‖z‖ := by
  by_cases hz0 : z = 0
  · subst hz0
    have hV0 : V T (0 : H n) = 0 := by
      show (⟪eImg T, T ((‖e n + 0‖⁻¹ : ℂ) • (e n + 0))⟫_ℂ)⁻¹ •
          T ((‖e n + 0‖⁻¹ : ℂ) • (e n + 0)) - eImg T = 0
      rw [add_zero, he_norm hn, Complex.ofReal_one, inv_one, one_smul]
      show (⟪eImg T, eImg T⟫_ℂ)⁻¹ • eImg T - eImg T = 0
      rw [heImg_inner_self hT hn, inv_one, one_smul, sub_self]
    rw [hV0, norm_zero]
  · obtain ⟨δ, hδ, hVz⟩ := V_colinear hT hn z hz hz0
    rw [hVz, norm_smul, hδ, norm_T_unit hT (hfz_norm hz0), mul_one]

/-- (11) Module du produit scalaire préservé par `V` sur `𝒫`. -/
theorem norm_inner_V (hT : IsWignerMap T) (w x : H n) (hw : InPerp w) (hx : InPerp x) :
    ‖⟪V T w, V T x⟫_ℂ‖ = ‖⟪w, x⟫_ℂ‖ := by
  sorry

/-- (12) Partie réelle du produit scalaire préservée par `V` sur `𝒫`. -/
theorem re_inner_V (hT : IsWignerMap T) (w x : H n) (hw : InPerp w) (hx : InPerp x) :
    (⟪V T w, V T x⟫_ℂ).re = (⟪w, x⟫_ℂ).re := by
  sorry

/-- (12a) Si `⟪w,x⟫` est déjà réel, `V` le préserve exactement (pas seulement sa
partie réelle ou son module). -/
theorem inner_V_eq_of_im_eq_zero (hT : IsWignerMap T) (w x : H n) (hw : InPerp w)
    (hx : InPerp x) (hreal : (⟪w, x⟫_ℂ).im = 0) : ⟪V T w, V T x⟫_ℂ = ⟪w, x⟫_ℂ := by
  sorry

end
end QuantumFoundations.Wigner
