import QuantumFoundations.Wigner.Bessel
import QuantumFoundations.Wigner.Scalar

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

/-- `V` envoie toujours `0` (élément trivial de `𝒫`) sur `0`. -/
private theorem V_zero (hT : IsWignerMap T) (hn : 2 ≤ n) : V T (0 : H n) = 0 := by
  show (⟪eImg T, T ((‖e n + 0‖⁻¹ : ℂ) • (e n + 0))⟫_ℂ)⁻¹ •
      T ((‖e n + 0‖⁻¹ : ℂ) • (e n + 0)) - eImg T = 0
  rw [add_zero, he_norm hn, Complex.ofReal_one, inv_one, one_smul]
  show (⟪eImg T, eImg T⟫_ℂ)⁻¹ • eImg T - eImg T = 0
  rw [heImg_inner_self hT hn, inv_one, one_smul, sub_self]

theorem norm_V (hT : IsWignerMap T) (hn : 2 ≤ n) (z : H n) (hz : InPerp z) :
    ‖V T z‖ = ‖z‖ := by
  by_cases hz0 : z = 0
  · subst hz0; rw [V_zero hT hn, norm_zero]
  · obtain ⟨δ, hδ, hVz⟩ := V_colinear hT hn z hz hz0
    rw [hVz, norm_smul, hδ, norm_T_unit hT (hfz_norm hz0), mul_one]

private theorem inner_fw_fx_norm {w x : H n} (hw0 : w ≠ 0) (hx0 : x ≠ 0) :
    ‖⟪(‖w‖⁻¹ : ℂ) • w, (‖x‖⁻¹ : ℂ) • x⟫_ℂ‖ = ‖w‖⁻¹ * ‖x‖⁻¹ * ‖⟪w, x⟫_ℂ‖ := by
  rw [inner_smul_left, inner_smul_right, map_inv₀, Complex.conj_ofReal, norm_mul, norm_mul,
    norm_inv, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_norm, abs_norm, mul_assoc]

/-- (11) Module du produit scalaire préservé par `V` sur `𝒫`. Preuve directe via la
colinéarité (`V_colinear` ci-dessus) : `Vw,Vx` sont des multiples de `T` appliqué aux
représentants unitaires, et `T` préserve le module du produit scalaire de deux
vecteurs unitaires (hypothèse `IsWignerMap`) — aucun besoin de repasser par `w`
(le vecteur bâti sur `e+z`, contrairement à ce que suggérait le plan initial). -/
theorem norm_inner_V (hT : IsWignerMap T) (hn : 2 ≤ n) (w x : H n) (hw : InPerp w)
    (hx : InPerp x) : ‖⟪V T w, V T x⟫_ℂ‖ = ‖⟪w, x⟫_ℂ‖ := by
  by_cases hw0 : w = 0
  · subst hw0; rw [V_zero hT hn]; simp
  by_cases hx0 : x = 0
  · subst hx0; rw [V_zero hT hn]; simp
  obtain ⟨δw, hδw, hVw⟩ := V_colinear hT hn w hw hw0
  obtain ⟨δx, hδx, hVx⟩ := V_colinear hT hn x hx hx0
  rw [hVw, hVx, inner_smul_left, inner_smul_right, norm_mul, norm_mul, Complex.norm_conj,
    hT _ _ (hfz_norm hw0) (hfz_norm hx0), inner_fw_fx_norm hw0 hx0, hδw, hδx]
  have hwR : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  have hxR : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  field_simp

/-- Identité clé (Bargmann §3, eq. 10) : en développant `V z = γ⁻¹•Tw - e'` sur les
deux arguments, les termes croisés `⟪Tw,e'⟫`/`⟪e',Tw⟩` s'annulent EXACTEMENT contre
`⟪e',e'⟫ = 1`, ne laissant que le terme principal moins `1`. C'est cette structure
« `1 + ...` » qui permet ensuite d'appliquer `re_eq_of_norm_eq` (W1). -/
private theorem inner_V_eq (hT : IsWignerMap T) (hn : 2 ≤ n) {z z' : H n} (hz : InPerp z)
    (hz' : InPerp z') :
    ⟪V T z, V T z'⟫_ℂ =
      (starRingEnd ℂ (⟪eImg T, T ((‖e n + z‖⁻¹ : ℂ) • (e n + z))⟫_ℂ))⁻¹ *
          (⟪eImg T, T ((‖e n + z'‖⁻¹ : ℂ) • (e n + z'))⟫_ℂ)⁻¹ *
          ⟪T ((‖e n + z‖⁻¹ : ℂ) • (e n + z)), T ((‖e n + z'‖⁻¹ : ℂ) • (e n + z'))⟫_ℂ -
        1 := by
  show ⟪(⟪eImg T, T ((‖e n + z‖⁻¹ : ℂ) • (e n + z))⟫_ℂ)⁻¹ • T ((‖e n + z‖⁻¹ : ℂ) • (e n + z))
        - eImg T,
      (⟪eImg T, T ((‖e n + z'‖⁻¹ : ℂ) • (e n + z'))⟫_ℂ)⁻¹ • T ((‖e n + z'‖⁻¹ : ℂ) • (e n + z'))
        - eImg T⟫_ℂ =
      (starRingEnd ℂ (⟪eImg T, T ((‖e n + z‖⁻¹ : ℂ) • (e n + z))⟫_ℂ))⁻¹ *
          (⟪eImg T, T ((‖e n + z'‖⁻¹ : ℂ) • (e n + z'))⟫_ℂ)⁻¹ *
          ⟪T ((‖e n + z‖⁻¹ : ℂ) • (e n + z)), T ((‖e n + z'‖⁻¹ : ℂ) • (e n + z'))⟫_ℂ -
        1
  set Tw := T ((‖e n + z‖⁻¹ : ℂ) • (e n + z)) with hTw_def
  set Tw' := T ((‖e n + z'‖⁻¹ : ℂ) • (e n + z')) with hTw'_def
  set γ := ⟪eImg T, Tw⟫_ℂ with hγ_def
  set γ' := ⟪eImg T, Tw'⟫_ℂ with hγ'_def
  have hγne : γ ≠ 0 := gamma_ne_zero hT hn hz
  have hγ'ne : γ' ≠ 0 := gamma_ne_zero hT hn hz'
  have e1 : ⟪γ⁻¹ • Tw, γ'⁻¹ • Tw'⟫_ℂ = (starRingEnd ℂ γ)⁻¹ * γ'⁻¹ * ⟪Tw, Tw'⟫_ℂ := by
    rw [inner_smul_left, inner_smul_right, map_inv₀]
    ring
  have e2 : ⟪γ⁻¹ • Tw, eImg T⟫_ℂ = 1 := by
    rw [inner_smul_left, ← inner_conj_symm Tw (eImg T), ← hγ_def, map_inv₀]
    exact inv_mul_cancel₀ (by simpa using hγne)
  have e3 : ⟪eImg T, γ'⁻¹ • Tw'⟫_ℂ = 1 := by
    rw [inner_smul_right, ← hγ'_def]
    exact inv_mul_cancel₀ hγ'ne
  have e4 : ⟪eImg T, eImg T⟫_ℂ = 1 := heImg_inner_self hT hn
  rw [inner_sub_left, inner_sub_right, inner_sub_right, e1, e2, e3, e4]
  ring

private theorem inner_ew_ewx_eq (hn : 2 ≤ n) {z z' : H n} (hz : InPerp z) (hz' : InPerp z') :
    ⟪(‖e n + z‖⁻¹ : ℂ) • (e n + z), (‖e n + z'‖⁻¹ : ℂ) • (e n + z')⟫_ℂ
      = (‖e n + z‖⁻¹ : ℂ) * (‖e n + z'‖⁻¹ : ℂ) * (1 + ⟪z, z'⟫_ℂ) := by
  rw [inner_smul_left, inner_smul_right, map_inv₀, Complex.conj_ofReal, inner_add_left,
    inner_add_right, inner_add_right, he_inner_self hn, hz', inner_z_e hz]
  ring

/-- Le module de `⟪Tw,Tw'⟫` (les images des représentants unitaires de `e+z`/`e+z'`)
se calcule en fonction de `⟪z,z'⟫` seul — c'est le pont entre `IsWignerMap` (qui ne
voit que des vecteurs unitaires) et l'énoncé (12), qui porte sur `z,z' ∈ 𝒫`
quelconques. -/
private theorem norm_Tw_Tw' (hT : IsWignerMap T) (hn : 2 ≤ n) {z z' : H n} (hz : InPerp z)
    (hz' : InPerp z') :
    ‖⟪T ((‖e n + z‖⁻¹ : ℂ) • (e n + z)), T ((‖e n + z'‖⁻¹ : ℂ) • (e n + z'))⟫_ℂ‖
      = ‖e n + z‖⁻¹ * ‖e n + z'‖⁻¹ * ‖1 + ⟪z, z'⟫_ℂ‖ := by
  rw [hT _ _ (norm_w hn hz) (norm_w hn hz'), inner_ew_ewx_eq hn hz hz', norm_mul, norm_mul,
    norm_inv, norm_inv, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_norm, abs_norm]

/-- (12) Partie réelle du produit scalaire préservée par `V` sur `𝒫`. Preuve : via
`inner_V_eq`, `⟪Vw,Vx⟫ = M - 1` avec `M := (conj γ)⁻¹γ'⁻¹⟪Tw,Tw'⟫` ; `‖M‖` se
simplifie en `‖1+⟪w,x⟫‖` (les facteurs `‖e+z‖`/`‖e+z'‖` s'annulent EXACTEMENT
contre `‖γ‖⁻¹`/`‖γ'‖⁻¹`, cf. `norm_gamma`), donc `‖1+⟪Vw,Vx⟫‖ = ‖1+⟪w,x⟫‖` ; combiné
à `‖⟪Vw,Vx⟫‖ = ‖⟪w,x⟫‖` (`norm_inner_V` ci-dessus), `re_eq_of_norm_eq` (W1) conclut. -/
theorem re_inner_V (hT : IsWignerMap T) (hn : 2 ≤ n) (w x : H n) (hw : InPerp w)
    (hx : InPerp x) : (⟪V T w, V T x⟫_ℂ).re = (⟪w, x⟫_ℂ).re := by
  have hone : ‖(1 : ℂ) + ⟪V T w, V T x⟫_ℂ‖ = ‖(1 : ℂ) + ⟪w, x⟫_ℂ‖ := by
    have hV := inner_V_eq hT hn hw hx
    have h1 : (1 : ℂ) + ⟪V T w, V T x⟫_ℂ =
        (starRingEnd ℂ (⟪eImg T, T ((‖e n + w‖⁻¹ : ℂ) • (e n + w))⟫_ℂ))⁻¹ *
          (⟪eImg T, T ((‖e n + x‖⁻¹ : ℂ) • (e n + x))⟫_ℂ)⁻¹ *
          ⟪T ((‖e n + w‖⁻¹ : ℂ) • (e n + w)), T ((‖e n + x‖⁻¹ : ℂ) • (e n + x))⟫_ℂ := by
      rw [hV]; ring
    rw [h1, norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_conj, norm_gamma hT hn hw,
      norm_gamma hT hn hx, norm_Tw_Tw' hT hn hw hx, inv_inv, inv_inv]
    have hnw : ‖e n + w‖ ≠ 0 := norm_ne_zero_iff.mpr (he_add_ne_zero hn hw)
    have hnx : ‖e n + x‖ ≠ 0 := norm_ne_zero_iff.mpr (he_add_ne_zero hn hx)
    field_simp
  exact re_eq_of_norm_eq (norm_inner_V hT hn w x hw hx) hone

/-- (12a) Si `⟪w,x⟫` est déjà réel, `V` le préserve exactement (pas seulement sa
partie réelle ou son module) : (11)+(12) forcent `Im⟪Vw,Vx⟫ = 0` par
`|z|² = Re(z)² + Im(z)²`. -/
theorem inner_V_eq_of_im_eq_zero (hT : IsWignerMap T) (hn : 2 ≤ n) (w x : H n) (hw : InPerp w)
    (hx : InPerp x) (hreal : (⟪w, x⟫_ℂ).im = 0) : ⟪V T w, V T x⟫_ℂ = ⟪w, x⟫_ℂ := by
  have h11 : ‖⟪V T w, V T x⟫_ℂ‖ = ‖⟪w, x⟫_ℂ‖ := norm_inner_V hT hn w x hw hx
  have h12 : (⟪V T w, V T x⟫_ℂ).re = (⟪w, x⟫_ℂ).re := re_inner_V hT hn w x hw hx
  have hns : Complex.normSq ⟪V T w, V T x⟫_ℂ = Complex.normSq ⟪w, x⟫_ℂ := by
    rw [← Complex.sq_norm, ← Complex.sq_norm, h11]
  rw [Complex.normSq_apply, Complex.normSq_apply, h12, hreal] at hns
  have him : (⟪V T w, V T x⟫_ℂ).im = 0 := by nlinarith [sq_nonneg (⟪V T w, V T x⟫_ℂ).im]
  have hxre : ⟪w, x⟫_ℂ = ((⟪w, x⟫_ℂ).re : ℂ) := by
    conv_lhs => rw [← Complex.re_add_im ⟪w, x⟫_ℂ]
    rw [hreal]; simp
  rw [hxre]
  exact Complex.ext h12 him

end
end QuantumFoundations.Wigner
