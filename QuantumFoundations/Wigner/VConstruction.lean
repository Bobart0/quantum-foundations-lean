import QuantumFoundations.Wigner.Defs

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

theorem norm_V (hT : IsWignerMap T) (z : H n) (hz : InPerp z) :
    ‖V T z‖ = ‖z‖ := by
  sorry

/-- Colinéarité définitionnelle : `V z` est un multiple scalaire de phase de
`T` appliqué au représentant unitaire de `z` (Bargmann §3.2 : « Clearly,
`Vz = f'β' ∈ (Tf)‖z‖ = Tz` »). Rend la compatibilité `⟪e,x⟫ = 0` de W5 GRATUITE,
sans Cauchy-Schwarz. -/
theorem V_colinear (hT : IsWignerMap T) (z : H n) (hz : InPerp z) (hz0 : z ≠ 0) :
    ∃ δ : ℂ, ‖δ‖ = 1 ∧ V T z = δ • T (‖z‖⁻¹ • z) := by
  sorry

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
