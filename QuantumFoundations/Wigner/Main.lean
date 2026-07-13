import QuantumFoundations.Wigner.Core

/-!
# W5 — Assemblage (Bargmann §5) et théorème de Wigner

`U` étend `chi`/`V` à tout l'espace par la décomposition `a = ⟪e,a⟫•e + (a −
⟪e,a⟫•e)` (le second terme est dans `𝒫`). La compatibilité `∀x, ∃c, T x = c•U x`
se scinde en deux cas : `⟪e,x⟫ ≠ 0` (calcul direct) et `⟪e,x⟫ = 0` (GRATUIT, via la
colinéarité définitionnelle de `V_colinear` — aucun Cauchy-Schwarz nécessaire,
contrairement à l'inquiétude initiale). La bijectivité de `U` (isométrie ⟹
injective ⟹ surjective en dimension finie) se fait en restreignant à la structure
ℝ-linéaire sous-jacente pour la branche antiunitaire (`LinearMap.injective_iff_surjective`
n'existe que pour des endomorphismes `K`-linéaires ; une application
conj-semilinéaire sur ℂ est ℝ-linéaire par restriction des scalaires) — aucune
coordonnée nécessaire.

**Énoncé final : formulation (A), sans hypothèse de bijectivité** (Bargmann §1.2-
§1.3) — l'injectivité au niveau des rayons découle de `hT` via Cauchy-Schwarz, et
en dimension finie `U` construit est automatiquement bijectif. Énoncé strictement
plus fort que Simon et al. (qui supposent la bijectivité, eq. 2.8).
-/

namespace QuantumFoundations.Wigner

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ} {T : H n → H n}

private theorem he_self (hn : 2 ≤ n) : ⟪e n, e n⟫_ℂ = (1 : ℂ) := by
  have h0 : 0 < n := by omega
  simp only [e, dif_pos h0, EuclideanSpace.inner_single_left, PiLp.single_apply]
  simp

private theorem chi_add (hT : IsWignerMap T) (hn : 2 ≤ n) (a b : ℂ) :
    chi T (a + b) = chi T a + chi T b := by
  rcases chi_dichotomy hT hn with h | h
  · rw [congrFun h, congrFun h, congrFun h]; rfl
  · rw [congrFun h, congrFun h, congrFun h, map_add]

private theorem chi_conj_mul (hT : IsWignerMap T) (hn : 2 ≤ n) (a b : ℂ) :
    (starRingEnd ℂ) (chi T a) * chi T b = chi T ((starRingEnd ℂ) a * b) := by
  rcases chi_dichotomy hT hn with h | h
  · rw [congrFun h, congrFun h, congrFun h]; rfl
  · rw [congrFun h, congrFun h, congrFun h, map_mul]

private theorem InPerp_z (hn : 2 ≤ n) (a : H n) : InPerp (a - ⟪e n, a⟫_ℂ • e n) := by
  show ⟪e n, a - ⟪e n, a⟫_ℂ • e n⟫_ℂ = 0
  rw [inner_sub_right, inner_smul_right, he_self hn, mul_one, sub_self]

theorem U_additive (hT : IsWignerMap T) (hn : 2 ≤ n) (a b : H n) :
    U T (a + b) = U T a + U T b := by
  show chi T ⟪e n, a + b⟫_ℂ • eImg T + V T (a + b - ⟪e n, a + b⟫_ℂ • e n)
      = chi T ⟪e n, a⟫_ℂ • eImg T + V T (a - ⟪e n, a⟫_ℂ • e n)
        + (chi T ⟪e n, b⟫_ℂ • eImg T + V T (b - ⟪e n, b⟫_ℂ • e n))
  have hsum : a + b - ⟪e n, a + b⟫_ℂ • e n
      = (a - ⟪e n, a⟫_ℂ • e n) + (b - ⟪e n, b⟫_ℂ • e n) := by
    rw [inner_add_right, add_smul]; abel
  rw [hsum, V_additive hT hn _ _ (InPerp_z hn a) (InPerp_z hn b), inner_add_right, chi_add hT hn]
  module

private theorem chi_mul (hT : IsWignerMap T) (hn : 2 ≤ n) (a b : ℂ) :
    chi T (a * b) = chi T a * chi T b := by
  rcases chi_dichotomy hT hn with h | h
  · rw [congrFun h, congrFun h, congrFun h]; rfl
  · rw [congrFun h, congrFun h, congrFun h, map_mul]

theorem U_chi_semilinear (hT : IsWignerMap T) (hn : 2 ≤ n) (c : ℂ) (a : H n) :
    U T (c • a) = chi T c • U T a := by
  show chi T ⟪e n, c • a⟫_ℂ • eImg T + V T (c • a - ⟪e n, c • a⟫_ℂ • e n)
      = chi T c • (chi T ⟪e n, a⟫_ℂ • eImg T + V T (a - ⟪e n, a⟫_ℂ • e n))
  have hz : c • a - ⟪e n, c • a⟫_ℂ • e n = c • (a - ⟪e n, a⟫_ℂ • e n) := by
    rw [inner_smul_right, smul_sub, mul_smul]
  rw [hz, V_chi_homogeneous hT hn c _ (InPerp_z hn a), inner_smul_right, chi_mul hT hn]
  module

private theorem he_norm (hn : 2 ≤ n) : ‖e n‖ = 1 := by
  have h0 : 0 < n := by omega
  simp only [e, dif_pos h0, PiLp.norm_single]
  norm_num

private theorem heImg_self (hT : IsWignerMap T) (hn : 2 ≤ n) : ⟪eImg T, eImg T⟫_ℂ = (1 : ℂ) := by
  have h1 : ‖⟪eImg T, eImg T⟫_ℂ‖ = ‖⟪e n, e n⟫_ℂ‖ := hT (e n) (e n) (he_norm hn) (he_norm hn)
  rw [he_self hn, norm_one, inner_self_eq_norm_sq_to_K] at h1
  have h2 : ‖eImg T‖ ^ 2 = 1 := by simpa using h1
  have h3 : ‖eImg T‖ = 1 := by nlinarith [h2, norm_nonneg (eImg T), sq_nonneg (‖eImg T‖ - 1)]
  rw [inner_self_eq_norm_sq_to_K, h3]; norm_num

private theorem inner_ab_decomp (hn : 2 ≤ n) (a b : H n) :
    ⟪a, b⟫_ℂ = (starRingEnd ℂ) ⟪e n, a⟫_ℂ * ⟪e n, b⟫_ℂ
      + ⟪a - ⟪e n, a⟫_ℂ • e n, b - ⟪e n, b⟫_ℂ • e n⟫_ℂ := by
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, he_self hn]
  rw [← inner_conj_symm a (e n)]
  ring

theorem inner_U_eq_chi_inner (hT : IsWignerMap T) (hn : 2 ≤ n) (a b : H n) :
    ⟪U T a, U T b⟫_ℂ = chi T ⟪a, b⟫_ℂ := by
  show ⟪chi T ⟪e n, a⟫_ℂ • eImg T + V T (a - ⟪e n, a⟫_ℂ • e n),
      chi T ⟪e n, b⟫_ℂ • eImg T + V T (b - ⟪e n, b⟫_ℂ • e n)⟫_ℂ = chi T ⟪a, b⟫_ℂ
  have hzap : InPerp (a - ⟪e n, a⟫_ℂ • e n) := InPerp_z hn a
  have hzbp : InPerp (b - ⟪e n, b⟫_ℂ • e n) := InPerp_z hn b
  have hc1 : ⟪eImg T, V T (b - ⟪e n, b⟫_ℂ • e n)⟫_ℂ = 0 := inner_eImg_V hT hn _ hzbp
  have hc2 : ⟪V T (a - ⟪e n, a⟫_ℂ • e n), eImg T⟫_ℂ = 0 := by
    have h := inner_eImg_V hT hn (a - ⟪e n, a⟫_ℂ • e n) hzap
    rw [← inner_conj_symm (eImg T) (V T (a - ⟪e n, a⟫_ℂ • e n))] at h
    have h2 := congrArg (starRingEnd ℂ) h
    simpa using h2
  rw [inner_add_left, inner_add_right, inner_add_right, inner_smul_left, inner_smul_left,
    inner_smul_right, inner_smul_right, heImg_self hT hn, mul_one, hc1, mul_zero, hc2,
    mul_zero, add_zero, zero_add, inner_V_eq_chi_inner hT hn _ _ hzap hzbp, chi_conj_mul hT hn,
    ← chi_add hT hn, ← inner_ab_decomp hn]

/-- Compatibilité de `U` avec `T` à une phase près, sur la sphère unité. Cœur de
la preuve de `wigner`. -/
theorem exists_phase_U (hT : IsWignerMap T) (hn : 2 ≤ n) (x : H n) (hx : ‖x‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U T x := by
  sorry

theorem U_bijective (hT : IsWignerMap T) (hn : 2 ≤ n) : Function.Bijective (U T) := by
  sorry

/-- **Théorème de Wigner** (dimension finie, sans hypothèse de bijectivité sur
`T`). Toute transformation sur les états purs qui préserve les probabilités de
transition `|⟨φ|ψ⟩|²` est induite par un unitaire ou un antiunitaire. -/
theorem wigner (n : ℕ) (T : H n → H n) (hT : IsWignerMap T) :
    (∃ U' : H n ≃ₗᵢ[ℂ] H n, ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U' x)
  ∨ (∃ U' : H n ≃ₛₗᵢ[starRingEnd ℂ] H n, ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U' x) := by
  rcases n with _ | _ | n
  · -- n = 0 : aucun vecteur unitaire dans H 0, vacuité.
    refine Or.inl ⟨LinearIsometryEquiv.refl ℂ (H 0), fun x hx => ?_⟩
    rw [Subsingleton.elim x 0] at hx
    simp at hx
  · -- n = 1 : les deux branches marchent (Bargmann §1.4) ; une seule "phase"
    -- possible dès que dim = 1. À prouver : reste un lemme court et autonome
    -- (aucune dépendance sur W1-W5), pas encore attaqué à ce stade du squelette.
    sorry
  · -- n ≥ 2 : cœur, via exists_phase_U + U_bijective + bundling dans les deux
    -- branches (LinearIsometryEquiv.mk / LinearEquiv.ofBijective).
    sorry

end
end QuantumFoundations.Wigner
