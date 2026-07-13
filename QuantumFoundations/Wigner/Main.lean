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

private theorem inner_e_w (hn : 2 ≤ n) {z : H n} (hz : InPerp z) :
    ⟪e n, ((‖e n + z‖⁻¹ : ℂ) • (e n + z))⟫_ℂ = (‖e n + z‖⁻¹ : ℂ) := by
  rw [inner_smul_right, inner_add_right, he_self hn, hz]
  ring

private theorem norm_gamma (hT : IsWignerMap T) (hn : 2 ≤ n) {z : H n} (hz : InPerp z) :
    ‖⟪eImg T, T ((‖e n + z‖⁻¹ : ℂ) • (e n + z))⟫_ℂ‖ = ‖e n + z‖⁻¹ := by
  show ‖⟪T (e n), T ((‖e n + z‖⁻¹ : ℂ) • (e n + z))⟫_ℂ‖ = ‖e n + z‖⁻¹
  rw [hT (e n) _ (he_norm hn) (norm_w hn hz), inner_e_w hn hz, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr (he_add_ne_zero hn hz))]

/-- Compatibilité de `U` avec `T` à une phase près, sur la sphère unité. Cœur de
la preuve de `wigner`. -/
theorem exists_phase_U (hT : IsWignerMap T) (hn : 2 ≤ n) (x : H n) (hx : ‖x‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U T x := by
  have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hx; exact one_ne_zero hx.symm
  by_cases hα0 : ⟪e n, x⟫_ℂ = 0
  · -- x ∈ 𝒫 : gratuit via V_colinear (W3), aucun Cauchy-Schwarz.
    have hxp : InPerp x := hα0
    have hUx : U T x = V T x := by
      have hchi0 : chi T (0 : ℂ) = 0 := by have h := chi_real hT hn 0; simpa using h
      show chi T ⟪e n, x⟫_ℂ • eImg T + V T (x - ⟪e n, x⟫_ℂ • e n) = V T x
      rw [hα0, hchi0, zero_smul, zero_smul, sub_zero, zero_add]
    obtain ⟨δ, hδnorm, hVx⟩ := V_colinear hT hn x hxp hx0
    rw [hx] at hVx hδnorm
    norm_num at hVx hδnorm
    have hδne : δ ≠ 0 := by intro h; rw [h, norm_zero] at hδnorm; exact zero_ne_one hδnorm
    refine ⟨δ⁻¹, by rw [norm_inv, hδnorm, inv_one], ?_⟩
    rw [hUx, hVx, smul_smul, inv_mul_cancel₀ hδne, one_smul]
  · -- α := ⟪e n,x⟫ ≠ 0
    set α := ⟪e n, x⟫_ℂ with hα_def
    have hαne : ‖α‖ ≠ 0 := norm_ne_zero_iff.mpr hα0
    set zx := x - α • e n with hzx_def
    have hzxp : InPerp zx := InPerp_z hn x
    set ζ := α⁻¹ • zx with hζ_def
    have hζp : InPerp ζ := by
      show ⟪e n, ζ⟫_ℂ = 0
      rw [hζ_def, inner_smul_right, hzxp]; ring
    have hzx_eq : zx = α • ζ := by
      rw [hζ_def, smul_smul, mul_inv_cancel₀ hα0, one_smul]
    have hx_decomp : x = α • (e n + ζ) := by
      have hxz : x = zx + α • e n := by rw [hzx_def]; abel
      rw [hxz, hzx_eq, smul_add]; abel
    set w := (‖e n + ζ‖⁻¹ : ℂ) • (e n + ζ) with hw_def
    have hnormw1 : ‖e n + ζ‖ = ‖α‖⁻¹ := by
      have h1 : ‖x‖ = ‖α‖ * ‖e n + ζ‖ := by rw [hx_decomp, norm_smul]
      rw [hx] at h1
      field_simp at h1 ⊢
      linarith [h1]
    set c0 : ℂ := α * (‖α‖ : ℂ)⁻¹ with hc0_def
    have hc0u : ‖c0‖ = 1 := by
      rw [hc0_def, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        mul_inv_cancel₀ hαne]
    have hwu : ‖w‖ = 1 := norm_w hn hζp
    have hx_eq_c0w : x = c0 • w := by
      rw [hx_decomp, hw_def, smul_smul]
      congr 1
      rw [hc0_def, hnormw1]
      push_cast
      rw [inv_inv, mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hαne : (‖α‖ : ℂ) ≠ 0), mul_one]
    obtain ⟨lam, hlamnorm, hTx⟩ := T_phase hT hwu hc0u
    rw [← hx_eq_c0w] at hTx
    set γ := ⟪eImg T, T w⟫_ℂ with hγ_def
    have hγnorm : ‖γ‖ = ‖α‖ := by rw [hγ_def, hw_def, norm_gamma hT hn hζp, hnormw1, inv_inv]
    have hγne : γ ≠ 0 := by intro h; rw [h, norm_zero] at hγnorm; exact hαne hγnorm.symm
    have hVζ_eq : V T ζ = γ⁻¹ • T w - eImg T := rfl
    have hTw_eq : T w = γ • (V T ζ + eImg T) := by
      have h1 : γ⁻¹ • T w = V T ζ + eImg T := by rw [hVζ_eq]; abel
      rw [← h1, smul_smul, mul_inv_cancel₀ hγne, one_smul]
    have hUx_eq : U T x = chi T α • (V T ζ + eImg T) := by
      show chi T α • eImg T + V T zx = chi T α • (V T ζ + eImg T)
      rw [hzx_eq, V_chi_homogeneous hT hn α ζ hζp, smul_add, add_comm (chi T α • V T ζ)]
    have hchiα_norm : ‖chi T α‖ = ‖α‖ := by
      rcases chi_dichotomy hT hn with h | h
      · rw [congrFun h]; rfl
      · rw [congrFun h]; exact Complex.norm_conj α
    have hchiα_ne : chi T α ≠ 0 := by rw [← norm_ne_zero_iff, hchiα_norm]; exact hαne
    set c := lam * γ * (chi T α)⁻¹ with hc_def
    have hcnorm : ‖c‖ = 1 := by
      rw [hc_def, norm_mul, norm_mul, norm_inv, hlamnorm, one_mul, hγnorm, hchiα_norm,
        mul_inv_cancel₀ hαne]
    refine ⟨c, hcnorm, ?_⟩
    rw [hTx, hTw_eq, hUx_eq, smul_smul, smul_smul]
    congr 1
    rw [hc_def, mul_assoc, inv_mul_cancel₀ hchiα_ne, mul_one]

/-- `U` préserve la norme, INDÉPENDAMMENT de la branche de `chi` (`inner_U_eq_chi_inner`
donne `⟪Ua,Ua⟫ = chi⟪a,a⟫`, et `chi` fixe le réel non-négatif `‖a‖²`). -/
private theorem U_norm_eq (hT : IsWignerMap T) (hn : 2 ≤ n) (a : H n) : ‖U T a‖ = ‖a‖ := by
  have haa : ⟪a, a⟫_ℂ = ((‖a‖ ^ 2 : ℝ) : ℂ) := by rw [inner_self_eq_norm_sq_to_K]; norm_cast
  have h1 : ⟪U T a, U T a⟫_ℂ = chi T ⟪a, a⟫_ℂ := inner_U_eq_chi_inner hT hn a a
  rw [haa, chi_real hT hn] at h1
  have hUaa : ⟪U T a, U T a⟫_ℂ = ((‖U T a‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hUaa] at h1
  have h3 : ‖U T a‖ ^ 2 = ‖a‖ ^ 2 := by exact_mod_cast h1
  nlinarith [h3, norm_nonneg (U T a), norm_nonneg a, sq_nonneg (‖U T a‖ - ‖a‖)]

private theorem U_injective (hT : IsWignerMap T) (hn : 2 ≤ n) : Function.Injective (U T) := by
  intro a b hab
  have h1 : U T a = U T (a - b) + U T b := by
    rw [← U_additive hT hn (a - b) b, sub_add_cancel]
  rw [h1] at hab
  have hUsub : U T (a - b) = 0 := add_eq_right.mp hab
  have hnorm : ‖a - b‖ = 0 := by rw [← U_norm_eq hT hn (a - b), hUsub, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

theorem U_bijective (hT : IsWignerMap T) (hn : 2 ≤ n) : Function.Bijective (U T) := by
  refine ⟨U_injective hT hn, ?_⟩
  rcases chi_dichotomy hT hn with h | h
  · let f : H n →ₗ[ℂ] H n :=
      { toFun := U T
        map_add' := U_additive hT hn
        map_smul' := fun c a => by rw [U_chi_semilinear hT hn c a, congrFun h]; rfl }
    exact (LinearMap.injective_iff_surjective (f := f)).mp (U_injective hT hn)
  · let g : H n →ₗ[ℝ] H n :=
      { toFun := U T
        map_add' := U_additive hT hn
        map_smul' := fun r a => by
          have hr := U_chi_semilinear hT hn (r : ℂ) a
          rw [congrFun h] at hr
          simpa using hr }
    exact (LinearMap.injective_iff_surjective (f := g)).mp (U_injective hT hn)

/-- Cas `n = 1` : `𝒫` est réduit à `{0}` (`dim H 1 = 1`), donc tout `x` est un
multiple scalaire de `e 1` — fait autonome, indépendant de `hn : 2 ≤ n`. -/
private theorem H1_eq_inner_smul_e (x : H 1) : x = ⟪e 1, x⟫_ℂ • e 1 := by
  have hi : ∀ i : Fin 1, i = 0 := fun i => Subsingleton.elim i 0
  ext i
  rw [hi i]
  have h0 : (0 : ℕ) < 1 := by norm_num
  simp only [e, dif_pos h0, EuclideanSpace.inner_single_left, PiLp.smul_apply, PiLp.single_apply]
  simp

private theorem he_norm_one : ‖e 1‖ = (1 : ℝ) := by
  have h0 : (0 : ℕ) < 1 := by norm_num
  simp only [e, dif_pos h0, PiLp.norm_single]
  norm_num

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
  · -- n = 1 : les deux branches marchent (Bargmann §1.4) ; branche linéaire par
    -- convention. Dérivation autonome (aucune dépendance sur W1-W5, `hn : 2 ≤ n`
    -- n'étant jamais disponible ici).
    have hnormeImg1 : ‖eImg T‖ = 1 := by
      have h1 : ‖⟪eImg T, eImg T⟫_ℂ‖ = ‖⟪e 1, e 1⟫_ℂ‖ := hT (e 1) (e 1) he_norm_one he_norm_one
      have hee : ⟪e 1, e 1⟫_ℂ = (1 : ℂ) := by
        have h0 : (0 : ℕ) < 1 := by norm_num
        simp only [e, dif_pos h0, EuclideanSpace.inner_single_left, PiLp.single_apply]
        simp
      rw [hee, norm_one, inner_self_eq_norm_sq_to_K] at h1
      have h2 : ‖eImg T‖ ^ 2 = 1 := by simpa using h1
      nlinarith [h2, norm_nonneg (eImg T), sq_nonneg (‖eImg T‖ - 1)]
    have heImg_ne : eImg T ≠ 0 := by
      intro h; rw [h, norm_zero] at hnormeImg1; exact zero_ne_one hnormeImg1
    let f1 : H 1 →ₗ[ℂ] H 1 :=
      { toFun := fun x => ⟪e 1, x⟫_ℂ • eImg T
        map_add' := fun a b => by simp only [inner_add_right, add_smul]
        map_smul' := fun c a => by simp only [inner_smul_right, smul_smul, RingHom.id_apply] }
    have hinj1 : Function.Injective f1 := by
      intro a b hab
      simp only [f1, LinearMap.coe_mk, AddHom.coe_mk] at hab
      have hsub : (⟪e 1, a⟫_ℂ - ⟪e 1, b⟫_ℂ) • eImg T = 0 := by rw [sub_smul, hab, sub_self]
      have heq : ⟪e 1, a⟫_ℂ = ⟪e 1, b⟫_ℂ := by
        rcases smul_eq_zero.mp hsub with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h heImg_ne
      rw [H1_eq_inner_smul_e a, H1_eq_inner_smul_e b, heq]
    have hsurj1 : Function.Surjective f1 := LinearMap.injective_iff_surjective.mp hinj1
    have hnorm1 : ∀ x : H 1, ‖f1 x‖ = ‖x‖ := by
      intro x
      show ‖⟪e 1, x⟫_ℂ • eImg T‖ = ‖x‖
      rw [norm_smul, hnormeImg1, mul_one]
      conv_rhs => rw [H1_eq_inner_smul_e x]
      rw [norm_smul, he_norm_one, mul_one]
    refine Or.inl ⟨LinearIsometryEquiv.mk (LinearEquiv.ofBijective f1 ⟨hinj1, hsurj1⟩) hnorm1,
      fun x hx => ?_⟩
    set β := ⟪e 1, x⟫_ℂ with hβ_def
    have hxβ : x = β • e 1 := H1_eq_inner_smul_e x
    have hβnorm : ‖β‖ = 1 := by
      have h1 : ‖x‖ = ‖β‖ * ‖e 1‖ := by rw [hxβ, norm_smul]
      rw [hx, he_norm_one, mul_one] at h1
      exact h1.symm
    obtain ⟨lam, hlamnorm, hTx⟩ := T_phase hT he_norm_one hβnorm
    rw [← hxβ] at hTx
    have hβne : β ≠ 0 := by intro h; rw [h, norm_zero] at hβnorm; exact zero_ne_one hβnorm
    refine ⟨lam * β⁻¹, ?_, ?_⟩
    · rw [norm_mul, norm_inv, hlamnorm, hβnorm, inv_one, mul_one]
    · show T x = (lam * β⁻¹) • (LinearEquiv.ofBijective f1 ⟨hinj1, hsurj1⟩ x)
      show T x = (lam * β⁻¹) • f1 x
      show T x = (lam * β⁻¹) • (β • eImg T)
      rw [smul_smul, mul_assoc, inv_mul_cancel₀ hβne, mul_one]
      exact hTx
  · -- n ≥ 2 : cœur, via exists_phase_U + U_bijective + bundling dans les deux
    -- branches (LinearIsometryEquiv.mk / LinearEquiv.ofBijective).
    have hn2 : 2 ≤ n + 1 + 1 := by omega
    rcases chi_dichotomy hT hn2 with hchi | hchi
    · let f : H (n + 1 + 1) →ₗ[ℂ] H (n + 1 + 1) :=
        { toFun := U T
          map_add' := U_additive hT hn2
          map_smul' := fun c a => by rw [U_chi_semilinear hT hn2 c a, congrFun hchi]; rfl }
      have hbij : Function.Bijective f := U_bijective hT hn2
      have hnorm : ∀ a, ‖(LinearEquiv.ofBijective f hbij) a‖ = ‖a‖ := fun a => U_norm_eq hT hn2 a
      exact Or.inl ⟨LinearIsometryEquiv.mk (LinearEquiv.ofBijective f hbij) hnorm,
        fun x hx => exists_phase_U hT hn2 x hx⟩
    · let g : H (n + 1 + 1) →ₛₗ[starRingEnd ℂ] H (n + 1 + 1) :=
        { toFun := U T
          map_add' := U_additive hT hn2
          map_smul' := fun c a => by rw [U_chi_semilinear hT hn2 c a, congrFun hchi] }
      have hbij : Function.Bijective g := U_bijective hT hn2
      have hnorm : ∀ a, ‖(LinearEquiv.ofBijective g hbij) a‖ = ‖a‖ := fun a => U_norm_eq hT hn2 a
      exact Or.inr ⟨LinearIsometryEquiv.mk (LinearEquiv.ofBijective g hbij) hnorm,
        fun x hx => exists_phase_U hT hn2 x hx⟩

end
end QuantumFoundations.Wigner
