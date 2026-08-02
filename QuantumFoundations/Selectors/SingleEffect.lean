import QuantumFoundations.Selectors.Pinning

/-!
**FR.** # Selectors — S6 : Proposition 2, classification par contrainte à effet unique

Contenu interprétativement neutre, comme le reste du sous-module. Pour un
effet `E₀`, un état unitaire `ψ` et un réel `c`, la contrainte
`Re tr(ρ E₀) = c` force `ρ = |ψ⟩⟨ψ|` pour toute matrice densité `ρ` si et
seulement si `ψ` engendre l'espace propre simple d'une valeur propre
extrémale (minimale ou maximale) de `E₀`, et `c` est cette valeur propre.
Le cas `E₀ = P_{ψ⊥}`, `c = 0` est le corollaire correspondant au minimum
simple nul, et se raccorde à `NSNC1` (S4).

Cette classification est un résultat de géométrie convexe/spectrale : elle
décrit exhaustivement les contraintes à effet unique qui suffiraient à
isoler un état pur, sans revendiquer qu'une telle contrainte doive être
acceptée comme principe physique. La famille `ρ_t` de `tDensity` n'est pas
la famille isotrope générique en jeu ici ; `Proposition 2` est indépendante
de la classification par covariance (S2/S3).

Décomposition en lemmes, dans l'ordre :
1. `density_supported_on_kernel_of_extremal_trace` : lemme spectral général
   (positivité d'un opérateur `A`, valeur de trace nulle ⟹ densité
   supportée sur `(ker A)ᗮ`), via la base propre de `A`
   (`LinearMap.IsSymmetric.eigenvectorBasis`) — sens extrémal ⟹ sélection.
2. Témoin orthogonal direct (`z := (ℂ∙ψ)ᗮ.starProjection x`) : pas de
   Cauchy–Schwarz stricte, pas de formule de trace croisée entre
   projecteurs purs.
3. `no_straddling_of_single_effect_selects` : une sélection unique interdit
   toute paire `q x < c < q y` (`q u := Re⟪E₀u,u⟫`), via une densité mixte
   construite explicitement et le témoin orthogonal.
4. Dichotomie min/max, extension par homogénéité quadratique aux vecteurs
   non unitaires.
5. Équation propre (`apply_eq_zero_of_quadratic_eq_zero`, déjà prouvé en
   S4, réutilisé tel quel) et simplicité de l'espace propre.
6. Assemblage : `single_effect_selector_iff`.

**EN.** # Selectors — S6: Proposition 2, single-effect-constraint classification

Interpretively neutral content, like the rest of the submodule. For an
effect `E₀`, a unit state `ψ`, and a real `c`, the constraint
`Re tr(ρ E₀) = c` forces `ρ = |ψ⟩⟨ψ|` for every density matrix `ρ` if and
only if `ψ` spans the simple eigenspace of an extremal (minimal or
maximal) eigenvalue of `E₀`, and `c` is that eigenvalue. The case
`E₀ = P_{ψ⊥}`, `c = 0` is the corollary corresponding to the simple null
minimum, and connects back to `NSNC1` (S4).

This classification is a convex/spectral geometry result: it exhaustively
describes the single-effect constraints that would suffice to isolate a
pure state, without claiming that any such constraint must be accepted as
a physical principle. The `tDensity` family `ρ_t` is not the generic
isotropic family at play here; Proposition 2 is independent of the
covariance classification (S2/S3).

Decomposed into lemmas, in order:
1. `density_supported_on_kernel_of_extremal_trace`: general spectral lemma
   (positivity of an operator `A`, vanishing trace value ⟹ density
   supported on `(ker A)ᗮ`), via `A`'s eigenbasis
   (`LinearMap.IsSymmetric.eigenvectorBasis`) — the extremal ⟹ selection
   direction.
2. Direct orthogonal witness (`z := (ℂ∙ψ)ᗮ.starProjection x`): no strict
   Cauchy–Schwarz, no cross-trace formula between pure projectors.
3. `no_straddling_of_single_effect_selects`: unique selection forbids any
   pair `q x < c < q y` (`q u := Re⟪E₀u,u⟫`), via an explicitly built mixed
   density and the orthogonal witness.
4. Min/max dichotomy, extension by quadratic homogeneity to non-unit
   vectors.
5. Eigenequation (`apply_eq_zero_of_quadratic_eq_zero`, already proved in
   S4, reused as-is) and simplicity of the eigenspace.
6. Assembly: `single_effect_selector_iff`.
-/

namespace QuantumFoundations.Selector

open scoped InnerProductSpace
open Gleason
open QuantumFoundations.Uhlhorn (projL_singleton_unit)

noncomputable section

variable {n : ℕ}

/-! ## Definitions -/

/-- **FR.** `ψ` est un vecteur propre de valeur propre `c`, minimum simple :
`c` minore la forme quadratique de `E₀` partout, et son espace propre est
exactement `ℂ ∙ ψ`.

**EN.** `ψ` is an eigenvector of eigenvalue `c`, a simple minimum: `c`
lower-bounds the quadratic form of `E₀` everywhere, and its eigenspace is
exactly `ℂ ∙ ψ`. -/
def IsSimpleMinimumEigenpair (E₀ : H n →ₗ[ℂ] H n) (ψ : H n) (c : ℝ) : Prop :=
  ‖ψ‖ = 1 ∧
  E₀ ψ = (c : ℂ) • ψ ∧
  (∀ x : H n, c * ‖x‖ ^ 2 ≤ (⟪E₀ x, x⟫_ℂ).re) ∧
  LinearMap.ker (E₀ - (c : ℂ) • LinearMap.id) = ℂ ∙ ψ

/-- **FR.** Symétrique : maximum simple.

**EN.** Symmetric: simple maximum. -/
def IsSimpleMaximumEigenpair (E₀ : H n →ₗ[ℂ] H n) (ψ : H n) (c : ℝ) : Prop :=
  ‖ψ‖ = 1 ∧
  E₀ ψ = (c : ℂ) • ψ ∧
  (∀ x : H n, (⟪E₀ x, x⟫_ℂ).re ≤ c * ‖x‖ ^ 2) ∧
  LinearMap.ker (E₀ - (c : ℂ) • LinearMap.id) = ℂ ∙ ψ

/-- **FR.** Extrémal simple : minimum simple ou maximum simple.

**EN.** Simple extremal: simple minimum or simple maximum. -/
def IsSimpleExtremalEigenpair (E₀ : H n →ₗ[ℂ] H n) (ψ : H n) (c : ℝ) : Prop :=
  IsSimpleMinimumEigenpair E₀ ψ c ∨ IsSimpleMaximumEigenpair E₀ ψ c

/-- **FR.** La contrainte `Re tr(ρ E₀) = c` sélectionne exactement l'état pur
`ψ` : la densité pure de `ψ` la satisfait (non-vacuité explicite), et c'est
la SEULE densité qui la satisfait.

**EN.** The constraint `Re tr(ρ E₀) = c` exactly selects the pure state
`ψ`: the pure density of `ψ` satisfies it (explicit nonvacuity), and it is
the ONLY density that does. -/
def SingleEffectExactlySelectsPureState (E₀ : H n →ₗ[ℂ] H n) (ψ : H n) (c : ℝ) : Prop :=
  (LinearMap.trace ℂ (H n) (projL (ℂ ∙ ψ) ∘ₗ E₀)).re = c ∧
  ∀ ρ : H n →ₗ[ℂ] H n, IsDensityOperator ρ →
    ((LinearMap.trace ℂ (H n) (ρ ∘ₗ E₀)).re = c ↔ ρ = projL (ℂ ∙ ψ))

/-! ## §1 General spectral support lemma (extremal ⟹ selects) -/

/-- **FR.** Si `A` est positif et `Re tr(ρA) = 0` pour une densité `ρ`,
alors `ρ` s'annule sur `(ker A)ᗮ`. Route : base propre de `A`
(`LinearMap.IsSymmetric.eigenvectorBasis`), valeurs propres réelles
non négatives (positivité de `A`), développement de la trace en somme de
termes réels non négatifs (positivité de `ρ` et de `A`), somme nulle ⟹
chaque terme nul ⟹ (pour les indices de valeur propre non nulle) `ρ`
s'annule sur le vecteur propre correspondant
(`apply_eq_zero_of_quadratic_eq_zero`) ; un vecteur de `(ker A)ᗮ` se
développe sans composante sur les vecteurs propres de valeur propre nulle.

**EN.** If `A` is positive and `Re tr(ρA) = 0` for a density `ρ`, then `ρ`
vanishes on `(ker A)ᗮ`. Route: eigenbasis of `A`
(`LinearMap.IsSymmetric.eigenvectorBasis`), real nonnegative eigenvalues
(positivity of `A`), expanding the trace as a sum of nonnegative real
terms (positivity of `ρ` and `A`), a vanishing sum forces every term to
vanish ⟹ (for nonzero-eigenvalue indices) `ρ` vanishes on the
corresponding eigenvector (`apply_eq_zero_of_quadratic_eq_zero`); a vector
of `(ker A)ᗮ` expands with no component on the zero-eigenvalue
eigenvectors. -/
theorem density_supported_on_kernel_of_extremal_trace
    {A : H n →ₗ[ℂ] H n} (hA : IsPositiveOp A)
    {ρ : H n →ₗ[ℂ] H n} (hρ : IsDensityOperator ρ)
    (htrace : (LinearMap.trace ℂ (H n) (ρ ∘ₗ A)).re = 0) :
    ∀ w : H n, w ∈ (LinearMap.ker A)ᗮ → ρ w = 0 := by
  have hfr : Module.finrank ℂ (H n) = n := by simp [H]
  set b := hA.1.eigenvectorBasis hfr with hb_def
  set a : Fin n → ℝ := hA.1.eigenvalues hfr with ha_def
  have hspec : ∀ i, A (b i) = (a i : ℂ) • b i := fun i => hA.1.apply_eigenvectorBasis hfr i
  have ha_nonneg : ∀ i, 0 ≤ a i := by
    intro i
    have h1 := hA.2 (b i)
    rw [hspec i, inner_smul_left] at h1
    have h2 : ⟪b i, b i⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, b.norm_eq_one i]; norm_num
    rw [h2, mul_one] at h1
    have hconj : (starRingEnd ℂ) (a i : ℂ) = (a i : ℂ) := Complex.conj_ofReal _
    rwa [hconj, Complex.ofReal_re] at h1
  have hker_iff : ∀ i, b i ∈ LinearMap.ker A ↔ a i = 0 := by
    intro i
    rw [LinearMap.mem_ker, hspec i]
    constructor
    · intro h
      by_contra hne
      have hbi_ne : (b i : H n) ≠ 0 := by
        have := b.norm_eq_one i
        intro hz; rw [hz, norm_zero] at this; norm_num at this
      apply hbi_ne
      have hac : (a i : ℂ) ≠ 0 := by exact_mod_cast hne
      exact (smul_eq_zero.mp h).resolve_left hac
    · intro h; rw [h]; simp
  have hborn_sum : (LinearMap.trace ℂ (H n) (ρ ∘ₗ A)).re
      = ∑ i, a i * (⟪b i, ρ (b i)⟫_ℂ).re := by
    rw [LinearMap.trace_eq_sum_inner (ρ ∘ₗ A) b, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [LinearMap.comp_apply, hspec i, map_smul, inner_smul_right, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hterm_nonneg : ∀ i, 0 ≤ a i * (⟪b i, ρ (b i)⟫_ℂ).re := by
    intro i
    apply mul_nonneg (ha_nonneg i)
    rw [← hρ.symmetric (b i) (b i)]
    exact hρ.nonneg (b i)
  have hterm_zero : ∀ i, a i * (⟪b i, ρ (b i)⟫_ℂ).re = 0 := by
    intro i
    have hsum0 : ∑ i, a i * (⟪b i, ρ (b i)⟫_ℂ).re = 0 := hborn_sum ▸ htrace
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hterm_nonneg i)).mp hsum0 i
      (Finset.mem_univ i)
  have hρbi_zero : ∀ i, a i ≠ 0 → ρ (b i) = 0 := by
    intro i hai
    have hre0 : (⟪b i, ρ (b i)⟫_ℂ).re = 0 := by
      have ht := hterm_zero i
      rcases mul_eq_zero.mp ht with h | h
      · exact absurd h hai
      · exact h
    have hsymmi : ⟪ρ (b i), b i⟫_ℂ = ⟪b i, ρ (b i)⟫_ℂ := hρ.symmetric (b i) (b i)
    have hreal : ⟪b i, ρ (b i)⟫_ℂ = ((⟪b i, ρ (b i)⟫_ℂ).re : ℂ) := by
      have hconjeq : (starRingEnd ℂ) ⟪b i, ρ (b i)⟫_ℂ = ⟪b i, ρ (b i)⟫_ℂ := by
        rw [inner_conj_symm, hsymmi]
      exact (Complex.conj_eq_iff_re.mp hconjeq).symm
    have hzero_c : ⟪b i, ρ (b i)⟫_ℂ = 0 := by rw [hreal, hre0]; norm_num
    apply apply_eq_zero_of_quadratic_eq_zero ⟨hρ.symmetric, hρ.nonneg⟩
    rw [hsymmi, hzero_c]
  intro w hw
  conv_lhs => rw [← OrthonormalBasis.sum_repr b w]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul]
  by_cases hai : a i = 0
  · have hc : (b.repr w).ofLp i = 0 := by
      have hbi_ker : b i ∈ LinearMap.ker A := (hker_iff i).mpr hai
      have hperp : ⟪b i, w⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).mp hw (b i) hbi_ker
      rw [OrthonormalBasis.repr_apply_apply, hperp]
    rw [hc, zero_smul]
  · rw [hρbi_zero i hai, smul_zero]

/-! ## §2 Direct orthogonal witness -/

private theorem z_mem_orthogonal (ψ x : H n) :
    (ℂ ∙ ψ)ᗮ.starProjection x ∈ (ℂ ∙ ψ)ᗮ :=
  Submodule.starProjection_apply_mem _ x

private theorem z_eq_sub (ψ x : H n) :
    (ℂ ∙ ψ)ᗮ.starProjection x = x - (ℂ ∙ ψ).starProjection x := by
  have h := Submodule.starProjection_orthogonal' (𝕜 := ℂ) (E := H n) (ℂ ∙ ψ)
  have hx := congrArg (· x) h
  simpa using hx

private theorem z_inner_psi_eq_zero (ψ x : H n) :
    ⟪ψ, (ℂ ∙ ψ)ᗮ.starProjection x⟫_ℂ = 0 :=
  (Submodule.mem_orthogonal _ _).mp (z_mem_orthogonal ψ x) ψ (Submodule.mem_span_singleton_self ψ)

private theorem sub_mem_span (ψ x : H n) :
    x - (ℂ ∙ ψ)ᗮ.starProjection x ∈ (ℂ ∙ ψ : Submodule ℂ (H n)) := by
  rw [z_eq_sub, sub_sub_cancel]
  exact Submodule.starProjection_apply_mem _ x

private theorem z_ne_zero_of_not_mem {ψ x : H n} (hx : x ∉ (ℂ ∙ ψ : Submodule ℂ (H n))) :
    (ℂ ∙ ψ)ᗮ.starProjection x ≠ 0 := by
  intro hz
  apply hx
  rw [z_eq_sub] at hz
  have hxeq : x = (ℂ ∙ ψ).starProjection x := sub_eq_zero.mp hz
  rw [hxeq]
  exact Submodule.starProjection_apply_mem _ x

private theorem inner_x_z_eq_norm_sq (ψ x : H n) :
    ⟪x, (ℂ ∙ ψ)ᗮ.starProjection x⟫_ℂ = (‖(ℂ ∙ ψ)ᗮ.starProjection x‖ : ℂ) ^ 2 := by
  set z := (ℂ ∙ ψ)ᗮ.starProjection x with hz_def
  have hsplit : x = (x - z) + z := by abel
  have hxz_mem : x - z ∈ (ℂ ∙ ψ : Submodule ℂ (H n)) := by rw [hz_def]; exact sub_mem_span ψ x
  have hzmem : z ∈ (ℂ ∙ ψ)ᗮ := z_mem_orthogonal ψ x
  have horth : ⟪x - z, z⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).mp hzmem (x - z) hxz_mem
  calc ⟪x, z⟫_ℂ = ⟪(x - z) + z, z⟫_ℂ := by rw [← hsplit]
    _ = ⟪x - z, z⟫_ℂ + ⟪z, z⟫_ℂ := by rw [inner_add_left]
    _ = ⟪z, z⟫_ℂ := by rw [horth, zero_add]
    _ = (‖z‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K z

/-- **FR.** Le projecteur pur sur `x` a une forme quadratique STRICTEMENT
positive en `z := (ℂ∙ψ)ᗮ.starProjection x`, dès que `x ∉ ℂ∙ψ` (donc `z≠0`).
Aucune Cauchy–Schwarz stricte : `⟪x,z⟩ = ⟪z,z⟩ = ‖z‖²` directement, via la
décomposition `x = (x-z)+z` avec `x-z ∈ ℂ∙ψ ⟂ z`.

**EN.** The pure projector onto `x` has a STRICTLY positive quadratic form
at `z := (ℂ∙ψ)ᗮ.starProjection x`, as soon as `x ∉ ℂ∙ψ` (hence `z≠0`). No
strict Cauchy–Schwarz: `⟪x,z⟩ = ⟪z,z⟩ = ‖z‖²` directly, via the
decomposition `x = (x-z)+z` with `x-z ∈ ℂ∙ψ ⟂ z`. -/
private theorem pureProjection_quadratic_pos {ψ x : H n} (hxu : ‖x‖ = 1)
    (hx : x ∉ (ℂ ∙ ψ : Submodule ℂ (H n))) :
    0 < (⟪projL (ℂ ∙ x) ((ℂ ∙ ψ)ᗮ.starProjection x), (ℂ ∙ ψ)ᗮ.starProjection x⟫_ℂ).re := by
  set z := (ℂ ∙ ψ)ᗮ.starProjection x with hz_def
  have hznz : z ≠ 0 := z_ne_zero_of_not_mem hx
  have hznorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hznz
  have hxz : ⟪x, z⟫_ℂ = (‖z‖ : ℂ) ^ 2 := inner_x_z_eq_norm_sq ψ x
  have hproj : projL (ℂ ∙ x) z = ⟪x, z⟫_ℂ • x := projL_singleton_unit x z hxu
  rw [hproj, inner_smul_left, hxz]
  have hconj : (starRingEnd ℂ) ((‖z‖ : ℂ) ^ 2) = (‖z‖ : ℂ) ^ 2 := by
    rw [map_pow, Complex.conj_ofReal]
  rw [hconj]
  have hcombine : (‖z‖ : ℂ) ^ 2 * (‖z‖ : ℂ) ^ 2 = ((‖z‖ ^ 4 : ℝ) : ℂ) := by push_cast; ring
  rw [hcombine, Complex.ofReal_re]
  positivity

/-! ## §3 Convex mixed density: value and non-identity with `P_ψ` -/

/-- **FR.** Combinaison convexe de deux sélecteurs purs : encore un
opérateur densité. Même structure que `tDensity_isDensity` (`Defs.lean`) —
symétrie/positivité/trace, sans redévelopper les projecteurs.

**EN.** Convex combination of two pure selectors: still a density
operator. Same structure as `tDensity_isDensity` (`Defs.lean`) —
symmetry/positivity/trace, without re-expanding the projectors. -/
private theorem densityOperator_convexCombination {x y : H n} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsDensityOperator ((t : ℂ) • projL (ℂ ∙ x) + ((1 - t : ℝ) : ℂ) • projL (ℂ ∙ y)) := by
  have hs0 : 0 ≤ 1 - t := by linarith
  have hconjt : (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
  have hconjs : (starRingEnd ℂ) ((1 - t : ℝ) : ℂ) = ((1 - t : ℝ) : ℂ) := Complex.conj_ofReal _
  refine ⟨?_, ?_, ?_⟩
  · exact (LinearMap.IsSymmetric.smul hconjt (Submodule.starProjection_isSymmetric (ℂ ∙ x))).add
      (LinearMap.IsSymmetric.smul hconjs (Submodule.starProjection_isSymmetric (ℂ ∙ y)))
  · intro w
    show 0 ≤ (⟪((t : ℂ) • projL (ℂ ∙ x) + ((1 - t : ℝ) : ℂ) • projL (ℂ ∙ y)) w, w⟫_ℂ).re
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, inner_add_left,
      inner_smul_left, inner_smul_left, hconjt, hconjs]
    have h1 : 0 ≤ (⟪projL (ℂ ∙ x) w, w⟫_ℂ).re := Submodule.re_inner_starProjection_nonneg (ℂ ∙ x) w
    have h2 : 0 ≤ (⟪projL (ℂ ∙ y) w, w⟫_ℂ).re := Submodule.re_inner_starProjection_nonneg (ℂ ∙ y) w
    rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have h3 := mul_nonneg ht0 h1
    have h4 := mul_nonneg hs0 h2
    linarith
  · show LinearMap.trace ℂ (H n)
      ((t : ℂ) • projL (ℂ ∙ x) + ((1 - t : ℝ) : ℂ) • projL (ℂ ∙ y)) = 1
    rw [map_add, map_smul, map_smul, trace_projL_singleton hx, trace_projL_singleton hy,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    push_cast; ring

/-- **FR.** `Re tr(P_x E₀) = Re⟪E₀ x, x⟩` pour `x` unitaire : cyclicité de la
trace (`trace_mul_comm`) + `Gleason.bornValue_span_singleton`.

**EN.** `Re tr(P_x E₀) = Re⟪E₀ x, x⟩` for unit `x`: trace cyclicity
(`trace_mul_comm`) + `Gleason.bornValue_span_singleton`. -/
private theorem trace_projL_comp_eq_born (E₀ : H n →ₗ[ℂ] H n) {x : H n} (hx : ‖x‖ = 1) :
    (LinearMap.trace ℂ (H n) (projL (ℂ ∙ x) ∘ₗ E₀)).re = (⟪E₀ x, x⟫_ℂ).re := by
  rw [← Module.End.mul_eq_comp, LinearMap.trace_mul_comm, Module.End.mul_eq_comp]
  exact Gleason.bornValue_span_singleton E₀ x hx

private theorem convexDensity_value (E₀ : H n →ₗ[ℂ] H n) {x y : H n} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {t : ℝ} :
    (LinearMap.trace ℂ (H n)
      (((t : ℂ) • projL (ℂ ∙ x) + ((1 - t : ℝ) : ℂ) • projL (ℂ ∙ y)) ∘ₗ E₀)).re
      = t * (⟪E₀ x, x⟫_ℂ).re + (1 - t) * (⟪E₀ y, y⟫_ℂ).re := by
  rw [LinearMap.add_comp, LinearMap.smul_comp, LinearMap.smul_comp, map_add, map_smul, map_smul,
    smul_eq_mul, smul_eq_mul, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    trace_projL_comp_eq_born E₀ hx, trace_projL_comp_eq_born E₀ hy]

/-- **FR.** La densité mixte construite avec `t ∈ (0,1)`, `x ∉ ℂ∙ψ`, n'est
JAMAIS `P_ψ` : au témoin `z`, sa forme quadratique est strictement positive
(terme en `x`, poids `t>0`, plus terme en `y`, poids `1-t≥0`), alors que
celle de `P_ψ` y est nulle (`z ⊥ ψ`).

**EN.** The mixed density built with `t ∈ (0,1)`, `x ∉ ℂ∙ψ`, is NEVER
`P_ψ`: at the witness `z`, its quadratic form is strictly positive (the
`x` term, weight `t>0`, plus the `y` term, weight `1-t≥0`), while that of
`P_ψ` vanishes there (`z ⊥ ψ`). -/
private theorem convexDensity_ne_pureState {ψ x y : H n} (hψ : ‖ψ‖ = 1) (hx : ‖x‖ = 1)
    (hxψ : x ∉ (ℂ ∙ ψ : Submodule ℂ (H n))) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (t : ℂ) • projL (ℂ ∙ x) + ((1 - t : ℝ) : ℂ) • projL (ℂ ∙ y) ≠ projL (ℂ ∙ ψ) := by
  intro heq
  set z := (ℂ ∙ ψ)ᗮ.starProjection x with hz_def
  have hleft : 0 <
      (⟪((t : ℂ) • projL (ℂ ∙ x) + ((1 - t : ℝ) : ℂ) • projL (ℂ ∙ y)) z, z⟫_ℂ).re := by
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, inner_add_left,
      inner_smul_left, inner_smul_left]
    have hconjt : (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
    have hconjs : (starRingEnd ℂ) ((1 - t : ℝ) : ℂ) = ((1 - t : ℝ) : ℂ) := Complex.conj_ofReal _
    rw [hconjt, hconjs, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have hxpos := pureProjection_quadratic_pos (ψ := ψ) hx hxψ
    have hypos : 0 ≤ (⟪projL (ℂ ∙ y) z, z⟫_ℂ).re := Submodule.re_inner_starProjection_nonneg (ℂ ∙ y) z
    have h1 := mul_pos ht0 hxpos
    have h2 := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t) hypos
    linarith
  have hright : (⟪projL (ℂ ∙ ψ) z, z⟫_ℂ).re = 0 := by
    have hz0 : projL (ℂ ∙ ψ) z = 0 := by
      rw [projL_singleton_unit ψ z hψ, z_inner_psi_eq_zero ψ x, zero_smul]
    rw [hz0, inner_zero_left]; simp
  rw [heq, hright] at hleft
  exact absurd hleft (lt_irrefl 0)

/-! ## §4 No straddling, then the min/max dichotomy -/

/-- **FR.** Si `x ∈ ℂ∙ψ` et `‖x‖=‖ψ‖=1`, la forme quadratique de `E₀` prend
la même valeur en `x` et en `ψ` (`x` est `ψ` à une phase unimodulaire près).

**EN.** If `x ∈ ℂ∙ψ` and `‖x‖=‖ψ‖=1`, the quadratic form of `E₀` takes the
same value at `x` and at `ψ` (`x` is `ψ` up to a unimodular phase). -/
private theorem quadratic_eq_of_mem_span (E₀ : H n →ₗ[ℂ] H n) {ψ x : H n} (hψ : ‖ψ‖ = 1)
    (hx : ‖x‖ = 1) (hmem : x ∈ (ℂ ∙ ψ : Submodule ℂ (H n))) :
    (⟪E₀ x, x⟫_ℂ).re = (⟪E₀ ψ, ψ⟫_ℂ).re := by
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hmem
  have hdnorm : ‖d‖ = 1 := by
    have h := congrArg norm hd
    rw [norm_smul, hψ, mul_one] at h
    rw [h]; exact hx
  have hdd : (starRingEnd ℂ) d * d = 1 := by rw [Complex.conj_mul', hdnorm]; norm_num
  rw [← hd, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, hdd, one_mul]

/-- **FR.** Une sélection unique interdit toute paire `x,y` unitaires avec
`Re⟪E₀x,x⟩ < c < Re⟪E₀y,y⟩`. Construit la densité mixte au coefficient
`t = (q y - c)/(q y - q x) ∈ (0,1)`, montre qu'elle satisfait la contrainte,
et la distingue de `P_ψ` via le témoin orthogonal — sauf si `x ∈ ℂ∙ψ`,
auquel cas `q x = q ψ = c` contredit directement `q x < c`.

**EN.** Unique selection forbids any pair of unit `x,y` with
`Re⟪E₀x,x⟩ < c < Re⟪E₀y,y⟩`. Builds the mixed density at coefficient
`t = (q y - c)/(q y - q x) ∈ (0,1)`, shows it satisfies the constraint, and
distinguishes it from `P_ψ` via the orthogonal witness — unless `x ∈ ℂ∙ψ`,
in which case `q x = q ψ = c` directly contradicts `q x < c`. -/
private theorem no_straddling_of_single_effect_selects
    {E₀ : H n →ₗ[ℂ] H n} {ψ : H n} {c : ℝ} (hψ : ‖ψ‖ = 1)
    (hselect : SingleEffectExactlySelectsPureState E₀ ψ c) :
    ¬ ∃ x : H n, ‖x‖ = 1 ∧ ∃ y : H n, ‖y‖ = 1 ∧
      (⟪E₀ x, x⟫_ℂ).re < c ∧ c < (⟪E₀ y, y⟫_ℂ).re := by
  rintro ⟨x, hx, y, hy, hqx, hqy⟩
  have hqpsi : (⟪E₀ ψ, ψ⟫_ℂ).re = c := by
    have := hselect.1
    rwa [trace_projL_comp_eq_born E₀ hψ] at this
  have hxψ : x ∉ (ℂ ∙ ψ : Submodule ℂ (H n)) := by
    intro hmem
    have := quadratic_eq_of_mem_span E₀ hψ hx hmem
    rw [hqpsi] at this
    linarith
  set a := (⟪E₀ x, x⟫_ℂ).re with ha_def
  set b := (⟪E₀ y, y⟫_ℂ).re with hb_def
  have hab : a < b := lt_trans hqx hqy
  have hba' : 0 < b - a := by rw [ha_def, hb_def] at hab ⊢; linarith
  set t : ℝ := (b - c) / (b - a) with ht_def
  have ht0 : 0 < t := by rw [ht_def]; exact div_pos (by linarith) hba'
  have ht1 : t < 1 := by rw [ht_def, div_lt_one hba']; linarith
  have hne : b - a ≠ 0 := ne_of_gt hba'
  have hval : t * a + (1 - t) * b = c := by
    rw [ht_def]; field_simp; ring
  have hρ := densityOperator_convexCombination hx hy ht0.le ht1.le
  have hρval : (LinearMap.trace ℂ (H n)
      (((t : ℂ) • projL (ℂ ∙ x) + ((1 - t : ℝ) : ℂ) • projL (ℂ ∙ y)) ∘ₗ E₀)).re = c := by
    rw [convexDensity_value E₀ hx hy]; exact hval
  have heq := (hselect.2 _ hρ).mp hρval
  exact convexDensity_ne_pureState hψ hx hxψ ht0 ht1 heq

/-- **FR.** Dichotomie logique pure : l'absence de `q x < c < q y` sur la
sphère unité force `c ≤ q` partout ou `q ≤ c` partout, sur la sphère unité.
Aucun contenu opératoriel.

**EN.** Pure logical dichotomy: the absence of `q x < c < q y` on the unit
sphere forces `c ≤ q` everywhere or `q ≤ c` everywhere, on the unit
sphere. No operator content. -/
private theorem forall_ge_or_forall_le_of_no_straddling (q : H n → ℝ) (c : ℝ)
    (hns : ¬ ∃ x : H n, ‖x‖ = 1 ∧ ∃ y : H n, ‖y‖ = 1 ∧ q x < c ∧ c < q y) :
    (∀ x : H n, ‖x‖ = 1 → c ≤ q x) ∨ (∀ x : H n, ‖x‖ = 1 → q x ≤ c) := by
  by_cases h : ∀ x : H n, ‖x‖ = 1 → c ≤ q x
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨x, hx, hqx⟩ := h
    intro y hy
    by_contra hqy
    push Not at hqy
    exact hns ⟨x, hx, y, hy, hqx, hqy⟩

/-! ## §5 Extending the unit-sphere bound to arbitrary vectors -/

private theorem quadratic_lower_bound_of_unit_lower_bound (E₀ : H n →ₗ[ℂ] H n) {c : ℝ}
    (hbound : ∀ x : H n, ‖x‖ = 1 → c * ‖x‖ ^ 2 ≤ (⟪E₀ x, x⟫_ℂ).re) (u : H n) :
    c * ‖u‖ ^ 2 ≤ (⟪E₀ u, u⟫_ℂ).re := by
  rcases eq_or_ne u 0 with hu0 | hu0
  · simp [hu0]
  · set v : H n := (‖u‖⁻¹ : ℂ) • u with hv_def
    have hvnorm : ‖v‖ = 1 := by
      rw [hv_def, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg u), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu0)]
    have huv : u = (‖u‖ : ℂ) • v := by
      rw [hv_def, smul_smul]
      have : (‖u‖ : ℂ) * (‖u‖⁻¹ : ℂ) = 1 := by
        have hune : (‖u‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hu0
        field_simp
      rw [this, one_smul]
    have hq : (⟪E₀ u, u⟫_ℂ).re = ‖u‖ ^ 2 * (⟪E₀ v, v⟫_ℂ).re := by
      conv_lhs => rw [huv]
      rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc]
      have hconj : (starRingEnd ℂ) (‖u‖ : ℂ) * (‖u‖ : ℂ) = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.conj_ofReal]; push_cast; ring
      rw [hconj, Complex.re_ofReal_mul]
    rw [hq]
    have := hbound v hvnorm
    rw [hvnorm] at this
    nlinarith [sq_nonneg (‖u‖ : ℝ), this]

private theorem quadratic_upper_bound_of_unit_upper_bound (E₀ : H n →ₗ[ℂ] H n) {c : ℝ}
    (hbound : ∀ x : H n, ‖x‖ = 1 → (⟪E₀ x, x⟫_ℂ).re ≤ c * ‖x‖ ^ 2) (u : H n) :
    (⟪E₀ u, u⟫_ℂ).re ≤ c * ‖u‖ ^ 2 := by
  rcases eq_or_ne u 0 with hu0 | hu0
  · simp [hu0]
  · set v : H n := (‖u‖⁻¹ : ℂ) • u with hv_def
    have hvnorm : ‖v‖ = 1 := by
      rw [hv_def, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg u), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu0)]
    have huv : u = (‖u‖ : ℂ) • v := by
      rw [hv_def, smul_smul]
      have : (‖u‖ : ℂ) * (‖u‖⁻¹ : ℂ) = 1 := by
        have hune : (‖u‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hu0
        field_simp
      rw [this, one_smul]
    have hq : (⟪E₀ u, u⟫_ℂ).re = ‖u‖ ^ 2 * (⟪E₀ v, v⟫_ℂ).re := by
      conv_lhs => rw [huv]
      rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc]
      have hconj : (starRingEnd ℂ) (‖u‖ : ℂ) * (‖u‖ : ℂ) = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.conj_ofReal]; push_cast; ring
      rw [hconj, Complex.re_ofReal_mul]
    rw [hq]
    have := hbound v hvnorm
    rw [hvnorm] at this
    nlinarith [sq_nonneg (‖u‖ : ℝ), this]

/-! ## §6 Eigenequation and simplicity of the eigenspace -/

private theorem isSymmetric_id : LinearMap.IsSymmetric (LinearMap.id : H n →ₗ[ℂ] H n) :=
  fun _ _ => rfl

private theorem inner_self_re_eq_norm_sq (x : H n) : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
  rw [inner_self_eq_norm_sq_to_K]; norm_cast

private theorem quadratic_real_of_symmetric {T : H n →ₗ[ℂ] H n} (hT : LinearMap.IsSymmetric T)
    (x : H n) : ⟪T x, x⟫_ℂ = ((⟪T x, x⟫_ℂ).re : ℂ) := by
  have hconjeq : (starRingEnd ℂ) ⟪T x, x⟫_ℂ = ⟪T x, x⟫_ℂ := by
    rw [inner_conj_symm, hT x x]
  exact (Complex.conj_eq_iff_re.mp hconjeq).symm

/-- **FR.** `E₀ ψ = c • ψ`, cas minimum : `A := E₀ - cI` est positif (borne
globale) et sa forme quadratique s'annule en `ψ` (valeur `c` atteinte) ;
`apply_eq_zero_of_quadratic_eq_zero` (S4, réutilisé tel quel) donne `Aψ=0`.

**EN.** `E₀ ψ = c • ψ`, minimum case: `A := E₀ - cI` is positive (global
bound) and its quadratic form vanishes at `ψ` (value `c` attained);
`apply_eq_zero_of_quadratic_eq_zero` (S4, reused as-is) gives `Aψ=0`. -/
private theorem eigen_equation_of_min {E₀ : H n →ₗ[ℂ] H n} {ψ : H n} {c : ℝ} (hψ : ‖ψ‖ = 1)
    (hE₀sym : LinearMap.IsSymmetric E₀)
    (hbound : ∀ x : H n, c * ‖x‖ ^ 2 ≤ (⟪E₀ x, x⟫_ℂ).re) (hqψ : (⟪E₀ ψ, ψ⟫_ℂ).re = c) :
    E₀ ψ = (c : ℂ) • ψ := by
  set A : H n →ₗ[ℂ] H n := E₀ - (c : ℂ) • LinearMap.id with hA_def
  have hAsym : LinearMap.IsSymmetric A :=
    hE₀sym.sub (LinearMap.IsSymmetric.smul (Complex.conj_ofReal c) isSymmetric_id)
  have hAnonneg : ∀ x : H n, 0 ≤ (⟪A x, x⟫_ℂ).re := by
    intro x
    show 0 ≤ (⟪E₀ x - (c : ℂ) • x, x⟫_ℂ).re
    rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal, Complex.sub_re,
      Complex.re_ofReal_mul, inner_self_re_eq_norm_sq]
    linarith [hbound x]
  have hψψ : ⟪ψ, ψ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  have hAψ : ⟪A ψ, ψ⟫_ℂ = 0 := by
    show ⟪E₀ ψ - (c : ℂ) • ψ, ψ⟫_ℂ = 0
    rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal,
      quadratic_real_of_symmetric hE₀sym ψ, hqψ, hψψ]
    ring
  have hAψ0 : A ψ = 0 := apply_eq_zero_of_quadratic_eq_zero ⟨hAsym, hAnonneg⟩ hAψ
  have hAψ0' : E₀ ψ - (c : ℂ) • ψ = 0 := hAψ0
  linear_combination (norm := module) hAψ0'

/-- **FR.** Symétrique au précédent, cas maximum : `A := cI - E₀`.

**EN.** Symmetric to the previous one, maximum case: `A := cI - E₀`. -/
private theorem eigen_equation_of_max {E₀ : H n →ₗ[ℂ] H n} {ψ : H n} {c : ℝ} (hψ : ‖ψ‖ = 1)
    (hE₀sym : LinearMap.IsSymmetric E₀)
    (hbound : ∀ x : H n, (⟪E₀ x, x⟫_ℂ).re ≤ c * ‖x‖ ^ 2) (hqψ : (⟪E₀ ψ, ψ⟫_ℂ).re = c) :
    E₀ ψ = (c : ℂ) • ψ := by
  set A : H n →ₗ[ℂ] H n := (c : ℂ) • LinearMap.id - E₀ with hA_def
  have hAsym : LinearMap.IsSymmetric A :=
    (LinearMap.IsSymmetric.smul (Complex.conj_ofReal c) isSymmetric_id).sub hE₀sym
  have hAnonneg : ∀ x : H n, 0 ≤ (⟪A x, x⟫_ℂ).re := by
    intro x
    show 0 ≤ (⟪(c : ℂ) • x - E₀ x, x⟫_ℂ).re
    rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal, Complex.sub_re,
      Complex.re_ofReal_mul, inner_self_re_eq_norm_sq]
    linarith [hbound x]
  have hψψ : ⟪ψ, ψ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  have hAψ : ⟪A ψ, ψ⟫_ℂ = 0 := by
    show ⟪(c : ℂ) • ψ - E₀ ψ, ψ⟫_ℂ = 0
    rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal,
      quadratic_real_of_symmetric hE₀sym ψ, hqψ, hψψ]
    ring
  have hAψ0 : A ψ = 0 := apply_eq_zero_of_quadratic_eq_zero ⟨hAsym, hAnonneg⟩ hAψ
  have hAψ0' : (c : ℂ) • ψ - E₀ ψ = 0 := hAψ0
  linear_combination (norm := module) -hAψ0'

/-- **FR.** Simplicité de l'espace propre : tout `x ∈ ker(E₀-cI)` est
colinéaire à `ψ`. Normalise `x`, vérifie que `x'` satisfait lui aussi la
contrainte à `c` (via `Gleason.bornValue_span_singleton`/
`trace_projL_comp_eq_born`), l'unicité de la sélection force
`projL(ℂ∙x')=projL(ℂ∙ψ)`, puis l'évaluation en `x'` donne `x'∈ℂ∙ψ`.

**EN.** Simplicity of the eigenspace: every `x ∈ ker(E₀-cI)` is collinear
with `ψ`. Normalize `x`, check that `x'` also satisfies the constraint at
`c` (via `Gleason.bornValue_span_singleton`/`trace_projL_comp_eq_born`),
uniqueness of the selection forces `projL(ℂ∙x')=projL(ℂ∙ψ)`, then
evaluating at `x'` gives `x'∈ℂ∙ψ`. -/
private theorem ker_eq_span_of_eigen {E₀ : H n →ₗ[ℂ] H n} {ψ : H n} {c : ℝ} (hψ : ‖ψ‖ = 1)
    (hEψ : E₀ ψ = (c : ℂ) • ψ)
    (hselect : SingleEffectExactlySelectsPureState E₀ ψ c) :
    LinearMap.ker (E₀ - (c : ℂ) • LinearMap.id) = ℂ ∙ ψ := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    have hEx : E₀ x = (c : ℂ) • x := by
      have hx' : E₀ x - (c : ℂ) • x = 0 := hx
      linear_combination (norm := module) hx'
    rcases eq_or_ne x 0 with hx0 | hx0
    · rw [hx0]; exact Submodule.zero_mem _
    · set x' : H n := (‖x‖⁻¹ : ℂ) • x with hx'_def
      have hx'norm : ‖x'‖ = 1 := by
        rw [hx'_def, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (norm_nonneg x), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx0)]
      have hEx' : E₀ x' = (c : ℂ) • x' := by
        rw [hx'_def, map_smul, hEx, smul_comm]
      have hconstraint : (LinearMap.trace ℂ (H n) (projL (ℂ ∙ x') ∘ₗ E₀)).re = c := by
        rw [trace_projL_comp_eq_born E₀ hx'norm, hEx', inner_smul_left, Complex.conj_ofReal]
        have hx'x' : ⟪x', x'⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hx'norm]; norm_num
        rw [hx'x', mul_one, Complex.ofReal_re]
      have hdensity : IsDensityOperator (projL (ℂ ∙ x') : H n →ₗ[ℂ] H n) :=
        (bornSelector n).isDensity x' hx'norm
      have heq : projL (ℂ ∙ x') = projL (ℂ ∙ ψ) := (hselect.2 _ hdensity).mp hconstraint
      have hx'eq : projL (ℂ ∙ x') x' = projL (ℂ ∙ ψ) x' := congrArg (· x') heq
      have hx'x' : ⟪x', x'⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hx'norm]; norm_num
      rw [projL_singleton_unit x' x' hx'norm, hx'x', one_smul,
        projL_singleton_unit ψ x' hψ] at hx'eq
      have hx'mem : x' ∈ (ℂ ∙ ψ : Submodule ℂ (H n)) :=
        Submodule.mem_span_singleton.mpr ⟨⟪ψ, x'⟫_ℂ, hx'eq.symm⟩
      have hxeq : x = (‖x‖ : ℂ) • x' := by
        rw [hx'_def, smul_smul]
        have hune : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx0
        rw [show (‖x‖ : ℂ) * (‖x‖⁻¹ : ℂ) = 1 by field_simp, one_smul]
      rw [hxeq]
      exact Submodule.smul_mem _ _ hx'mem
  · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
    have : E₀ ψ - (c : ℂ) • ψ = 0 := by rw [hEψ]; module
    exact this

/-! ## §7 Final assembly -/

private theorem born_value_at_eigen {E₀ : H n →ₗ[ℂ] H n} {ψ : H n} {c : ℝ} (hψ : ‖ψ‖ = 1)
    (hEψ : E₀ ψ = (c : ℂ) • ψ) :
    (LinearMap.trace ℂ (H n) (projL (ℂ ∙ ψ) ∘ₗ E₀)).re = c := by
  rw [trace_projL_comp_eq_born E₀ hψ, hEψ, inner_smul_left, Complex.conj_ofReal]
  have hψψ : ⟪ψ, ψ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hψ]; norm_num
  rw [hψψ, mul_one, Complex.ofReal_re]

private theorem selects_of_extremal_min {E₀ : H n →ₗ[ℂ] H n} {ψ : H n} {c : ℝ}
    (hE₀sym : LinearMap.IsSymmetric E₀) (hψ : ‖ψ‖ = 1)
    (hEψ : E₀ ψ = (c : ℂ) • ψ) (hbound : ∀ x : H n, c * ‖x‖ ^ 2 ≤ (⟪E₀ x, x⟫_ℂ).re)
    (hker : LinearMap.ker (E₀ - (c : ℂ) • LinearMap.id) = ℂ ∙ ψ) :
    SingleEffectExactlySelectsPureState E₀ ψ c := by
  refine ⟨born_value_at_eigen hψ hEψ, ?_⟩
  intro ρ hρ
  refine ⟨fun hval => ?_, fun heq => heq ▸ born_value_at_eigen hψ hEψ⟩
  set A : H n →ₗ[ℂ] H n := E₀ - (c : ℂ) • LinearMap.id with hA_def
  have hApos : IsPositiveOp A :=
    ⟨(hE₀sym.sub (LinearMap.IsSymmetric.smul (Complex.conj_ofReal c) isSymmetric_id)), by
        intro x
        show 0 ≤ (⟪E₀ x - (c : ℂ) • x, x⟫_ℂ).re
        rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal, Complex.sub_re,
          Complex.re_ofReal_mul, inner_self_re_eq_norm_sq]
        linarith [hbound x]⟩
  have htrace0 : (LinearMap.trace ℂ (H n) (ρ ∘ₗ A)).re = 0 := by
    have h1 : ρ ∘ₗ A = ρ ∘ₗ E₀ - (c : ℂ) • ρ := by
      rw [hA_def, LinearMap.comp_sub]
      congr 1
      ext w
      simp [LinearMap.comp_apply, LinearMap.smul_apply]
    rw [h1, map_sub, map_smul, smul_eq_mul, hρ.trace_one, mul_one, Complex.sub_re, hval,
      Complex.ofReal_re]
    ring
  have hsupp := density_supported_on_kernel_of_extremal_trace hApos hρ htrace0
  rw [hker] at hsupp
  exact QuantumFoundations.BornRule.eq_projL_of_vanishes_on_orthogonal hρ hψ
    (fun w hw => hsupp w (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hw))

private theorem selects_of_extremal_max {E₀ : H n →ₗ[ℂ] H n} {ψ : H n} {c : ℝ}
    (hE₀sym : LinearMap.IsSymmetric E₀) (hψ : ‖ψ‖ = 1)
    (hEψ : E₀ ψ = (c : ℂ) • ψ) (hbound : ∀ x : H n, (⟪E₀ x, x⟫_ℂ).re ≤ c * ‖x‖ ^ 2)
    (hker : LinearMap.ker (E₀ - (c : ℂ) • LinearMap.id) = ℂ ∙ ψ) :
    SingleEffectExactlySelectsPureState E₀ ψ c := by
  refine ⟨born_value_at_eigen hψ hEψ, ?_⟩
  intro ρ hρ
  refine ⟨fun hval => ?_, fun heq => heq ▸ born_value_at_eigen hψ hEψ⟩
  set A : H n →ₗ[ℂ] H n := (c : ℂ) • LinearMap.id - E₀ with hA_def
  have hApos : IsPositiveOp A :=
    ⟨(LinearMap.IsSymmetric.smul (Complex.conj_ofReal c) isSymmetric_id).sub hE₀sym,
      by
        intro x
        show 0 ≤ (⟪(c : ℂ) • x - E₀ x, x⟫_ℂ).re
        rw [inner_sub_left, inner_smul_left, Complex.conj_ofReal, Complex.sub_re,
          Complex.re_ofReal_mul, inner_self_re_eq_norm_sq]
        linarith [hbound x]⟩
  have htrace0 : (LinearMap.trace ℂ (H n) (ρ ∘ₗ A)).re = 0 := by
    have h1 : ρ ∘ₗ A = (c : ℂ) • ρ - ρ ∘ₗ E₀ := by
      rw [hA_def, LinearMap.comp_sub]
      congr 1
      ext w
      simp [LinearMap.comp_apply, LinearMap.smul_apply]
    rw [h1, map_sub, map_smul, smul_eq_mul, hρ.trace_one, mul_one, Complex.sub_re, hval,
      Complex.ofReal_re]
    ring
  have hAneg : A = -(E₀ - (c : ℂ) • LinearMap.id) := by rw [hA_def]; module
  have hker' : LinearMap.ker A = ℂ ∙ ψ := by rw [hAneg, LinearMap.ker_neg]; exact hker
  have hsupp := density_supported_on_kernel_of_extremal_trace hApos hρ htrace0
  rw [hker'] at hsupp
  exact QuantumFoundations.BornRule.eq_projL_of_vanishes_on_orthogonal hρ hψ
    (fun w hw => hsupp w (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hw))

/--
**FR.** **Proposition 2 (théorème principal)** : la contrainte à effet unique
`Re tr(ρE₀) = c` sélectionne exactement l'état pur `ψ` si et seulement si
`(ψ, c)` est une paire propre extrémale simple de `E₀`.

**EN.** **Proposition 2 (main theorem)**: the single-effect constraint
`Re tr(ρE₀) = c` exactly selects the pure state `ψ` if and only if
`(ψ, c)` is a simple extremal eigenpair of `E₀`.
-/
theorem single_effect_selector_iff {E₀ : H n →ₗ[ℂ] H n} {ψ : H n} {c : ℝ} (hE₀ : IsEffect E₀)
    (hψ : ‖ψ‖ = 1) :
    SingleEffectExactlySelectsPureState E₀ ψ c ↔ IsSimpleExtremalEigenpair E₀ ψ c := by
  have hE₀sym : LinearMap.IsSymmetric E₀ := hE₀.1.1
  constructor
  · intro hselect
    have hqψ : (⟪E₀ ψ, ψ⟫_ℂ).re = c := by
      have h1 := hselect.1; rwa [trace_projL_comp_eq_born E₀ hψ] at h1
    have hns := no_straddling_of_single_effect_selects hψ hselect
    rcases forall_ge_or_forall_le_of_no_straddling (fun x => (⟪E₀ x, x⟫_ℂ).re) c hns with
      hmin | hmax
    · left
      have hmin' : ∀ x : H n, ‖x‖ = 1 → c * ‖x‖ ^ 2 ≤ (⟪E₀ x, x⟫_ℂ).re := by
        intro x hx; rw [hx]; simpa using hmin x hx
      have hbound := quadratic_lower_bound_of_unit_lower_bound E₀ hmin'
      have hEψ := eigen_equation_of_min hψ hE₀sym hbound hqψ
      exact ⟨hψ, hEψ, hbound, ker_eq_span_of_eigen hψ hEψ hselect⟩
    · right
      have hmax' : ∀ x : H n, ‖x‖ = 1 → (⟪E₀ x, x⟫_ℂ).re ≤ c * ‖x‖ ^ 2 := by
        intro x hx; rw [hx]; simpa using hmax x hx
      have hbound := quadratic_upper_bound_of_unit_upper_bound E₀ hmax'
      have hEψ := eigen_equation_of_max hψ hE₀sym hbound hqψ
      exact ⟨hψ, hEψ, hbound, ker_eq_span_of_eigen hψ hEψ hselect⟩
  · rintro (⟨_, hEψ, hbound, hker⟩ | ⟨_, hEψ, hbound, hker⟩)
    · exact selects_of_extremal_min hE₀sym hψ hEψ hbound hker
    · exact selects_of_extremal_max hE₀sym hψ hEψ hbound hker

/-! ## §8 Corollaries: `P_{ψ⊥}`/`c=0`, `P_ψ`/`c=1`, non-selecting witnesses -/

private theorem ker_projL_compl_eq_span (ψ : H n) (hψ : ‖ψ‖ = 1) :
    LinearMap.ker (projL (ℂ ∙ ψ)ᗮ) = ℂ ∙ ψ := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    have h2 : projL (ℂ ∙ ψ) x + projL (ℂ ∙ ψ)ᗮ x = x :=
      congrArg (· x) (projL_add_projL_compl (ℂ ∙ ψ))
    rw [hx, add_zero] at h2
    rw [← h2, projL_singleton_unit ψ x hψ]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self ψ)
  · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
    have h1 : projL (ℂ ∙ ψ) ψ = ψ := by
      rw [projL_singleton_unit ψ ψ hψ, inner_self_eq_norm_sq_to_K, hψ]; norm_num
    have h2 : projL (ℂ ∙ ψ) ψ + projL (ℂ ∙ ψ)ᗮ ψ = ψ :=
      congrArg (· ψ) (projL_add_projL_compl (ℂ ∙ ψ))
    rw [h1] at h2
    exact add_left_cancel (h2.trans (add_zero ψ).symm)

private theorem inner_projL_self_eq_norm_sq (ψ x : H n) :
    ⟪projL (ℂ ∙ ψ) x, x⟫_ℂ = (‖projL (ℂ ∙ ψ) x‖ : ℂ) ^ 2 := by
  set p := projL (ℂ ∙ ψ) x with hp_def
  have hsplit : x = (x - p) + p := by abel
  have hpmem : p ∈ (ℂ ∙ ψ : Submodule ℂ (H n)) := by
    rw [hp_def]; exact Submodule.starProjection_apply_mem _ x
  have hxpeq : x - p = projL (ℂ ∙ ψ)ᗮ x := by
    have h2 : projL (ℂ ∙ ψ) x + projL (ℂ ∙ ψ)ᗮ x = x :=
      congrArg (· x) (projL_add_projL_compl (ℂ ∙ ψ))
    rw [hp_def]
    linear_combination (norm := module) -h2
  have hxpmem : x - p ∈ (ℂ ∙ ψ)ᗮ := by
    rw [hxpeq]; exact Submodule.starProjection_apply_mem _ x
  have horth : ⟪p, x - p⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).mp hxpmem p hpmem
  calc ⟪p, x⟫_ℂ = ⟪p, (x - p) + p⟫_ℂ := by rw [← hsplit]
    _ = ⟪p, x - p⟫_ℂ + ⟪p, p⟫_ℂ := by rw [inner_add_right]
    _ = ⟪p, p⟫_ℂ := by rw [horth, zero_add]
    _ = (‖p‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K p

private theorem inner_projL_re_le_norm_sq (ψ x : H n) :
    (⟪projL (ℂ ∙ ψ) x, x⟫_ℂ).re ≤ ‖x‖ ^ 2 := by
  rw [inner_projL_self_eq_norm_sq]
  have hle : ‖projL (ℂ ∙ ψ) x‖ ≤ ‖x‖ := Submodule.norm_starProjection_apply_le _ x
  have h1 : ((‖projL (ℂ ∙ ψ) x‖ : ℂ) ^ 2).re = ‖projL (ℂ ∙ ψ) x‖ ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [h1]
  nlinarith [norm_nonneg (projL (ℂ ∙ ψ) x), norm_nonneg x]

/-- **FR.** Toute projection orthogonale est un effet.

**EN.** Every orthogonal projection is an effect. -/
private theorem isEffect_projL (A : Submodule ℂ (H n)) : IsEffect (projL A) := by
  refine ⟨⟨Submodule.starProjection_isSymmetric A, Submodule.re_inner_starProjection_nonneg A⟩, ?_⟩
  have h1 : (1 : H n →ₗ[ℂ] H n) - projL A = projL Aᗮ := by
    have h2 := projL_add_projL_compl A
    linear_combination (norm := module) -h2
  rw [h1]
  exact ⟨Submodule.starProjection_isSymmetric Aᗮ, Submodule.re_inner_starProjection_nonneg Aᗮ⟩

/--
**FR.** **Corollaire** : la contrainte `Re tr(ρ P_{ψ⊥}) = 0` sélectionne
exactement l'état pur `ψ` — le minimum simple nul. C'est le point de contact
avec S4 : `nsnc1_iff_born_from_proposition_two` ci-dessous montre que c'est
exactement `NSNC1`, reformulé via la classification générale de la
Proposition 2.

**EN.** **Corollary**: the constraint `Re tr(ρ P_{ψ⊥}) = 0` exactly selects
the pure state `ψ` — the simple null minimum. This is the point of contact
with S4: `nsnc1_iff_born_from_proposition_two` below shows this is exactly
`NSNC1`, reformulated via the general classification of Proposition 2.
-/
theorem orthogonal_complement_projection_single_effect_selector {ψ : H n} (hψ : ‖ψ‖ = 1) :
    SingleEffectExactlySelectsPureState (projL (ℂ ∙ ψ)ᗮ) ψ 0 := by
  apply (single_effect_selector_iff (isEffect_projL (ℂ ∙ ψ)ᗮ) hψ).mpr
  left
  have hEψ : projL (ℂ ∙ ψ)ᗮ ψ = ((0 : ℝ) : ℂ) • ψ := by
    have h1 : projL (ℂ ∙ ψ) ψ = ψ := by
      rw [projL_singleton_unit ψ ψ hψ, inner_self_eq_norm_sq_to_K, hψ]; norm_num
    have h2 : projL (ℂ ∙ ψ) ψ + projL (ℂ ∙ ψ)ᗮ ψ = ψ :=
      congrArg (· ψ) (projL_add_projL_compl (ℂ ∙ ψ))
    rw [h1] at h2
    have h3 : projL (ℂ ∙ ψ)ᗮ ψ = 0 := add_left_cancel (h2.trans (add_zero ψ).symm)
    rw [h3]; simp
  refine ⟨hψ, hEψ, ?_, ?_⟩
  · intro x
    show (0 : ℝ) * ‖x‖ ^ 2 ≤ (⟪projL (ℂ ∙ ψ)ᗮ x, x⟫_ℂ).re
    rw [zero_mul]
    exact Submodule.re_inner_starProjection_nonneg (ℂ ∙ ψ)ᗮ x
  · have h1 : projL (ℂ ∙ ψ)ᗮ - ((0 : ℝ) : ℂ) • LinearMap.id = projL (ℂ ∙ ψ)ᗮ := by simp
    rw [h1]
    exact ker_projL_compl_eq_span ψ hψ

/-- **FR.** Ce que dit `NSNC1` est exactement ce que sélectionne
`P_{ψ⊥}`/`c=0` dans la classification de Proposition 2 : les deux notions
de pinning coïncident, l'une comme prémisse-pont sur la famille des
sélecteurs (S4), l'autre comme instance de la classification par contrainte
à effet unique (S6).

**EN.** What `NSNC1` says is exactly what `P_{ψ⊥}`/`c=0` selects in the
Proposition 2 classification: the two notions of pinning coincide, one as
a bridge premise on the family of selectors (S4), the other as an instance
of the single-effect-constraint classification (S6). -/
theorem nsnc1_iff_born_from_proposition_two (σ : Selector n) {ψ : H n} (hψ : ‖ψ‖ = 1) :
    bornValue (σ.ρ ψ) ((ℂ ∙ ψ)ᗮ) = 0 ↔ σ.ρ ψ = projL (ℂ ∙ ψ) := by
  have hsel := orthogonal_complement_projection_single_effect_selector hψ
  have hden := σ.isDensity ψ hψ
  exact hsel.2 (σ.ρ ψ) hden

/--
**FR.** **Corollaire** : la contrainte `Re tr(ρ P_ψ) = 1` sélectionne
exactement l'état pur `ψ` — le maximum simple unité.

**EN.** **Corollary**: the constraint `Re tr(ρ P_ψ) = 1` exactly selects
the pure state `ψ` — the simple unit maximum.
-/
theorem pure_state_projection_single_effect_selector {ψ : H n} (hψ : ‖ψ‖ = 1) :
    SingleEffectExactlySelectsPureState (projL (ℂ ∙ ψ)) ψ 1 := by
  apply (single_effect_selector_iff (isEffect_projL (ℂ ∙ ψ)) hψ).mpr
  right
  have hEψ : projL (ℂ ∙ ψ) ψ = ((1 : ℝ) : ℂ) • ψ := by
    have h1 : projL (ℂ ∙ ψ) ψ = ψ := by
      rw [projL_singleton_unit ψ ψ hψ, inner_self_eq_norm_sq_to_K, hψ]; norm_num
    rw [h1]; simp
  refine ⟨hψ, hEψ, ?_, ?_⟩
  · intro x
    show (⟪projL (ℂ ∙ ψ) x, x⟫_ℂ).re ≤ (1 : ℝ) * ‖x‖ ^ 2
    rw [one_mul]
    exact inner_projL_re_le_norm_sq ψ x
  · have h1 : projL (ℂ ∙ ψ) - ((1 : ℝ) : ℂ) • LinearMap.id = -(projL (ℂ ∙ ψ)ᗮ) := by
      have h2 := projL_add_projL_compl (ℂ ∙ ψ)
      have h3 : ((1 : ℝ) : ℂ) • (LinearMap.id : H n →ₗ[ℂ] H n) = LinearMap.id := by simp
      rw [h3]
      linear_combination (norm := module) h2
    rw [h1, LinearMap.ker_neg]
    exact ker_projL_compl_eq_span ψ hψ

/--
**FR.** **Contre-modèle, valeur non extrémale** : si `c` est strictement
encadré par les valeurs de la forme quadratique de `E₀` en deux vecteurs
unitaires, aucun état pur n'est sélectionné par la contrainte — corollaire
direct de `no_straddling_of_single_effect_selects`.

**EN.** **Counter-model, non-extremal value**: if `c` is strictly straddled
by the values of `E₀`'s quadratic form at two unit vectors, no pure state
is selected by the constraint — direct corollary of
`no_straddling_of_single_effect_selects`.
-/
theorem no_single_effect_selector_of_straddled {E₀ : H n →ₗ[ℂ] H n} {c : ℝ}
    {x y : H n} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hqx : (⟪E₀ x, x⟫_ℂ).re < c)
    (hqy : c < (⟪E₀ y, y⟫_ℂ).re) :
    ¬ ∃ ψ : H n, ‖ψ‖ = 1 ∧ SingleEffectExactlySelectsPureState E₀ ψ c := by
  rintro ⟨ψ, hψ, hselect⟩
  exact no_straddling_of_single_effect_selects hψ hselect ⟨x, hx, y, hy, hqx, hqy⟩

/-- **FR.** Instance concrète, `n = 2` : pour `E₀ = P_{e₀}`, la valeur
intermédiaire `c = 1/2` (entre `q(e₁) = 0` et `q(e₀) = 1`) ne sélectionne
aucun état pur.

**EN.** Concrete instance, `n = 2`: for `E₀ = P_{e₀}`, the intermediate
value `c = 1/2` (between `q(e₁) = 0` and `q(e₀) = 1`) selects no pure
state. -/
theorem interior_value_does_not_select :
    ¬ ∃ ψ : H 2, ‖ψ‖ = 1 ∧
      SingleEffectExactlySelectsPureState
        (projL (ℂ ∙ (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)))) ψ (1 / 2) := by
  set e0 : H 2 := EuclideanSpace.single (0 : Fin 2) (1 : ℂ) with he0_def
  set e1 : H 2 := EuclideanSpace.single (1 : Fin 2) (1 : ℂ) with he1_def
  have he0 : ‖e0‖ = 1 := by rw [he0_def, PiLp.norm_single]; norm_num
  have he1 : ‖e1‖ = 1 := by rw [he1_def, PiLp.norm_single]; norm_num
  have hqe1 : (⟪projL (ℂ ∙ e0) e1, e1⟫_ℂ).re < (1 / 2 : ℝ) := by
    have h1 : projL (ℂ ∙ e0) e1 = ⟪e0, e1⟫_ℂ • e0 := projL_singleton_unit e0 e1 he0
    have h2 : ⟪e0, e1⟫_ℂ = 0 := by
      rw [he0_def, he1_def, EuclideanSpace.inner_single_left]; simp
    rw [h1, h2, zero_smul, inner_zero_left]
    norm_num
  have hqe0 : (1 / 2 : ℝ) < (⟪projL (ℂ ∙ e0) e0, e0⟫_ℂ).re := by
    have h1 : projL (ℂ ∙ e0) e0 = ⟪e0, e0⟫_ℂ • e0 := projL_singleton_unit e0 e0 he0
    have h2 : ⟪e0, e0⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, he0]; norm_num
    rw [h1, h2, one_smul, h2]
    norm_num
  exact no_single_effect_selector_of_straddled he1 he0 hqe1 hqe0

/--
**FR.** **Contre-modèle, extremum dégénéré** : l'identité (`E₀ = id`) admet
`c = 1` comme valeur extrémale triviale (minimum = maximum, atteinte
partout), mais son espace propre est l'espace ENTIER, non simple dès que
`n ≥ 2` — aucun état pur n'est donc sélectionné.

**EN.** **Counter-model, degenerate extremum**: the identity (`E₀ = id`)
has `c = 1` as a trivial extremal value (minimum = maximum, attained
everywhere), but its eigenspace is the WHOLE space, not simple as soon as
`n ≥ 2` — hence no pure state is selected. -/
theorem identity_degenerate_extremum_does_not_select (hn : 2 ≤ n) (ψ : H n) (hψ : ‖ψ‖ = 1) :
    ¬ SingleEffectExactlySelectsPureState (LinearMap.id : H n →ₗ[ℂ] H n) ψ 1 := by
  intro hselect
  have hE₀ : IsEffect (LinearMap.id : H n →ₗ[ℂ] H n) := by
    refine ⟨⟨isSymmetric_id, fun x => by
        show 0 ≤ (⟪x, x⟫_ℂ).re
        rw [inner_self_re_eq_norm_sq]; positivity⟩, ?_⟩
    have h1 : (1 : H n →ₗ[ℂ] H n) - LinearMap.id = 0 := by ext x; simp
    rw [h1]
    exact ⟨fun x y => by simp, fun x => by simp⟩
  rw [single_effect_selector_iff hE₀ hψ] at hselect
  have hnetop : (ℂ ∙ ψ : Submodule ℂ (H n)) ≠ ⊤ := by
    intro htop
    have hfr1 : Module.finrank ℂ (ℂ ∙ ψ : Submodule ℂ (H n)) = 1 := by
      apply finrank_span_singleton
      intro hz; rw [hz, norm_zero] at hψ; norm_num at hψ
    have hfr2 : Module.finrank ℂ (H n) = n := by simp [H]
    rw [htop, finrank_top, hfr2] at hfr1
    omega
  apply hnetop
  rcases hselect with ⟨_, _, _, hker⟩ | ⟨_, _, _, hker⟩ <;>
  · rw [← hker]
    have h1 : (LinearMap.id : H n →ₗ[ℂ] H n) - ((1 : ℝ) : ℂ) • LinearMap.id = 0 := by simp
    rw [h1, LinearMap.ker_zero]

end
end QuantumFoundations.Selector
