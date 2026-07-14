import QuantumFoundations.Uhlhorn.GleasonExtend
import QuantumFoundations.Uhlhorn.Spectral
import Gleason.Main

/-!
# U3b — L'argument « Gleason appliqué deux fois »

Combine `Gleason.gleason` (importé comme boîte noire), U3a
(`exists_projMeasure_of_frameFunctionOnLines`) et U2
(`eq_projL_of_positive_le_one_trace_one_inner_one`).

**Écart par rapport à la stratégie de reconnaissance** : le « Sous-lemme 1 »
envisagé (résolution de l'identité comme identité D'OPÉRATEURS,
`∑ i, projL (ℂ ∙ (b i)) = 1`, via `Gleason.projL_sup_of_pairwise_isOrtho`) s'est
avéré NON NÉCESSAIRE. `LinearMap.trace_eq_sum_inner` donne directement la trace
de `D` comme somme sur N'IMPORTE QUELLE base orthonormée — en particulier la
base `b'` image de `φ` (garantie complète par `SendsONBToONB`), sans jamais
former explicitement l'opérateur `∑ i, projL (ℂ ∙ (b' i))`. Un « Sous-lemme 0 »
(densité ⟹ effet, absent de `gleason-theorem-lean`, confirmé en reconnaissance)
a en revanche bien été nécessaire, dérivé ici par la même technique de
décomposition de trace que U2.
-/

namespace QuantumFoundations.Uhlhorn

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ}

/-- Un opérateur densité a une forme quadratique bornée par `1` en tout vecteur
unitaire — même technique de décomposition de trace autour de `x` qu'en U2. -/
private theorem density_inner_le_one {ρ : H n →ₗ[ℂ] H n} (hρ : IsDensityOperator ρ)
    {x : H n} (hx : ‖x‖ = 1) : (⟪ρ x, x⟫_ℂ).re ≤ 1 := by
  have hn1 : 1 ≤ n := one_le_of_norm_eq_one hx
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_extension_complex hn1 (fun _ : Fin 1 => x)
    (by rw [orthonormal_iff_ite]; intro i j; fin_cases i; fin_cases j; simp [hx])
  set i0 : Fin n := Fin.castLE hn1 (0 : Fin 1) with hi0
  have hbi0 : b i0 = x := hb 0
  have htrace_sum : LinearMap.trace ℂ (H n) ρ = ∑ i, ⟪b i, ρ (b i)⟫_ℂ :=
    LinearMap.trace_eq_sum_inner ρ b
  have hnn : ∀ i, 0 ≤ (⟪b i, ρ (b i)⟫_ℂ).re := by
    intro i
    rw [← hρ.symmetric (b i) (b i)]
    exact hρ.nonneg (b i)
  have hle : (⟪b i0, ρ (b i0)⟫_ℂ).re ≤ ∑ i, (⟪b i, ρ (b i)⟫_ℂ).re :=
    Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ i0)
  rw [← Complex.re_sum, ← htrace_sum, hρ.trace_one] at hle
  rw [hbi0] at hle
  rw [hρ.symmetric x x]
  simpa using hle

private theorem sub_nonneg_of_density {ρ : H n →ₗ[ℂ] H n} (hρ : IsDensityOperator ρ) (z : H n) :
    0 ≤ (⟪(1 - ρ) z, z⟫_ℂ).re := by
  rcases eq_or_ne z 0 with hz0 | hz0
  · simp [hz0]
  · set x : H n := (‖z‖⁻¹ : ℂ) • z with hx_def
    have hxnorm : ‖x‖ = 1 := by
      rw [hx_def, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg z), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz0)]
    have hz_eq : z = (‖z‖ : ℂ) • x := by
      rw [hx_def, smul_smul, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz0), Complex.ofReal_one, one_smul]
    have hinner : ⟪ρ z, z⟫_ℂ = (((‖z‖ : ℝ) ^ 2 : ℝ) : ℂ) * ⟪ρ x, x⟫_ℂ := by
      conv_lhs => rw [hz_eq]
      rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
      push_cast; ring
    have hle := density_inner_le_one hρ hxnorm
    have hzz : ⟪z, z⟫_ℂ = (((‖z‖ : ℝ) ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [LinearMap.sub_apply, Module.End.one_apply, inner_sub_left, hzz, hinner,
      Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re]
    nlinarith [sq_nonneg (‖z‖ : ℝ), hle]

/-- **Sous-lemme 0** (absent de `gleason-theorem-lean`, confirmé en
reconnaissance) : positivité + trace `1` en dimension finie force `≤ 1`
(les valeurs propres d'une densité sont positives et somment à `1`, donc
chacune est `≤ 1`). -/
private theorem isEffect_of_isDensityOperator {ρ : H n →ₗ[ℂ] H n} (hρ : IsDensityOperator ρ) :
    IsEffect ρ := by
  have h1 : IsPositiveOp ρ := ⟨hρ.symmetric, hρ.nonneg⟩
  have h2symm : LinearMap.IsSymmetric (1 - ρ) := LinearMap.IsSymmetric.one.sub hρ.symmetric
  have h2nn : ∀ z, 0 ≤ (⟪(1 - ρ) z, z⟫_ℂ).re := sub_nonneg_of_density hρ
  have h2 : IsPositiveOp (1 - ρ) := ⟨h2symm, h2nn⟩
  exact ⟨h1, h2⟩

/-- **Sous-lemme 2** (première application de `Gleason.gleason`) : pour toute
densité `D` fixée, `P ↦ bornValue D (φ P : Submodule)` est une fonction-cadre
sur les droites (U3a s'applique), d'où une densité `E` (dépendant de `D`) telle
que `bornValue D (φ P) = bornValue E P` pour tout `P`. -/
private theorem exists_density_born_eq (hn : 3 ≤ n) (φ : Proj1 n → Proj1 n)
    (hφ : SendsONBToONB φ) (D : H n →ₗ[ℂ] H n) (hD : IsDensityOperator D) :
    ∃ E : H n →ₗ[ℂ] H n, IsDensityOperator E ∧
      ∀ P : Proj1 n, bornValue D (φ P : Submodule ℂ (H n)) = bornValue E (P : Submodule ℂ (H n)) := by
  have hframe : IsFrameFunctionOnLines (fun P => bornValue D (φ P : Submodule ℂ (H n))) := by
    constructor
    · intro P
      show 0 ≤ bornValue D (φ P : Submodule ℂ (H n))
      obtain ⟨x, hx, hxP⟩ := exists_unit_vector_of_proj1 (φ P)
      rw [hxP, bornValue_span_singleton D x hx]
      exact hD.nonneg x
    · intro b
      obtain ⟨b', hb'⟩ := hφ b
      have hterm : ∀ i, bornValue D (φ (Proj1.mk_unit (b i) (b.norm_eq_one i)) : Submodule ℂ (H n))
          = (⟪D (b' i), b' i⟫_ℂ).re := by
        intro i
        rw [hb' i, bornValue_span_singleton D (b' i) (b'.norm_eq_one i)]
      show ∑ i, bornValue D (φ (Proj1.mk_unit (b i) (b.norm_eq_one i)) : Submodule ℂ (H n)) = 1
      rw [Finset.sum_congr rfl (fun i _ => hterm i)]
      have hsymmterm : ∀ i, (⟪D (b' i), b' i⟫_ℂ).re = (⟪b' i, D (b' i)⟫_ℂ).re := by
        intro i; rw [hD.symmetric (b' i) (b' i)]
      rw [Finset.sum_congr rfl (fun i _ => hsymmterm i), ← Complex.re_sum,
        ← LinearMap.trace_eq_sum_inner D b', hD.trace_one]
      norm_num
  obtain ⟨m, hm⟩ := exists_projMeasure_of_frameFunctionOnLines n
    (fun P => bornValue D (φ P : Submodule ℂ (H n))) hframe
  obtain ⟨E, ⟨hE_dens, hE_born⟩, -⟩ := Gleason.gleason hn m
  refine ⟨E, hE_dens, fun P => ?_⟩
  rw [← hm P, hE_born (P : Submodule ℂ (H n))]

private theorem traceProd_self_eq_one (P : Proj1 n) : TraceProd P P = 1 := by
  obtain ⟨x, hx, hxP⟩ := exists_unit_vector_of_proj1 P
  have hPeq : Proj1.mk_unit x hx = P := Subtype.ext hxP.symm
  show bornValue (projL (P : Submodule ℂ (H n))) (P : Submodule ℂ (H n)) = 1
  rw [← hPeq]
  show bornValue (projL (ℂ ∙ x)) (ℂ ∙ x) = 1
  rw [bornValue_span_singleton (projL (ℂ ∙ x)) x hx, projL_singleton_unit x x hx,
    inner_smul_left]
  have hxx : ⟪x, x⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hx]; norm_num
  rw [hxx, mul_one]
  simp

private theorem isDensityOperator_projL_of_proj1 (P : Proj1 n) :
    IsDensityOperator (projL (P : Submodule ℂ (H n))) := by
  obtain ⟨x, hx, hxP⟩ := exists_unit_vector_of_proj1 P
  rw [hxP]
  refine ⟨Submodule.starProjection_isSymmetric (ℂ ∙ x), ?_, ?_⟩
  · intro z
    exact Submodule.re_inner_starProjection_nonneg (ℂ ∙ x) z
  · have heq : projL (ℂ ∙ x) = (InnerProductSpace.rankOne ℂ x x : H n →ₗ[ℂ] H n) := by
      apply LinearMap.ext
      intro y
      rw [projL_singleton_unit x y hx]
      show ⟪x, y⟫_ℂ • x = (InnerProductSpace.rankOne ℂ x x : H n →L[ℂ] H n) y
      rw [InnerProductSpace.rankOne_apply]
    rw [heq, InnerProductSpace.trace_rankOne]
    rw [inner_self_eq_norm_sq_to_K, hx]
    norm_num

/-- **U3b** : si `φ` envoie tout COSP (système orthonormé complet — en dimension
finie, toute base orthonormée) sur un COSP, alors `φ` préserve
`tr(φ(P)φ(Q)) = tr(PQ)` pour TOUTE paire `P, Q` — pas seulement les paires
orthogonales.

Stratégie (`Sous-lemme 3` + assemblage de la reconnaissance) : fixe `P` (le
premier argument du but), applique `exists_density_born_eq` à
`D := projL (φ P)`, obtient `E`. Spécialise l'égalité `(*)` en `P` lui-même :
`bornValue D (φ P) = TraceProd (φ P) (φ P) = 1`, d'où `bornValue E P = 1` puis,
via U2, `E = projL P`. Réinjecte dans `(*)` en `Q` : `TraceProd (φ P) (φ Q) =
bornValue D (φ Q) = bornValue E Q = bornValue (projL P) Q = TraceProd P Q`. -/
theorem traceProd_preserved_of_sendsONBToONB (hn : 3 ≤ n) (φ : Proj1 n → Proj1 n)
    (hφ : SendsONBToONB φ) :
    ∀ P Q : Proj1 n, TraceProd (φ P) (φ Q) = TraceProd P Q := by
  intro P Q
  obtain ⟨E, hE_dens, hE_eq⟩ := exists_density_born_eq hn φ hφ (projL (φ P : Submodule ℂ (H n)))
    (isDensityOperator_projL_of_proj1 (φ P))
  have hspec := hE_eq P
  have hlhs : bornValue (projL (φ P : Submodule ℂ (H n))) (φ P : Submodule ℂ (H n)) = 1 :=
    traceProd_self_eq_one (φ P)
  rw [hlhs] at hspec
  obtain ⟨x, hx, hxP⟩ := exists_unit_vector_of_proj1 P
  rw [hxP, bornValue_span_singleton E x hx] at hspec
  have himE : (⟪E x, x⟫_ℂ).im = 0 := by
    have hconj : (starRingEnd ℂ) ⟪E x, x⟫_ℂ = ⟪x, E x⟫_ℂ := inner_conj_symm _ _
    rw [← hE_dens.symmetric x x] at hconj
    exact Complex.conj_eq_iff_im.mp hconj
  have hEx1 : ⟪E x, x⟫_ℂ = 1 := Complex.ext hspec.symm (by rw [himE]; simp)
  have hE_eff : IsEffect E := isEffect_of_isDensityOperator hE_dens
  have hEP : E = projL (P : Submodule ℂ (H n)) := by
    rw [hxP]
    exact eq_projL_of_positive_le_one_trace_one_inner_one hE_eff hE_dens.trace_one hx hEx1
  have hfinal := hE_eq Q
  rw [hEP] at hfinal
  exact hfinal

end
end QuantumFoundations.Uhlhorn
