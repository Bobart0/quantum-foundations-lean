import QuantumFoundations.BornRule.Pinning

/-!
# B4 — Assemblage final : le Théorème de Cohérence de Grain

`hker_derivation` relie (Null) à l'hypothèse abstraite `hker` de B3, via un
argument de recalibrage (`w` non nécessairement unitaire, `u := w/‖w‖`) ;
`full_rho_facts` combine B2 (`exists_rho`) et B3 (`eq_projL_of_vanishes_on_orthogonal`)
en un unique `ρ` (une seule application de `Gleason.gleason` — deux applications
séparées ne renverraient pas nécessairement le même témoin, `Gleason.gleason`
étant un théorème d'existence, pas un objet canonique) ; `grainCoherenceTheorem`
assemble le tout via `refinePerspective`/`refine_filter_eq_cellLines` (B1).

**Écart favorable trouvé en reconnaissance** : l'étape de recalibrage de
`hker_derivation` (montrer que la valeur de `g`/`Est` en `w` et en son
renormalisé `u` coïncident) est un `congrArg` immédiat sur l'égalité de
sous-espaces `ℂ∙w = ℂ∙u` transportée en égalité de `Proj1 n` (`Subtype.ext`),
PAS une nouvelle application de `lemma4_noncontextual` : `g` est une fonction
ordinaire de `Proj1 n`, deux arguments égaux donnent des images égales sans
argument de non-contextualité supplémentaire (contrairement au prototype
`tstar-born-rule-lean`, où `gline` recalculait un `Perspective.binary` distinct
à chaque vecteur et devait invoquer `lemma4_noncontextual` pour recoller les
deux perspectives `binary(ℂ∙w)` et `binary(ℂ∙u)`).
-/

namespace QuantumFoundations.BornRule

open scoped InnerProductSpace
open scoped Classical
open Gleason
open QuantumFoundations.Uhlhorn (Proj1 projL_singleton_unit)

noncomputable section

variable {n : ℕ} (Est : Perspective n → Submodule ℂ (H n) → ℝ)

/-- L'hypothèse `hker` de B3 (`ρ` s'annule sur l'orthogonal de `v`), dérivée de
(Null) : `w` est recalibré en un vecteur unitaire `u` de même droite, sur
lequel (Null) + B2 donnent directement `g u = 0`, puis
`Gleason.positive_inner_self_eq_zero` conclut `ρ w = 0`.

Écart favorable supplémentaire : ni `hv : ‖v‖ = 1` ni (Grain)/(Norm) ne sont
nécessaires ici — `AxNul` ne suppose pas `v` unitaire, et le recalibrage
`gline w = gline u` se fait par simple `congrArg`/`Subtype.ext` (voir note
d'en-tête), sans invoquer `lemma4_noncontextual`. -/
theorem hker_derivation (hn3 : 3 ≤ n) {v : H n} (hNul : AxNul Est v)
    {ρ : H n →ₗ[ℂ] H n} (hρ : IsDensityOperator ρ)
    (hgleason : ∀ x : H n, ∀ hx : ‖x‖ = 1,
      g Est (by omega) (Proj1.mk_unit x hx) = (⟪ρ x, x⟫_ℂ).re) :
    ∀ w : H n, ⟪v, w⟫_ℂ = 0 → ρ w = 0 := by
  intro w hw_perp
  rcases eq_or_ne w 0 with hw0 | hw0
  · simp [hw0]
  · set u : H n := (‖w‖⁻¹ : ℂ) • w with hu_def
    have hwnorm_ne : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw0
    have hwu : w = (‖w‖ : ℂ) • u := by
      rw [hu_def, smul_smul, mul_inv_cancel₀ hwnorm_ne, one_smul]
    have hu_ne : u ≠ 0 := by rw [hu_def]; simp [hwnorm_ne, hw0]
    have hu_norm : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg w), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)]
    have hline_eq : (ℂ ∙ w : Submodule ℂ (H n)) = ℂ ∙ u := by
      rw [hwu]; exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hwnorm_ne) u
    have hPeq : (⟨ℂ ∙ w, finrank_span_singleton hw0⟩ : Proj1 n) = Proj1.mk_unit u hu_norm :=
      Subtype.ext hline_eq
    have hg_eq : g Est (by omega) (⟨ℂ ∙ w, finrank_span_singleton hw0⟩ : Proj1 n)
        = g Est (by omega) (Proj1.mk_unit u hu_norm) := congrArg (g Est (by omega)) hPeq
    have hvperp : v ∈ (ℂ ∙ w : Submodule ℂ (H n))ᗮ :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.mpr hw_perp
    have hg0 : g Est (by omega) (⟨ℂ ∙ w, finrank_span_singleton hw0⟩ : Proj1 n) = 0 := by
      unfold g
      exact hNul _ _ (Finset.mem_insert_self _ _) hvperp
    have hgu0 : (⟪ρ u, u⟫_ℂ).re = 0 := by
      rw [← hgleason u hu_norm, ← hg_eq, hg0]
    have him_u : (⟪ρ u, u⟫_ℂ).im = 0 := by
      have hconj : (starRingEnd ℂ) ⟪ρ u, u⟫_ℂ = ⟪u, ρ u⟫_ℂ := inner_conj_symm _ _
      rw [← hρ.symmetric u u] at hconj
      exact Complex.conj_eq_iff_im.mp hconj
    have hρuu0 : ⟪ρ u, u⟫_ℂ = 0 := Complex.ext (by rw [hgu0]; simp) (by rw [him_u]; simp)
    have hscale : ⟪ρ w, w⟫_ℂ = (((‖w‖ : ℝ) ^ 2 : ℝ) : ℂ) * ⟪ρ u, u⟫_ℂ := by
      conv_lhs => rw [hwu]
      rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
      push_cast; ring
    have hρww0 : ⟪ρ w, w⟫_ℂ = 0 := by rw [hscale, hρuu0, mul_zero]
    exact Gleason.positive_inner_self_eq_zero hρ.symmetric hρ.nonneg hρww0

/-- Combine B2 (`exists_rho`) et B3 (`eq_projL_of_vanishes_on_orthogonal`) via
`hker_derivation` : une seule application de `Gleason.gleason` fournit un `ρ`
qui est À LA FOIS `projL (ℂ∙v)` et compatible avec `g` sur tout vecteur
unitaire. -/
theorem full_rho_facts (hn3 : 3 ≤ n) (hA : AxGrain Est) (hN : AxNorm Est) (hPos : AxPos Est)
    {v : H n} (hv : ‖v‖ = 1) (hNul : AxNul Est v) :
    ∃ ρ : H n →ₗ[ℂ] H n, ρ = projL (ℂ ∙ v) ∧
      ∀ x : H n, ∀ hx : ‖x‖ = 1, g Est (by omega) (Proj1.mk_unit x hx) = (⟪ρ x, x⟫_ℂ).re := by
  obtain ⟨ρ, hρ_dens, hgleason⟩ := exists_rho Est hn3 hA hN hPos
  refine ⟨ρ, ?_, hgleason⟩
  exact eq_projL_of_vanishes_on_orthogonal hρ_dens hv
    (hker_derivation Est hn3 hNul hρ_dens hgleason)

/-- The Grain Coherence Theorem (« 𝒢 » in the companion articles). For an
arbitrary perspective D and cell c, E D c is the sum of squared overlaps of v
on an orthonormal basis of c — the Born rule in fully general form, derived
from (Grain), (Norm), (Pos), (Null) alone, with Gleason's theorem imported as
a genuine theorem (Gleason.gleason) rather than an axiom. -/
theorem grainCoherenceTheorem (hn3 : 3 ≤ n) (hA : AxGrain Est) (hN : AxNorm Est)
    (hPos : AxPos Est) {v : H n} (hv : ‖v‖ = 1) (hNul : AxNul Est v)
    (D : Perspective n) {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
    Est D c = ∑ i : Fin (Module.finrank ℂ c),
      ‖⟪v, ((stdOrthonormalBasis ℂ c i : c) : H n)⟫_ℂ‖ ^ 2 := by
  obtain ⟨ρ, hρeq, hgleason⟩ := full_rho_facts Est hn3 hA hN hPos hv hNul
  have hgrain := hA (refinePerspective D) D (refinePerspective_refines D) c hc
  rw [refine_filter_eq_cellLines D c hc] at hgrain
  rw [hgrain, cellLines_sum_eq c (Est (refinePerspective D))]
  apply Finset.sum_congr rfl
  intro i _
  set f : H n := ((stdOrthonormalBasis ℂ c i : c) : H n) with hf_def
  have hf_ne : f ≠ 0 := by
    have hnorm : ‖(stdOrthonormalBasis ℂ c i : c)‖ = 1 := (stdOrthonormalBasis ℂ c).orthonormal.1 i
    rw [hf_def]
    intro hzero
    rw [Submodule.coe_eq_zero] at hzero
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have hf_unit : ‖f‖ = 1 := (stdOrthonormalBasis ℂ c).orthonormal.1 i
  have hmem : (ℂ ∙ f) ∈ (refinePerspective D).cells := by
    simp only [refinePerspective, Finset.mem_biUnion]
    exact ⟨c, hc, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hEeq : Est (refinePerspective D) (ℂ ∙ f) = g Est (by omega) (Proj1.mk_unit f hf_unit) := by
    unfold g
    exact lemma4_noncontextual Est hA hN hmem (Finset.mem_insert_self _ _)
  rw [hEeq, hgleason f hf_unit, hρeq, projL_singleton_unit v f hv, inner_smul_left]
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_eq_norm_sq _

end
end QuantumFoundations.BornRule
