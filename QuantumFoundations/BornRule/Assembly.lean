import QuantumFoundations.BornRule.Pinning

/-!
**FR.** # B4 — Assemblage final : le Théorème de Cohérence de Grain

`hker_derivation` relie (Null) à l'hypothèse abstraite `hker` de B3, via un
argument de recalibrage (`w` non nécessairement unitaire, `u := w/‖w‖`) ;
`full_rho_facts` combine B2 (`exists_rho`) et B3 (`eq_projL_of_vanishes_on_orthogonal`)
en un unique `ρ` (une seule application de `Gleason.gleason` — deux applications
séparées ne renverraient pas nécessairement le même témoin, `Gleason.gleason`
étant un théorème d'existence, pas un objet canonique) ; `grainCoherenceTheorem`
assemble le tout via `refinePerspective`/`refine_filter_eq_cellLines` (B1).

L'étape de recalibrage de `hker_derivation` (montrer que la valeur de `g`/`Est`
en `w` et en son renormalisé `u` coïncident) est un `congrArg` immédiat sur
l'égalité de sous-espaces `ℂ∙w = ℂ∙u` transportée en égalité de `Proj1 n`
(`Subtype.ext`) : `g` étant une fonction ordinaire de `Proj1 n`, deux
arguments égaux donnent des images égales sans argument de non-contextualité
supplémentaire.

**EN.** # B4 — Final assembly: the Grain Coherence Theorem

hker_derivation connects (Null) to the abstract hypothesis hker of B3 through
a rescaling argument (w not necessarily unit, u := w/‖w‖);
full_rho_facts combines B2 (exists_rho) and B3 (eq_projL_of_vanishes_on_orthogonal)
into a single ρ (one application of Gleason.gleason only—two separate
applications would not necessarily return the same witness, since
Gleason.gleason is an existence theorem, not a canonical object);
grainCoherenceTheorem assembles the result via
refinePerspective/refine_filter_eq_cellLines (B1).

The rescaling step in hker_derivation (showing that the value of g/Est
at w agrees with its value at the normalized vector u) is an immediate
congrArg applied to the equality of subspaces ℂ∙w = ℂ∙u, transported to
an equality in Proj1 n (Subtype.ext): since g is an ordinary function
on Proj1 n, equal arguments have equal images, with no additional
non-contextuality argument.
-/

namespace QuantumFoundations.BornRule

open scoped InnerProductSpace
open scoped Classical
open Gleason
open QuantumFoundations.Uhlhorn (Proj1 projL_singleton_unit)

noncomputable section

variable {n : ℕ} (Est : Perspective n → Submodule ℂ (H n) → ℝ)

/--
**FR.** L'hypothèse `hker` de B3 (`ρ` s'annule sur l'orthogonal de `v`), dérivée de
(Null) : `w` est recalibré en un vecteur unitaire `u` de même droite, sur
lequel (Null) + B2 donnent directement `g u = 0`, puis
`Gleason.positive_inner_self_eq_zero` conclut `ρ w = 0`.

Ni `hv : ‖v‖ = 1` ni (Grain)/(Norm) ne sont nécessaires ici — `AxNul` ne
suppose pas `v` unitaire, et le recalibrage `g w = g u` se fait par simple
`congrArg`/`Subtype.ext` (voir note d'en-tête), sans invoquer
`lemma4_noncontextual`.

**EN.** The B3 hypothesis hker (ρ vanishes on the orthogonal complement of v),
derived from (Null): w is rescaled to a unit vector u spanning the same
line, on which (Null) + B2 directly yield g u = 0; then
Gleason.positive_inner_self_eq_zero gives ρ w = 0.

Neither hv : ‖v‖ = 1 nor (Grain)/(Norm) is needed here—AxNul does not
assume that v is unit, and the rescaling equality g w = g u follows from
a simple congrArg/Subtype.ext argument (see the header note), without
invoking lemma4_noncontextual.
-/
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

/--
**FR.** Combine B2 (`exists_rho`) et B3 (`eq_projL_of_vanishes_on_orthogonal`) via
`hker_derivation` : une seule application de `Gleason.gleason` fournit un `ρ`
qui est À LA FOIS `projL (ℂ∙v)` et compatible avec `g` sur tout vecteur
unitaire.

**EN.** Combines B2 (exists_rho) and B3 (eq_projL_of_vanishes_on_orthogonal) via
hker_derivation: a single application of Gleason.gleason provides a ρ
that is BOTH projL (ℂ∙v) and compatible with g on every unit vector.
-/
theorem full_rho_facts (hn3 : 3 ≤ n) (hA : AxGrain Est) (hN : AxNorm Est) (hPos : AxPos Est)
    {v : H n} (hv : ‖v‖ = 1) (hNul : AxNul Est v) :
    ∃ ρ : H n →ₗ[ℂ] H n, ρ = projL (ℂ ∙ v) ∧
      ∀ x : H n, ∀ hx : ‖x‖ = 1, g Est (by omega) (Proj1.mk_unit x hx) = (⟪ρ x, x⟫_ℂ).re := by
  obtain ⟨ρ, hρ_dens, hgleason⟩ := exists_rho Est hn3 hA hN hPos
  refine ⟨ρ, ?_, hgleason⟩
  exact eq_projL_of_vanishes_on_orthogonal hρ_dens hv
    (hker_derivation Est hn3 hNul hρ_dens hgleason)

/--
**FR.** **Théorème de Cohérence de Grain.** Pour une perspective `D` (partition de
`H n` en cellules orthogonales non nulles) et une cellule `c` de `D`, toute
règle d'estimation `Est` satisfaisant (Grain), (Norm), (Pos) et, pour un
vecteur unitaire `v` fixé, (Null), vérifie `Est D c = ∑ᵢ ‖⟪v,fᵢ⟫‖²` sur toute
base orthonormée `(fᵢ)` de `c` — la règle de Born en toute généralité, dérivée
des quatre axiomes de cohérence seuls, SANS supposer `Est` a priori de la
forme d'une trace. Résultat composé, pas autonome : s'appuie sur le théorème
de Gleason (Gleason 1957, *Measures on the closed subspaces of a Hilbert
space*), importé comme un vrai théorème (`Gleason.gleason`, dépendance externe
épinglée) plutôt que comme un axiome, ainsi que sur l'infrastructure interne
du bloc Uhlhorn (U2, U3a).

**EN.** Grain Coherence Theorem. For a perspective D (a partition of
H n into nonzero orthogonal cells) and a cell c of D, every estimation
rule Est satisfying (Grain), (Norm), (Pos), and, for a fixed unit vector v,
(Null), satisfies Est D c = ∑ᵢ ‖⟪v,fᵢ⟫‖² for every orthonormal basis (fᵢ)
of c—the Born rule in full generality, derived from the four coherence
axioms alone, WITHOUT assuming a priori that Est has trace form. This is a
composite rather than self-contained result: it relies on Gleason's theorem
(Gleason 1957, Measures on the closed subspaces of a Hilbert space),
imported as an actual theorem (Gleason.gleason, pinned external dependency)
rather than as an axiom, as well as on the internal infrastructure of the
Uhlhorn block (U2, U3a).
-/
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

/--
**FR.** Version en notation projecteur de `grainCoherenceTheorem`. Il s'agit du
même résultat, la somme des carrés des coefficients dans une base orthonormée
de `c` étant la norme au carré de la projection orthogonale sur `c`.

**EN.** Projector-notation version of grainCoherenceTheorem. This is the same
result, since the sum of the squared coefficients in an orthonormal basis
of c is the squared norm of the orthogonal projection onto c.
-/
theorem grainCoherenceTheorem_projector (hn3 : 3 ≤ n) (hA : AxGrain Est)
    (hN : AxNorm Est) (hPos : AxPos Est) {v : H n} (hv : ‖v‖ = 1)
    (hNul : AxNul Est v) (D : Perspective n) {c : Submodule ℂ (H n)}
    (hc : c ∈ D.cells) : Est D c = ‖projL c v‖ ^ 2 := by
  rw [grainCoherenceTheorem Est hn3 hA hN hPos hv hNul D hc]
  have hpyth := sum_sq_projL_of_pairwise_isOrtho
    (cellLines c) (cellLines_ortho_within c) v
  rw [Finset.sup_id_eq_sSup, cellLines_sSup] at hpyth
  rw [hpyth, cellLines_sum_eq]
  apply Finset.sum_congr rfl
  intro i _
  have hf_unit : ‖((stdOrthonormalBasis ℂ c i : c) : H n)‖ = 1 :=
    (stdOrthonormalBasis ℂ c).orthonormal.1 i
  rw [projL_singleton_unit _ _ hf_unit, norm_smul, hf_unit, mul_one,
    norm_inner_symm]

#print axioms grainCoherenceTheorem_projector

end
end QuantumFoundations.BornRule
