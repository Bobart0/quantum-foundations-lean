import QuantumFoundations.BornRule.Pinning

/-!
**FR.** # Selectors — S1 : sélecteurs, covariance, famille à un paramètre, NSNC-1

Contenu interprétativement neutre : rien d'everettien n'entre dans ce module.
Un **sélecteur** associe à chaque état pur un opérateur densité. On étudie ceux
qui sont **unitairement covariants** (`IsCovariant`), on isole la famille
candidate à un paramètre réel `t ∈ [0,1]` (`tDensity`/`tSelector`, la famille
isotrope/dépolarisante), le cas particulier `t = 1` (`bornSelector`, la règle
de Born), et une prémisse-pont (`NSNC1`, « pas de successeur, pas de chance »).
La covariance seule ne fixe pas `t` (théorème 3, `Classification.lean`) ; c'est
`NSNC1` qui le fait (théorème 1, `Pinning.lean`).

**EN.** # Selectors — S1: selectors, covariance, one-parameter family, NSNC-1

Interpretively neutral content: nothing Everettian enters this module. A
**selector** assigns a density operator to every pure state. We study those
that are **unitarily covariant** (`IsCovariant`), isolate the candidate
one-parameter family `t ∈ [0,1]` (`tDensity`/`tSelector`, the
isotropic/depolarizing family), the special case `t = 1` (`bornSelector`, the
Born rule), and a bridge premise (`NSNC1`, "no successor, no chance").
Covariance alone does not fix `t` (Theorem 3, `Classification.lean`); `NSNC1`
does (Theorem 1, `Pinning.lean`).
-/

namespace QuantumFoundations.Selector

open scoped InnerProductSpace
open Gleason
open QuantumFoundations.Uhlhorn (projL_singleton_unit)

noncomputable section

variable {n : ℕ}

/--
**FR.** Un sélecteur associe à chaque vecteur d'état un opérateur, qui est une
densité sur les vecteurs unitaires.

**EN.** A selector associates to each state vector an operator, which is a
density operator on unit vectors.
-/
structure Selector (n : ℕ) where
  ρ : H n → (H n →ₗ[ℂ] H n)
  isDensity : ∀ ψ : H n, ‖ψ‖ = 1 → IsDensityOperator (ρ ψ)

/--
**FR.** Covariance unitaire : `σ(Uψ) = U σ(ψ) U†`.

**EN.** Unitary covariance: `σ(Uψ) = U σ(ψ) U†`.
-/
def IsCovariant (σ : Selector n) : Prop :=
  ∀ (U : H n ≃ₗᵢ[ℂ] H n) (ψ : H n), ‖ψ‖ = 1 →
    σ.ρ (U ψ) = U.toLinearMap ∘ₗ σ.ρ ψ ∘ₗ U.symm.toLinearMap

/--
**FR.** Pont vers `LinearEquiv.conj`, qui est multiplicatif et injectif : à
prouver par `rfl` (voir `BranchesRiedel/Local.lean`, `commute_of_conj_commute`,
où ce `rfl` est déjà utilisé). Sers-t'en dans toutes les preuves de
conjugaison.

**EN.** Bridge to `LinearEquiv.conj`, which is multiplicative and injective:
to be proved by `rfl` (see `BranchesRiedel/Local.lean`,
`commute_of_conj_commute`, where this `rfl` is already used). Use it in every
conjugation proof.
-/
theorem isCovariant_iff_conj (σ : Selector n) :
    IsCovariant σ ↔ ∀ (U : H n ≃ₗᵢ[ℂ] H n) (ψ : H n), ‖ψ‖ = 1 →
      σ.ρ (U ψ) = U.toLinearEquiv.conj (σ.ρ ψ) :=
  Iff.rfl

/--
**FR.** Famille candidate : `ρ_t(ψ) = t·P_ψ + ((1−t)/(n−1))·P_{ψ⊥}`.
Définition TOTALE (pattern « définition totale + valeur poubelle + lemmes de
spec », `AGENTS.md` §Conventions) : elle ne prend aucune preuve en argument.

**EN.** Candidate family: `ρ_t(ψ) = t·P_ψ + ((1−t)/(n−1))·P_{ψ⊥}`. TOTAL
definition (the "total definition + junk value + specification lemmas"
pattern, `AGENTS.md` §Conventions): it takes no proof as an argument.
-/
noncomputable def tDensity (n : ℕ) (t : ℝ) (ψ : H n) : H n →ₗ[ℂ] H n :=
  (t : ℂ) • projL (ℂ ∙ ψ) + (((1 - t) / ((n : ℝ) - 1) : ℝ) : ℂ) • projL (ℂ ∙ ψ)ᗮ

/-- **FR.** Trace de la projection de rang 1 sur un vecteur unitaire : `1`, via
`InnerProductSpace.rankOne`/`trace_rankOne` (même route que
`Uhlhorn.GleasonTwice.isDensityOperator_projL_of_proj1`, spécifique à
`Proj1 n` là-bas ; ici directement sur `‖ψ‖ = 1`).

**EN.** Trace of the rank-1 projection onto a unit vector: `1`, via
`InnerProductSpace.rankOne`/`trace_rankOne` (same route as
`Uhlhorn.GleasonTwice.isDensityOperator_projL_of_proj1`, specific to `Proj1 n`
there; here directly on `‖ψ‖ = 1`). -/
private theorem trace_projL_singleton {ψ : H n} (hψ : ‖ψ‖ = 1) :
    LinearMap.trace ℂ (H n) (projL (ℂ ∙ ψ)) = 1 := by
  have heq : projL (ℂ ∙ ψ) = (InnerProductSpace.rankOne ℂ ψ ψ : H n →ₗ[ℂ] H n) := by
    apply LinearMap.ext
    intro y
    rw [projL_singleton_unit ψ y hψ]
    show ⟪ψ, y⟫_ℂ • ψ = (InnerProductSpace.rankOne ℂ ψ ψ : H n →L[ℂ] H n) y
    rw [InnerProductSpace.rankOne_apply]
  rw [heq, InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq_to_K, hψ]
  norm_num

/-- **FR.** Trace de la projection sur l'orthogonal d'un vecteur unitaire :
`n − 1`, par `projL A + projL Aᗮ = projL ⊤ = id` (`projL_sup_of_isOrtho`,
`Submodule.starProjection_top`) et linéarité de la trace.

**EN.** Trace of the projection onto the orthogonal complement of a unit
vector: `n − 1`, via `projL A + projL Aᗮ = projL ⊤ = id`
(`projL_sup_of_isOrtho`, `Submodule.starProjection_top`) and linearity of the
trace. -/
private theorem trace_projL_compl_singleton {ψ : H n} (hψ : ‖ψ‖ = 1) :
    LinearMap.trace ℂ (H n) (projL (ℂ ∙ ψ)ᗮ) = (n : ℂ) - 1 := by
  have hortho : (ℂ ∙ ψ) ⟂ (ℂ ∙ ψ)ᗮ := Submodule.le_orthogonal_orthogonal _
  have hsup : (ℂ ∙ ψ) ⊔ (ℂ ∙ ψ)ᗮ = ⊤ := Submodule.sup_orthogonal_of_hasOrthogonalProjection
  have hproj_sum : projL ((ℂ ∙ ψ) ⊔ (ℂ ∙ ψ)ᗮ) = projL (ℂ ∙ ψ) + projL (ℂ ∙ ψ)ᗮ :=
    Gleason.projL_sup_of_isOrtho hortho
  rw [hsup] at hproj_sum
  have htop : projL (⊤ : Submodule ℂ (H n)) = LinearMap.id := by
    show ((⊤ : Submodule ℂ (H n)).starProjection : H n →L[ℂ] H n).toLinearMap = LinearMap.id
    rw [Submodule.starProjection_top]
    rfl
  rw [htop] at hproj_sum
  have hfinrank : Module.finrank ℂ (H n) = n := by simp [H]
  have htrace_sum : LinearMap.trace ℂ (H n) (projL (ℂ ∙ ψ) + projL (ℂ ∙ ψ)ᗮ) = (n : ℂ) := by
    rw [← hproj_sum, LinearMap.trace_id, hfinrank]
  rw [map_add, trace_projL_singleton hψ] at htrace_sum
  linear_combination htrace_sum

/--
**FR.** Pour `n ≥ 2` et `t ∈ [0,1]`, `tDensity n t ψ` est un opérateur densité
sur tout vecteur unitaire `ψ`.

**EN.** For `n ≥ 2` and `t ∈ [0,1]`, `tDensity n t ψ` is a density operator on
every unit vector `ψ`.
-/
theorem tDensity_isDensity (hn : 2 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {ψ : H n} (hψ : ‖ψ‖ = 1) : IsDensityOperator (tDensity n t ψ) := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  set s : ℝ := (1 - t) / ((n : ℝ) - 1) with hs_def
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hn1.le
  have hconjt : (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
  have hconjs : (starRingEnd ℂ) (s : ℂ) = (s : ℂ) := Complex.conj_ofReal s
  refine ⟨?_, ?_, ?_⟩
  · show LinearMap.IsSymmetric (tDensity n t ψ)
    unfold tDensity
    exact (LinearMap.IsSymmetric.smul hconjt (Submodule.starProjection_isSymmetric (ℂ ∙ ψ))).add
      (LinearMap.IsSymmetric.smul hconjs (Submodule.starProjection_isSymmetric (ℂ ∙ ψ)ᗮ))
  · intro x
    show 0 ≤ (⟪tDensity n t ψ x, x⟫_ℂ).re
    unfold tDensity
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, inner_add_left,
      inner_smul_left, inner_smul_left, hconjt, hconjs]
    have h1 : 0 ≤ (⟪projL (ℂ ∙ ψ) x, x⟫_ℂ).re := Submodule.re_inner_starProjection_nonneg (ℂ ∙ ψ) x
    have h2 : 0 ≤ (⟪projL (ℂ ∙ ψ)ᗮ x, x⟫_ℂ).re :=
      Submodule.re_inner_starProjection_nonneg (ℂ ∙ ψ)ᗮ x
    show 0 ≤ ((t : ℂ) * ⟪projL (ℂ ∙ ψ) x, x⟫_ℂ + (s : ℂ) * ⟪projL (ℂ ∙ ψ)ᗮ x, x⟫_ℂ).re
    rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have h3 := mul_nonneg ht0 h1
    have h4 := mul_nonneg hs0 h2
    linarith
  · show LinearMap.trace ℂ (H n) (tDensity n t ψ) = 1
    unfold tDensity
    rw [map_add, map_smul, map_smul, trace_projL_singleton hψ, trace_projL_compl_singleton hψ,
      smul_eq_mul, smul_eq_mul]
    have heq : (s : ℂ) * ((n : ℂ) - 1) = (1 : ℂ) - (t : ℂ) := by
      rw [hs_def]
      push_cast
      have hne : ((n : ℂ) - 1) ≠ 0 := by
        have hne' : ((n : ℝ) - 1) ≠ 0 := ne_of_gt hn1
        exact_mod_cast hne'
      field_simp
    rw [heq]
    ring

/--
**FR.** Le sélecteur de la famille candidate, à paramètre `t` fixé.

**EN.** The selector of the candidate family, at a fixed parameter `t`.
-/
noncomputable def tSelector (n : ℕ) (hn : 2 ≤ n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Selector n :=
  ⟨tDensity n t, fun _ hψ => tDensity_isDensity hn ht0 ht1 hψ⟩

private theorem bornSelector_isDensity (ψ : H n) (hψ : ‖ψ‖ = 1) :
    IsDensityOperator (projL (ℂ ∙ ψ) : H n →ₗ[ℂ] H n) :=
  ⟨Submodule.starProjection_isSymmetric (ℂ ∙ ψ),
    fun z => Submodule.re_inner_starProjection_nonneg (ℂ ∙ ψ) z,
    trace_projL_singleton hψ⟩

/--
**FR.** Le sélecteur de Born : `ρ(ψ) = P_ψ`, valable pour tout `n ≥ 1`.

**EN.** The Born selector: `ρ(ψ) = P_ψ`, valid for every `n ≥ 1`.
-/
noncomputable def bornSelector (n : ℕ) : Selector n :=
  ⟨fun ψ => projL (ℂ ∙ ψ), bornSelector_isDensity⟩

/--
**FR.** Le sélecteur de Born est le cas `t = 1` de la famille candidate.

**EN.** The Born selector is the `t = 1` case of the candidate family.
-/
theorem bornSelector_eq_tDensity_one {ψ : H n} (_hψ : ‖ψ‖ = 1) :
    (bornSelector n).ρ ψ = tDensity n 1 ψ := by
  show projL (ℂ ∙ ψ) = tDensity n 1 ψ
  unfold tDensity
  norm_num

/--
**FR.** Prémisse-pont NSNC-1 : « pas de successeur, pas de chance ». Le poids
de Born de `σ(ψ)` sur l'orthogonal de `ψ` est nul.

**EN.** Bridge premise NSNC-1: "no successor, no chance". The Born value of
`σ(ψ)` on the orthogonal complement of `ψ` vanishes.
-/
def NSNC1 (σ : Selector n) : Prop :=
  ∀ ψ : H n, ‖ψ‖ = 1 → bornValue (σ.ρ ψ) ((ℂ ∙ ψ)ᗮ) = 0

end
end QuantumFoundations.Selector
