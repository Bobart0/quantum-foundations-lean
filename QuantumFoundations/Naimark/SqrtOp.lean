import QuantumFoundations.Naimark.Defs
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Racine carrée positive (dimension finie, construction spectrale)

Pas de raccourci Mathlib retenu (voir étape 0 : `CFC.sqrt` existe mais vit côté
`ContinuousLinearMap`/ordre de Loewner — casts inutiles par rapport à la convention
`H n →ₗ[ℂ] H n` du projet). Construction spectrale maison, calquée sur la preuve de
`ContinuousLinearMap.isPositive_iff_eq_sum_rankOne` dans Mathlib.

Pattern « définition TOTALE + valeur poubelle » : hors du cas symétrique, `sqrtOp`
vaut `0` (junk), comme `Real.sqrt` sur les négatifs.

## Conventions figées en étape 0 (N1)

* `InnerProductSpace.rankOne_apply (x : E) (y z : F) : rankOne 𝕜 x y z = ⟪y, z⟫ • x`
  (Mathlib, `Analysis.InnerProductSpace.LinearMap`) — donc
  `(rankOne ℂ (b i) (b i) : H n →ₗ[ℂ] H n) x = ⟪b i, x⟫_ℂ • b i`.
* `Gleason.IsPositiveOp T := LinearMap.IsSymmetric T ∧ ∀ x, 0 ≤ (⟪T x, x⟫_ℂ).re`
  (Gleason/Busch/Effects.lean) — positivité sur `⟪T x, x⟫`, littéralement la même
  proposition que `LinearMap.IsPositive T` de Mathlib (`IsSymmetric T ∧ ∀ x, 0 ≤ re ⟪T x, x⟫`,
  `Analysis.InnerProductSpace.Positive`) : les deux notions coïncident par construction
  du champ `re` (`RCLike.re = Complex.re` pour `𝕜 = ℂ`), d'où un pont direct
  `⟨hT.1, hT.2⟩ : T.IsPositive` sans preuve supplémentaire.
* Signatures spectrales retenues en N0
  (`Mathlib.Analysis.InnerProductSpace.Spectrum`, pour `hT : T.IsSymmetric`,
  `hn : Module.finrank ℂ (H n) = n`, ici toujours `finrank_euclideanSpace_fin`) :
  - `hT.eigenvalues hn : Fin n → ℝ`
  - `hT.eigenvectorBasis hn : OrthonormalBasis (Fin n) ℂ (H n)`
  - `hT.apply_eigenvectorBasis hn i : T (hT.eigenvectorBasis hn i)
      = (hT.eigenvalues hn i : ℂ) • hT.eigenvectorBasis hn i`
-/

namespace QuantumFoundations

open scoped InnerProductSpace
open Gleason Classical

noncomputable section

variable {n : ℕ}

/-- Racine carrée positive de `T`, par décomposition spectrale `Σᵢ √λᵢ • rankOne (bᵢ) (bᵢ)`
si `T` est symétrique, `0` sinon (valeur poubelle, hors scope si `T` n'est pas positif). -/
noncomputable def sqrtOp (T : H n →ₗ[ℂ] H n) : H n →ₗ[ℂ] H n :=
  if hT : LinearMap.IsSymmetric T then
    ∑ i, (Real.sqrt (hT.eigenvalues finrank_euclideanSpace_fin i) : ℂ) •
      (InnerProductSpace.rankOne ℂ (hT.eigenvectorBasis finrank_euclideanSpace_fin i)
        (hT.eigenvectorBasis finrank_euclideanSpace_fin i) : H n →ₗ[ℂ] H n)
  else 0

/-- Dépliage de `sqrtOp` sur le cas symétrique, en explicitant `rankOne` via
`InnerProductSpace.rankOne_apply` (convention : `rankOne x y z = ⟪y,z⟫ • x`). -/
private theorem sqrtOp_apply {T : H n →ₗ[ℂ] H n} (hT : LinearMap.IsSymmetric T) (x : H n) :
    sqrtOp T x = ∑ i, (Real.sqrt (hT.eigenvalues finrank_euclideanSpace_fin i) : ℂ) •
      (⟪hT.eigenvectorBasis finrank_euclideanSpace_fin i, x⟫_ℂ •
        hT.eigenvectorBasis finrank_euclideanSpace_fin i) := by
  simp only [sqrtOp, dif_pos hT, LinearMap.sum_apply, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply]

/-- `sqrtOp T` est positif dès que `T` l'est. -/
theorem sqrtOp_isPositive {T : H n →ₗ[ℂ] H n} (hT : IsPositiveOp T) :
    IsPositiveOp (sqrtOp T) := by
  sorry

/-- `sqrtOp T` est bien une racine carrée de `T` au sens opératoriel : `√T ∘ √T = T`.
(Unicité de la racine carrée positive : hors scope de ce jalon.) -/
theorem sqrtOp_mul_self {T : H n →ₗ[ℂ] H n} (hT : IsPositiveOp T) :
    sqrtOp T ∘ₗ sqrtOp T = T := by
  sorry

end
end QuantumFoundations
