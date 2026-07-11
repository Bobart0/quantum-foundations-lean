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
