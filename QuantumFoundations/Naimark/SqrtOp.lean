import QuantumFoundations.Naimark.Defs
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Positive

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

/-- `sqrtOp T` agit sur un vecteur propre de `T` par multiplication par `√λⱼ`
(la somme spectrale s'effondre sur le seul terme `j` par orthonormalité de la base). -/
private theorem sqrtOp_apply_basis {T : H n →ₗ[ℂ] H n} (hT : LinearMap.IsSymmetric T)
    (j : Fin n) :
    sqrtOp T (hT.eigenvectorBasis finrank_euclideanSpace_fin j) =
      (Real.sqrt (hT.eigenvalues finrank_euclideanSpace_fin j) : ℂ) •
        hT.eigenvectorBasis finrank_euclideanSpace_fin j := by
  rw [sqrtOp_apply hT, Finset.sum_eq_single j]
  · rw [(hT.eigenvectorBasis finrank_euclideanSpace_fin).inner_eq_ite, if_pos rfl]
    simp
  · intro i _ hij
    rw [(hT.eigenvectorBasis finrank_euclideanSpace_fin).inner_eq_ite, if_neg hij]
    simp
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Les valeurs propres d'un opérateur positif sont positives : pont d'une ligne vers
`LinearMap.IsPositive.nonneg_eigenvalues` (Mathlib), via la coïncidence de
`Gleason.IsPositiveOp` et `LinearMap.IsPositive` (cf. en-tête). -/
private theorem eigenvalues_nonneg {T : H n →ₗ[ℂ] H n} (hP : IsPositiveOp T) (j : Fin n) :
    0 ≤ hP.1.eigenvalues finrank_euclideanSpace_fin j := by
  have hPos : T.IsPositive := ⟨hP.1, hP.2⟩
  exact hPos.nonneg_eigenvalues finrank_euclideanSpace_fin j

/-- `sqrtOp T` est positif dès que `T` l'est. -/
theorem sqrtOp_isPositive {T : H n →ₗ[ℂ] H n} (hT : IsPositiveOp T) :
    IsPositiveOp (sqrtOp T) := by
  obtain ⟨hSym, hPos⟩ := hT
  set b := hSym.eigenvectorBasis finrank_euclideanSpace_fin
  set lam := hSym.eigenvalues finrank_euclideanSpace_fin
  constructor
  · intro x y
    simp only [sqrtOp_apply hSym x, sqrtOp_apply hSym y, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_conj_symm x (b i)]
    ring
  · intro x
    simp only [sqrtOp_apply hSym x, sum_inner, inner_smul_left, Complex.conj_ofReal,
      Complex.re_sum]
    apply Finset.sum_nonneg
    intro i _
    rw [mul_comm ((starRingEnd ℂ) ⟪b i, x⟫_ℂ) ⟪b i, x⟫_ℂ, Complex.mul_conj, Complex.re_ofReal_mul]
    exact mul_nonneg (Real.sqrt_nonneg _) (Complex.normSq_nonneg _)

/-- `sqrtOp T` est bien une racine carrée de `T` au sens opératoriel : `√T ∘ √T = T`.
Par extensionnalité sur la base propre (`Basis.ext`), pas de double somme.
(Unicité de la racine carrée positive : hors scope de ce jalon.) -/
theorem sqrtOp_mul_self {T : H n →ₗ[ℂ] H n} (hT : IsPositiveOp T) :
    sqrtOp T ∘ₗ sqrtOp T = T := by
  apply (hT.1.eigenvectorBasis finrank_euclideanSpace_fin).toBasis.ext
  intro j
  rw [show (hT.1.eigenvectorBasis finrank_euclideanSpace_fin).toBasis j
      = hT.1.eigenvectorBasis finrank_euclideanSpace_fin j from rfl]
  show sqrtOp T (sqrtOp T (hT.1.eigenvectorBasis finrank_euclideanSpace_fin j)) = _
  rw [sqrtOp_apply_basis hT.1, map_smul, sqrtOp_apply_basis hT.1, smul_smul,
    ← Complex.ofReal_mul, Real.mul_self_sqrt (eigenvalues_nonneg hT j)]
  exact (hT.1.apply_eigenvectorBasis finrank_euclideanSpace_fin j).symm

end
end QuantumFoundations
