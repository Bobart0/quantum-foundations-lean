import QuantumFoundations.Naimark.Main

/-!
# N5 (optionnel) — forme unitaire/ancilla (Paris §3.2 Thm 4, Watrous Cor. 2.43)

`dilV P` est une isométrie `H n →ₗᵢ K`, pas un unitaire de `K`. Ce fichier construit
un unitaire `U : K ≃ₗᵢ K` qui ÉTEND `dilV P` au sens `U ∘ₗ singleL i₀ = dilV P`, pour
un indice ancilla `i₀ : Fin m` fixé arbitrairement (Watrous Cor. 2.43 / Paris Thm 4).

## Architecture (deux tentatives précédentes documentées dans SORRIES.md)

Ni `Submodule.orthogonalDecomposition`/`WithLp` (tentative 1), ni
`Submodule` + `LinearIsometryEquiv.equivRange` + `.trans` (tentative 2, provoque un
timeout Lean déterministe au `whnf` dès l'assemblage, indépendant de la difficulté
mathématique) : la route retenue ici évite ENTIÈREMENT les types dépendants
`Submodule`/`↥A` en travaillant avec deux familles orthonormées de `K` indexées par
`Fin m × Fin n` tout entier (l'indice canonique de `DilSpace n m`), complétées en
bases orthonormées complètes via `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`,
puis recollées en un unique unitaire de `K` via `Orthonormal.equiv`.

Point technique retenu (à répéter si le symptôme réapparaît) : composer
`(orthonormal_family ...).exists_orthonormalBasis_extension_of_card_eq ...` INLINE
dans un `obtain` déclenche le même timeout au `whnf` que la tentative 2, MÊME SANS
`Submodule` — la cause n'est donc pas `Submodule` en soi mais l'inférence
d'implicites lors de la composition directe de lemmes lourds. Isoler l'énoncé
combiné dans un lemme `private` à part entière (`orthonormalBasisExtension` ici),
appliqué ensuite par simple application de fonction aux deux cas concrets
(`singleL n m i₀` et `dilV P`), supprime le timeout.
-/

namespace QuantumFoundations

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n m : ℕ}

/-- Si `adjoint f ∘ₗ f = id` alors `f` préserve la norme. -/
private theorem isometry_of_adjoint_comp_self {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] {f : E →ₗ[ℂ] F}
    (hf : LinearMap.adjoint f ∘ₗ f = LinearMap.id) (x : E) : ‖f x‖ = ‖x‖ := by
  have h1 : ⟪f x, f x⟫_ℂ = ⟪x, x⟫_ℂ := by
    rw [← LinearMap.adjoint_inner_right f x (f x), ← LinearMap.comp_apply, hf, LinearMap.id_apply]
  have h2 : (‖f x‖ : ℝ) ^ 2 = ‖x‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), h1]
  nlinarith [norm_nonneg (f x), norm_nonneg x, sq_nonneg (‖f x‖ - ‖x‖)]

/-- Si `adjoint f ∘ₗ f = id` alors `f` préserve le produit scalaire. -/
private theorem inner_of_adjoint_comp_self {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] {f : E →ₗ[ℂ] F}
    (hf : LinearMap.adjoint f ∘ₗ f = LinearMap.id) (x y : E) : ⟪f x, f y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [← LinearMap.adjoint_inner_right f x (f y), ← LinearMap.comp_apply, hf, LinearMap.id_apply]

private theorem singleL_adjoint_comp_self (i : Fin m) :
    LinearMap.adjoint (singleL n m i) ∘ₗ singleL n m i = LinearMap.id := by
  rw [adjoint_singleL, coordL_singleL, if_pos rfl]

/-- Base orthonormée standard de `H n`. -/
private noncomputable def stdBasisH (n : ℕ) : OrthonormalBasis (Fin n) ℂ (H n) :=
  EuclideanSpace.basisFun (Fin n) ℂ

/-- Le bloc `i₀` de `Fin m × Fin n`, vu comme sous-ensemble d'indices. -/
private def sSlice (m n : ℕ) (i₀ : Fin m) : Set (Fin m × Fin n) := {p | p.1 = i₀}

/-- Pour toute isométrie `f : H n →ₗᵢ K`, la famille `p ↦ f (eₚ.₂)` est orthonormée sur
le bloc `sSlice i₀` (les vecteurs de base de `H n` transportés par `f`). -/
private theorem orthonormal_family (f : H n →ₗ[ℂ] DilSpace n m)
    (hf : LinearMap.adjoint f ∘ₗ f = LinearMap.id) (i₀ : Fin m) :
    Orthonormal ℂ ((sSlice m n i₀).restrict (fun p : Fin m × Fin n => f (stdBasisH n p.2))) := by
  constructor
  · rintro ⟨p, hp⟩
    show ‖f (stdBasisH n p.2)‖ = 1
    rw [isometry_of_adjoint_comp_self hf]
    exact (stdBasisH n).orthonormal.1 p.2
  · rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
    show ⟪f (stdBasisH n p.2), f (stdBasisH n q.2)⟫_ℂ = 0
    rw [inner_of_adjoint_comp_self hf]
    have hpq2 : p.2 ≠ q.2 := by
      intro h
      exact hpq (by simp only [Subtype.mk.injEq]; exact Prod.ext (hp.trans hq.symm) h)
    exact (stdBasisH n).orthonormal.2 hpq2

/-- Complétion de la famille orthonormée `p ↦ f (eₚ.₂)` (définie sur le bloc `i₀`) en
une base orthonormée complète de `DilSpace n m`. Isolé en lemme à part (plutôt que
composé inline) : voir la note d'architecture en tête de fichier. -/
private theorem orthonormalBasisExtension (f : H n →ₗ[ℂ] DilSpace n m)
    (hf : LinearMap.adjoint f ∘ₗ f = LinearMap.id) (i₀ : Fin m) :
    ∃ b : OrthonormalBasis (Fin m × Fin n) ℂ (DilSpace n m),
      ∀ p ∈ sSlice m n i₀, b p = f (stdBasisH n p.2) :=
  (orthonormal_family f hf i₀).exists_orthonormalBasis_extension_of_card_eq
    (finrank_euclideanSpace (ι := Fin m × Fin n) (𝕜 := ℂ))

private theorem orthonormal_toBasis {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (b : OrthonormalBasis ι ℂ E) : Orthonormal ℂ ⇑b.toBasis := by
  rw [OrthonormalBasis.coe_toBasis]; exact b.orthonormal

/-- **Extension unitaire** (Watrous Cor. 2.43 / Paris Thm 4) : pour tout indice ancilla
`i₀`, `dilV P` s'étend en un unitaire `U` de `DilSpace n m` (`U ∘ₗ singleL i₀ = dilV P`).
Construction : deux bases orthonormées complètes de `K`, l'une prolongeant
`singleL i₀ ∘ (base de H n)`, l'autre `dilV P ∘ (base de H n)`, recollées par
`Orthonormal.equiv`. -/
theorem exists_unitary_extension (P : POVM n m) (i₀ : Fin m) :
    ∃ U : DilSpace n m ≃ₗᵢ[ℂ] DilSpace n m, U.toLinearMap ∘ₗ singleL n m i₀ = dilV P := by
  obtain ⟨b, hb⟩ := orthonormalBasisExtension (singleL n m i₀) (singleL_adjoint_comp_self i₀) i₀
  obtain ⟨b', hb'⟩ := orthonormalBasisExtension (dilV P) (dilV_isometry P) i₀
  set U := Orthonormal.equiv (orthonormal_toBasis b) (orthonormal_toBasis b')
    (Equiv.refl (Fin m × Fin n)) with hU
  refine ⟨U, ?_⟩
  apply (stdBasisH n).toBasis.ext
  intro k
  show U (singleL n m i₀ ((stdBasisH n).toBasis k)) = dilV P ((stdBasisH n).toBasis k)
  have hek : (stdBasisH n).toBasis k = stdBasisH n k := rfl
  rw [hek]
  have hbp : b.toBasis (i₀, k) = singleL n m i₀ (stdBasisH n k) := by
    rw [OrthonormalBasis.coe_toBasis]; exact hb (i₀, k) rfl
  have hbp' : b'.toBasis (i₀, k) = dilV P (stdBasisH n k) := by
    rw [OrthonormalBasis.coe_toBasis]; exact hb' (i₀, k) rfl
  rw [← hbp, hU, Orthonormal.equiv_apply, Equiv.refl_apply, hbp']

/-- **Forme "ancilla" complète** : la POVM `P` se réalise en préparant l'ancilla dans
le bloc `i₀` (`singleL i₀`), en appliquant un unitaire global `U` de `DilSpace n m`,
puis en mesurant la mesure projective `dilProj` — corollaire direct de
`exists_unitary_extension` et `naimark_born`. -/
theorem naimark_projective_form (P : POVM n m) (i₀ : Fin m) :
    ∃ U : DilSpace n m ≃ₗᵢ[ℂ] DilSpace n m, ∀ (i : Fin m) (x : H n),
      ⟪x, P.E i x⟫_ℂ = ⟪U (singleL n m i₀ x), dilProj n m i (U (singleL n m i₀ x))⟫_ℂ := by
  obtain ⟨U, hU⟩ := exists_unitary_extension P i₀
  refine ⟨U, fun i x => ?_⟩
  rw [show U (singleL n m i₀ x) = dilV P x from LinearMap.congr_fun hU x]
  exact naimark_born P i x

end
end QuantumFoundations
