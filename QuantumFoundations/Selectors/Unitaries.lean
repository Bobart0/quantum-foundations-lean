import QuantumFoundations.Selectors.Defs

/-!
**FR.** # Selectors — boîte à outils unitaire (support de S3)

Unitaires fixant un vecteur donné d'une base orthonormée `b`, plus la
transitivité unitaire sur la sphère unité, utilisés par la preuve de
`covariant_iff_tSelector` dans `Classification.lean`. Aucun énoncé public de
ce module ne figure dans la liste des jalons S1–S5 : c'est un détail
d'implémentation de S3.

Deux familles d'unitaires, chacune construite via `OrthonormalBasis.equiv` :

- **réflexions** `reflIso b m` : fixe `b m` au signe près (`-b m`), fixe tout
  le reste de la base. Nécessite une base auxiliaire `reflAt b m` (signe
  changé en `m`) car aucune permutation ne peut réaliser un changement de
  signe.
- **transpositions** `swapIso b i j` : échange `b i` et `b j`, fixe le reste ;
  se construit directement sur la MÊME base `b` des deux côtés
  (`b.equiv b (Equiv.swap i j)`), d'où `swapIso_symm` immédiat via
  `OrthonormalBasis.equiv_symm` — pas besoin de l'argument d'involution par
  extension linéaire requis pour `reflIso_symm_apply`.

**EN.** # Selectors — unitary toolbox (support for S3)

Unitaries fixing a given vector of an orthonormal basis `b`, plus unitary
transitivity on the unit sphere, used by the proof of
`covariant_iff_tSelector` in `Classification.lean`. No public statement of
this module appears in the S1–S5 milestone list: it is an S3 implementation
detail.

Two families of unitaries, each built via `OrthonormalBasis.equiv`:

- **reflections** `reflIso b m`: fixes `b m` up to sign (`-b m`), fixes
  everything else in the basis. Requires an auxiliary basis `reflAt b m`
  (sign flipped at `m`) since no permutation can realize a sign change.
- **transpositions** `swapIso b i j`: swaps `b i` and `b j`, fixes the rest;
  built directly on the SAME basis `b` on both sides
  (`b.equiv b (Equiv.swap i j)`), hence `swapIso_symm` is immediate via
  `OrthonormalBasis.equiv_symm` — no need for the linear-extension involution
  argument required for `reflIso_symm_apply`.
-/

namespace QuantumFoundations.Selector

open scoped InnerProductSpace
open Gleason
open QuantumFoundations.Uhlhorn (one_le_of_norm_eq_one)

noncomputable section

variable {n : ℕ}

private theorem orthonormal_reflFamily (b : OrthonormalBasis (Fin n) ℂ (H n)) (m : Fin n) :
    Orthonormal ℂ (fun i => if i = m then -(b i : H n) else (b i : H n)) := by
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hi : i = m <;> by_cases hj : j = m <;> simp [hi, hj, b.inner_eq_ite, Ne.symm]

private theorem span_reflFamily (b : OrthonormalBasis (Fin n) ℂ (H n)) (m : Fin n) :
    (⊤ : Submodule ℂ (H n)) ≤ Submodule.span ℂ
      (Set.range (fun i => if i = m then -(b i : H n) else (b i : H n))) := by
  rw [← b.toBasis.span_eq, Submodule.span_le]
  rintro x ⟨i, rfl⟩
  rw [OrthonormalBasis.coe_toBasis]
  by_cases hi : i = m
  · have hfm : (fun i => if i = m then -(b i : H n) else (b i : H n)) m = -(b m : H n) := by simp
    have hmem_neg : (-(b m : H n)) ∈ Submodule.span ℂ
        (Set.range (fun i => if i = m then -(b i : H n) else (b i : H n))) := by
      rw [← hfm]; exact Submodule.subset_span ⟨m, rfl⟩
    have hbi : (b i : H n) = -(-(b m : H n)) := by rw [hi, neg_neg]
    rw [hbi]
    exact Submodule.neg_mem _ hmem_neg
  · exact Submodule.subset_span ⟨i, by simp [hi]⟩

/-- **FR.** Base auxiliaire portant le signe changé en `m` : engendre le même
sous-espace `⊤` que `b` (`neg_mem`), donc c'est une base orthonormée légitime.

**EN.** Auxiliary basis carrying the sign flipped at `m`: spans the same `⊤`
as `b` (`neg_mem`), hence is a legitimate orthonormal basis. -/
private noncomputable def reflAt (b : OrthonormalBasis (Fin n) ℂ (H n)) (m : Fin n) :
    OrthonormalBasis (Fin n) ℂ (H n) :=
  OrthonormalBasis.mk (orthonormal_reflFamily b m) (span_reflFamily b m)

/-- **FR.** La réflexion de signe en `m` : fixe `b i` pour `i ≠ m`, envoie
`b m` sur `-(b m)`.

**EN.** The sign reflection at `m`: fixes `b i` for `i ≠ m`, sends `b m` to
`-(b m)`. -/
noncomputable def reflIso (b : OrthonormalBasis (Fin n) ℂ (H n)) (m : Fin n) : H n ≃ₗᵢ[ℂ] H n :=
  b.equiv (reflAt b m) (Equiv.refl (Fin n))

theorem reflIso_apply (b : OrthonormalBasis (Fin n) ℂ (H n)) (m i : Fin n) :
    reflIso b m (b i) = if i = m then -(b i : H n) else (b i : H n) := by
  unfold reflIso
  rw [OrthonormalBasis.equiv_apply_basis]
  show (reflAt b m) (Equiv.refl (Fin n) i) = _
  unfold reflAt
  rw [OrthonormalBasis.coe_mk]
  simp

private theorem reflIso_involutive_basis (b : OrthonormalBasis (Fin n) ℂ (H n)) (m i : Fin n) :
    reflIso b m (reflIso b m (b i)) = b i := by
  rw [reflIso_apply]
  by_cases hi : i = m
  · subst hi
    rw [if_pos rfl, map_neg, reflIso_apply, if_pos rfl, neg_neg]
  · rw [if_neg hi, reflIso_apply, if_neg hi]

private theorem reflIso_involutive (b : OrthonormalBasis (Fin n) ℂ (H n)) (m : Fin n) :
    (reflIso b m).toLinearMap ∘ₗ (reflIso b m).toLinearMap = LinearMap.id := by
  apply b.toBasis.ext
  intro i
  simp only [LinearMap.comp_apply, LinearMap.id_apply, OrthonormalBasis.coe_toBasis]
  exact reflIso_involutive_basis b m i

/-- **FR.** `reflIso b m` est sa propre inverse (une réflexion est une
involution) : agrément sur la base `b` (`reflIso_involutive`), remonté via
`LinearIsometryEquiv.symm_apply_apply`, sans devoir montrer
`(reflIso b m).symm = reflIso b m` comme égalité d'équivalences.

**EN.** `reflIso b m` is its own inverse (a reflection is an involution):
agreement on the basis `b` (`reflIso_involutive`), lifted via
`LinearIsometryEquiv.symm_apply_apply`, without having to show
`(reflIso b m).symm = reflIso b m` as an equality of equivalences. -/
theorem reflIso_symm_apply (b : OrthonormalBasis (Fin n) ℂ (H n)) (m : Fin n) (x : H n) :
    (reflIso b m).symm x = reflIso b m x := by
  have hxx : reflIso b m (reflIso b m x) = x := by
    have h := reflIso_involutive b m
    have hx := congrArg (· x) h
    simpa using hx
  calc (reflIso b m).symm x = (reflIso b m).symm (reflIso b m (reflIso b m x)) := by rw [hxx]
    _ = reflIso b m x := (reflIso b m).symm_apply_apply _

/-- **FR.** La transposition `i ↔ j` : fixe `b k` pour `k ∉ {i,j}`, échange
`b i` et `b j`.

**EN.** The transposition `i ↔ j`: fixes `b k` for `k ∉ {i,j}`, swaps `b i`
and `b j`. -/
noncomputable def swapIso (b : OrthonormalBasis (Fin n) ℂ (H n)) (i j : Fin n) : H n ≃ₗᵢ[ℂ] H n :=
  b.equiv b (Equiv.swap i j)

theorem swapIso_apply (b : OrthonormalBasis (Fin n) ℂ (H n)) (i j k : Fin n) :
    swapIso b i j (b k) = b (Equiv.swap i j k) :=
  OrthonormalBasis.equiv_apply_basis b b (Equiv.swap i j) k

theorem swapIso_symm (b : OrthonormalBasis (Fin n) ℂ (H n)) (i j : Fin n) :
    (swapIso b i j).symm = swapIso b i j := by
  unfold swapIso
  rw [OrthonormalBasis.equiv_symm, Equiv.symm_swap]

/-- **FR.** Adjoint d'une isométrie linéaire = son inverse : fait général,
utilisé pour faire passer `reflIso`/`swapIso` de l'autre côté d'un produit
scalaire.

**EN.** Adjoint of a linear isometry = its inverse: general fact, used to
move `reflIso`/`swapIso` to the other side of an inner product. -/
theorem adjoint_apply (U : H n ≃ₗᵢ[ℂ] H n) (x y : H n) : ⟪x, U y⟫_ℂ = ⟪U.symm x, y⟫_ℂ := by
  conv_lhs => rw [← U.apply_symm_apply x]
  rw [U.inner_map_map]

/-- **FR.** Transitivité unitaire sur la sphère unité : deux vecteurs
unitaires quelconques sont reliés par une isométrie (recollement de deux
extensions en base orthonormée sur le même indice `i₀`).

**EN.** Unitary transitivity on the unit sphere: any two unit vectors are
related by an isometry (gluing two orthonormal-basis extensions at the same
index `i₀`). -/
theorem exists_isometry_apply_eq {ψ φ : H n} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    ∃ U : H n ≃ₗᵢ[ℂ] H n, U ψ = φ := by
  have hn1 : 1 ≤ n := one_le_of_norm_eq_one hψ
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_extension_complex hn1 (fun _ : Fin 1 => ψ)
    (by rw [orthonormal_iff_ite]; intro i j; fin_cases i; fin_cases j; simp [hψ])
  obtain ⟨b', hb'⟩ := exists_orthonormalBasis_extension_complex hn1 (fun _ : Fin 1 => φ)
    (by rw [orthonormal_iff_ite]; intro i j; fin_cases i; fin_cases j; simp [hφ])
  refine ⟨b.equiv b' (Equiv.refl (Fin n)), ?_⟩
  have heq := OrthonormalBasis.equiv_apply_basis b b' (Equiv.refl (Fin n)) (Fin.castLE hn1 0)
  rw [hb 0, Equiv.refl_apply, hb' 0] at heq
  exact heq

end
end QuantumFoundations.Selector
