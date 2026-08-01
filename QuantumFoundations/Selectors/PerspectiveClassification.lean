import QuantumFoundations.Selectors.PerspectiveStabilizer

/-!
**FR.** # Selectors — Module B, classification des densités cellwise-invariantes

Classifie les opérateurs densité invariants sous
`PerspectiveCellwiseStabilizer D` (`PerspectiveStabilizer.lean`) : ce sont
exactement les opérateurs "bloc-scalaires" `blockScalarOperator D t`, qui
agissent comme `t c • id` sur chaque cellule `c ∈ D.cells`, pour une famille
de poids `t` positive et de trace `1` (`IsBlockDensityWeights`).

La preuve n'utilise PAS le lemme de Schur : à la place, les témoins
`reflIso`/`swapIso` (déjà présents dans `Unitaries.lean`, réutilisés tels
quels dès qu'un vecteur de base choisi tombe dans la cellule visée) donnent
directement :
- tout vecteur unitaire `v` d'une cellule est vecteur propre de tout `ρ`
  symétrique cellwise-invariant, de valeur propre réelle `⟨v,ρv⟩`
  (`eigenvector_of_cellwiseInvariant`) ;
- deux vecteurs unitaires orthogonaux d'UNE MÊME cellule ont la même valeur
  propre (`eigenvalue_const_of_cellwiseInvariant`), via l'échange `swapIso`.

Ces deux faits, combinés par décomposition de Gram-Schmidt (au lieu d'une
base orthonormée complète de la cellule), donnent que `ρ` restreint à toute
cellule est un multiple scalaire réel de l'identité
(`cellRestriction_eq_scalar`), puis, sommé sur les cellules via la
résolution de l'identité `sum_projL_cells_eq_id`, le théorème principal
`cellwiseInvariant_density_iff_blockScalar`.

**EN.** # Selectors — Module B, classification of cellwise-invariant densities

Classifies the density operators invariant under
`PerspectiveCellwiseStabilizer D` (`PerspectiveStabilizer.lean`): they are
exactly the "block-scalar" operators `blockScalarOperator D t`, acting as
`t c • id` on each cell `c ∈ D.cells`, for a family of weights `t` that is
nonnegative and has trace `1` (`IsBlockDensityWeights`).

The proof does NOT use Schur's lemma: instead, the `reflIso`/`swapIso`
witnesses (already present in `Unitaries.lean`, reused as-is whenever a
chosen basis vector happens to land in the target cell) give directly:
- any unit vector `v` in a cell is an eigenvector of any symmetric,
  cellwise-invariant `ρ`, with real eigenvalue `⟨v,ρv⟩`
  (`eigenvector_of_cellwiseInvariant`);
- two orthogonal unit vectors of the SAME cell share the same eigenvalue
  (`eigenvalue_const_of_cellwiseInvariant`), via the `swapIso` exchange.

These two facts, combined through a Gram-Schmidt decomposition (rather than
a full orthonormal basis of the cell), show that `ρ` restricted to any cell
is a real scalar multiple of the identity (`cellRestriction_eq_scalar`),
then, summed over cells via the resolution of the identity
`sum_projL_cells_eq_id`, the main theorem
`cellwiseInvariant_density_iff_blockScalar`.
-/

namespace QuantumFoundations.Selector

open scoped InnerProductSpace
open Gleason
open QuantumFoundations.BornRule
open scoped Classical

noncomputable section

variable {n : ℕ}

theorem reflIso_apply_general (b : OrthonormalBasis (Fin n) ℂ (H n)) (m : Fin n) (x : H n) :
    reflIso b m x = x - (2 * ⟪(b m : H n), x⟫_ℂ) • (b m : H n) := by
  have key : (reflIso b m).toLinearMap
      = LinearMap.id - (2:ℂ) • (InnerProductSpace.rankOne ℂ (b m : H n) (b m : H n) : H n →ₗ[ℂ] H n) := by
    apply b.toBasis.ext
    intro i
    rw [OrthonormalBasis.coe_toBasis]
    show reflIso b m (b i) = _
    rw [reflIso_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply]
    have hrk : (InnerProductSpace.rankOne ℂ (b m : H n) (b m : H n) : H n →ₗ[ℂ] H n) (b i)
        = ⟪(b m : H n), (b i : H n)⟫_ℂ • (b m : H n) := InnerProductSpace.rankOne_apply _ _ _
    rw [hrk]
    by_cases him : i = m
    · subst him
      have hself : ⟪(b i : H n), (b i : H n)⟫_ℂ = 1 := by
        rw [b.inner_eq_ite, if_pos rfl]
      rw [if_pos rfl, hself]
      module
    · rw [if_neg him]
      have hz : ⟪(b m : H n), (b i : H n)⟫_ℂ = 0 := by
        rw [b.inner_eq_ite, if_neg (Ne.symm him)]
      rw [hz]
      module
  have h2 := LinearMap.congr_fun key x
  simpa [mul_smul] using h2

theorem swapIso_fixes_of_zero (b : OrthonormalBasis (Fin n) ℂ (H n)) (i j : Fin n) {x : H n}
    (hi : ⟪(b i : H n), x⟫_ℂ = 0) (hj : ⟪(b j : H n), x⟫_ℂ = 0) :
    swapIso b i j x = x := by
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum]
  conv_rhs => rw [← b.sum_repr x]
  apply Finset.sum_congr rfl
  intro l _
  rw [map_smul, swapIso_apply]
  rw [b.repr_apply_apply]
  by_cases hli : l = i
  · subst hli
    rw [Equiv.swap_apply_left, hi]
    simp
  by_cases hlj : l = j
  · subst hlj
    rw [Equiv.swap_apply_right, hj]
    simp
  rw [Equiv.swap_apply_of_ne_of_ne hli hlj]

/-- `reflIso b m` fixes every cell setwise, and preserves `c`, as soon as `b m ∈ c`. -/
theorem reflIso_mem_cellwiseStabilizer {D : Perspective n} {b : OrthonormalBasis (Fin n) ℂ (H n)}
    {m : Fin n} {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) (hbm : b m ∈ c) :
    reflIso b m ∈ PerspectiveCellwiseStabilizer D := by
  intro c' hc'
  by_cases heq : c' = c
  · rw [heq]
    apply Submodule.ext
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show reflIso b m y ∈ c
      rw [reflIso_apply_general]
      exact Submodule.sub_mem _ hy (Submodule.smul_mem _ _ hbm)
    · intro hx
      refine ⟨reflIso b m x, ?_, ?_⟩
      · rw [reflIso_apply_general]
        exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _ hbm)
      · show reflIso b m (reflIso b m x) = x
        rw [show reflIso b m (reflIso b m x) = reflIso b m ((reflIso b m).symm x) from
          congrArg (reflIso b m) (reflIso_symm_apply b m x).symm]
        exact (reflIso b m).apply_symm_apply x
  · have hortho : c' ≤ c ᗮ := D.ortho c' hc' c hc heq
    apply Submodule.ext
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show reflIso b m y ∈ c'
      have hzero : ⟪(b m : H n), y⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal c y).mp (hortho hy) (b m) hbm
      rw [reflIso_apply_general, hzero]
      simpa using hy
    · intro hx
      have hzero : ⟪(b m : H n), x⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal c x).mp (hortho hx) (b m) hbm
      refine ⟨x, hx, ?_⟩
      show reflIso b m x = x
      rw [reflIso_apply_general, hzero]
      simp

end

noncomputable section

theorem swapIso_apply_general (b : OrthonormalBasis (Fin n) ℂ (H n)) {i j : Fin n} (hij : i ≠ j)
    (x : H n) :
    swapIso b i j x
      = x + ⟪(b i : H n), x⟫_ℂ • ((b j : H n) - (b i : H n))
        + ⟪(b j : H n), x⟫_ℂ • ((b i : H n) - (b j : H n)) := by
  have key : (swapIso b i j).toLinearMap = LinearMap.id
      + (InnerProductSpace.rankOne ℂ ((b j : H n) - (b i : H n)) (b i : H n) : H n →ₗ[ℂ] H n)
      + (InnerProductSpace.rankOne ℂ ((b i : H n) - (b j : H n)) (b j : H n) : H n →ₗ[ℂ] H n) := by
    apply b.toBasis.ext
    intro l
    rw [OrthonormalBasis.coe_toBasis]
    show swapIso b i j (b l) = _
    rw [swapIso_apply]
    simp only [LinearMap.add_apply, LinearMap.id_apply]
    have hrk1 : (InnerProductSpace.rankOne ℂ ((b j : H n) - (b i : H n)) (b i : H n)
        : H n →ₗ[ℂ] H n) (b l) = ⟪(b i : H n), (b l : H n)⟫_ℂ • ((b j : H n) - (b i : H n)) :=
      InnerProductSpace.rankOne_apply _ _ _
    have hrk2 : (InnerProductSpace.rankOne ℂ ((b i : H n) - (b j : H n)) (b j : H n)
        : H n →ₗ[ℂ] H n) (b l) = ⟪(b j : H n), (b l : H n)⟫_ℂ • ((b i : H n) - (b j : H n)) :=
      InnerProductSpace.rankOne_apply _ _ _
    rw [hrk1, hrk2]
    by_cases hli : l = i
    · rw [hli, Equiv.swap_apply_left, b.inner_eq_ite, b.inner_eq_ite, if_pos rfl,
        if_neg (Ne.symm hij)]
      module
    · by_cases hlj : l = j
      · rw [hlj, Equiv.swap_apply_right, b.inner_eq_ite, b.inner_eq_ite, if_neg hij,
          if_pos rfl]
        module
      · rw [Equiv.swap_apply_of_ne_of_ne hli hlj, b.inner_eq_ite, b.inner_eq_ite,
          if_neg (Ne.symm hli), if_neg (Ne.symm hlj)]
        module
  have h2 := LinearMap.congr_fun key x
  simpa [smul_sub] using h2

end

theorem swapIso_mem_cellwiseStabilizer {D : Perspective n} {b : OrthonormalBasis (Fin n) ℂ (H n)}
    {i j : Fin n} (hij : i ≠ j) {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) (hbi : b i ∈ c)
    (hbj : b j ∈ c) : swapIso b i j ∈ PerspectiveCellwiseStabilizer D := by
  intro c' hc'
  by_cases heq : c' = c
  · rw [heq]
    apply Submodule.ext
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show swapIso b i j y ∈ c
      rw [swapIso_apply_general b hij]
      exact Submodule.add_mem _ (Submodule.add_mem _ hy
        (Submodule.smul_mem _ _ (Submodule.sub_mem _ hbj hbi)))
        (Submodule.smul_mem _ _ (Submodule.sub_mem _ hbi hbj))
    · intro hx
      refine ⟨swapIso b i j x, ?_, ?_⟩
      · rw [swapIso_apply_general b hij]
        exact Submodule.add_mem _ (Submodule.add_mem _ hx
          (Submodule.smul_mem _ _ (Submodule.sub_mem _ hbj hbi)))
          (Submodule.smul_mem _ _ (Submodule.sub_mem _ hbi hbj))
      · show swapIso b i j (swapIso b i j x) = x
        rw [show swapIso b i j (swapIso b i j x) = swapIso b i j ((swapIso b i j).symm x) from
          congrArg (swapIso b i j) (by rw [swapIso_symm])]
        exact (swapIso b i j).apply_symm_apply x
  · have hortho : c' ≤ c ᗮ := D.ortho c' hc' c hc heq
    apply Submodule.ext
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show swapIso b i j y ∈ c'
      have hzi : ⟪(b i : H n), y⟫_ℂ = 0 := (Submodule.mem_orthogonal c y).mp (hortho hy) (b i) hbi
      have hzj : ⟪(b j : H n), y⟫_ℂ = 0 := (Submodule.mem_orthogonal c y).mp (hortho hy) (b j) hbj
      rw [swapIso_apply_general b hij, hzi, hzj]
      simpa using hy
    · intro hx
      have hzi : ⟪(b i : H n), x⟫_ℂ = 0 := (Submodule.mem_orthogonal c x).mp (hortho hx) (b i) hbi
      have hzj : ⟪(b j : H n), x⟫_ℂ = 0 := (Submodule.mem_orthogonal c x).mp (hortho hx) (b j) hbj
      refine ⟨x, hx, ?_⟩
      show swapIso b i j x = x
      rw [swapIso_apply_general b hij, hzi, hzj]
      simp

noncomputable section

theorem exists_global_single (v : H n) (hv : ‖v‖ = 1) :
    ∃ (b : OrthonormalBasis (Fin n) ℂ (H n)) (m : Fin n), b m = v := by
  have hn1 : 1 ≤ n := QuantumFoundations.Uhlhorn.one_le_of_norm_eq_one hv
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_extension_complex hn1 (fun _ : Fin 1 => v)
    (by rw [orthonormal_iff_ite]; intro i j; fin_cases i; fin_cases j; simp [hv])
  exact ⟨b, Fin.castLE hn1 0, by have := hb 0; simpa using this⟩

theorem exists_global_pair (hn2 : 2 ≤ n) (v w : H n) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (horth : ⟪v, w⟫_ℂ = 0) :
    ∃ (b : OrthonormalBasis (Fin n) ℂ (H n)) (i j : Fin n), i ≠ j ∧ b i = v ∧ b j = w := by
  have hwv : ⟪w, v⟫_ℂ = 0 := by rw [← inner_conj_symm, horth]; simp
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_extension_complex hn2
      (fun k : Fin 2 => if k = 0 then v else w)
    (by
      rw [orthonormal_iff_ite]
      intro i j
      fin_cases i <;> fin_cases j <;> simp [hv, hw, horth, hwv])
  refine ⟨b, Fin.castLE hn2 0, Fin.castLE hn2 1, by simp [Fin.ext_iff], ?_, ?_⟩
  · have := hb 0; simpa using this
  · have := hb 1; simpa using this

/-- Natural output of a single-vector reflection witness: for `v` a unit vector in
some cell, and `w` fixed by the reflection at `v` (i.e. `⟪v,w⟫ = 0`), the entry
`⟨v, ρ w⟩` vanishes for any `ρ` invariant under the cellwise stabilizer. -/
theorem inner_reflected_apply_eq_zero {D : Perspective n} {ρ : H n →ₗ[ℂ] H n}
    (hinv : IsInvariantUnder (PerspectiveCellwiseStabilizer D) ρ) {c : Submodule ℂ (H n)}
    (hc : c ∈ D.cells) {v w : H n} (hv : v ∈ c) (hvnorm : ‖v‖ = 1)
    (hvw : ⟪v, w⟫_ℂ = 0) : ⟪v, ρ w⟫_ℂ = 0 := by
  obtain ⟨b, m, hbm⟩ := exists_global_single v hvnorm
  set U := reflIso b m with hU_def
  have hUmem : U ∈ PerspectiveCellwiseStabilizer D := by
    rw [hU_def]; exact reflIso_mem_cellwiseStabilizer hc (hbm ▸ hv)
  have hfix : U w = w := by rw [hU_def, reflIso_apply_general, hbm, hvw]; simp
  have hsymmfix : U.symm w = w := by
    rw [hU_def, reflIso_symm_apply, reflIso_apply_general, hbm, hvw]; simp
  have hfixed : ρ w = U (ρ w) := by
    have heq := hinv U hUmem
    have happ : U (ρ (U.symm w)) = ρ w := by
      have h2 := LinearMap.congr_fun heq w
      simpa using h2
    rw [hsymmfix] at happ
    exact happ.symm
  have hself : ⟪v, v⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hvnorm]; norm_num
  have hUsymmv : U.symm v = -v := by
    rw [hU_def, reflIso_symm_apply, reflIso_apply_general, hbm, hself]; module
  have hflip : ⟪v, U (ρ w)⟫_ℂ = ⟪U.symm v, ρ w⟫_ℂ := adjoint_apply U v (ρ w)
  rw [hUsymmv, inner_neg_left] at hflip
  have h1 : ⟪v, ρ w⟫_ℂ = ⟪v, U (ρ w)⟫_ℂ := by rw [← hfixed]
  rw [hflip] at h1
  linear_combination h1 / 2

private theorem sum_inner_smul_self (b : OrthonormalBasis (Fin n) ℂ (H n)) (x : H n) :
    ∑ i, ⟪b i, x⟫_ℂ • b i = x := by
  conv_rhs => rw [← b.sum_repr x]
  apply Finset.sum_congr rfl
  intro i _
  rw [b.repr_apply_apply]

/-- Eigenvector fact: a unit vector `v` in a cell `c` is an eigenvector of any
symmetric, cellwise-invariant `ρ`, with real eigenvalue `⟨v,ρv⟩`. -/
theorem eigenvector_of_cellwiseInvariant {D : Perspective n} {ρ : H n →ₗ[ℂ] H n}
    (hsymm : LinearMap.IsSymmetric ρ) (hinv : IsInvariantUnder (PerspectiveCellwiseStabilizer D) ρ)
    {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) {v : H n} (hv : v ∈ c) (hvnorm : ‖v‖ = 1) :
    ρ v = ⟪v, ρ v⟫_ℂ • v := by
  obtain ⟨b, m, hbm⟩ := exists_global_single v hvnorm
  have hexp : ∑ l, ⟪b l, ρ v⟫_ℂ • b l = ρ v := sum_inner_smul_self b (ρ v)
  have hcollapse : ∑ l, ⟪b l, ρ v⟫_ℂ • b l = ⟪(b m : H n), ρ v⟫_ℂ • (b m : H n) := by
    apply Finset.sum_eq_single m
    · intro l _ hlm
      have hlv : ⟪v, (b l : H n)⟫_ℂ = 0 := by
        rw [← hbm, b.inner_eq_ite, if_neg (Ne.symm hlm)]
      have hzero : ⟪b l, ρ v⟫_ℂ = 0 := by
        have h1 : ⟪(b l : H n), ρ v⟫_ℂ = ⟪ρ (b l : H n), v⟫_ℂ := (hsymm (b l) v).symm
        have h2 : ⟪ρ (b l : H n), v⟫_ℂ = (starRingEnd ℂ) ⟪v, ρ (b l : H n)⟫_ℂ := (inner_conj_symm _ _).symm
        have h3 : ⟪v, ρ (b l : H n)⟫_ℂ = 0 :=
          inner_reflected_apply_eq_zero hinv hc hv hvnorm hlv
        rw [h1, h2, h3]; simp
      rw [hzero, zero_smul]
    · intro h; exact absurd (Finset.mem_univ m) h
  rw [hcollapse, hbm] at hexp
  exact hexp.symm

end

noncomputable section

/-- Constant-eigenvalue fact: two orthonormal unit vectors in the SAME cell give
the same eigenvalue, for any symmetric, cellwise-invariant `ρ`. -/
theorem eigenvalue_const_of_cellwiseInvariant {D : Perspective n} {ρ : H n →ₗ[ℂ] H n}
    (hsymm : LinearMap.IsSymmetric ρ) (hinv : IsInvariantUnder (PerspectiveCellwiseStabilizer D) ρ)
    {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) {v w : H n} (hv : v ∈ c) (hw : w ∈ c)
    (hvnorm : ‖v‖ = 1) (hwnorm : ‖w‖ = 1) (hvw : ⟪v, w⟫_ℂ = 0) :
    ⟪v, ρ v⟫_ℂ = ⟪w, ρ w⟫_ℂ := by
  have hn2 : 2 ≤ n := by
    have hvw_ne : v ≠ w := by
      intro h
      rw [h] at hvw
      have : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hwnorm]; norm_num
      rw [this] at hvw; norm_num at hvw
    have hfr : (2 : ℕ) ≤ Module.finrank ℂ (H n) := by
      have hindep : LinearIndependent ℂ ![v, w] := by
        rw [LinearIndependent.pair_iff]
        intro s t hst
        have h1 : ⟪v, s • v + t • w⟫_ℂ = 0 := by rw [hst]; simp
        have h2 : ⟪v, v⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hvnorm]; norm_num
        rw [inner_add_right, inner_smul_right, inner_smul_right, h2, hvw, mul_one, mul_zero,
          add_zero] at h1
        refine ⟨by simpa using h1, ?_⟩
        have h3 : ⟪w, s • v + t • w⟫_ℂ = 0 := by rw [hst]; simp
        have h4 : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hwnorm]; norm_num
        have h5 : ⟪w, v⟫_ℂ = 0 := by rw [← inner_conj_symm, hvw]; simp
        rw [inner_add_right, inner_smul_right, inner_smul_right, h4, h5, mul_one, mul_zero,
          zero_add] at h3
        simpa using h3
      have := hindep.fintype_card_le_finrank
      simpa using this
    have hnn : Module.finrank ℂ (H n) = n := by simp
    omega
  obtain ⟨b, i, j, hij, hbi, hbj⟩ := exists_global_pair hn2 v w hvnorm hwnorm hvw
  set U := swapIso b i j with hU_def
  have hUmem : U ∈ PerspectiveCellwiseStabilizer D := by
    rw [hU_def]; exact swapIso_mem_cellwiseStabilizer hij hc (hbi ▸ hv) (hbj ▸ hw)
  have hUv : U v = w := by rw [hU_def, ← hbi, ← hbj, swapIso_apply, Equiv.swap_apply_left]
  have hUw : U w = v := by rw [hU_def, ← hbi, ← hbj, swapIso_apply, Equiv.swap_apply_right]
  have hUsymmU : U.symm = U := by rw [hU_def, swapIso_symm]
  have hUsymmv : U.symm v = w := by rw [hUsymmU]; exact hUv
  have heq := hinv U hUmem
  have happ : U (ρ (U.symm v)) = ρ v := by
    have h2 := LinearMap.congr_fun heq v
    simpa using h2
  rw [hUsymmv] at happ
  have hρw : ρ w = ⟪w, ρ w⟫_ℂ • w := eigenvector_of_cellwiseInvariant hsymm hinv hc hw hwnorm
  rw [hρw, map_smul, hUw] at happ
  have hρv : ρ v = ⟪v, ρ v⟫_ℂ • v := eigenvector_of_cellwiseInvariant hsymm hinv hc hv hvnorm
  rw [hρv] at happ
  have hv_ne : v ≠ 0 := by
    intro h; rw [h, norm_zero] at hvnorm; norm_num at hvnorm
  have := smul_left_injective ℂ hv_ne happ.symm
  exact_mod_cast this

end

noncomputable section

private theorem cells_sup_eq_top (D : Perspective n) : D.cells.sup id = ⊤ := by
  rw [Finset.sup_eq_sSup_image, Set.image_id]
  exact D.span

/-- Resolution of the identity over a perspective's cells. -/
theorem sum_projL_cells_eq_id (D : Perspective n) :
    ∑ c ∈ D.cells, projL c = LinearMap.id := by
  have h := Gleason.projL_sup_of_pairwise_isOrtho D.cells id
    (fun c hc c' hc' hne => Submodule.isOrtho_iff_le.mpr (D.ortho c hc c' hc' hne))
  simp only [id_eq] at h
  rw [cells_sup_eq_top D] at h
  rw [← h]
  apply LinearMap.ext
  intro x
  show (⊤ : Submodule ℂ (H n)).starProjection x = x
  exact Submodule.starProjection_eq_self_iff.mpr Submodule.mem_top

end

noncomputable section

/-- The block-scalar operator for weights `t`: on each cell `c`, act as `t c`
times the identity. Total definition (junk value for arbitrary `t`); validity
as a density is `blockScalarOperator_isDensity`. -/
def blockScalarOperator (D : Perspective n) (t : Submodule ℂ (H n) → ℝ) : H n →ₗ[ℂ] H n :=
  ∑ c ∈ D.cells, (t c : ℂ) • projL c

/-- A finite family of nonnegative weights on `D`'s cells whose block-scalar
operator has trace `1`. -/
def IsBlockDensityWeights (D : Perspective n) (t : Submodule ℂ (H n) → ℝ) : Prop :=
  (∀ c ∈ D.cells, 0 ≤ t c) ∧ LinearMap.trace ℂ (H n) (blockScalarOperator D t) = 1

theorem blockScalarOperator_isSymmetric (D : Perspective n) (t : Submodule ℂ (H n) → ℝ) :
    LinearMap.IsSymmetric (blockScalarOperator D t) := by
  intro x y
  show ⟪(∑ c ∈ D.cells, (t c : ℂ) • projL c) x, y⟫_ℂ
    = ⟪x, (∑ c ∈ D.cells, (t c : ℂ) • projL c) y⟫_ℂ
  simp_rw [LinearMap.sum_apply, LinearMap.smul_apply, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  exact Submodule.starProjection_isSymmetric c x y

theorem blockScalarOperator_nonneg (D : Perspective n) {t : Submodule ℂ (H n) → ℝ}
    (ht : ∀ c ∈ D.cells, 0 ≤ t c) (x : H n) :
    0 ≤ (⟪blockScalarOperator D t x, x⟫_ℂ).re := by
  show 0 ≤ (⟪(∑ c ∈ D.cells, (t c : ℂ) • projL c) x, x⟫_ℂ).re
  simp_rw [LinearMap.sum_apply, LinearMap.smul_apply, sum_inner, inner_smul_left,
    Complex.conj_ofReal]
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro c hc
  rw [Complex.re_ofReal_mul]
  exact mul_nonneg (ht c hc) (Submodule.re_inner_starProjection_nonneg c x)

theorem blockScalarOperator_isDensity (D : Perspective n) {t : Submodule ℂ (H n) → ℝ}
    (ht : IsBlockDensityWeights D t) : IsDensityOperator (blockScalarOperator D t) :=
  ⟨blockScalarOperator_isSymmetric D t, blockScalarOperator_nonneg D ht.1, ht.2⟩

private theorem conj_projL'' (U : H n ≃ₗᵢ[ℂ] H n) (A : Submodule ℂ (H n)) :
    U.toLinearMap ∘ₗ projL A ∘ₗ U.symm.toLinearMap = projL (A.map U.toLinearMap) := by
  apply LinearMap.ext
  intro x
  exact (Submodule.starProjection_map_apply U A x).symm

theorem blockScalarOperator_isInvariantUnder_cellwiseStabilizer (D : Perspective n)
    (t : Submodule ℂ (H n) → ℝ) :
    IsInvariantUnder (PerspectiveCellwiseStabilizer D) (blockScalarOperator D t) := by
  intro U hU
  show U.toLinearMap ∘ₗ (∑ c ∈ D.cells, (t c : ℂ) • projL c) ∘ₗ U.symm.toLinearMap
    = ∑ c ∈ D.cells, (t c : ℂ) • projL c
  have hterm : ∀ c ∈ D.cells, U.toLinearMap ∘ₗ ((t c : ℂ) • projL c) ∘ₗ U.symm.toLinearMap
      = (t c : ℂ) • projL c := by
    intro c hc
    have heq2 : U.toLinearMap ∘ₗ ((t c : ℂ) • projL c) ∘ₗ U.symm.toLinearMap
        = (t c : ℂ) • (U.toLinearMap ∘ₗ projL c ∘ₗ U.symm.toLinearMap) := by
      apply LinearMap.ext
      intro x
      show U ((t c : ℂ) • projL c (U.symm x)) = (t c : ℂ) • U (projL c (U.symm x))
      rw [map_smul]
    rw [heq2, conj_projL'', hU c hc]
  apply LinearMap.ext
  intro x
  show U ((∑ c ∈ D.cells, (t c : ℂ) • projL c) (U.symm x)) = (∑ c ∈ D.cells, (t c : ℂ) • projL c) x
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro c hc
  have := LinearMap.congr_fun (hterm c hc) x
  simpa using this

end

private theorem inner_self_real {ρ : H n →ₗ[ℂ] H n}
    (hsymm : LinearMap.IsSymmetric ρ) (v : H n) :
    ((⟪v, ρ v⟫_ℂ).re : ℂ) = ⟪v, ρ v⟫_ℂ := by
  have h1 : ⟪ρ v, v⟫_ℂ = ⟪v, ρ v⟫_ℂ := hsymm v v
  have h2 : ⟪ρ v, v⟫_ℂ = (starRingEnd ℂ) ⟪v, ρ v⟫_ℂ := (inner_conj_symm _ _).symm
  rw [h2] at h1
  exact Complex.conj_eq_iff_re.mp h1

private theorem exists_unit_mem_of_ne_bot {c : Submodule ℂ (H n)} (hne : c ≠ ⊥) :
    ∃ v : H n, v ∈ c ∧ ‖v‖ = 1 := by
  obtain ⟨x0, hx0mem, hx0ne⟩ := c.ne_bot_iff.mp hne
  refine ⟨((‖x0‖⁻¹ : ℝ) : ℂ) • x0, Submodule.smul_mem _ _ hx0mem, ?_⟩
  rw [norm_smul]
  simp [norm_ne_zero_iff.mpr hx0ne]

/-- For a symmetric, cellwise-invariant `ρ`, the restriction of `ρ` to a cell
`c` is a real scalar multiple of the identity on `c`. -/
theorem cellRestriction_eq_scalar {D : Perspective n} {ρ : H n →ₗ[ℂ] H n}
    (hsymm : LinearMap.IsSymmetric ρ) (hinv : IsInvariantUnder (PerspectiveCellwiseStabilizer D) ρ)
    {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
    ∃ t : ℝ, ∀ x ∈ c, ρ x = (t : ℂ) • x := by
  have hne : c ≠ ⊥ := D.nz c hc
  obtain ⟨x0, hx0mem, hx0ne⟩ := c.ne_bot_iff.mp hne
  set v0 : H n := ((‖x0‖⁻¹ : ℝ) : ℂ) • x0 with hv0_def
  have hx0norm_ne : ‖x0‖ ≠ 0 := norm_ne_zero_iff.mpr hx0ne
  have hv0norm : ‖v0‖ = 1 := by
    rw [hv0_def, norm_smul]
    simp [hx0norm_ne]
  have hv0mem : v0 ∈ c := by rw [hv0_def]; exact Submodule.smul_mem _ _ hx0mem
  set t : ℝ := (⟪v0, ρ v0⟫_ℂ).re with ht_def
  have htc : (t : ℂ) = ⟪v0, ρ v0⟫_ℂ := inner_self_real hsymm v0
  have hv0v0 : ⟪v0, v0⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hv0norm]; norm_num
  refine ⟨t, ?_⟩
  intro x hxmem
  by_cases hx0' : x = 0
  · rw [hx0']; simp
  set w : H n := x - ⟪v0, x⟫_ℂ • v0 with hw_def
  have hwmem : w ∈ c := Submodule.sub_mem _ hxmem (Submodule.smul_mem _ _ hv0mem)
  have hv0w : ⟪v0, w⟫_ℂ = 0 := by
    rw [hw_def, inner_sub_right, inner_smul_right, hv0v0, mul_one, sub_self]
  by_cases hw0 : w = 0
  · have hxeq : x = ⟪v0, x⟫_ℂ • v0 := by
      have h0 : x - ⟪v0, x⟫_ℂ • v0 = 0 := by rw [← hw_def, hw0]
      exact sub_eq_zero.mp h0
    have hρv0 : ρ v0 = (t : ℂ) • v0 := by
      rw [htc]; exact eigenvector_of_cellwiseInvariant hsymm hinv hc hv0mem hv0norm
    rw [hxeq, map_smul, hρv0, hv0_def]
    module
  · set w' : H n := ((‖w‖⁻¹ : ℝ) : ℂ) • w with hw'_def
    have hwnorm_ne : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
    have hw'norm : ‖w'‖ = 1 := by
      rw [hw'_def, norm_smul]
      simp [hwnorm_ne]
    have hw'mem' : w' ∈ c := by rw [hw'_def]; exact Submodule.smul_mem _ _ hwmem
    have hv0w' : ⟪v0, w'⟫_ℂ = 0 := by
      rw [hw'_def, inner_smul_right, hv0w, mul_zero]
    have heigen : ⟪v0, ρ v0⟫_ℂ = ⟪w', ρ w'⟫_ℂ :=
      eigenvalue_const_of_cellwiseInvariant hsymm hinv hc hv0mem hw'mem' hv0norm hw'norm hv0w'
    have htc' : (t : ℂ) = ⟪w', ρ w'⟫_ℂ := by rw [htc, heigen]
    have hρw' : ρ w' = (t : ℂ) • w' :=
      by rw [htc']; exact eigenvector_of_cellwiseInvariant hsymm hinv hc hw'mem' hw'norm
    have hρw : ρ w = (t : ℂ) • w := by
      have hweq : w = (‖w‖ : ℂ) • w' := by
        rw [hw'_def, smul_smul]
        rw [show (‖w‖ : ℂ) * ((‖w‖⁻¹ : ℝ) : ℂ) = 1 by
          rw [Complex.ofReal_inv]
          exact mul_inv_cancel₀ (by exact_mod_cast hwnorm_ne)]
        simp
      rw [hweq, map_smul, hρw']
      module
    have hρv0 : ρ v0 = (t : ℂ) • v0 := by
      rw [htc]; exact eigenvector_of_cellwiseInvariant hsymm hinv hc hv0mem hv0norm
    have hxeq : x = ⟪v0, x⟫_ℂ • v0 + w := by rw [hw_def]; module
    rw [hxeq, map_add, map_smul, hρv0, hρw]
    module

/-- Classification of cellwise-invariant densities: `ρ` is a density operator
invariant under `PerspectiveCellwiseStabilizer D` iff it is a block-scalar
operator with nonnegative, trace-one weights on `D`'s cells. -/
theorem cellwiseInvariant_density_iff_blockScalar (D : Perspective n) (ρ : H n →ₗ[ℂ] H n) :
    (IsDensityOperator ρ ∧ IsInvariantUnder (PerspectiveCellwiseStabilizer D) ρ)
      ↔ ∃ t : Submodule ℂ (H n) → ℝ, IsBlockDensityWeights D t ∧ ρ = blockScalarOperator D t := by
  constructor
  · rintro ⟨hdensity, hinv⟩
    classical
    let t : Submodule ℂ (H n) → ℝ := fun c =>
      if h : c ∈ D.cells then (cellRestriction_eq_scalar hdensity.symmetric hinv h).choose else 0
    have ht : ∀ c (hc : c ∈ D.cells), ∀ x ∈ c, ρ x = (t c : ℂ) • x := by
      intro c hc
      simp only [t, dif_pos hc]
      exact (cellRestriction_eq_scalar hdensity.symmetric hinv hc).choose_spec
    have hrho_eq : ρ = blockScalarOperator D t := by
      apply LinearMap.ext
      intro x
      have hxsum : x = ∑ c ∈ D.cells, projL c x := by
        have h := LinearMap.congr_fun (sum_projL_cells_eq_id D) x
        rw [LinearMap.sum_apply] at h
        simpa using h.symm
      have hstep : ρ x = ρ (∑ c ∈ D.cells, projL c x) := by rw [← hxsum]
      show ρ x = (blockScalarOperator D t) x
      rw [hstep, map_sum]
      show ∑ c ∈ D.cells, ρ (projL c x) = (∑ c ∈ D.cells, (t c : ℂ) • projL c) x
      rw [LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro c hc
      rw [LinearMap.smul_apply]
      exact ht c hc (projL c x) (Submodule.starProjection_apply_mem c x)
    have ht_nonneg : ∀ c ∈ D.cells, 0 ≤ t c := by
      intro c hc
      obtain ⟨v, hvmem, hvnorm⟩ := exists_unit_mem_of_ne_bot (D.nz c hc)
      have hρv : ρ v = (t c : ℂ) • v := ht c hc v hvmem
      have hvv : ⟪v, v⟫_ℂ = 1 := by
        rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hvnorm]; norm_num
      have hnonneg := hdensity.nonneg v
      rw [hρv, inner_smul_left, hvv, mul_one, Complex.conj_ofReal] at hnonneg
      simpa using hnonneg
    have ht_trace : LinearMap.trace ℂ (H n) (blockScalarOperator D t) = 1 := by
      rw [← hrho_eq]; exact hdensity.trace_one
    exact ⟨t, ⟨ht_nonneg, ht_trace⟩, hrho_eq⟩
  · rintro ⟨t, htw, hρeq⟩
    rw [hρeq]
    exact ⟨blockScalarOperator_isDensity D htw, blockScalarOperator_isInvariantUnder_cellwiseStabilizer D t⟩

noncomputable section

private noncomputable def setwiseImage' (D : Perspective n) {U : H n ≃ₗᵢ[ℂ] H n}
    (hU : U ∈ PerspectiveSetwiseStabilizer D) (c : Submodule ℂ (H n)) : Submodule ℂ (H n) :=
  if h : c ∈ D.cells then (hU c h).choose else c

private theorem setwiseImage'_mem (D : Perspective n) {U : H n ≃ₗᵢ[ℂ] H n}
    (hU : U ∈ PerspectiveSetwiseStabilizer D) {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
    setwiseImage' D hU c ∈ D.cells := by
  show (if h : c ∈ D.cells then (hU c h).choose else c) ∈ D.cells
  rw [dif_pos hc]
  exact (hU c hc).choose_spec.1

private theorem setwiseImage'_spec (D : Perspective n) {U : H n ≃ₗᵢ[ℂ] H n}
    (hU : U ∈ PerspectiveSetwiseStabilizer D) {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
    c.map U.toLinearMap = setwiseImage' D hU c := by
  show c.map U.toLinearMap = (if h : c ∈ D.cells then (hU c h).choose else c)
  rw [dif_pos hc]
  exact (hU c hc).choose_spec.2

private theorem conj_projL''' (U : H n ≃ₗᵢ[ℂ] H n) (A : Submodule ℂ (H n)) :
    U.toLinearMap ∘ₗ projL A ∘ₗ U.symm.toLinearMap = projL (A.map U.toLinearMap) := by
  apply LinearMap.ext
  intro x
  exact (Submodule.starProjection_map_apply U A x).symm

/-- If `t` gives equal weight on every setwise orbit, the block-scalar operator
is invariant under the full `PerspectiveSetwiseStabilizer`. -/
theorem blockScalarOperator_isInvariantUnder_setwiseStabilizer_of_orbitConstant (D : Perspective n)
    {t : Submodule ℂ (H n) → ℝ}
    (horbit : ∀ U ∈ PerspectiveSetwiseStabilizer D, ∀ c ∈ D.cells, t c = t (c.map U.toLinearMap)) :
    IsInvariantUnder (PerspectiveSetwiseStabilizer D) (blockScalarOperator D t) := by
  intro U hU
  show U.toLinearMap ∘ₗ (∑ c ∈ D.cells, (t c : ℂ) • projL c) ∘ₗ U.symm.toLinearMap
    = ∑ c ∈ D.cells, (t c : ℂ) • projL c
  set φ := setwiseImage' D hU with hφ_def
  have hφmem : ∀ c ∈ D.cells, φ c ∈ D.cells := fun c hc => setwiseImage'_mem D hU hc
  have hφ : ∀ c ∈ D.cells, c.map U.toLinearMap = φ c := fun c hc => setwiseImage'_spec D hU hc
  have hφ_inj : Set.InjOn φ (D.cells : Set (Submodule ℂ (H n))) := by
    intro c1 hc1 c2 hc2 heq
    have h1 := hφ c1 hc1
    have h2 := hφ c2 hc2
    rw [heq] at h1
    exact Submodule.map_injective_of_injective U.injective (h1.trans h2.symm)
  have hφ_mapsTo : Set.MapsTo φ (D.cells : Set (Submodule ℂ (H n))) (D.cells : Set (Submodule ℂ (H n))) :=
    fun c hc => hφmem c hc
  have hφ_surjOn : Set.SurjOn φ (D.cells : Set (Submodule ℂ (H n))) (D.cells : Set (Submodule ℂ (H n))) :=
    Finset.surjOn_of_injOn_of_card_le φ hφ_mapsTo hφ_inj (le_refl _)
  set ψinv : Submodule ℂ (H n) → Submodule ℂ (H n) :=
    fun c => if h : c ∈ D.cells then (hφ_surjOn h).choose else c with hψinv_def
  have hψinv_mem : ∀ c ∈ D.cells, ψinv c ∈ D.cells := by
    intro c hc
    rw [hψinv_def]; simp only [dif_pos hc]; exact (hφ_surjOn hc).choose_spec.1
  have hψinv : ∀ c ∈ D.cells, φ (ψinv c) = c := by
    intro c hc
    rw [hψinv_def]; simp only [dif_pos hc]; exact (hφ_surjOn hc).choose_spec.2
  have hψinv_left : ∀ c ∈ D.cells, ψinv (φ c) = c := by
    intro c hc
    exact hφ_inj (hψinv_mem (φ c) (hφmem c hc)) hc (hψinv (φ c) (hφmem c hc))
  have horbit_c : ∀ c ∈ D.cells, t c = t (φ c) := by
    intro c hc; rw [← hφ c hc]; exact horbit U hU c hc
  have hstep1 : U.toLinearMap ∘ₗ (∑ c ∈ D.cells, (t c : ℂ) • projL c) ∘ₗ U.symm.toLinearMap
      = ∑ c ∈ D.cells, (t (φ c) : ℂ) • projL (φ c) := by
    rw [show U.toLinearMap ∘ₗ (∑ c ∈ D.cells, (t c : ℂ) • projL c) ∘ₗ U.symm.toLinearMap
        = ∑ c ∈ D.cells, U.toLinearMap ∘ₗ ((t c : ℂ) • projL c) ∘ₗ U.symm.toLinearMap from by
      apply LinearMap.ext; intro x
      show U ((∑ c ∈ D.cells, (t c : ℂ) • projL c) (U.symm x))
        = (∑ c ∈ D.cells, U.toLinearMap ∘ₗ ((t c : ℂ) • projL c) ∘ₗ U.symm.toLinearMap) x
      rw [LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro c _
      rfl]
    apply Finset.sum_congr rfl
    intro c hc
    have hUc : U.toLinearMap ∘ₗ projL c ∘ₗ U.symm.toLinearMap = projL (φ c) := by
      rw [conj_projL''', hφ c hc]
    rw [show U.toLinearMap ∘ₗ ((t c : ℂ) • projL c) ∘ₗ U.symm.toLinearMap
        = (t c : ℂ) • (U.toLinearMap ∘ₗ projL c ∘ₗ U.symm.toLinearMap) from by
      apply LinearMap.ext; intro x
      show U ((t c : ℂ) • projL c (U.symm x)) = (t c : ℂ) • U (projL c (U.symm x))
      rw [map_smul]]
    rw [hUc, horbit_c c hc]
  have hstep2 : ∑ c ∈ D.cells, (t (φ c) : ℂ) • projL (φ c) = ∑ c ∈ D.cells, (t c : ℂ) • projL c :=
    Finset.sum_nbij' φ ψinv hφmem hψinv_mem hψinv_left hψinv (fun c _ => rfl)
  rw [hstep1, hstep2]

end

/-- The block-scalar operator acts on a point of a cell `c` by the single
scalar `t c` (the other cells' terms vanish since cells are pairwise
orthogonal). -/
theorem blockScalarOperator_apply_of_mem {D : Perspective n} {t : Submodule ℂ (H n) → ℝ}
    {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) {x : H n} (hx : x ∈ c) :
    blockScalarOperator D t x = (t c : ℂ) • x := by
  show (∑ c' ∈ D.cells, (t c' : ℂ) • projL c') x = (t c : ℂ) • x
  rw [LinearMap.sum_apply]
  rw [Finset.sum_eq_single c]
  · rw [LinearMap.smul_apply]
    congr 1
    exact Submodule.starProjection_eq_self_iff.mpr hx
  · intro c' hc' hne
    rw [LinearMap.smul_apply]
    have hortho : c ≤ c' ᗮ := D.ortho c hc c' hc' (Ne.symm hne)
    have hzero : projL c' x = 0 := (Submodule.starProjection_apply_eq_zero_iff c').mpr (hortho hx)
    rw [hzero, smul_zero]
  · intro h; exact absurd hc h

/-- Classification of setwise-invariant densities: `ρ` is a density operator
invariant under `PerspectiveSetwiseStabilizer D` iff it is a block-scalar
operator with nonnegative, trace-one weights that are, moreover, CONSTANT
across every setwise orbit of `D`'s cells. -/
theorem setwiseInvariant_density_iff_blockScalar_orbitConstant (D : Perspective n)
    (ρ : H n →ₗ[ℂ] H n) :
    (IsDensityOperator ρ ∧ IsInvariantUnder (PerspectiveSetwiseStabilizer D) ρ)
      ↔ ∃ t : Submodule ℂ (H n) → ℝ, IsBlockDensityWeights D t ∧ ρ = blockScalarOperator D t ∧
          ∀ U ∈ PerspectiveSetwiseStabilizer D, ∀ c ∈ D.cells, t c = t (c.map U.toLinearMap) := by
  constructor
  · rintro ⟨hdensity, hinv⟩
    have hinv_cellwise : IsInvariantUnder (PerspectiveCellwiseStabilizer D) ρ :=
      fun U hU => hinv U (PerspectiveCellwiseStabilizer_le_PerspectiveSetwiseStabilizer D hU)
    obtain ⟨t, htw, hρeq⟩ := (cellwiseInvariant_density_iff_blockScalar D ρ).mp ⟨hdensity, hinv_cellwise⟩
    refine ⟨t, htw, hρeq, ?_⟩
    intro U hU c hc
    obtain ⟨c', hc'mem, hc'eq⟩ := hU c hc
    rw [hc'eq]
    obtain ⟨v, hvmem, hvnorm⟩ := exists_unit_mem_of_ne_bot (D.nz c hc)
    have hUvmem : U v ∈ c' := hc'eq ▸ Submodule.mem_map_of_mem hvmem
    have hcomm : ρ (U v) = U (ρ v) := by
      have h1 := LinearMap.congr_fun (hinv U hU) (U v)
      simpa using h1.symm
    have hρv : ρ v = (t c : ℂ) • v := by rw [hρeq]; exact blockScalarOperator_apply_of_mem hc hvmem
    have hρUv : ρ (U v) = (t c' : ℂ) • (U v) := by
      rw [hρeq]; exact blockScalarOperator_apply_of_mem hc'mem hUvmem
    rw [hρv, map_smul] at hcomm
    rw [hρUv] at hcomm
    have hUv_ne : U v ≠ 0 := by
      intro h
      have : ‖U v‖ = 0 := by rw [h]; simp
      rw [LinearIsometryEquiv.norm_map, hvnorm] at this
      norm_num at this
    have := smul_left_injective ℂ hUv_ne hcomm.symm
    exact_mod_cast this
  · rintro ⟨t, htw, hρeq, horbit⟩
    rw [hρeq]
    exact ⟨blockScalarOperator_isDensity D htw,
      blockScalarOperator_isInvariantUnder_setwiseStabilizer_of_orbitConstant D horbit⟩

end QuantumFoundations.Selector
