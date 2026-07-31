import QuantumFoundations.Selectors.Pinning

/-!
**FR.** # Selectors — Module B, dépendance structurelle : le sélecteur déphasant

Contenu interprétativement neutre, comme le reste du sous-module. Étant
donné une base orthonormée `b`, le **sélecteur déphasant** associe à un
état pur `ψ` la densité obtenue en effaçant les cohérences hors-diagonale
de `|ψ⟩⟨ψ|` dans la base `b` :

`dephasedDensity b ψ = ∑ i, |⟨b i, ψ⟩|² • |b i⟩⟨b i|`.

C'est une densité valide pour tout `ψ` unitaire (`dephasedDensity_isDensity`),
mais elle dépend explicitement du choix de `b` : ce n'est **pas** un
sélecteur covariant (`dephasingSelector_not_covariant`), et elle viole
`NSNC1` (`dephasingSelector_violates_nsnc1`), diffère du sélecteur de Born
(`dephasingSelector_ne_bornSelector`). Le témoin de non-covariance est
l'unitaire de Hadamard `hadamardUnitary`, construit sur la paire d'indices
`(i0, i1)` de `b` via `OrthonormalBasis.equiv` (même patron que `reflIso`/
`swapIso` dans `Unitaries.lean`).

**EN.** # Selectors — Module B, structural dependence: the dephasing selector

Interpretively neutral content, like the rest of the submodule. Given an
orthonormal basis `b`, the **dephasing selector** assigns to a pure state
`ψ` the density obtained by erasing the off-diagonal coherences of
`|ψ⟩⟨ψ|` in the basis `b`:

`dephasedDensity b ψ = ∑ i, |⟨b i, ψ⟩|² • |b i⟩⟨b i|`.

It is a valid density for every unit `ψ` (`dephasedDensity_isDensity`), but
it depends explicitly on the choice of `b`: it is **not** a covariant
selector (`dephasingSelector_not_covariant`), it violates `NSNC1`
(`dephasingSelector_violates_nsnc1`), and it differs from the Born selector
(`dephasingSelector_ne_bornSelector`). The non-covariance witness is the
Hadamard unitary `hadamardUnitary`, built on the index pair `(i0, i1)` of
`b` via `OrthonormalBasis.equiv` (same pattern as `reflIso`/`swapIso` in
`Unitaries.lean`).
-/

namespace QuantumFoundations.Selector

open scoped InnerProductSpace
open Gleason
open QuantumFoundations.Uhlhorn (projL_singleton_unit)

noncomputable section

variable {n : ℕ}

/-!
### The dephasing selector
-/

/--
**FR.** La projection de rang 1 sur le `i`-ème vecteur de `b`.

**EN.** The rank-one projection onto the `i`-th vector of `b`.
-/
def basisProjection (b : OrthonormalBasis (Fin n) ℂ (H n)) (i : Fin n) : H n →ₗ[ℂ] H n :=
  projL (ℂ ∙ b i)

theorem basisProjection_apply (b : OrthonormalBasis (Fin n) ℂ (H n)) (i : Fin n) (x : H n) :
    basisProjection b i x = ⟪b i, x⟫_ℂ • b i :=
  projL_singleton_unit (b i) x (b.norm_eq_one i)

/--
**FR.** Le poids de Born de `ψ` sur le `i`-ème vecteur de `b`.

**EN.** The Born weight of `ψ` on the `i`-th vector of `b`.
-/
def basisWeight (b : OrthonormalBasis (Fin n) ℂ (H n)) (ψ : H n) (i : Fin n) : ℝ :=
  ‖⟪b i, ψ⟫_ℂ‖ ^ 2

theorem basisWeight_nonneg (b : OrthonormalBasis (Fin n) ℂ (H n)) (ψ : H n) (i : Fin n) :
    0 ≤ basisWeight b ψ i := sq_nonneg _

theorem basisWeight_sum (b : OrthonormalBasis (Fin n) ℂ (H n)) (ψ : H n) :
    ∑ i, basisWeight b ψ i = ‖ψ‖ ^ 2 :=
  OrthonormalBasis.sum_sq_norm_inner_right b ψ

/--
**FR.** La densité déphasée dans la base `b` : le mélange des projecteurs
de `b` pondéré par les poids de Born de `ψ`. Diagonale par construction
dans la base `b`, quel que soit `ψ`.

**EN.** The density dephased in the basis `b`: the mixture of `b`'s
projectors weighted by the Born weights of `ψ`. Diagonal by construction
in the basis `b`, for every `ψ`.
-/
noncomputable def dephasedDensity (b : OrthonormalBasis (Fin n) ℂ (H n)) (ψ : H n) :
    H n →ₗ[ℂ] H n :=
  ∑ i, (basisWeight b ψ i : ℂ) • basisProjection b i

theorem dephasedDensity_isSymmetric (b : OrthonormalBasis (Fin n) ℂ (H n)) (ψ : H n) :
    LinearMap.IsSymmetric (dephasedDensity b ψ) := by
  intro x y
  show ⟪(∑ i, (basisWeight b ψ i : ℂ) • basisProjection b i) x, y⟫_ℂ
    = ⟪x, (∑ i, (basisWeight b ψ i : ℂ) • basisProjection b i) y⟫_ℂ
  simp_rw [LinearMap.sum_apply, LinearMap.smul_apply, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  show ⟪(ℂ ∙ b i).starProjection x, y⟫_ℂ = ⟪x, (ℂ ∙ b i).starProjection y⟫_ℂ
  exact Submodule.starProjection_isSymmetric (ℂ ∙ b i) x y

theorem dephasedDensity_nonneg (b : OrthonormalBasis (Fin n) ℂ (H n)) (ψ x : H n) :
    0 ≤ (⟪dephasedDensity b ψ x, x⟫_ℂ).re := by
  show 0 ≤ (⟪(∑ i, (basisWeight b ψ i : ℂ) • basisProjection b i) x, x⟫_ℂ).re
  simp_rw [LinearMap.sum_apply, LinearMap.smul_apply, sum_inner, inner_smul_left,
    Complex.conj_ofReal]
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [Complex.re_ofReal_mul]
  exact mul_nonneg (basisWeight_nonneg b ψ i)
    (Submodule.re_inner_starProjection_nonneg (ℂ ∙ b i) x)

theorem dephasedDensity_trace (b : OrthonormalBasis (Fin n) ℂ (H n)) (ψ : H n) :
    LinearMap.trace ℂ (H n) (dephasedDensity b ψ) = (‖ψ‖ ^ 2 : ℂ) := by
  show LinearMap.trace ℂ (H n) (∑ i, (basisWeight b ψ i : ℂ) • basisProjection b i) = _
  rw [map_sum]
  simp_rw [map_smul]
  have htr : ∀ i, LinearMap.trace ℂ (H n) (basisProjection b i) = 1 :=
    fun i => trace_projL_singleton (b.norm_eq_one i)
  simp_rw [htr, smul_eq_mul, mul_one]
  rw [← Complex.ofReal_sum, basisWeight_sum]
  norm_cast

theorem dephasedDensity_isDensity (b : OrthonormalBasis (Fin n) ℂ (H n)) {ψ : H n}
    (hψ : ‖ψ‖ = 1) : IsDensityOperator (dephasedDensity b ψ) :=
  ⟨dephasedDensity_isSymmetric b ψ, dephasedDensity_nonneg b ψ, by
    rw [dephasedDensity_trace, hψ]; norm_num⟩

/--
**FR.** Le sélecteur déphasant associé à `b`.

**EN.** The dephasing selector associated with `b`.
-/
noncomputable def dephasingSelector (b : OrthonormalBasis (Fin n) ℂ (H n)) : Selector n where
  ρ := dephasedDensity b
  isDensity := fun _ hψ => dephasedDensity_isDensity b hψ

/--
**FR.** Formule générale : `dephasedDensity b ψ` reste diagonale sur `x`
quelconque, écrite comme somme sur `b`.

**EN.** General formula: `dephasedDensity b ψ` stays diagonal on an
arbitrary `x`, written as a sum over `b`.
-/
theorem dephasedDensity_apply (b : OrthonormalBasis (Fin n) ℂ (H n)) (ψ x : H n) :
    dephasedDensity b ψ x = ∑ i, (basisWeight b ψ i : ℂ) • (⟪b i, x⟫_ℂ • b i) := by
  show (∑ i, (basisWeight b ψ i : ℂ) • basisProjection b i) x = _
  rw [LinearMap.sum_apply]
  simp_rw [LinearMap.smul_apply, basisProjection_apply]

/--
**FR.** Spécialisation de `dephasedDensity_apply` à un vecteur de `b` : la
somme s'effondre sur le seul terme `i = j`.

**EN.** Specialization of `dephasedDensity_apply` to a vector of `b`: the
sum collapses to the single term `i = j`.
-/
theorem dephasedDensity_apply_basis (b : OrthonormalBasis (Fin n) ℂ (H n)) (ψ : H n) (j : Fin n) :
    dephasedDensity b ψ (b j) = (basisWeight b ψ j : ℂ) • b j := by
  rw [dephasedDensity_apply]
  have hcol : ∀ i, (basisWeight b ψ i : ℂ) • (⟪b i, b j⟫_ℂ • b i)
      = if i = j then (basisWeight b ψ j : ℂ) • b j else 0 := by
    intro i
    rw [b.inner_eq_ite]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  simp_rw [hcol]
  rw [Finset.sum_ite_eq' Finset.univ j]
  simp

/--
**FR.** Cas particulier crucial pour B4/B5 : dépasé un vecteur de base
`b j` ne fait rien — `dephasedDensity b (b j)` est exactement le
projecteur pur `basisProjection b j`.

**EN.** Special case crucial for B4/B5: dephasing a basis vector `b j`
does nothing — `dephasedDensity b (b j)` is exactly the pure projector
`basisProjection b j`.
-/
theorem dephasedDensity_basis_eq_basisProjection (b : OrthonormalBasis (Fin n) ℂ (H n))
    (j : Fin n) : dephasedDensity b (b j) = basisProjection b j := by
  show (∑ i, (basisWeight b (b j) i : ℂ) • basisProjection b i) = basisProjection b j
  have hw : ∀ i, (basisWeight b (b j) i : ℂ) • basisProjection b i
      = if i = j then basisProjection b j else 0 := by
    intro i
    have : basisWeight b (b j) i = if i = j then 1 else 0 := by
      show ‖⟪b i, b j⟫_ℂ‖ ^ 2 = _
      rw [b.inner_eq_ite]
      by_cases h : i = j <;> simp [h]
    by_cases h : i = j
    · subst h; rw [this, if_pos rfl, if_pos rfl]; norm_num
    · rw [this, if_neg h, if_neg h]; norm_num
  simp_rw [hw]
  rw [Finset.sum_ite_eq' Finset.univ j]
  simp

/--
**FR.** Formule matricielle : `dephasedDensity b ψ` est diagonale dans la
base `b`, avec `basisWeight b ψ j` sur la diagonale.

**EN.** Matrix-entry formula: `dephasedDensity b ψ` is diagonal in the
basis `b`, with `basisWeight b ψ j` on the diagonal.
-/
theorem dephasedDensity_matrix_entry (b : OrthonormalBasis (Fin n) ℂ (H n)) (ψ : H n)
    (i j : Fin n) :
    ⟪b i, dephasedDensity b ψ (b j)⟫_ℂ = if i = j then (basisWeight b ψ j : ℂ) else 0 := by
  rw [dephasedDensity_apply_basis, inner_smul_right, b.inner_eq_ite]
  by_cases h : i = j
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

/-!
### The Hadamard witness

Two auxiliary indices `i0 ≠ i1` of `b` (exist since `n ≥ 2`), a "plus"/
"minus" pair built from them, and the unitary `hadamardUnitary` sending
`b i0 ↦ plusVector`, `b i1 ↦ minusVector`, fixing every other basis
vector — the standard 2×2 Hadamard rotation, embedded in `H n` and built
via `OrthonormalBasis.equiv` exactly as `reflIso`/`swapIso` in
`Unitaries.lean`.
-/

variable (hn : 2 ≤ n) (b : OrthonormalBasis (Fin n) ℂ (H n))

/-- The first auxiliary index, `⟨0, _⟩`, available since `n ≥ 2`. -/
def i0 : Fin n := ⟨0, by omega⟩

/-- The second auxiliary index, `⟨1, _⟩`, available since `n ≥ 2`. -/
def i1 : Fin n := ⟨1, by omega⟩

theorem i0_ne_i1 : i0 hn ≠ i1 hn := by simp [i0, i1]

/-- `1/√2`, the Hadamard normalization constant. -/
def alphaC : ℝ := (Real.sqrt 2)⁻¹

theorem alphaC_pos : 0 < alphaC := by rw [alphaC]; positivity

theorem alphaC_sq : alphaC * alphaC * 2 = 1 := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [alphaC]; field_simp; linarith [h2]

private theorem cast_helper (x : ℝ) (hx : x * x * 2 = 1) : ((x : ℂ)) * ((x : ℂ) * 2) = 1 := by
  have heq : ((x : ℂ)) * ((x : ℂ) * 2) = ((x * x * 2 : ℝ) : ℂ) := by push_cast; ring
  rw [heq, hx]; norm_num

/-- The Hadamard `(alphaC : ℂ) * (alphaC : ℂ) = 1/2` identity, factored out
since it recurs in every weight/inner-product computation below. -/
theorem alphaC_mul_self_eq_half : (alphaC : ℂ) * (alphaC : ℂ) = 1 / 2 := by
  have := cast_helper alphaC alphaC_sq
  linear_combination this / 2

/-- `plusVector = α(b i0 + b i1)`, the Hadamard "plus" state. -/
def plusVector : H n := (alphaC : ℂ) • (b (i0 hn) + b (i1 hn))

/-- `minusVector = α(b i0 - b i1)`, the Hadamard "minus" state. -/
def minusVector : H n := (alphaC : ℂ) • (b (i0 hn) - b (i1 hn))

theorem plusVector_inner_self : ⟪plusVector hn b, plusVector hn b⟫_ℂ = 1 := by
  rw [plusVector, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    inner_add_right, b.inner_eq_ite, b.inner_eq_ite, b.inner_eq_ite, b.inner_eq_ite,
    if_pos rfl, if_pos rfl, if_neg (i0_ne_i1 hn), if_neg (Ne.symm (i0_ne_i1 hn)),
    Complex.conj_ofReal]
  have : (1 : ℂ) + 0 + (0 + 1) = 2 := by ring
  rw [this]; exact cast_helper alphaC alphaC_sq

/-- `‖plusVector‖ = 1`, used wherever `plusVector` must be fed through
`projL_singleton_unit` (S1's rank-one projector formula). -/
theorem plusVector_norm_eq_one : ‖plusVector hn b‖ = 1 := by
  have h1 := plusVector_inner_self hn b
  have h2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (plusVector hn b)
  rw [h1] at h2
  have h3 : (‖plusVector hn b‖ : ℂ) ^ 2 = 1 := h2.symm
  have h4 : ‖plusVector hn b‖ ^ 2 = 1 := by exact_mod_cast h3
  nlinarith [norm_nonneg (plusVector hn b)]

theorem minusVector_inner_self : ⟪minusVector hn b, minusVector hn b⟫_ℂ = 1 := by
  rw [minusVector, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right,
    inner_sub_right, b.inner_eq_ite, b.inner_eq_ite, b.inner_eq_ite, b.inner_eq_ite,
    if_pos rfl, if_pos rfl, if_neg (i0_ne_i1 hn), if_neg (Ne.symm (i0_ne_i1 hn)),
    Complex.conj_ofReal]
  have : (1 : ℂ) - 0 - (0 - 1) = 2 := by ring
  rw [this]; exact cast_helper alphaC alphaC_sq

theorem plus_minus_inner_eq_zero : ⟪plusVector hn b, minusVector hn b⟫_ℂ = 0 := by
  rw [plusVector, minusVector, inner_smul_left, inner_smul_right, inner_add_left, inner_sub_right,
    inner_sub_right, b.inner_eq_ite, b.inner_eq_ite, b.inner_eq_ite, b.inner_eq_ite,
    if_pos rfl, if_pos rfl, if_neg (i0_ne_i1 hn), if_neg (Ne.symm (i0_ne_i1 hn))]
  ring

theorem minus_plus_inner_eq_zero : ⟪minusVector hn b, plusVector hn b⟫_ℂ = 0 := by
  rw [← inner_conj_symm, plus_minus_inner_eq_zero]; simp

theorem plusVector_inner_other {j : Fin n} (hj0 : j ≠ i0 hn) (hj1 : j ≠ i1 hn) :
    ⟪plusVector hn b, b j⟫_ℂ = 0 := by
  rw [plusVector, inner_smul_left, inner_add_left, b.inner_eq_ite, b.inner_eq_ite,
    if_neg (Ne.symm hj0), if_neg (Ne.symm hj1)]
  ring

theorem minusVector_inner_other {j : Fin n} (hj0 : j ≠ i0 hn) (hj1 : j ≠ i1 hn) :
    ⟪minusVector hn b, b j⟫_ℂ = 0 := by
  rw [minusVector, inner_smul_left, inner_sub_left, b.inner_eq_ite, b.inner_eq_ite,
    if_neg (Ne.symm hj0), if_neg (Ne.symm hj1)]
  ring

theorem other_inner_plusVector {j : Fin n} (hj0 : j ≠ i0 hn) (hj1 : j ≠ i1 hn) :
    ⟪b j, plusVector hn b⟫_ℂ = 0 := by
  rw [← inner_conj_symm, plusVector_inner_other hn b hj0 hj1]; simp

theorem other_inner_minusVector {j : Fin n} (hj0 : j ≠ i0 hn) (hj1 : j ≠ i1 hn) :
    ⟪b j, minusVector hn b⟫_ℂ = 0 := by
  rw [← inner_conj_symm, minusVector_inner_other hn b hj0 hj1]; simp

/-- `⟨b i1, plusVector⟩ = α`, factored out since it recurs in the
non-covariance witness (B4) and the NSNC-1/Born counterexamples (B5). -/
theorem inner_i1_plusVector : ⟪b (i1 hn), plusVector hn b⟫_ℂ = (alphaC : ℂ) := by
  rw [plusVector, inner_smul_right, inner_add_right, b.inner_eq_ite, b.inner_eq_ite,
    if_neg (Ne.symm (i0_ne_i1 hn)), if_pos rfl]
  ring

/-- `basisWeight b plusVector i1 = 1/2`, the Hadamard weight identity used
throughout B4/B5. -/
theorem basisWeight_plusVector_i1 : basisWeight b (plusVector hn b) (i1 hn) = 1 / 2 := by
  show ‖⟪b (i1 hn), plusVector hn b⟫_ℂ‖ ^ 2 = 1 / 2
  rw [inner_i1_plusVector, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  nlinarith [alphaC_sq]

theorem inner_i0_minusVector : ⟪b (i0 hn), minusVector hn b⟫_ℂ = (alphaC : ℂ) := by
  rw [minusVector, inner_smul_right, inner_sub_right, b.inner_eq_ite, b.inner_eq_ite,
    if_pos rfl, if_neg (i0_ne_i1 hn)]
  ring

/--
**FR.** Le vecteur `hadamardBasisVector b i` : `plusVector` en `i0`,
`minusVector` en `i1`, `b i` ailleurs.

**EN.** The vector `hadamardBasisVector b i`: `plusVector` at `i0`,
`minusVector` at `i1`, `b i` elsewhere.
-/
def hadamardBasisVector (i : Fin n) : H n :=
  if i = i0 hn then plusVector hn b else if i = i1 hn then minusVector hn b else b i

theorem hadamardBasisVector_orthonormal : Orthonormal ℂ (hadamardBasisVector hn b) := by
  rw [orthonormal_iff_ite]
  intro i j
  unfold hadamardBasisVector
  by_cases hi0 : i = i0 hn
  · by_cases hj0 : j = i0 hn
    · rw [if_pos hi0, if_pos hj0, hi0, hj0]; simp only [if_pos rfl]
      exact plusVector_inner_self hn b
    · by_cases hj1 : j = i1 hn
      · rw [if_pos hi0, if_pos hj1]; rw [hi0, hj1, if_neg (i0_ne_i1 hn)]
        exact plus_minus_inner_eq_zero hn b
      · rw [if_pos hi0, if_neg hj0, if_neg hj1]
        rw [hi0, if_neg (fun h => hj0 (hi0 ▸ h.symm ▸ hi0).symm)]
        exact plusVector_inner_other hn b hj0 hj1
  · by_cases hi1 : i = i1 hn
    · by_cases hj0 : j = i0 hn
      · rw [if_neg hi0, if_pos hi1, if_pos hj0]
        rw [hi1, hj0, if_neg (Ne.symm (i0_ne_i1 hn))]
        exact minus_plus_inner_eq_zero hn b
      · by_cases hj1 : j = i1 hn
        · rw [if_neg hi0, if_pos hi1, if_neg hj0, if_pos hj1, hi1, hj1]; simp only [if_pos rfl]
          exact minusVector_inner_self hn b
        · rw [if_neg hi0, if_pos hi1, if_neg hj0, if_neg hj1]
          rw [hi1, if_neg (Ne.symm hj1)]
          exact minusVector_inner_other hn b hj0 hj1
    · by_cases hj0 : j = i0 hn
      · rw [if_neg hi0, if_neg hi1, if_pos hj0, hj0]
        rw [if_neg hi0]
        exact other_inner_plusVector hn b hi0 hi1
      · by_cases hj1 : j = i1 hn
        · rw [if_neg hi0, if_neg hi1, if_neg hj0, if_pos hj1, hj1]
          rw [if_neg hi1]
          exact other_inner_minusVector hn b hi0 hi1
        · rw [if_neg hi0, if_neg hi1, if_neg hj0, if_neg hj1]
          exact b.inner_eq_ite i j

theorem hadamardBasisVector_span :
    (⊤ : Submodule ℂ (H n)) ≤ Submodule.span ℂ (Set.range (hadamardBasisVector hn b)) := by
  rw [← b.toBasis.span_eq, Submodule.span_le]
  rintro x ⟨i, rfl⟩
  rw [OrthonormalBasis.coe_toBasis]
  by_cases hi0 : i = i0 hn
  · subst hi0
    have hmem_plus : plusVector hn b ∈ Submodule.span ℂ (Set.range (hadamardBasisVector hn b)) := by
      apply Submodule.subset_span
      exact ⟨i0 hn, by unfold hadamardBasisVector; rw [if_pos rfl]⟩
    have hmem_minus :
        minusVector hn b ∈ Submodule.span ℂ (Set.range (hadamardBasisVector hn b)) := by
      apply Submodule.subset_span
      refine ⟨i1 hn, ?_⟩
      unfold hadamardBasisVector
      rw [if_neg (Ne.symm (i0_ne_i1 hn)), if_pos rfl]
    have hsum : plusVector hn b + minusVector hn b = ((2 * alphaC : ℝ) : ℂ) • b (i0 hn) := by
      rw [plusVector, minusVector]; push_cast; module
    have h2a_ne : (2 * alphaC : ℝ) ≠ 0 := by
      have : (0 : ℝ) < alphaC := alphaC_pos
      linarith
    have hbi0 : b (i0 hn) = ((2 * alphaC : ℝ) : ℂ)⁻¹ • (plusVector hn b + minusVector hn b) := by
      rw [hsum, smul_smul, inv_mul_cancel₀ (by exact_mod_cast h2a_ne), one_smul]
    rw [hbi0]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ hmem_plus hmem_minus)
  · by_cases hi1 : i = i1 hn
    · subst hi1
      have hmem_plus :
          plusVector hn b ∈ Submodule.span ℂ (Set.range (hadamardBasisVector hn b)) := by
        apply Submodule.subset_span
        exact ⟨i0 hn, by unfold hadamardBasisVector; rw [if_pos rfl]⟩
      have hmem_minus :
          minusVector hn b ∈ Submodule.span ℂ (Set.range (hadamardBasisVector hn b)) := by
        apply Submodule.subset_span
        refine ⟨i1 hn, ?_⟩
        unfold hadamardBasisVector
        rw [if_neg (Ne.symm (i0_ne_i1 hn)), if_pos rfl]
      have hsub : plusVector hn b - minusVector hn b = ((2 * alphaC : ℝ) : ℂ) • b (i1 hn) := by
        rw [plusVector, minusVector]; push_cast; module
      have h2a_ne : (2 * alphaC : ℝ) ≠ 0 := by
        have : (0 : ℝ) < alphaC := alphaC_pos
        linarith
      have hbi1 : b (i1 hn) = ((2 * alphaC : ℝ) : ℂ)⁻¹ • (plusVector hn b - minusVector hn b) := by
        rw [hsub, smul_smul, inv_mul_cancel₀ (by exact_mod_cast h2a_ne), one_smul]
      rw [hbi1]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hmem_plus hmem_minus)
    · apply Submodule.subset_span
      exact ⟨i, by unfold hadamardBasisVector; rw [if_neg hi0, if_neg hi1]⟩

/-- The Hadamard-rotated orthonormal basis. -/
noncomputable def hadamardBasis : OrthonormalBasis (Fin n) ℂ (H n) :=
  OrthonormalBasis.mk (hadamardBasisVector_orthonormal hn b) (hadamardBasisVector_span hn b)

/--
**FR.** L'unitaire de Hadamard : envoie `b i0 ↦ plusVector`,
`b i1 ↦ minusVector`, fixe le reste de `b`. Témoin de non-covariance pour
`dephasingSelector` (B4).

**EN.** The Hadamard unitary: sends `b i0 ↦ plusVector`,
`b i1 ↦ minusVector`, fixes the rest of `b`. Non-covariance witness for
`dephasingSelector` (B4).
-/
noncomputable def hadamardUnitary : H n ≃ₗᵢ[ℂ] H n :=
  b.equiv (hadamardBasis hn b) (Equiv.refl (Fin n))

theorem hadamardUnitary_apply (i : Fin n) :
    hadamardUnitary hn b (b i) = hadamardBasisVector hn b i := by
  unfold hadamardUnitary
  rw [OrthonormalBasis.equiv_apply_basis]
  show (hadamardBasis hn b) (Equiv.refl (Fin n) i) = _
  unfold hadamardBasis
  rw [OrthonormalBasis.coe_mk]
  simp

theorem hadamardUnitary_apply_i0 : hadamardUnitary hn b (b (i0 hn)) = plusVector hn b := by
  rw [hadamardUnitary_apply, hadamardBasisVector, if_pos rfl]

theorem hadamardUnitary_apply_i1 : hadamardUnitary hn b (b (i1 hn)) = minusVector hn b := by
  rw [hadamardUnitary_apply, hadamardBasisVector, if_neg (Ne.symm (i0_ne_i1 hn)), if_pos rfl]

theorem hadamardUnitary_apply_other {j : Fin n} (hj0 : j ≠ i0 hn) (hj1 : j ≠ i1 hn) :
    hadamardUnitary hn b (b j) = b j := by
  rw [hadamardUnitary_apply, hadamardBasisVector, if_neg hj0, if_neg hj1]

/-- `hadamardUnitary` sends `minusVector` back to `b i1` — the Hadamard
rotation restricted to `span{b i0, b i1}` is its own inverse. Needed to
compute `hadamardUnitary.symm (b i1)` in the non-covariance proof (B4). -/
theorem hadamardUnitary_apply_minusVector :
    hadamardUnitary hn b (minusVector hn b) = b (i1 hn) := by
  have hcomb : plusVector hn b - minusVector hn b = ((2 * alphaC : ℝ) : ℂ) • b (i1 hn) := by
    rw [plusVector, minusVector]; push_cast; module
  have key : (alphaC : ℂ) • (plusVector hn b - minusVector hn b) = b (i1 hn) := by
    rw [hcomb, smul_smul]
    have : (alphaC : ℂ) * ((2 * alphaC : ℝ) : ℂ) = 1 := by
      push_cast
      linear_combination cast_helper alphaC alphaC_sq
    rw [this, one_smul]
  rw [show minusVector hn b = (alphaC : ℂ) • (b (i0 hn) - b (i1 hn)) from rfl,
    map_smul, map_sub, hadamardUnitary_apply_i0, hadamardUnitary_apply_i1, key]

/-!
### B4: the dephasing selector is not covariant

Witness: `U := hadamardUnitary`, `ψ := b i0`. On the `b i1` component,
`dephasingSelector b`'s covariance equation would force
`(1/2) • b i1 = (1/2) • b i0 + (1/2) • b i1`, i.e. `b i0 = 0` — absurd.
-/

theorem dephasingSelector_not_covariant (hn : 2 ≤ n) : ¬ IsCovariant (dephasingSelector b) := by
  intro hcov
  have heq := hcov (hadamardUnitary hn b) (b (i0 hn)) (b.norm_eq_one (i0 hn))
  have hLHS : (dephasingSelector b).ρ (hadamardUnitary hn b (b (i0 hn))) (b (i1 hn))
      = (1 / 2 : ℂ) • b (i1 hn) := by
    show dephasedDensity b (hadamardUnitary hn b (b (i0 hn))) (b (i1 hn)) = _
    rw [hadamardUnitary_apply_i0, dephasedDensity_apply_basis, basisWeight_plusVector_i1]
    norm_num
  have hsymm : (hadamardUnitary hn b).symm (b (i1 hn)) = minusVector hn b := by
    apply (hadamardUnitary hn b).injective
    rw [LinearIsometryEquiv.apply_symm_apply, hadamardUnitary_apply_minusVector]
  have hRHS : ((hadamardUnitary hn b).toLinearMap ∘ₗ (dephasingSelector b).ρ (b (i0 hn))
      ∘ₗ (hadamardUnitary hn b).symm.toLinearMap) (b (i1 hn))
      = (1 / 2 : ℂ) • b (i0 hn) + (1 / 2 : ℂ) • b (i1 hn) := by
    show hadamardUnitary hn b
      ((dephasingSelector b).ρ (b (i0 hn)) ((hadamardUnitary hn b).symm (b (i1 hn)))) = _
    rw [hsymm]
    show hadamardUnitary hn b (dephasedDensity b (b (i0 hn)) (minusVector hn b)) = _
    rw [dephasedDensity_basis_eq_basisProjection, basisProjection_apply, inner_i0_minusVector hn b,
      map_smul, hadamardUnitary_apply_i0, plusVector, smul_smul, alphaC_mul_self_eq_half, smul_add]
  rw [heq, hRHS] at hLHS
  have hb0_ne_zero : b (i0 hn) ≠ 0 := by
    intro h
    have := b.norm_eq_one (i0 hn)
    rw [h, norm_zero] at this
    norm_num at this
  have hz : (1 / 2 : ℂ) • b (i0 hn) = 0 := by linear_combination (norm := module) hLHS
  rcases smul_eq_zero.mp hz with h | h
  · norm_num at h
  · exact hb0_ne_zero h

/-!
### B5: matrix entry, Born-selector inequality, NSNC-1 violation

Same witness (`plusVector`, `b i1` matrix entry) drives all three: the
dephased density and the Born (pure) density of `plusVector` disagree at
`b i1`, hence `dephasingSelector b` is not the Born selector and violates
`NSNC1` at `plusVector`.
-/

theorem dephasedDensity_plusVector_ne_projL :
    dephasedDensity b (plusVector hn b) ≠ projL (ℂ ∙ plusVector hn b) := by
  intro heq
  have hL : dephasedDensity b (plusVector hn b) (b (i1 hn)) = (1 / 2 : ℂ) • b (i1 hn) := by
    rw [dephasedDensity_apply_basis, basisWeight_plusVector_i1]; norm_num
  have hR : projL (ℂ ∙ plusVector hn b) (b (i1 hn))
      = (1 / 2 : ℂ) • b (i0 hn) + (1 / 2 : ℂ) • b (i1 hn) := by
    rw [projL_singleton_unit (plusVector hn b) (b (i1 hn)) (plusVector_norm_eq_one hn b)]
    have hinner : ⟪plusVector hn b, b (i1 hn)⟫_ℂ = (alphaC : ℂ) := by
      rw [← inner_conj_symm, inner_i1_plusVector]; simp
    rw [hinner, plusVector, smul_smul, alphaC_mul_self_eq_half, smul_add]
  rw [heq, hR] at hL
  have hb0_ne_zero : b (i0 hn) ≠ 0 := by
    intro h
    have := b.norm_eq_one (i0 hn)
    rw [h, norm_zero] at this
    norm_num at this
  have hz : (1 / 2 : ℂ) • b (i0 hn) = 0 := by linear_combination (norm := module) hL
  rcases smul_eq_zero.mp hz with h | h
  · norm_num at h
  · exact hb0_ne_zero h

theorem dephasingSelector_violates_nsnc1 (hn : 2 ≤ n) : ¬ NSNC1 (dephasingSelector b) := by
  rw [nsnc1_iff_born]
  push_neg
  exact ⟨plusVector hn b, plusVector_norm_eq_one hn b, dephasedDensity_plusVector_ne_projL hn b⟩

theorem dephasingSelector_ne_bornSelector (hn : 2 ≤ n) :
    dephasingSelector b ≠ bornSelector n := by
  intro heq
  apply dephasedDensity_plusVector_ne_projL hn b
  show (dephasingSelector b).ρ (plusVector hn b) = _
  rw [heq]; rfl

end
end QuantumFoundations.Selector
