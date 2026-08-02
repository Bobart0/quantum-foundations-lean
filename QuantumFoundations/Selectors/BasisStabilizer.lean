import QuantumFoundations.Selectors.Dephasing
import QuantumFoundations.Selectors.SubgroupCovariance

/-!
**FR.** # Selectors — Module B, stabilisateurs d'une base et classification des densités

Deux sous-groupes naturels attachés à une base orthonormée `b`, du plus
petit au plus grand :

- **`BasisPhaseStabilizer b`** : les isométries qui fixent chaque droite
  `ℂ∙(b i)` — une transformation de phase par vecteur de base, aucune
  permutation. Le sélecteur déphasant `dephasingSelector b` lui est
  covariant (`dephasingSelector_isCovariantUnder_basisPhaseStabilizer`),
  et les densités qui lui sont invariantes sont exactement les densités
  **diagonales** dans `b` (`phaseInvariant_density_iff_diagonal`).
- **`BasisMonomialStabilizer b`** : les isométries qui envoient chaque
  droite `ℂ∙(b i)` sur une AUTRE droite `ℂ∙(b j)` de la même famille —
  matrices monomiales (phase + permutation). Contient le premier
  (`BasisPhaseStabilizer_le_BasisMonomialStabilizer`). Le sélecteur
  déphasant lui est encore covariant
  (`dephasingSelector_isCovariantUnder_basisMonomialStabilizer`), mais les
  densités qui lui sont invariantes sont contraintes bien plus fort :
  exactement l'état **maximalement mélangé** `(1/n)•Id`
  (`monomialInvariant_density_iff_maximallyMixed`) — **pas** « toutes les
  densités » comme on pourrait le croire à tort
  (`exists_density_not_invariant_under_basisMonomialStabilizer`, correction
  explicite de cette affirmation fausse).

Témoin de non-covariance/stricte inclusion : l'unitaire de Hadamard
`hadamardUnitary` (`Dephasing.lean`) appartient au groupe unitaire complet
mais PAS à `BasisPhaseStabilizer b`
(`hadamardUnitary_not_mem_BasisPhaseStabilizer`).

**EN.** # Selectors — Module B, basis stabilizers and density classification

Two natural subgroups attached to an orthonormal basis `b`, from smallest
to largest:

- **`BasisPhaseStabilizer b`**: the isometries that fix every line
  `ℂ∙(b i)` — a phase transformation per basis vector, no permutation. The
  dephasing selector `dephasingSelector b` is covariant under it
  (`dephasingSelector_isCovariantUnder_basisPhaseStabilizer`), and the
  densities invariant under it are exactly the **diagonal** densities in
  `b` (`phaseInvariant_density_iff_diagonal`).
- **`BasisMonomialStabilizer b`**: the isometries that send every line
  `ℂ∙(b i)` to SOME OTHER line `ℂ∙(b j)` of the same family — monomial
  matrices (phase + permutation). Contains the first
  (`BasisPhaseStabilizer_le_BasisMonomialStabilizer`). The dephasing
  selector is still covariant under it
  (`dephasingSelector_isCovariantUnder_basisMonomialStabilizer`), but the
  densities invariant under it are constrained far more strongly: exactly
  the **maximally mixed** state `(1/n)•Id`
  (`monomialInvariant_density_iff_maximallyMixed`) — **not** "every
  density" as one might mistakenly believe
  (`exists_density_not_invariant_under_basisMonomialStabilizer`, an
  explicit correction of that false claim).

Non-covariance/strict-inclusion witness: the Hadamard unitary
`hadamardUnitary` (`Dephasing.lean`) belongs to the full unitary group but
NOT to `BasisPhaseStabilizer b`
(`hadamardUnitary_not_mem_BasisPhaseStabilizer`).
-/

namespace QuantumFoundations.Selector

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ}

private theorem map_span_singleton' (U : H n ≃ₗᵢ[ℂ] H n) (ψ : H n) :
    (ℂ ∙ ψ).map U.toLinearMap = ℂ ∙ (U ψ) := by
  rw [Submodule.map_span, Set.image_singleton]; rfl

/-!
### The phase stabilizer of a basis
-/

/--
**FR.** Le stabilisateur de phase de `b` : les isométries qui fixent
chaque droite `ℂ∙(b i)` (mais peuvent la faire tourner d'une phase).

**EN.** The phase stabilizer of `b`: the isometries that fix every line
`ℂ∙(b i)` (but may rotate it by a phase).
-/
def BasisPhaseStabilizer (b : OrthonormalBasis (Fin n) ℂ (H n)) : Subgroup (H n ≃ₗᵢ[ℂ] H n) where
  carrier := {U | ∀ i, (ℂ ∙ b i).map U.toLinearMap = ℂ ∙ b i}
  one_mem' := by intro i; show (ℂ ∙ b i).map LinearMap.id = ℂ ∙ b i; rw [Submodule.map_id]
  mul_mem' := by
    intro U V hU hV i
    show (ℂ ∙ b i).map (U.toLinearMap ∘ₗ V.toLinearMap) = ℂ ∙ b i
    rw [Submodule.map_comp, hV i, hU i]
  inv_mem' := by
    intro U hU i
    have h := congrArg (Submodule.map U⁻¹.toLinearMap) (hU i)
    rw [← Submodule.map_comp] at h
    rw [show U⁻¹.toLinearMap ∘ₗ U.toLinearMap = LinearMap.id from by ext x; simp] at h
    rw [Submodule.map_id] at h
    exact h.symm

theorem BasisPhaseStabilizer_le_top (b : OrthonormalBasis (Fin n) ℂ (H n)) :
    BasisPhaseStabilizer b ≤ ⊤ := le_top

/-- `U` fixing every line of `b` implies `U (b i) = c • b i` for some unit-modulus `c`,
and `U⁻¹ (b i) = conj c • b i`. -/
private theorem phase_of_mem_BasisPhaseStabilizer {b : OrthonormalBasis (Fin n) ℂ (H n)}
    {U : H n ≃ₗᵢ[ℂ] H n} (hU : U ∈ BasisPhaseStabilizer b) (i : Fin n) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ U (b i) = c • b i ∧ U.symm (b i) = (starRingEnd ℂ) c • b i := by
  have hmem : U (b i) ∈ (ℂ ∙ b i) := by
    rw [← hU i]
    exact Submodule.mem_map.mpr ⟨b i, Submodule.mem_span_singleton_self _, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hnorm : ‖c‖ = 1 := by
    have h1 : ‖U (b i)‖ = 1 := by rw [U.norm_map]; exact b.norm_eq_one i
    rw [← hc, norm_smul, b.norm_eq_one i, mul_one] at h1
    exact h1
  refine ⟨c, hnorm, hc.symm, ?_⟩
  have hc_ne : c ≠ 0 := by intro h; rw [h] at hnorm; simp at hnorm
  have hsymm_apply : U.symm (U (b i)) = b i := U.symm_apply_apply (b i)
  rw [hc.symm, map_smul] at hsymm_apply
  have hinv : U.symm (b i) = c⁻¹ • b i := by
    have h2 : c⁻¹ • (c • U.symm (b i)) = c⁻¹ • b i := by rw [hsymm_apply]
    rwa [smul_smul, inv_mul_cancel₀ hc_ne, one_smul] at h2
  rw [hinv, Complex.inv_eq_conj hnorm]

/--
**FR.** L'unitaire de Hadamard tourne la droite `ℂ∙(b i0)` vers la droite
STRICTEMENT différente `ℂ∙(plusVector)` : il n'appartient donc pas au
stabilisateur de phase, bien qu'il appartienne au groupe unitaire complet.

**EN.** The Hadamard unitary rotates the line `ℂ∙(b i0)` to the STRICTLY
different line `ℂ∙(plusVector)`: it therefore does not belong to the phase
stabilizer, even though it belongs to the full unitary group.
-/
theorem hadamardUnitary_not_mem_BasisPhaseStabilizer (hn : 2 ≤ n)
    (b : OrthonormalBasis (Fin n) ℂ (H n)) :
    hadamardUnitary hn b ∉ BasisPhaseStabilizer b := by
  intro hmem
  have hline : (ℂ ∙ b (i0 hn)).map (hadamardUnitary hn b).toLinearMap = ℂ ∙ b (i0 hn) := hmem (i0 hn)
  rw [map_span_singleton', hadamardUnitary_apply_i0] at hline
  have hmem_line : plusVector hn b ∈ (ℂ ∙ b (i0 hn)) := hline ▸ Submodule.mem_span_singleton_self _
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem_line
  have hinner := inner_i1_plusVector hn b
  rw [← hk, inner_smul_right, b.inner_eq_ite, if_neg (Ne.symm (i0_ne_i1 hn)), mul_zero] at hinner
  have : (alphaC : ℝ) = 0 := by exact_mod_cast hinner.symm
  linarith [alphaC_pos]

/-- Weight is phase-invariant: `‖⟨b i, U ψ⟩‖ = ‖⟨b i, ψ⟩‖` when `U` fixes the line of `b i`. -/
private theorem basisWeight_invariant_of_phase {b : OrthonormalBasis (Fin n) ℂ (H n)}
    {U : H n ≃ₗᵢ[ℂ] H n} (hU : U ∈ BasisPhaseStabilizer b) (ψ : H n) (i : Fin n) :
    basisWeight b (U ψ) i = basisWeight b ψ i := by
  obtain ⟨c, hc1, _, hcsymm⟩ := phase_of_mem_BasisPhaseStabilizer hU i
  show ‖⟪b i, U ψ⟫_ℂ‖ ^ 2 = ‖⟪b i, ψ⟫_ℂ‖ ^ 2
  have hiso : ⟪U.symm (b i), ψ⟫_ℂ = ⟪b i, U ψ⟫_ℂ := by
    conv_rhs => rw [show b i = U (U.symm (b i)) from (U.apply_symm_apply (b i)).symm]
    exact (U.inner_map_map (U.symm (b i)) ψ).symm
  rw [hcsymm, inner_smul_left, Complex.conj_conj] at hiso
  rw [← hiso, norm_mul, hc1, one_mul]

theorem dephasingSelector_isCovariantUnder_basisPhaseStabilizer
    (b : OrthonormalBasis (Fin n) ℂ (H n)) :
    IsCovariantUnder (BasisPhaseStabilizer b) (dephasingSelector b) := by
  intro U hU ψ _hψ
  apply LinearMap.ext
  intro x
  show dephasedDensity b (U ψ) x = U (dephasedDensity b ψ (U.symm x))
  rw [dephasedDensity_apply, dephasedDensity_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, map_smul]
  obtain ⟨c, _hc1, hcU, hUsymm⟩ := phase_of_mem_BasisPhaseStabilizer hU i
  rw [hcU, basisWeight_invariant_of_phase hU ψ i]
  simp only [smul_smul]
  congr 1
  have hiso : ⟪b i, x⟫_ℂ = ⟪U.symm (b i), U.symm x⟫_ℂ := (U.symm.inner_map_map (b i) x).symm
  rw [hUsymm, inner_smul_left, Complex.conj_conj] at hiso
  rw [hiso]
  ring

/-!
### The monomial stabilizer of a basis
-/

/-- Distinct basis indices give distinct lines: if `ℂ ∙ b i = ℂ ∙ b j` then `i = j`. -/
private theorem line_eq_iff {b : OrthonormalBasis (Fin n) ℂ (H n)} {i j : Fin n} :
    (ℂ ∙ b i) = (ℂ ∙ b j) ↔ i = j := by
  constructor
  · intro heq
    by_contra hij
    have hmem : b i ∈ (ℂ ∙ b j) := heq ▸ Submodule.mem_span_singleton_self _
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
    have hinner : ⟪b j, b i⟫_ℂ = 0 := by rw [b.inner_eq_ite, if_neg (Ne.symm hij)]
    rw [← hk, inner_smul_right, b.inner_eq_ite, if_pos rfl, mul_one] at hinner
    have hbi0 : b i = 0 := by rw [← hk, hinner, zero_smul]
    have := b.norm_eq_one i
    rw [hbi0, norm_zero] at this
    norm_num at this
  · rintro rfl; rfl

/--
**FR.** Le stabilisateur monomial de `b` : les isométries qui envoient
chaque droite `ℂ∙(b i)` sur une droite (potentiellement différente)
`ℂ∙(b j)` de la même famille — phase ET permutation.

**EN.** The monomial stabilizer of `b`: the isometries that send every
line `ℂ∙(b i)` to a (possibly different) line `ℂ∙(b j)` of the same
family — phase AND permutation.
-/
def BasisMonomialStabilizer (b : OrthonormalBasis (Fin n) ℂ (H n)) :
    Subgroup (H n ≃ₗᵢ[ℂ] H n) where
  carrier := {U | ∀ i, ∃ j, (ℂ ∙ b i).map U.toLinearMap = ℂ ∙ b j}
  one_mem' := by
    intro i
    exact ⟨i, by show (ℂ ∙ b i).map LinearMap.id = ℂ ∙ b i; rw [Submodule.map_id]⟩
  mul_mem' := by
    intro U V hU hV i
    obtain ⟨j, hj⟩ := hV i
    obtain ⟨k, hk⟩ := hU j
    refine ⟨k, ?_⟩
    show (ℂ ∙ b i).map (U.toLinearMap ∘ₗ V.toLinearMap) = ℂ ∙ b k
    rw [Submodule.map_comp, hj, hk]
  inv_mem' := by
    intro U hU
    choose φ hφ using hU
    have hφ_inj : Function.Injective φ := by
      intro i1 i2 heq
      have h1 := hφ i1
      have h2 := hφ i2
      rw [heq] at h1
      have hmap_eq : (ℂ ∙ b i1).map U.toLinearMap = (ℂ ∙ b i2).map U.toLinearMap := h1.trans h2.symm
      exact line_eq_iff.mp (Submodule.map_injective_of_injective U.injective hmap_eq)
    have hφ_bij : Function.Bijective φ := Finite.injective_iff_bijective.mp hφ_inj
    intro i
    obtain ⟨i', hi'⟩ := hφ_bij.surjective i
    refine ⟨i', ?_⟩
    have h := congrArg (Submodule.map U⁻¹.toLinearMap) (hφ i')
    rw [← Submodule.map_comp] at h
    rw [show U⁻¹.toLinearMap ∘ₗ U.toLinearMap = LinearMap.id from by ext x; simp] at h
    rw [Submodule.map_id, hi'] at h
    exact h.symm

theorem BasisPhaseStabilizer_le_BasisMonomialStabilizer (b : OrthonormalBasis (Fin n) ℂ (H n)) :
    BasisPhaseStabilizer b ≤ BasisMonomialStabilizer b := by
  intro U hU i
  exact ⟨i, hU i⟩

/-- `U` monomial for `b` implies `U (b i) = c • b (e i)` along a permutation `e`,
for some unit-modulus `c`, with the matching inverse relation. -/
private theorem monomial_of_mem_BasisMonomialStabilizer {b : OrthonormalBasis (Fin n) ℂ (H n)}
    {U : H n ≃ₗᵢ[ℂ] H n} (hU : U ∈ BasisMonomialStabilizer b) :
    ∃ e : Fin n ≃ Fin n, ∀ i, ∃ c : ℂ, ‖c‖ = 1 ∧ U (b i) = c • b (e i) ∧
      U.symm (b (e i)) = (starRingEnd ℂ) c • b i := by
  choose φ hφ using hU
  have hφ_inj : Function.Injective φ := by
    intro i1 i2 heq
    have h1 := hφ i1
    have h2 := hφ i2
    rw [heq] at h1
    have hmap_eq : (ℂ ∙ b i1).map U.toLinearMap = (ℂ ∙ b i2).map U.toLinearMap := h1.trans h2.symm
    exact line_eq_iff.mp (Submodule.map_injective_of_injective U.injective hmap_eq)
  have hφ_bij : Function.Bijective φ := Finite.injective_iff_bijective.mp hφ_inj
  refine ⟨Equiv.ofBijective φ hφ_bij, fun i => ?_⟩
  have he : (Equiv.ofBijective φ hφ_bij) i = φ i := rfl
  rw [he]
  have hmem : U (b i) ∈ (ℂ ∙ b (φ i)) := by
    rw [← hφ i]
    exact Submodule.mem_map.mpr ⟨b i, Submodule.mem_span_singleton_self _, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hnorm : ‖c‖ = 1 := by
    have h1 : ‖U (b i)‖ = 1 := by rw [U.norm_map]; exact b.norm_eq_one i
    rw [← hc, norm_smul, b.norm_eq_one (φ i), mul_one] at h1
    exact h1
  refine ⟨c, hnorm, hc.symm, ?_⟩
  have hc_ne : c ≠ 0 := by intro h; rw [h] at hnorm; simp at hnorm
  have hsymm_apply : U.symm (U (b i)) = b i := U.symm_apply_apply (b i)
  rw [hc.symm, map_smul] at hsymm_apply
  have hinv : U.symm (b (φ i)) = c⁻¹ • b i := by
    have h2 : c⁻¹ • (c • U.symm (b (φ i))) = c⁻¹ • b i := by rw [hsymm_apply]
    rwa [smul_smul, inv_mul_cancel₀ hc_ne, one_smul] at h2
  rw [hinv, Complex.inv_eq_conj hnorm]

private theorem basisWeight_monomial {b : OrthonormalBasis (Fin n) ℂ (H n)}
    {U : H n ≃ₗᵢ[ℂ] H n} {e : Fin n ≃ Fin n} {c : ℂ} (hc1 : ‖c‖ = 1)
    (hUsymm : U.symm (b (e i)) = (starRingEnd ℂ) c • b i) (ψ : H n) :
    basisWeight b (U ψ) (e i) = basisWeight b ψ i := by
  show ‖⟪b (e i), U ψ⟫_ℂ‖ ^ 2 = ‖⟪b i, ψ⟫_ℂ‖ ^ 2
  have hiso : ⟪U.symm (b (e i)), ψ⟫_ℂ = ⟪b (e i), U ψ⟫_ℂ := by
    conv_rhs => rw [show b (e i) = U (U.symm (b (e i))) from (U.apply_symm_apply (b (e i))).symm]
    exact (U.inner_map_map (U.symm (b (e i))) ψ).symm
  rw [hUsymm, inner_smul_left, Complex.conj_conj] at hiso
  rw [← hiso, norm_mul, hc1, one_mul]

theorem dephasingSelector_isCovariantUnder_basisMonomialStabilizer
    (b : OrthonormalBasis (Fin n) ℂ (H n)) :
    IsCovariantUnder (BasisMonomialStabilizer b) (dephasingSelector b) := by
  intro U hU ψ _hψ
  obtain ⟨e, he⟩ := monomial_of_mem_BasisMonomialStabilizer hU
  apply LinearMap.ext
  intro x
  show dephasedDensity b (U ψ) x = U (dephasedDensity b ψ (U.symm x))
  rw [dephasedDensity_apply, dephasedDensity_apply, map_sum]
  symm
  apply Fintype.sum_equiv e
  intro i
  obtain ⟨c, hc1, hcU, hUsymm⟩ := he i
  rw [map_smul, map_smul, hcU]
  rw [basisWeight_monomial (i := i) hc1 hUsymm ψ]
  simp only [smul_smul]
  congr 1
  have hc_ne : c ≠ 0 := by intro h; rw [h] at hc1; simp at hc1
  have hcc : (starRingEnd ℂ) c * c = 1 := by
    rw [← Complex.inv_eq_conj hc1, inv_mul_cancel₀ hc_ne]
  have hiso : ⟪b i, U.symm x⟫_ℂ = (starRingEnd ℂ) c * ⟪b (e i), x⟫_ℂ := by
    have hstep : ⟪U (b i), U (U.symm x)⟫_ℂ = ⟪b i, U.symm x⟫_ℂ := U.inner_map_map (b i) (U.symm x)
    rw [U.apply_symm_apply, hcU, inner_smul_left] at hstep
    exact hstep.symm
  rw [hiso]
  linear_combination (basisWeight b ψ i : ℂ) * ⟪b (e i), x⟫_ℂ * hcc

/-!
### Density classification: phase-invariant densities are diagonal
-/

/--
**FR.** Une densité diagonale dans `b`, de poids `p` (vecteur de
probabilité). Définition TOTALE (`p` arbitraire, pas nécessairement un
vecteur de probabilité) : la validité en tant que densité est un lemme
séparé (`diagonalDensity_isDensity`).

**EN.** A density diagonal in `b`, with weights `p` (a probability
vector). TOTAL definition (`p` arbitrary, not necessarily a probability
vector): validity as a density is a separate lemma
(`diagonalDensity_isDensity`).
-/
def diagonalDensity (b : OrthonormalBasis (Fin n) ℂ (H n)) (p : Fin n → ℝ) : H n →ₗ[ℂ] H n :=
  ∑ i, (p i : ℂ) • basisProjection b i

/-- A finite family of nonnegative reals summing to `1`. -/
def IsProbabilityVector (p : Fin n → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

theorem diagonalDensity_apply_basis (b : OrthonormalBasis (Fin n) ℂ (H n)) (p : Fin n → ℝ)
    (j : Fin n) : diagonalDensity b p (b j) = (p j : ℂ) • b j := by
  show (∑ i, (p i : ℂ) • basisProjection b i) (b j) = _
  rw [LinearMap.sum_apply]
  simp_rw [LinearMap.smul_apply]
  have hcol : ∀ i, (p i : ℂ) • basisProjection b i (b j) = if i = j then (p j : ℂ) • b j else 0 := by
    intro i
    rw [basisProjection_apply, b.inner_eq_ite]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  simp_rw [hcol]
  rw [Finset.sum_ite_eq' Finset.univ j]
  simp

theorem diagonalDensity_apply (b : OrthonormalBasis (Fin n) ℂ (H n)) (p : Fin n → ℝ) (x : H n) :
    diagonalDensity b p x = ∑ i, (p i : ℂ) • (⟪b i, x⟫_ℂ • b i) := by
  show (∑ i, (p i : ℂ) • basisProjection b i) x = _
  rw [LinearMap.sum_apply]
  simp_rw [LinearMap.smul_apply, basisProjection_apply]

theorem diagonalDensity_isSymmetric (b : OrthonormalBasis (Fin n) ℂ (H n)) (p : Fin n → ℝ) :
    LinearMap.IsSymmetric (diagonalDensity b p) := by
  intro x y
  show ⟪(∑ i, (p i : ℂ) • basisProjection b i) x, y⟫_ℂ
    = ⟪x, (∑ i, (p i : ℂ) • basisProjection b i) y⟫_ℂ
  simp_rw [LinearMap.sum_apply, LinearMap.smul_apply, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  show ⟪(ℂ ∙ b i).starProjection x, y⟫_ℂ = ⟪x, (ℂ ∙ b i).starProjection y⟫_ℂ
  exact Submodule.starProjection_isSymmetric (ℂ ∙ b i) x y

theorem diagonalDensity_nonneg (b : OrthonormalBasis (Fin n) ℂ (H n)) {p : Fin n → ℝ}
    (hp : ∀ i, 0 ≤ p i) (x : H n) : 0 ≤ (⟪diagonalDensity b p x, x⟫_ℂ).re := by
  show 0 ≤ (⟪(∑ i, (p i : ℂ) • basisProjection b i) x, x⟫_ℂ).re
  simp_rw [LinearMap.sum_apply, LinearMap.smul_apply, sum_inner, inner_smul_left,
    Complex.conj_ofReal]
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [Complex.re_ofReal_mul]
  exact mul_nonneg (hp i) (Submodule.re_inner_starProjection_nonneg (ℂ ∙ b i) x)

theorem diagonalDensity_trace (b : OrthonormalBasis (Fin n) ℂ (H n)) (p : Fin n → ℝ) :
    LinearMap.trace ℂ (H n) (diagonalDensity b p) = ((∑ i, p i : ℝ) : ℂ) := by
  show LinearMap.trace ℂ (H n) (∑ i, (p i : ℂ) • basisProjection b i) = _
  rw [map_sum]
  simp_rw [map_smul]
  have htr : ∀ i, LinearMap.trace ℂ (H n) (basisProjection b i) = 1 :=
    fun i => trace_projL_singleton (b.norm_eq_one i)
  simp_rw [htr, smul_eq_mul, mul_one]
  rw [Complex.ofReal_sum]

theorem diagonalDensity_isDensity (b : OrthonormalBasis (Fin n) ℂ (H n)) {p : Fin n → ℝ}
    (hp : IsProbabilityVector p) : IsDensityOperator (diagonalDensity b p) :=
  ⟨diagonalDensity_isSymmetric b p, diagonalDensity_nonneg b hp.1, by
    rw [diagonalDensity_trace, hp.2]; norm_num⟩

theorem reflIso_mem_BasisPhaseStabilizer (b : OrthonormalBasis (Fin n) ℂ (H n)) (m : Fin n) :
    reflIso b m ∈ BasisPhaseStabilizer b := by
  intro i
  rw [map_span_singleton', reflIso_apply]
  by_cases h : i = m
  · rw [if_pos h, h]
    rw [show (-(b m) : H n) = (-1 : ℂ) • b m from by module]
    exact Submodule.span_singleton_smul_eq (by norm_num) (b m)
  · rw [if_neg h]

/--
**FR.** Si `ρ` est invariante sous le stabilisateur de phase de `b`, elle
est diagonale dans `b` : `⟨b i, ρ (b j)⟩ = 0` pour `i ≠ j`. Témoin : la
réflexion de signe `reflIso b i`, qui fixe `b j` et retourne `b i`.

**EN.** If `ρ` is invariant under the phase stabilizer of `b`, it is
diagonal in `b`: `⟨b i, ρ (b j)⟩ = 0` for `i ≠ j`. Witness: the sign
reflection `reflIso b i`, which fixes `b j` and flips `b i`.
-/
theorem offDiagonal_eq_zero_of_phaseInvariant {b : OrthonormalBasis (Fin n) ℂ (H n)}
    {ρ : H n →ₗ[ℂ] H n} (hinv : IsInvariantUnder (BasisPhaseStabilizer b) ρ) {i j : Fin n}
    (hij : i ≠ j) : ⟪b i, ρ (b j)⟫_ℂ = 0 := by
  set U := reflIso b i with hU_def
  have hUmem : U ∈ BasisPhaseStabilizer b := reflIso_mem_BasisPhaseStabilizer b i
  have hfix : U (b j) = b j := by rw [hU_def, reflIso_apply, if_neg (Ne.symm hij)]
  have hsymmfix : U.symm (b j) = b j := by
    rw [hU_def, reflIso_symm_apply, reflIso_apply, if_neg (Ne.symm hij)]
  have hfixed : ρ (b j) = U (ρ (b j)) := by
    have heq := hinv U hUmem
    have happ : U (ρ (U.symm (b j))) = ρ (b j) := by
      have h2 := LinearMap.congr_fun heq (b j)
      simpa using h2
    rw [hsymmfix] at happ
    exact happ.symm
  have hflip : ⟪b i, U (ρ (b j))⟫_ℂ = ⟪U.symm (b i), ρ (b j)⟫_ℂ := adjoint_apply U (b i) (ρ (b j))
  rw [show U.symm (b i) = -(b i) from by rw [hU_def, reflIso_symm_apply, reflIso_apply, if_pos rfl],
    inner_neg_left] at hflip
  have h1 : ⟪b i, ρ (b j)⟫_ℂ = ⟪b i, U (ρ (b j))⟫_ℂ := by rw [← hfixed]
  rw [hflip] at h1
  linear_combination h1 / 2

private theorem sum_inner_smul_self (b : OrthonormalBasis (Fin n) ℂ (H n)) (x : H n) :
    ∑ i, ⟪b i, x⟫_ℂ • b i = x := by
  conv_rhs => rw [← b.sum_repr x]
  apply Finset.sum_congr rfl
  intro i _
  rw [b.repr_apply_apply]

/--
**FR.** **Classification.** Une densité est invariante sous le
stabilisateur de PHASE de `b` si et seulement si elle est diagonale dans
`b` avec un vecteur de probabilité sur la diagonale.

**EN.** **Classification.** A density is invariant under the PHASE
stabilizer of `b` if and only if it is diagonal in `b` with a probability
vector on the diagonal.
-/
theorem phaseInvariant_density_iff_diagonal (b : OrthonormalBasis (Fin n) ℂ (H n))
    (ρ : H n →ₗ[ℂ] H n) :
    (IsDensityOperator ρ ∧ IsInvariantUnder (BasisPhaseStabilizer b) ρ) ↔
      ∃ p : Fin n → ℝ, IsProbabilityVector p ∧ ρ = diagonalDensity b p := by
  constructor
  · rintro ⟨hdens, hinv⟩
    set p : Fin n → ℝ := fun i => (⟪b i, ρ (b i)⟫_ℂ).re with hp_def
    have hreal : ∀ i, ⟪b i, ρ (b i)⟫_ℂ = (p i : ℂ) := by
      intro i
      have hsymmk : ⟪ρ (b i), b i⟫_ℂ = ⟪b i, ρ (b i)⟫_ℂ := hdens.symmetric (b i) (b i)
      have hconjeq : (starRingEnd ℂ) ⟪b i, ρ (b i)⟫_ℂ = ⟪b i, ρ (b i)⟫_ℂ := by
        rw [inner_conj_symm, hsymmk]
      rw [hp_def]
      exact (Complex.conj_eq_iff_re.mp hconjeq).symm
    have hρ_diag : ∀ i, ρ (b i) = (p i : ℂ) • b i := by
      intro i
      have hexp : ∑ k, ⟪b k, ρ (b i)⟫_ℂ • b k = ρ (b i) := sum_inner_smul_self b (ρ (b i))
      have hcollapse : ∑ k, ⟪b k, ρ (b i)⟫_ℂ • b k = ⟪b i, ρ (b i)⟫_ℂ • b i := by
        apply Finset.sum_eq_single
        · intro k _ hk
          rw [offDiagonal_eq_zero_of_phaseInvariant hinv hk, zero_smul]
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [hcollapse, hreal i] at hexp
      exact hexp.symm
    have hρ_eq : ρ = diagonalDensity b p := by
      apply b.toBasis.ext
      intro i
      rw [OrthonormalBasis.coe_toBasis, diagonalDensity_apply_basis]
      exact hρ_diag i
    refine ⟨p, ⟨?_, ?_⟩, hρ_eq⟩
    · intro i
      have h1 : (⟪ρ (b i), b i⟫_ℂ).re = p i := by
        show (⟪ρ (b i), b i⟫_ℂ).re = (⟪b i, ρ (b i)⟫_ℂ).re
        rw [hdens.symmetric (b i) (b i)]
      rw [← h1]
      exact hdens.nonneg (b i)
    · have h1 := hdens.trace_one
      rw [hρ_eq, diagonalDensity_trace] at h1
      exact_mod_cast h1
  · rintro ⟨p, hp, rfl⟩
    refine ⟨diagonalDensity_isDensity b hp, ?_⟩
    intro U hU
    apply LinearMap.ext
    intro x
    show U (diagonalDensity b p (U.symm x)) = diagonalDensity b p x
    rw [diagonalDensity_apply, diagonalDensity_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, map_smul]
    obtain ⟨c, _hc1, hcU, hUsymm⟩ := phase_of_mem_BasisPhaseStabilizer hU i
    rw [hcU]
    simp only [smul_smul]
    congr 1
    have hiso2 : ⟪b i, x⟫_ℂ = ⟪U.symm (b i), U.symm x⟫_ℂ := (U.symm.inner_map_map (b i) x).symm
    rw [hUsymm, inner_smul_left, Complex.conj_conj] at hiso2
    rw [hiso2]
    ring

/-!
### Density classification: monomial-invariant densities are maximally mixed
-/

theorem swapIso_mem_BasisMonomialStabilizer (b : OrthonormalBasis (Fin n) ℂ (H n)) (i j : Fin n) :
    swapIso b i j ∈ BasisMonomialStabilizer b := by
  intro k
  refine ⟨Equiv.swap i j k, ?_⟩
  rw [map_span_singleton', swapIso_apply]

theorem basisProjection_sum_eq_one (b : OrthonormalBasis (Fin n) ℂ (H n)) :
    ∑ i, basisProjection b i = LinearMap.id := by
  apply LinearMap.ext; intro x
  show (∑ i, basisProjection b i) x = x
  rw [LinearMap.sum_apply]
  simp_rw [basisProjection_apply]
  conv_rhs => rw [← OrthonormalBasis.sum_repr b x]
  apply Finset.sum_congr rfl
  intro i _
  rw [OrthonormalBasis.repr_apply_apply]

/--
**FR.** L'état maximalement mélangé `(1/n)•Id`, indépendant de tout choix
de base par construction.

**EN.** The maximally mixed state `(1/n)•Id`, basis-independent by
construction.
-/
noncomputable def maximallyMixedDensity (n : ℕ) : H n →ₗ[ℂ] H n := ((n : ℝ)⁻¹ : ℂ) • LinearMap.id

theorem diagonalDensity_const_eq_maximallyMixed (b : OrthonormalBasis (Fin n) ℂ (H n))
    (_hn : 0 < n) : diagonalDensity b (fun _ => (n : ℝ)⁻¹) = maximallyMixedDensity n := by
  show (∑ i : Fin n, (((n : ℝ)⁻¹ : ℝ) : ℂ) • basisProjection b i) = _
  rw [← Finset.smul_sum]
  rw [show (∑ i : Fin n, basisProjection b i) = LinearMap.id from basisProjection_sum_eq_one b]
  unfold maximallyMixedDensity
  norm_cast

/--
**FR.** **Classification.** Une densité est invariante sous le
stabilisateur MONOMIAL de `b` si et seulement si elle est l'état
maximalement mélangé — bien plus restrictif que la classification par le
seul stabilisateur de phase.

**EN.** **Classification.** A density is invariant under the MONOMIAL
stabilizer of `b` if and only if it is the maximally mixed state — far
more restrictive than the classification by the phase stabilizer alone.
-/
theorem monomialInvariant_density_iff_maximallyMixed (b : OrthonormalBasis (Fin n) ℂ (H n))
    (hn : 0 < n) (ρ : H n →ₗ[ℂ] H n) :
    (IsDensityOperator ρ ∧ IsInvariantUnder (BasisMonomialStabilizer b) ρ) ↔
      ρ = maximallyMixedDensity n := by
  constructor
  · rintro ⟨hdens, hinv⟩
    have hinv' : IsInvariantUnder (BasisPhaseStabilizer b) ρ :=
      isInvariantUnder_mono (BasisPhaseStabilizer_le_BasisMonomialStabilizer b) hinv
    obtain ⟨p, hp, hρ_eq⟩ := (phaseInvariant_density_iff_diagonal b ρ).mp ⟨hdens, hinv'⟩
    have hconst : ∀ i j : Fin n, p i = p j := by
      intro i j
      have hUmem : swapIso b i j ∈ BasisMonomialStabilizer b :=
        swapIso_mem_BasisMonomialStabilizer b i j
      have heq := hinv (swapIso b i j) hUmem
      have happ : (swapIso b i j) (ρ ((swapIso b i j).symm (b i))) = ρ (b i) := by
        have h2 := LinearMap.congr_fun heq (b i)
        simpa using h2
      rw [swapIso_symm, swapIso_apply, Equiv.swap_apply_left, hρ_eq, diagonalDensity_apply_basis,
        map_smul, swapIso_apply, Equiv.swap_apply_right, diagonalDensity_apply_basis] at happ
      have hbi_ne : (b i : H n) ≠ 0 := by
        intro h
        have := b.norm_eq_one i
        rw [h, norm_zero] at this
        norm_num at this
      have : (p j : ℂ) = (p i : ℂ) := by
        have hs := happ
        rw [smul_left_injective ℂ hbi_ne |>.eq_iff] at hs
        exact hs
      exact_mod_cast this.symm
    have hp_val : ∀ i, p i = (n : ℝ)⁻¹ := by
      intro i
      have hsum : (n : ℝ) * p i = 1 := by
        have heq2 : ∑ j : Fin n, p j = (n : ℝ) * p i := by
          rw [Finset.sum_congr rfl (fun j _ => hconst j i), Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
        rw [← heq2, hp.2]
      have hn_ne : (n : ℝ) ≠ 0 := by positivity
      field_simp
      linarith [hsum]
    have hp_eq : p = fun _ => (n : ℝ)⁻¹ := funext hp_val
    rw [hρ_eq, hp_eq, diagonalDensity_const_eq_maximallyMixed b hn]
  · rintro rfl
    have hp : IsProbabilityVector (fun _ : Fin n => (n : ℝ)⁻¹) := by
      constructor
      · intro i; positivity
      · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hn_ne : (n : ℝ) ≠ 0 := by positivity
        field_simp
    refine ⟨(diagonalDensity_const_eq_maximallyMixed b hn) ▸ diagonalDensity_isDensity b hp, ?_⟩
    have htop : IsInvariantUnder (⊤ : Subgroup (H n ≃ₗᵢ[ℂ] H n)) (maximallyMixedDensity n) := by
      intro U _
      show U.toLinearMap ∘ₗ maximallyMixedDensity n ∘ₗ U.symm.toLinearMap = maximallyMixedDensity n
      unfold maximallyMixedDensity
      apply LinearMap.ext
      intro x
      simp
    exact isInvariantUnder_mono le_top htop

/-!
### Correcting the false claim, and the two-dimensional case
-/

/--
**FR.** Correction de l'affirmation fausse « le stabilisateur (monomial)
d'une base admet toutes les densités » : c'est faux —
`monomialInvariant_density_iff_maximallyMixed` montre qu'il n'en admet
exactement qu'UNE, l'état maximalement mélangé. Témoin explicite : la
densité de Born (pure) sur `b i0`, qui diffère de l'état maximalement
mélangé en `b i1`.

**EN.** Correction of the false claim "a basis's (monomial) stabilizer
admits all densities": this is false —
`monomialInvariant_density_iff_maximallyMixed` shows it admits EXACTLY
one, the maximally mixed state. Explicit witness: the (pure) Born density
on `b i0`, which disagrees with the maximally mixed state at `b i1`.
-/
theorem exists_density_not_invariant_under_basisMonomialStabilizer
    (hn : 2 ≤ n) (b : OrthonormalBasis (Fin n) ℂ (H n)) :
    ∃ ρ : H n →ₗ[ℂ] H n, IsDensityOperator ρ ∧
      ¬ IsInvariantUnder (BasisMonomialStabilizer b) ρ := by
  refine ⟨projL (ℂ ∙ b (i0 hn)),
    ⟨Submodule.starProjection_isSymmetric _,
      fun z => Submodule.re_inner_starProjection_nonneg (ℂ ∙ b (i0 hn)) z,
      trace_projL_singleton (b.norm_eq_one (i0 hn))⟩, ?_⟩
  intro hinv
  have hdens : IsDensityOperator (projL (ℂ ∙ b (i0 hn)) : H n →ₗ[ℂ] H n) :=
    ⟨Submodule.starProjection_isSymmetric _,
      fun z => Submodule.re_inner_starProjection_nonneg (ℂ ∙ b (i0 hn)) z,
      trace_projL_singleton (b.norm_eq_one (i0 hn))⟩
  have heq := (monomialInvariant_density_iff_maximallyMixed b (by omega) _).mp ⟨hdens, hinv⟩
  have h1 : (projL (ℂ ∙ b (i0 hn)) : H n →ₗ[ℂ] H n) (b (i1 hn)) = 0 := by
    rw [QuantumFoundations.Uhlhorn.projL_singleton_unit (b (i0 hn)) (b (i1 hn))
        (b.norm_eq_one (i0 hn)), b.inner_eq_ite, if_neg (i0_ne_i1 hn), zero_smul]
  have h2 : maximallyMixedDensity n (b (i1 hn)) = ((n : ℝ)⁻¹ : ℂ) • b (i1 hn) := by
    show (((n : ℝ)⁻¹ : ℂ) • LinearMap.id) (b (i1 hn)) = _
    simp
  rw [heq, h2] at h1
  have hn_ne : ((n : ℝ)⁻¹ : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, inv_eq_zero, Nat.cast_eq_zero]
    omega
  have hbi1_ne : (b (i1 hn) : H n) ≠ 0 := by
    intro h
    have := b.norm_eq_one (i1 hn)
    rw [h, norm_zero] at this
    norm_num at this
  exact hbi1_ne ((smul_eq_zero.mp h1).resolve_left hn_ne)

/--
**FR.** Spécialisation en dimension 2 : la classification monomiale se
lit `ρ = (1/2)•Id`.

**EN.** Two-dimensional specialization: the monomial classification reads
`ρ = (1/2)•Id`.
-/
theorem twoDimensional_monomialInvariant_density_eq_halfIdentity
    (b : OrthonormalBasis (Fin 2) ℂ (H 2)) (ρ : H 2 →ₗ[ℂ] H 2) :
    (IsDensityOperator ρ ∧ IsInvariantUnder (BasisMonomialStabilizer b) ρ) ↔
      ρ = ((2 : ℝ)⁻¹ : ℂ) • LinearMap.id := by
  have := monomialInvariant_density_iff_maximallyMixed b (by norm_num) ρ
  rwa [maximallyMixedDensity] at this

end
end QuantumFoundations.Selector
