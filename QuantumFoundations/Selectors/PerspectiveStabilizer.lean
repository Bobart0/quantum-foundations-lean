import QuantumFoundations.Selectors.PerspectiveDephasing

/-!
**FR.** # Selectors — Module B, stabilisateurs d'une perspective générale

Généralise `BasisPhaseStabilizer`/`BasisMonomialStabilizer`
(`BasisStabilizer.lean`) aux perspectives quelconques
(`QuantumFoundations.BornRule.Perspective`), cellules de dimension
arbitraire :

- **`PerspectiveCellwiseStabilizer D`** : les isométries qui fixent
  chaque cellule `c ∈ D.cells` SETWISE (`c.map U = c`), sans contrainte
  sur l'action de `U` À L'INTÉRIEUR de `c` — l'analogue exact de
  `BasisPhaseStabilizer` (qui, pour des cellules de dimension 1,
  contraint exactement à une phase). Caractérisé de façon équivalente par
  la commutation avec la projection de chaque cellule
  (`mem_cellwiseStabilizer_iff_commutes_cellProjection`).
- **`PerspectiveSetwiseStabilizer D`** : les isométries qui envoient
  chaque cellule sur une AUTRE cellule de la même famille — l'analogue de
  `BasisMonomialStabilizer`. Contient le premier
  (`PerspectiveCellwiseStabilizer_le_PerspectiveSetwiseStabilizer`).

Le sélecteur de pinçage `perspectiveDephasingSelector D`
(`PerspectiveDephasing.lean`) est covariant sous les DEUX groupes
(`perspectiveDephasingSelector_isCovariantUnder_cellwiseStabilizer`,
`..._setwiseStabilizer`) : la preuve route par la commutation
`U ∘ P_c = P_{U(c)} ∘ U` (`Submodule.starProjection_map_apply`), le
transport de la densité de Born pure (`U ∘ |ψ⟩⟨ψ| ∘ U⁻¹ = |Uψ⟩⟨Uψ|`), et,
pour le stabilisateur setwise, un réindiçage de la somme sur les cellules
via la bijection induite par `U` (`Finset.sum_nbij'`,
`Finset.surjOn_of_injOn_of_card_le`).

**EN.** # Selectors — Module B, stabilizers of a general perspective

Generalizes `BasisPhaseStabilizer`/`BasisMonomialStabilizer`
(`BasisStabilizer.lean`) to arbitrary perspectives
(`QuantumFoundations.BornRule.Perspective`), with cells of arbitrary
dimension:

- **`PerspectiveCellwiseStabilizer D`**: the isometries that fix every
  cell `c ∈ D.cells` SETWISE (`c.map U = c`), with no constraint on how
  `U` acts INSIDE `c` — the exact analogue of `BasisPhaseStabilizer`
  (which, for dimension-1 cells, constrains exactly to a phase).
  Equivalently characterized by commuting with each cell's projection
  (`mem_cellwiseStabilizer_iff_commutes_cellProjection`).
- **`PerspectiveSetwiseStabilizer D`**: the isometries that send every
  cell to SOME OTHER cell of the same family — the analogue of
  `BasisMonomialStabilizer`. Contains the first
  (`PerspectiveCellwiseStabilizer_le_PerspectiveSetwiseStabilizer`).

The pinching selector `perspectiveDephasingSelector D`
(`PerspectiveDephasing.lean`) is covariant under BOTH groups
(`perspectiveDephasingSelector_isCovariantUnder_cellwiseStabilizer`,
`..._setwiseStabilizer`): the proof routes through the commutation
`U ∘ P_c = P_{U(c)} ∘ U` (`Submodule.starProjection_map_apply`), the
transport of the pure Born density (`U ∘ |ψ⟩⟨ψ| ∘ U⁻¹ = |Uψ⟩⟨Uψ|`), and,
for the setwise stabilizer, a reindexing of the sum over cells via the
bijection induced by `U` (`Finset.sum_nbij'`,
`Finset.surjOn_of_injOn_of_card_le`).
-/

namespace QuantumFoundations.Selector

open scoped InnerProductSpace
open Gleason
open QuantumFoundations.BornRule
open scoped Classical

noncomputable section

variable {n : ℕ}

private theorem conj_projL' (U : H n ≃ₗᵢ[ℂ] H n) (A : Submodule ℂ (H n)) :
    U.toLinearMap ∘ₗ projL A ∘ₗ U.symm.toLinearMap = projL (A.map U.toLinearMap) := by
  apply LinearMap.ext
  intro x
  exact (Submodule.starProjection_map_apply U A x).symm

private theorem projL_injective {A B : Submodule ℂ (H n)} (h : projL A = projL B) : A = B := by
  apply Submodule.ext
  intro x
  constructor
  · intro hx
    have hAx : A.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
    have h2 : projL B x = x := by rw [← h]; exact hAx
    exact Submodule.starProjection_eq_self_iff.mp h2
  · intro hx
    have hBx : B.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
    have h2 : projL A x = x := by rw [h]; exact hBx
    exact Submodule.starProjection_eq_self_iff.mp h2

/--
**FR.** Le stabilisateur cellule-par-cellule de `D` : les isométries qui
fixent SETWISE chaque cellule.

**EN.** The cell-by-cell stabilizer of `D`: the isometries that fix every
cell SETWISE.
-/
def PerspectiveCellwiseStabilizer (D : Perspective n) : Subgroup (H n ≃ₗᵢ[ℂ] H n) where
  carrier := {U | ∀ c ∈ D.cells, c.map U.toLinearMap = c}
  one_mem' := by
    intro c _
    show c.map LinearMap.id = c
    rw [Submodule.map_id]
  mul_mem' := by
    intro U V hU hV c hc
    show c.map (U.toLinearMap ∘ₗ V.toLinearMap) = c
    rw [Submodule.map_comp, hV c hc, hU c hc]
  inv_mem' := by
    intro U hU c hc
    have h := congrArg (Submodule.map U⁻¹.toLinearMap) (hU c hc)
    rw [← Submodule.map_comp] at h
    rw [show U⁻¹.toLinearMap ∘ₗ U.toLinearMap = LinearMap.id from by ext x; simp] at h
    rw [Submodule.map_id] at h
    exact h.symm

/--
**FR.** Le stabilisateur setwise de `D` : les isométries qui envoient
chaque cellule sur une (potentiellement différente) cellule de `D`.

**EN.** The setwise stabilizer of `D`: the isometries that send every
cell to a (possibly different) cell of `D`.
-/
def PerspectiveSetwiseStabilizer (D : Perspective n) : Subgroup (H n ≃ₗᵢ[ℂ] H n) where
  carrier := {U | ∀ c ∈ D.cells, ∃ c' ∈ D.cells, c.map U.toLinearMap = c'}
  one_mem' := by
    intro c hc
    exact ⟨c, hc, by show c.map LinearMap.id = c; rw [Submodule.map_id]⟩
  mul_mem' := by
    intro U V hU hV c hc
    obtain ⟨c', hc', hVc⟩ := hV c hc
    obtain ⟨c'', hc'', hUc'⟩ := hU c' hc'
    refine ⟨c'', hc'', ?_⟩
    show c.map (U.toLinearMap ∘ₗ V.toLinearMap) = c''
    rw [Submodule.map_comp, hVc, hUc']
  inv_mem' := by
    intro U hU
    classical
    set φ : Submodule ℂ (H n) → Submodule ℂ (H n) :=
      fun c => if h : c ∈ D.cells then (hU c h).choose else c with hφ_def
    have hφmem : ∀ c ∈ D.cells, φ c ∈ D.cells := by
      intro c hc; rw [hφ_def]; simp only [dif_pos hc]; exact (hU c hc).choose_spec.1
    have hφ : ∀ c ∈ D.cells, c.map U.toLinearMap = φ c := by
      intro c hc; rw [hφ_def]; simp only [dif_pos hc]; exact (hU c hc).choose_spec.2
    have hφ_inj : Set.InjOn φ (D.cells : Set (Submodule ℂ (H n))) := by
      intro c1 hc1 c2 hc2 heq
      have h1 := hφ c1 hc1
      have h2 := hφ c2 hc2
      rw [heq] at h1
      have hmap_eq : c1.map U.toLinearMap = c2.map U.toLinearMap := h1.trans h2.symm
      exact Submodule.map_injective_of_injective U.injective hmap_eq
    have hφ_mapsTo : Set.MapsTo φ (D.cells : Set (Submodule ℂ (H n))) (D.cells : Set (Submodule ℂ (H n))) :=
      fun c hc => hφmem c hc
    have hφ_surjOn : Set.SurjOn φ (D.cells : Set (Submodule ℂ (H n))) (D.cells : Set (Submodule ℂ (H n))) :=
      Finset.surjOn_of_injOn_of_card_le φ hφ_mapsTo hφ_inj (le_refl _)
    intro c hc
    obtain ⟨c', hc', hc'eq⟩ := hφ_surjOn hc
    refine ⟨c', hc', ?_⟩
    have h := congrArg (Submodule.map U⁻¹.toLinearMap) (hφ c' hc')
    rw [← Submodule.map_comp] at h
    rw [show U⁻¹.toLinearMap ∘ₗ U.toLinearMap = LinearMap.id from by ext x; simp] at h
    rw [Submodule.map_id, hc'eq] at h
    exact h.symm

theorem PerspectiveCellwiseStabilizer_le_PerspectiveSetwiseStabilizer (D : Perspective n) :
    PerspectiveCellwiseStabilizer D ≤ PerspectiveSetwiseStabilizer D := by
  intro U hU c hc
  exact ⟨c, hc, hU c hc⟩

/-- The image cell picked out by a setwise-stabilizing `U`, as a plain
(non-dependent) function -- needed to reindex sums over `D.cells` via a
bijection. -/
private noncomputable def setwiseImage (D : Perspective n) {U : H n ≃ₗᵢ[ℂ] H n}
    (hU : U ∈ PerspectiveSetwiseStabilizer D) (c : Submodule ℂ (H n)) : Submodule ℂ (H n) :=
  if h : c ∈ D.cells then (hU c h).choose else c

private theorem setwiseImage_mem (D : Perspective n) {U : H n ≃ₗᵢ[ℂ] H n}
    (hU : U ∈ PerspectiveSetwiseStabilizer D) {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
    setwiseImage D hU c ∈ D.cells := by
  show (if h : c ∈ D.cells then (hU c h).choose else c) ∈ D.cells
  rw [dif_pos hc]
  exact (hU c hc).choose_spec.1

private theorem setwiseImage_spec (D : Perspective n) {U : H n ≃ₗᵢ[ℂ] H n}
    (hU : U ∈ PerspectiveSetwiseStabilizer D) {c : Submodule ℂ (H n)} (hc : c ∈ D.cells) :
    c.map U.toLinearMap = setwiseImage D hU c := by
  show c.map U.toLinearMap = (if h : c ∈ D.cells then (hU c h).choose else c)
  rw [dif_pos hc]
  exact (hU c hc).choose_spec.2

theorem mem_cellwiseStabilizer_iff_commutes_cellProjection (D : Perspective n)
    (U : H n ≃ₗᵢ[ℂ] H n) :
    U ∈ PerspectiveCellwiseStabilizer D ↔
      ∀ c : Perspective.Cell D, U.toLinearMap ∘ₗ cellProjection D c ∘ₗ U.symm.toLinearMap
        = cellProjection D c := by
  constructor
  · intro hU c
    show U.toLinearMap ∘ₗ projL (c.1 : Submodule ℂ (H n)) ∘ₗ U.symm.toLinearMap = projL c.1
    rw [conj_projL', hU c.1 c.2]
  · intro hU c hc
    have h := hU ⟨c, hc⟩
    show c.map U.toLinearMap = c
    apply projL_injective
    rw [← conj_projL']
    exact h

end

private theorem comp_sum' {ι : Type*} (s : Finset ι) (f : ι → (H n →ₗ[ℂ] H n)) (g : H n →ₗ[ℂ] H n) :
    g ∘ₗ (∑ i ∈ s, f i) = ∑ i ∈ s, g ∘ₗ f i := by
  apply LinearMap.ext; intro x; simp [LinearMap.sum_apply]

private theorem sum_comp' {ι : Type*} (s : Finset ι) (f : ι → (H n →ₗ[ℂ] H n)) (g : H n →ₗ[ℂ] H n) :
    (∑ i ∈ s, f i) ∘ₗ g = ∑ i ∈ s, f i ∘ₗ g := by
  apply LinearMap.ext; intro x; simp [LinearMap.sum_apply]

private theorem conj_bornDensity (U : H n ≃ₗᵢ[ℂ] H n) (ψ : H n) :
    U.toLinearMap ∘ₗ projL (ℂ ∙ ψ) ∘ₗ U.symm.toLinearMap = projL (ℂ ∙ (U ψ)) := by
  rw [conj_projL']
  congr 1
  rw [Submodule.map_span, Set.image_singleton]; rfl

theorem perspectiveDephasingSelector_isCovariantUnder_cellwiseStabilizer (D : Perspective n) :
    IsCovariantUnder (PerspectiveCellwiseStabilizer D) (perspectiveDephasingSelector D) := by
  intro U hU ψ _hψ
  show perspectiveDephasedDensity D (U ψ)
    = U.toLinearMap ∘ₗ perspectiveDephasedDensity D ψ ∘ₗ U.symm.toLinearMap
  show (∑ c ∈ D.cells, projL c ∘ₗ projL (ℂ ∙ (U ψ)) ∘ₗ projL c)
    = U.toLinearMap ∘ₗ (∑ c ∈ D.cells, projL c ∘ₗ projL (ℂ ∙ ψ) ∘ₗ projL c) ∘ₗ U.symm.toLinearMap
  rw [sum_comp', comp_sum']
  apply Finset.sum_congr rfl
  intro c hc
  have hUc : U.toLinearMap ∘ₗ projL c ∘ₗ U.symm.toLinearMap = projL c := by
    rw [conj_projL', hU c hc]
  have hcomm : ∀ y, U (projL c y) = projL c (U y) := by
    intro y
    have h1 := LinearMap.congr_fun hUc (U y)
    simpa using h1
  have hcomm' : ∀ z, U.symm (projL c z) = projL c (U.symm z) := by
    intro z
    have h2 := hcomm (U.symm z)
    rw [U.apply_symm_apply] at h2
    have h3 : U.symm (U (projL c (U.symm z))) = U.symm (projL c z) := by rw [h2]
    simpa using h3.symm
  show projL c ∘ₗ projL (ℂ ∙ (U ψ)) ∘ₗ projL c
    = U.toLinearMap ∘ₗ (projL c ∘ₗ projL (ℂ ∙ ψ) ∘ₗ projL c) ∘ₗ U.symm.toLinearMap
  apply LinearMap.ext
  intro x
  show projL c (projL (ℂ ∙ (U ψ)) (projL c x))
    = U (projL c (projL (ℂ ∙ ψ) (projL c (U.symm x))))
  rw [← hcomm' x]
  have hQ : ∀ y, U.symm (projL (ℂ ∙ (U ψ)) y) = projL (ℂ ∙ ψ) (U.symm y) := by
    intro y
    have h4 := LinearMap.congr_fun (conj_bornDensity U ψ) y
    simp only [LinearMap.comp_apply] at h4
    have h5 : U.symm (U (projL (ℂ ∙ ψ) (U.symm y))) = U.symm (projL (ℂ ∙ (U ψ)) y) :=
      congrArg U.symm h4
    simpa using h5.symm
  rw [← hQ]
  rw [← hcomm' (projL (ℂ ∙ (U ψ)) (projL c x))]
  rw [U.apply_symm_apply]

theorem perspectiveDephasingSelector_isCovariantUnder_setwiseStabilizer (D : Perspective n) :
    IsCovariantUnder (PerspectiveSetwiseStabilizer D) (perspectiveDephasingSelector D) := by
  intro U hU ψ _hψ
  show perspectiveDephasedDensity D (U ψ)
    = U.toLinearMap ∘ₗ perspectiveDephasedDensity D ψ ∘ₗ U.symm.toLinearMap
  show (∑ c ∈ D.cells, projL c ∘ₗ projL (ℂ ∙ (U ψ)) ∘ₗ projL c)
    = U.toLinearMap ∘ₗ (∑ c ∈ D.cells, projL c ∘ₗ projL (ℂ ∙ ψ) ∘ₗ projL c) ∘ₗ U.symm.toLinearMap
  rw [sum_comp', comp_sum']
  set φ := setwiseImage D hU with hφ_def
  have hφmem : ∀ c ∈ D.cells, φ c ∈ D.cells := fun c hc => setwiseImage_mem D hU hc
  have hφ : ∀ c ∈ D.cells, c.map U.toLinearMap = φ c := fun c hc => setwiseImage_spec D hU hc
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
  symm
  apply Finset.sum_nbij' φ ψinv hφmem hψinv_mem
  · intro c hc
    exact hφ_inj (hψinv_mem (φ c) (hφmem c hc)) hc (hψinv (φ c) (hφmem c hc))
  · exact hψinv
  · intro c hc
    show U.toLinearMap ∘ₗ (projL c ∘ₗ projL (ℂ ∙ ψ) ∘ₗ projL c) ∘ₗ U.symm.toLinearMap
      = projL (φ c) ∘ₗ projL (ℂ ∙ (U ψ)) ∘ₗ projL (φ c)
    have hUc' : U.toLinearMap ∘ₗ projL c ∘ₗ U.symm.toLinearMap = projL (φ c) := by
      rw [conj_projL', hφ c hc]
    have hcomm : ∀ y, U (projL c y) = projL (φ c) (U y) := by
      intro y
      have h1 := LinearMap.congr_fun hUc' (U y)
      simpa using h1
    have hcomm' : ∀ z, U.symm (projL (φ c) z) = projL c (U.symm z) := by
      intro z
      have h2 := hcomm (U.symm z)
      rw [U.apply_symm_apply] at h2
      have h3 : U.symm (U (projL c (U.symm z))) = U.symm (projL (φ c) z) := by rw [h2]
      simpa using h3.symm
    apply LinearMap.ext
    intro x
    show U (projL c (projL (ℂ ∙ ψ) (projL c (U.symm x))))
      = projL (φ c) (projL (ℂ ∙ (U ψ)) (projL (φ c) x))
    rw [← hcomm' x]
    have hQ : ∀ y, U.symm (projL (ℂ ∙ (U ψ)) y) = projL (ℂ ∙ ψ) (U.symm y) := by
      intro y
      have h4 := LinearMap.congr_fun (conj_bornDensity U ψ) y
      simp only [LinearMap.comp_apply] at h4
      have h5 : U.symm (U (projL (ℂ ∙ ψ) (U.symm y))) = U.symm (projL (ℂ ∙ (U ψ)) y) :=
        congrArg U.symm h4
      simpa using h5.symm
    rw [← hQ]
    rw [← hcomm' (projL (ℂ ∙ (U ψ)) (projL (φ c) x))]
    rw [U.apply_symm_apply]

end QuantumFoundations.Selector
