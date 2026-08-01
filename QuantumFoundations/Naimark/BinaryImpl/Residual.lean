import QuantumFoundations.Naimark.BinaryImpl.MinimalUniqueness

/-!
**FR.** # Secteurs résiduels : les deux multiplicités qui distinguent des
implémentations non minimales

Pour une implémentation `I` PAS nécessairement minimale, l'orthogonal
`residualSubspace I := (minimalSubspace I)ᗮ` porte la partie de l'espace
ambiant que les deux jambes n'engendrent pas. Comme `I.cell` préserve
`minimalSubspace I` (`minimalSubspace_isReducing`, `Minimal.lean`), il
préserve aussi son orthogonal, et s'y comporte ENCORE comme une
projection : `residualEvent I`/`residualComplement I` sont ses deux
secteurs propres (`+1`/`0`) à l'intérieur du résidu.

Les dimensions `excessEventDim`/`excessComplementDim` de ces deux secteurs
sont EXACTEMENT les deux multiplicités qui distinguent, à effet fixé, deux
implémentations non minimales (`StrictClassification.lean` les identifie
comme invariants complets de `StrictIso`). Les décompositions additives
(`ambientDim_decomposition`, `projectorRank_decomposition`,
`projectorNullity_decomposition`) expriment toutes les quantités globales
de `I` comme somme d'une partie MINIMALE (qui ne dépend que de `E`, via
`eventGeneratedEquiv`/`complementGeneratedEquiv` de `GramRange.lean`) et
d'une partie RÉSIDUELLE (qui dépend de `I`).

**EN.** # Residual sectors: the two multiplicities distinguishing
non-minimal implementations

For an implementation `I` NOT necessarily minimal, the orthogonal
complement `residualSubspace I := (minimalSubspace I)ᗮ` carries the part
of the ambient space the two legs do not generate. Since `I.cell`
preserves `minimalSubspace I` (`minimalSubspace_isReducing`,
`Minimal.lean`), it also preserves its orthogonal complement, and STILL
behaves there as a projection: `residualEvent I`/`residualComplement I`
are its two eigenspaces (`+1`/`0`) inside the residue.

The dimensions `excessEventDim`/`excessComplementDim` of these two sectors
are EXACTLY the two multiplicities that distinguish, at a fixed effect,
two non-minimal implementations (`StrictClassification.lean` identifies
them as complete invariants of `StrictIso`). The additive decompositions
(`ambientDim_decomposition`, `projectorRank_decomposition`,
`projectorNullity_decomposition`) express every global quantity of `I` as
the sum of a MINIMAL part (depending only on `E`, via
`eventGeneratedEquiv`/`complementGeneratedEquiv` from `GramRange.lean`)
and a RESIDUAL part (depending on `I`).
-/

namespace QuantumFoundations.Naimark.BinaryImpl

open QuantumFoundations Gleason
open scoped InnerProductSpace

noncomputable section

variable {n : ℕ} {E : H n →ₗ[ℂ] H n} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The residual subspace: the part of the ambient space NOT accounted for
by the two legs. -/
def residualSubspace (I : BinaryImpl n E ι) : Submodule ℂ (EuclideanSpace ℂ ι) :=
  (minimalSubspace I)ᗮ

/-- The residual "event" sector: the part of the residual subspace on
which `I.cell` acts as the identity. -/
def residualEvent (I : BinaryImpl n E ι) : Submodule ℂ (EuclideanSpace ℂ ι) :=
  LinearMap.range I.cell ⊓ residualSubspace I

/-- The residual "complement" sector: the part of the residual subspace on
which `I.cell` acts as zero. -/
def residualComplement (I : BinaryImpl n E ι) : Submodule ℂ (EuclideanSpace ℂ ι) :=
  LinearMap.ker I.cell ⊓ residualSubspace I

private theorem range_le_ker_orthogonal (I : BinaryImpl n E ι) :
    LinearMap.range I.cell ≤ (LinearMap.ker I.cell)ᗮ := by
  rintro y ⟨x, rfl⟩
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [LinearMap.mem_ker] at hu
  rw [← I.cell_symmetric u x, hu, inner_zero_left]

theorem residualEvent_orthogonal_residualComplement (I : BinaryImpl n E ι) :
    residualEvent I ≤ (residualComplement I)ᗮ := by
  have h1 : residualEvent I ≤ LinearMap.range I.cell := inf_le_left
  have h2 : residualComplement I ≤ LinearMap.ker I.cell := inf_le_left
  calc residualEvent I ≤ LinearMap.range I.cell := h1
    _ ≤ (LinearMap.ker I.cell)ᗮ := range_le_ker_orthogonal I
    _ ≤ (residualComplement I)ᗮ := Submodule.orthogonal_le h2

theorem residualEvent_sup_residualComplement_eq_residualSubspace (I : BinaryImpl n E ι) :
    residualEvent I ⊔ residualComplement I = residualSubspace I := by
  apply le_antisymm
  · rw [sup_le_iff]
    exact ⟨inf_le_right, inf_le_right⟩
  · intro z hz
    have hdecomp : z = I.cell z + I.complementCell z := by
      have h := LinearMap.congr_fun I.cell_add_complement_eq_one z
      simpa using h.symm
    rw [hdecomp]
    apply Submodule.add_mem
    · exact Submodule.mem_sup_left ⟨⟨z, rfl⟩, minimalSubspace_isReducing I z hz⟩
    · have hzc : I.complementCell z ∈ LinearMap.ker I.cell := by
        rw [LinearMap.mem_ker]
        have h := LinearMap.congr_fun I.cell_comp_complement_eq_zero z
        simpa using h
      have hzr : I.complementCell z ∈ residualSubspace I := by
        show I.complementCell z ∈ residualSubspace I
        have hcz : I.cell z ∈ residualSubspace I := minimalSubspace_isReducing I z hz
        have : I.complementCell z = z - I.cell z := by
          show (1 - I.cell) z = z - I.cell z
          simp
        rw [this]
        exact Submodule.sub_mem _ hz hcz
      exact Submodule.mem_sup_right ⟨hzc, hzr⟩

theorem minimalSubspace_sup_residualSubspace_eq_top (I : BinaryImpl n E ι) :
    minimalSubspace I ⊔ residualSubspace I = ⊤ :=
  Submodule.sup_orthogonal_of_hasOrthogonalProjection

/-- Excess dimension on the event side: the "wasted" dimension of a
non-minimal implementation, on the side where `I.cell` acts as the
identity. -/
def excessEventDim (I : BinaryImpl n E ι) : ℕ :=
  Module.finrank ℂ (residualEvent I)

/-- Excess dimension on the complement side. -/
def excessComplementDim (I : BinaryImpl n E ι) : ℕ :=
  Module.finrank ℂ (residualComplement I)

private theorem inf_eq_bot_of_le_orthogonal {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [FiniteDimensional ℂ K] (A B : Submodule ℂ K) (h : A ≤ Bᗮ) : A ⊓ B = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxB⟩ := hx
  have h1 := h hxA
  rw [Submodule.mem_orthogonal] at h1
  have hzero := h1 x hxB
  rw [inner_self_eq_zero] at hzero
  exact hzero

theorem minimalSubspace_finrank_add_residualSubspace_finrank (I : BinaryImpl n E ι) :
    Module.finrank ℂ (minimalSubspace I) + Module.finrank ℂ (residualSubspace I) = I.ambientDim := by
  show _ = Fintype.card ι
  rw [← finrank_euclideanSpace (𝕜 := ℂ) (ι := ι), ← finrank_top ℂ (EuclideanSpace ℂ ι),
    ← minimalSubspace_sup_residualSubspace_eq_top I, ← Submodule.finrank_sup_add_finrank_inf_eq]
  have hbot : minimalSubspace I ⊓ residualSubspace I = ⊥ :=
    inf_eq_bot_of_le_orthogonal _ _ (Submodule.le_orthogonal_orthogonal (minimalSubspace I))
  rw [hbot]
  simp

theorem residualSubspace_finrank_eq_excess_sum (I : BinaryImpl n E ι) :
    Module.finrank ℂ (residualSubspace I) = excessEventDim I + excessComplementDim I := by
  rw [excessEventDim, excessComplementDim, ← residualEvent_sup_residualComplement_eq_residualSubspace I,
    ← Submodule.finrank_sup_add_finrank_inf_eq]
  have hbot : residualEvent I ⊓ residualComplement I = ⊥ :=
    inf_eq_bot_of_le_orthogonal _ _ (residualEvent_orthogonal_residualComplement I)
  rw [hbot]
  simp

theorem ambientDim_decomposition (I : BinaryImpl n E ι) :
    I.ambientDim = Module.finrank ℂ (minimalSubspace I) + excessEventDim I + excessComplementDim I := by
  have h1 := minimalSubspace_finrank_add_residualSubspace_finrank I
  have h2 := residualSubspace_finrank_eq_excess_sum I
  omega

private theorem cell_mem_eventGenerated_of_mem_minimalSubspace (I : BinaryImpl n E ι)
    {y : EuclideanSpace ℂ ι} (hy : y ∈ minimalSubspace I) : I.cell y ∈ eventGenerated I := by
  rw [minimalSubspace, Submodule.mem_sup] at hy
  obtain ⟨a, ⟨x1, rfl⟩, b, ⟨x2, rfl⟩, rfl⟩ := hy
  rw [map_add]
  have ha : I.cell (eventLeg I x1) = eventLeg I x1 := by
    show I.cell (I.cell (I.encoding x1)) = I.cell (I.encoding x1)
    have h := LinearMap.congr_fun I.cell_idempotent (I.encoding x1)
    simpa using h
  have hb : I.cell (complementLeg I x2) = 0 := by
    show I.cell (I.complementCell (I.encoding x2)) = 0
    have h := LinearMap.congr_fun I.cell_comp_complement_eq_zero (I.encoding x2)
    simpa using h
  rw [ha, hb, add_zero]
  exact ⟨x1, rfl⟩

private theorem cell_mem_residualEvent_of_mem_residualSubspace (I : BinaryImpl n E ι)
    {z : EuclideanSpace ℂ ι} (hz : z ∈ residualSubspace I) : I.cell z ∈ residualEvent I :=
  ⟨⟨z, rfl⟩, minimalSubspace_isReducing I z hz⟩

theorem range_cell_eq_eventGenerated_sup_residualEvent (I : BinaryImpl n E ι) :
    LinearMap.range I.cell = eventGenerated I ⊔ residualEvent I := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
      (minimalSubspace_sup_residualSubspace_eq_top I ▸ Submodule.mem_top (x := x))
    rw [map_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (cell_mem_eventGenerated_of_mem_minimalSubspace I ha))
      (Submodule.mem_sup_right (cell_mem_residualEvent_of_mem_residualSubspace I hb))
  · rw [sup_le_iff]
    exact ⟨eventGenerated_le_cellRange I, inf_le_left⟩

theorem eventGenerated_orthogonal_residualEvent (I : BinaryImpl n E ι) :
    eventGenerated I ≤ (residualEvent I)ᗮ := by
  have h1 : eventGenerated I ≤ minimalSubspace I := le_sup_left
  have h2 : residualEvent I ≤ residualSubspace I := inf_le_right
  have h3 : minimalSubspace I = (residualSubspace I)ᗮ := (Submodule.orthogonal_orthogonal (minimalSubspace I)).symm
  calc eventGenerated I ≤ minimalSubspace I := h1
    _ = (residualSubspace I)ᗮ := h3
    _ ≤ (residualEvent I)ᗮ := Submodule.orthogonal_le h2

theorem projectorRank_decomposition (I : BinaryImpl n E ι) :
    I.projectorRank = Module.finrank ℂ (eventGenerated I) + excessEventDim I := by
  show Module.finrank ℂ (LinearMap.range I.cell) = Module.finrank ℂ (eventGenerated I)
    + Module.finrank ℂ (residualEvent I)
  rw [range_cell_eq_eventGenerated_sup_residualEvent I, ← Submodule.finrank_sup_add_finrank_inf_eq]
  have hbot : eventGenerated I ⊓ residualEvent I = ⊥ :=
    inf_eq_bot_of_le_orthogonal _ _ (eventGenerated_orthogonal_residualEvent I)
  rw [hbot]
  simp

theorem minimalSubspace_finrank_eq_sum (I : BinaryImpl n E ι) :
    Module.finrank ℂ (minimalSubspace I)
      = Module.finrank ℂ (eventGenerated I) + Module.finrank ℂ (complementGenerated I) := by
  rw [minimalSubspace, ← Submodule.finrank_sup_add_finrank_inf_eq]
  have hbot : eventGenerated I ⊓ complementGenerated I = ⊥ :=
    inf_eq_bot_of_le_orthogonal _ _ (eventGenerated_orthogonal_complementGenerated I)
  rw [hbot]
  simp

theorem projectorNullity_decomposition (I : BinaryImpl n E ι) :
    I.projectorNullity = Module.finrank ℂ (complementGenerated I) + excessComplementDim I := by
  have h1 := I.projectorRank_add_nullity
  have h2 := ambientDim_decomposition I
  have h3 := projectorRank_decomposition I
  have h4 := minimalSubspace_finrank_eq_sum I
  omega

theorem eventGenerated_finrank_eq_of_sameEffect (I : BinaryImpl n E ι) (J : BinaryImpl n E κ) :
    Module.finrank ℂ (eventGenerated I) = Module.finrank ℂ (eventGenerated J) :=
  (eventGeneratedEquiv I J).toLinearEquiv.finrank_eq

theorem complementGenerated_finrank_eq_of_sameEffect (I : BinaryImpl n E ι) (J : BinaryImpl n E κ) :
    Module.finrank ℂ (complementGenerated I) = Module.finrank ℂ (complementGenerated J) :=
  (complementGeneratedEquiv I J).toLinearEquiv.finrank_eq

theorem minimalSubspace_finrank_eq_of_sameEffect (I : BinaryImpl n E ι) (J : BinaryImpl n E κ) :
    Module.finrank ℂ (minimalSubspace I) = Module.finrank ℂ (minimalSubspace J) := by
  rw [minimalSubspace_finrank_eq_sum, minimalSubspace_finrank_eq_sum,
    eventGenerated_finrank_eq_of_sameEffect I J, complementGenerated_finrank_eq_of_sameEffect I J]

end

end QuantumFoundations.Naimark.BinaryImpl
