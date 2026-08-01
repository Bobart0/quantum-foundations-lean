import QuantumFoundations.Naimark.BinaryImpl.OmegaAssembly

/-!
**FR.** # Classification stricte complète

À effet fixé, deux implémentations sont strictement isomorphes si et
seulement si leurs deux dimensions résiduelles coïncident. La preuve de la
réciproque utilise un espace Ω commun : l'assemblage est surjectif et son
Gram ne dépend pas de l'implémentation, ce qui fournit une isométrie
ambiante qui entrelace aussi les cellules.

**EN.** # Complete strict classification

At fixed effect, two implementations are strictly isomorphic if and only if
their two residual dimensions agree. The converse uses a common Ω-space:
the assembly is surjective and its Gram is implementation-independent, which
provides an ambient isometry intertwining the cells as well.
-/

namespace QuantumFoundations.Naimark.BinaryImpl

open QuantumFoundations Gleason
open scoped InnerProductSpace

noncomputable section

variable {n : ℕ} {E : H n →ₗ[ℂ] H n} {ι κ : Type}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A strict isomorphism forces equal event-side residual dimensions. -/
theorem StrictIso.excessEventDim_eq {I : BinaryImpl n E ι} {J : BinaryImpl n E κ}
    (h : BinaryImpl.StrictIso I J) : excessEventDim I = excessEventDim J := by
  have h1 : I.projectorRank = J.projectorRank := h.projectorRange_finrank_eq
  have h2 := projectorRank_decomposition I
  have h3 := projectorRank_decomposition J
  have h4 := eventGenerated_finrank_eq_of_sameEffect I J
  omega

/-- A strict isomorphism forces equal complement-side residual dimensions. -/
theorem StrictIso.excessComplementDim_eq {I : BinaryImpl n E ι} {J : BinaryImpl n E κ}
    (h : BinaryImpl.StrictIso I J) : excessComplementDim I = excessComplementDim J := by
  have h1 : I.projectorNullity = J.projectorNullity := h.projectorKernel_finrank_eq
  have h2 := projectorNullity_decomposition I
  have h3 := projectorNullity_decomposition J
  have h4 := complementGenerated_finrank_eq_of_sameEffect I J
  omega

/-- Equal residual dimensions yield a strict isomorphism. -/
theorem strictIso_of_residualDims_eq {I : BinaryImpl n E ι} {J : BinaryImpl n E κ}
    (hr : excessEventDim I = excessEventDim J)
    (hs : excessComplementDim I = excessComplementDim J) :
    BinaryImpl.StrictIso I J := by
  let r := excessEventDim I
  let s := excessComplementDim I
  have hrI : excessEventDim I = r := rfl
  have hsI : excessComplementDim I = s := rfl
  have hrJ : excessEventDim J = r := hr.symm
  have hsJ : excessComplementDim J = s := hs.symm
  have hIsurj : Function.Surjective (omegaAssembly I r s hrI hsI) :=
    omegaAssembly_surjective I r s hrI hsI
  have hJsurj : Function.Surjective (omegaAssembly J r s hrJ hsJ) :=
    omegaAssembly_surjective J r s hrJ hsJ
  obtain ⟨U, hU⟩ :=
    exists_isometryEquiv_of_adjoint_comp_self_eq_of_surjective
      (omegaAssembly I r s hrI hsI) (omegaAssembly J r s hrJ hsJ)
      (omegaAssembly_gram_eq I J r s hrI hsI hrJ hsJ) hIsurj hJsurj
  refine ⟨U, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    let w : DilSpace n 2 := singleL n 2 0 x + singleL n 2 1 x
    calc
      U (I.encoding x) = U (combinedLeg I w) := by
        congr 1
        simpa [w] using (combinedLeg_doubled I x).symm
      _ = U (omegaAssembly I r s hrI hsI (omegaMinimalSingle n r s w)) := by
        rw [omegaAssembly_minimal_single]
      _ = omegaAssembly J r s hrJ hsJ (omegaMinimalSingle n r s w) := hU _
      _ = combinedLeg J w := omegaAssembly_minimal_single J r s hrJ hsJ w
      _ = J.encoding x := combinedLeg_doubled J x
  · apply LinearMap.ext
    intro y
    obtain ⟨z, hz⟩ := hIsurj y
    have hcellI := LinearMap.congr_fun (cell_omegaAssembly I r s hrI hsI) z
    have hcellJ := LinearMap.congr_fun (cell_omegaAssembly J r s hrJ hsJ) z
    simp only [LinearMap.comp_apply] at hcellI hcellJ
    have hy : omegaAssembly I r s hrI hsI z = y := hz
    have hUy : U y = omegaAssembly J r s hrJ hsJ z := by
      rw [← hU z, hy]
    calc
      U (I.cell y) =
          U (I.cell (omegaAssembly I r s hrI hsI z)) := by rw [hy]
      _ = U (omegaAssembly I r s hrI hsI (omegaSourceCell n r s z)) := by
        rw [hcellI]
      _ = omegaAssembly J r s hrJ hsJ (omegaSourceCell n r s z) := hU _
      _ = J.cell (omegaAssembly J r s hrJ hsJ z) := hcellJ.symm
      _ = J.cell (U y) := by rw [hUy]

/-- Complete classification of strict isomorphism by the two residual
dimensions. -/
theorem strictIso_iff_residualDims_eq {I : BinaryImpl n E ι} {J : BinaryImpl n E κ} :
    BinaryImpl.StrictIso I J ↔
      excessEventDim I = excessEventDim J ∧
      excessComplementDim I = excessComplementDim J := by
  constructor
  · intro h
    exact ⟨StrictIso.excessEventDim_eq h, StrictIso.excessComplementDim_eq h⟩
  · rintro ⟨hr, hs⟩
    exact strictIso_of_residualDims_eq hr hs

end

end QuantumFoundations.Naimark.BinaryImpl


