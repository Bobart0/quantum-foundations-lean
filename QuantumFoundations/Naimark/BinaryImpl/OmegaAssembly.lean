import QuantumFoundations.Naimark.BinaryImpl.SumCoordinates
import QuantumFoundations.Naimark.BinaryImpl.OrthogonalCoordinates
namespace QuantumFoundations.Naimark.BinaryImpl
open QuantumFoundations Gleason
open scoped InnerProductSpace
noncomputable section
abbrev OmegaMinimalIndex (n : ℕ) := Fin 2 × Fin n
abbrev OmegaTailIndex (r s : ℕ) := Sum (Fin r) (Fin s)
abbrev OmegaIndex (n r s : ℕ) := Sum (OmegaMinimalIndex n) (OmegaTailIndex r s)
abbrev OmegaSpace (n r s : ℕ) := EuclideanSpace ℂ (OmegaIndex n r s)
def omegaMinimalSingle (n r s : ℕ) : DilSpace n 2 →ₗ[ℂ] OmegaSpace n r s := euclideanSumInl _ _
def omegaMinimalCoord (n r s : ℕ) : OmegaSpace n r s →ₗ[ℂ] DilSpace n 2 := euclideanSumFst _ _
def omegaEventSingle (n r s : ℕ) : H r →ₗ[ℂ] OmegaSpace n r s := euclideanSumInr _ _ ∘ₗ euclideanSumInl _ _
def omegaEventCoord (n r s : ℕ) : OmegaSpace n r s →ₗ[ℂ] H r := euclideanSumFst _ _ ∘ₗ euclideanSumSnd _ _
def omegaComplementSingle (n r s : ℕ) : H s →ₗ[ℂ] OmegaSpace n r s := euclideanSumInr _ _ ∘ₗ euclideanSumInr _ _
def omegaComplementCoord (n r s : ℕ) : OmegaSpace n r s →ₗ[ℂ] H s := euclideanSumSnd _ _ ∘ₗ euclideanSumSnd _ _
theorem omegaMinimalCoord_single (w : DilSpace n 2) : omegaMinimalCoord n r s (omegaMinimalSingle n r s w) = w := by
  simp only [omegaMinimalCoord, omegaMinimalSingle, LinearMap.comp_apply]
  exact euclideanSumFst_inl_apply w
theorem omegaEventCoord_single (x : H r) : omegaEventCoord n r s (omegaEventSingle n r s x) = x := by
  simp only [omegaEventCoord, omegaEventSingle, LinearMap.comp_apply]
  rw [euclideanSumSnd_inr_apply, euclideanSumFst_inl_apply]
theorem omegaComplementCoord_single (x : H s) : omegaComplementCoord n r s (omegaComplementSingle n r s x) = x := by
  simp only [omegaComplementCoord, omegaComplementSingle, LinearMap.comp_apply]
  rw [euclideanSumSnd_inr_apply, euclideanSumSnd_inr_apply]
theorem omegaMinimalCoord_eventSingle (x : H r) : omegaMinimalCoord n r s (omegaEventSingle n r s x) = 0 := by
  simp only [omegaMinimalCoord, omegaEventSingle, LinearMap.comp_apply]
  exact euclideanSumFst_inr_apply (α := OmegaMinimalIndex n) (β := OmegaTailIndex r s) _
theorem omegaMinimalCoord_complementSingle (x : H s) : omegaMinimalCoord n r s (omegaComplementSingle n r s x) = 0 := by
  simp only [omegaMinimalCoord, omegaComplementSingle, LinearMap.comp_apply]
  exact euclideanSumFst_inr_apply (α := OmegaMinimalIndex n) (β := OmegaTailIndex r s) _
theorem omegaEventCoord_minimalSingle (w : DilSpace n 2) : omegaEventCoord n r s (omegaMinimalSingle n r s w) = 0 := by
  simp only [omegaEventCoord, omegaMinimalSingle, LinearMap.comp_apply]
  rw [euclideanSumSnd_inl_apply]
  simp only [map_zero]
theorem omegaEventCoord_complementSingle (x : H s) : omegaEventCoord n r s (omegaComplementSingle n r s x) = 0 := by
  simp only [omegaEventCoord, omegaComplementSingle, LinearMap.comp_apply]
  rw [euclideanSumSnd_inr_apply]
  exact euclideanSumFst_inr_apply (α := Fin r) (β := Fin s) _
theorem omegaComplementCoord_minimalSingle (w : DilSpace n 2) : omegaComplementCoord n r s (omegaMinimalSingle n r s w) = 0 := by
  simp only [omegaComplementCoord, omegaMinimalSingle, LinearMap.comp_apply]
  rw [euclideanSumSnd_inl_apply]
  simp only [map_zero]
theorem omegaComplementCoord_eventSingle (x : H r) : omegaComplementCoord n r s (omegaEventSingle n r s x) = 0 := by
  simp only [omegaComplementCoord, omegaEventSingle, LinearMap.comp_apply]
  rw [euclideanSumSnd_inr_apply]
  exact euclideanSumSnd_inl_apply (α := Fin r) (β := Fin s) _
theorem omega_decomposition (z : OmegaSpace n r s) :
    omegaMinimalSingle n r s (omegaMinimalCoord n r s z) + omegaEventSingle n r s (omegaEventCoord n r s z) +
      omegaComplementSingle n r s (omegaComplementCoord n r s z) = z := by
  have htail := euclideanSum_decomposition (α := Fin r) (β := Fin s)
    (euclideanSumSnd (OmegaMinimalIndex n) (OmegaTailIndex r s) z)
  have houter := euclideanSum_decomposition (α := OmegaMinimalIndex n) (β := OmegaTailIndex r s) z
  simp only [omegaMinimalSingle, omegaMinimalCoord, omegaEventSingle, omegaEventCoord,
    omegaComplementSingle, omegaComplementCoord, LinearMap.comp_apply]
  rw [add_assoc, ← map_add (euclideanSumInr (OmegaMinimalIndex n) (OmegaTailIndex r s))]
  rw [htail]
  exact houter
theorem omega_resolution_of_identity :
    omegaMinimalSingle n r s ∘ₗ omegaMinimalCoord n r s + omegaEventSingle n r s ∘ₗ omegaEventCoord n r s +
      omegaComplementSingle n r s ∘ₗ omegaComplementCoord n r s = LinearMap.id := by
  apply LinearMap.ext; intro z
  change omegaMinimalSingle n r s (omegaMinimalCoord n r s z) + omegaEventSingle n r s (omegaEventCoord n r s z) +
    omegaComplementSingle n r s (omegaComplementCoord n r s z) = z
  exact omega_decomposition z
theorem adjoint_omegaMinimalSingle : LinearMap.adjoint (omegaMinimalSingle n r s) = omegaMinimalCoord n r s := by
  rw [omegaMinimalSingle, omegaMinimalCoord, adjoint_euclideanSumInl]
theorem adjoint_omegaEventSingle : LinearMap.adjoint (omegaEventSingle n r s) = omegaEventCoord n r s := by
  rw [omegaEventSingle, omegaEventCoord, LinearMap.adjoint_comp, adjoint_euclideanSumInl, adjoint_euclideanSumInr]
theorem adjoint_omegaComplementSingle : LinearMap.adjoint (omegaComplementSingle n r s) = omegaComplementCoord n r s := by
  rw [omegaComplementSingle, omegaComplementCoord, LinearMap.adjoint_comp, adjoint_euclideanSumInr, adjoint_euclideanSumInr]
def omegaSourceCell (n r s : ℕ) : OmegaSpace n r s →ₗ[ℂ] OmegaSpace n r s :=
  omegaMinimalSingle n r s ∘ₗ dilProj n 2 0 ∘ₗ omegaMinimalCoord n r s + omegaEventSingle n r s ∘ₗ omegaEventCoord n r s
theorem omegaSourceCell_apply (z : OmegaSpace n r s) :
    omegaSourceCell n r s z = omegaMinimalSingle n r s (dilProj n 2 0 (omegaMinimalCoord n r s z)) +
      omegaEventSingle n r s (omegaEventCoord n r s z) := rfl
theorem omegaSourceCell_minimal (w : DilSpace n 2) : omegaSourceCell n r s (omegaMinimalSingle n r s w) = omegaMinimalSingle n r s (dilProj n 2 0 w) := by
  rw [omegaSourceCell_apply, omegaMinimalCoord_single, omegaEventCoord_minimalSingle]
  simp only [map_zero, add_zero]
theorem omegaSourceCell_event (x : H r) : omegaSourceCell n r s (omegaEventSingle n r s x) = omegaEventSingle n r s x := by
  rw [omegaSourceCell_apply, omegaMinimalCoord_eventSingle, omegaEventCoord_single]
  simp only [map_zero, zero_add]
theorem omegaSourceCell_complement (x : H s) : omegaSourceCell n r s (omegaComplementSingle n r s x) = 0 := by
  rw [omegaSourceCell_apply, omegaMinimalCoord_complementSingle, omegaEventCoord_complementSingle]
  simp only [map_zero, add_zero]
theorem omegaSourceCell_idempotent : omegaSourceCell n r s ∘ₗ omegaSourceCell n r s = omegaSourceCell n r s := by
  apply LinearMap.ext
  intro z
  change omegaSourceCell n r s (omegaSourceCell n r s z) = omegaSourceCell n r s z
  calc
    omegaSourceCell n r s (omegaSourceCell n r s z) =
        omegaSourceCell n r s (omegaSourceCell n r s
          (omegaMinimalSingle n r s (omegaMinimalCoord n r s z) +
            omegaEventSingle n r s (omegaEventCoord n r s z) +
            omegaComplementSingle n r s (omegaComplementCoord n r s z))) := by
              rw [omega_decomposition]
    _ = omegaSourceCell n r s
        (omegaSourceCell n r s (omegaMinimalSingle n r s (omegaMinimalCoord n r s z)) +
          omegaSourceCell n r s (omegaEventSingle n r s (omegaEventCoord n r s z)) +
          omegaSourceCell n r s (omegaComplementSingle n r s (omegaComplementCoord n r s z))) := by
            simp only [map_add]
    _ = omegaSourceCell n r s
        (omegaMinimalSingle n r s (dilProj n 2 0 (omegaMinimalCoord n r s z)) +
          omegaEventSingle n r s (omegaEventCoord n r s z)) := by
            rw [omegaSourceCell_minimal, omegaSourceCell_event,
              omegaSourceCell_complement]
            simp only [map_zero, add_zero]
    _ = omegaSourceCell n r s z := by
      have h := congrArg (omegaSourceCell n r s) (omega_decomposition z)
      rw [omegaSourceCell_apply] at h
      simp only [map_add, omegaMinimalCoord_single, omegaMinimalCoord_eventSingle,
        omegaMinimalCoord_complementSingle, omegaEventCoord_minimalSingle,
        omegaEventCoord_single, omegaEventCoord_complementSingle, map_zero,
        zero_add, add_zero] at h
      rw [omegaSourceCell_apply]
      simp only [map_add, omegaMinimalCoord_single, omegaMinimalCoord_eventSingle,
        omegaEventCoord_minimalSingle, omegaEventCoord_single, map_zero,
        zero_add, add_zero]
      have hp := LinearMap.congr_fun (dilProj_idempotent (n := n) (m := 2) 0)
        (omegaMinimalCoord n r s z)
      simp only [LinearMap.comp_apply] at hp
      rw [hp]
      exact h
theorem omegaSourceCell_symmetric : LinearMap.IsSymmetric (omegaSourceCell n r s) := by
  rw [omegaSourceCell]
  apply LinearMap.IsSymmetric.add
  · rw [show omegaMinimalCoord n r s = LinearMap.adjoint (omegaMinimalSingle n r s) from (adjoint_omegaMinimalSingle).symm]
    intro x y; simp only [LinearMap.comp_apply]
    calc
      ⟪omegaMinimalSingle n r s (dilProj n 2 0 (LinearMap.adjoint (omegaMinimalSingle n r s) x)), y⟫_ℂ =
          ⟪dilProj n 2 0 (LinearMap.adjoint (omegaMinimalSingle n r s) x), LinearMap.adjoint (omegaMinimalSingle n r s) y⟫_ℂ := by rw [LinearMap.adjoint_inner_right]
      _ = ⟪LinearMap.adjoint (omegaMinimalSingle n r s) x, dilProj n 2 0 (LinearMap.adjoint (omegaMinimalSingle n r s) y)⟫_ℂ := dilProj_isSymmetric 0 _ _
      _ = ⟪x, omegaMinimalSingle n r s (dilProj n 2 0 (LinearMap.adjoint (omegaMinimalSingle n r s) y))⟫_ℂ := LinearMap.adjoint_inner_left _ _ _
  · rw [show omegaEventCoord n r s = LinearMap.adjoint (omegaEventSingle n r s) from (adjoint_omegaEventSingle).symm]
    intro x y; simp only [LinearMap.comp_apply]
    calc
      ⟪omegaEventSingle n r s (LinearMap.adjoint (omegaEventSingle n r s) x), y⟫_ℂ =
          ⟪LinearMap.adjoint (omegaEventSingle n r s) x, LinearMap.adjoint (omegaEventSingle n r s) y⟫_ℂ := by rw [LinearMap.adjoint_inner_right]
      _ = ⟪x, omegaEventSingle n r s (LinearMap.adjoint (omegaEventSingle n r s) y)⟫_ℂ := LinearMap.adjoint_inner_left _ _ _
theorem omegaSourceCell_isProjection : (omegaSourceCell n r s).IsSymmetricProjection :=
  ⟨omegaSourceCell_idempotent, omegaSourceCell_symmetric⟩

variable {n : ℕ} {E : H n →ₗ[ℂ] H n} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def residualEventEmbedOfDim (I : BinaryImpl n E ι) (r : ℕ)
    (hr : excessEventDim I = r) : H r →ₗ[ℂ] EuclideanSpace ℂ ι := by
  subst r
  exact (ofFinrank (residualEvent I)).embed

def residualComplementEmbedOfDim (I : BinaryImpl n E ι) (s : ℕ)
    (hs : excessComplementDim I = s) : H s →ₗ[ℂ] EuclideanSpace ℂ ι := by
  subst s
  exact (ofFinrank (residualComplement I)).embed

private theorem residualEventEmbed_range (I : BinaryImpl n E ι) (r : ℕ)
    (hr : excessEventDim I = r) :
    LinearMap.range (residualEventEmbedOfDim I r hr) = residualEvent I := by
  subst r
  exact (ofFinrank (residualEvent I)).range_embed

private theorem residualComplementEmbed_range (I : BinaryImpl n E ι) (s : ℕ)
    (hs : excessComplementDim I = s) :
    LinearMap.range (residualComplementEmbedOfDim I s hs) = residualComplement I := by
  subst s
  exact (ofFinrank (residualComplement I)).range_embed

def omegaAssembly (I : BinaryImpl n E ι) (r s : ℕ)
    (hr : excessEventDim I = r) (hs : excessComplementDim I = s) :
    OmegaSpace n r s →ₗ[ℂ] EuclideanSpace ℂ ι :=
  combinedLeg I ∘ₗ omegaMinimalCoord n r s +
    residualEventEmbedOfDim I r hr ∘ₗ omegaEventCoord n r s +
    residualComplementEmbedOfDim I s hs ∘ₗ omegaComplementCoord n r s

theorem omegaAssembly_apply (I : BinaryImpl n E ι) (r s : ℕ)
    (hr : excessEventDim I = r) (hs : excessComplementDim I = s)
    (z : OmegaSpace n r s) :
    omegaAssembly I r s hr hs z =
      combinedLeg I (omegaMinimalCoord n r s z) +
      residualEventEmbedOfDim I r hr (omegaEventCoord n r s z) +
      residualComplementEmbedOfDim I s hs (omegaComplementCoord n r s z) := rfl

theorem omegaAssembly_minimal_single (I : BinaryImpl n E ι) (r s : ℕ)
    (hr : excessEventDim I = r) (hs : excessComplementDim I = s) (w : DilSpace n 2) :
    omegaAssembly I r s hr hs (omegaMinimalSingle n r s w) = combinedLeg I w := by
  rw [omegaAssembly_apply, omegaMinimalCoord_single,
    omegaEventCoord_minimalSingle, omegaComplementCoord_minimalSingle]
  simp only [map_zero, add_zero, zero_add]

theorem omegaAssembly_event_single (I : BinaryImpl n E ι) (r s : ℕ)
    (hr : excessEventDim I = r) (hs : excessComplementDim I = s) (x : H r) :
    omegaAssembly I r s hr hs (omegaEventSingle n r s x) =
      residualEventEmbedOfDim I r hr x := by
  rw [omegaAssembly_apply, omegaMinimalCoord_eventSingle,
    omegaEventCoord_single, omegaComplementCoord_eventSingle]
  simp only [map_zero, add_zero, zero_add]

theorem omegaAssembly_complement_single (I : BinaryImpl n E ι) (r s : ℕ)
    (hr : excessEventDim I = r) (hs : excessComplementDim I = s) (x : H s) :
    omegaAssembly I r s hr hs (omegaComplementSingle n r s x) =
      residualComplementEmbedOfDim I s hs x := by
  rw [omegaAssembly_apply, omegaMinimalCoord_complementSingle,
    omegaEventCoord_complementSingle, omegaComplementCoord_single]
  simp only [map_zero, add_zero, zero_add]

theorem omegaAssembly_surjective (I : BinaryImpl n E ι) (r s : ℕ)
    (hr : excessEventDim I = r) (hs : excessComplementDim I = s) :
    Function.Surjective (omegaAssembly I r s hr hs) := by
  intro y
  obtain ⟨yMin, hyMin, yRes, hyRes, rfl⟩ := Submodule.mem_sup.mp
    (minimalSubspace_sup_residualSubspace_eq_top I ▸ Submodule.mem_top (x := y))
  obtain ⟨yEvent, hyEvent, yComplement, hyComplement, rfl⟩ :=
    Submodule.mem_sup.mp
      (residualEvent_sup_residualComplement_eq_residualSubspace I ▸ hyRes)
  have hMin : yMin ∈ LinearMap.range (combinedLeg I) := by
    rw [range_combinedLeg I]
    exact hyMin
  obtain ⟨w, hw⟩ := hMin
  have hEvent : yEvent ∈ LinearMap.range (residualEventEmbedOfDim I r hr) := by
    rw [residualEventEmbed_range I r hr]
    exact hyEvent
  obtain ⟨u, hu⟩ := hEvent
  have hComplement : yComplement ∈
      LinearMap.range (residualComplementEmbedOfDim I s hs) := by
    rw [residualComplementEmbed_range I s hs]
    exact hyComplement
  obtain ⟨v, hv⟩ := hComplement
  refine ⟨omegaMinimalSingle n r s w + omegaEventSingle n r s u +
    omegaComplementSingle n r s v, ?_⟩
  rw [map_add, map_add, omegaAssembly_minimal_single,
    omegaAssembly_event_single, omegaAssembly_complement_single, hw, hu, hv]
  rw [add_assoc]


private theorem cell_residualEventEmbed (I : BinaryImpl n E ι) (r : ℕ)
    (hr : excessEventDim I = r) (u : H r) :
    I.cell (residualEventEmbedOfDim I r hr u) =
      residualEventEmbedOfDim I r hr u := by
  have hu := LinearMap.mem_range_self (residualEventEmbedOfDim I r hr) u
  rw [residualEventEmbed_range I r hr] at hu
  change residualEventEmbedOfDim I r hr u ∈ LinearMap.range I.cell ⊓ residualSubspace I at hu
  obtain ⟨x, hx⟩ := hu.1
  rw [← hx]
  have h := LinearMap.congr_fun I.cell_idempotent x
  simpa [LinearMap.comp_apply] using h

private theorem cell_residualComplementEmbed (I : BinaryImpl n E ι) (s : ℕ)
    (hs : excessComplementDim I = s) (v : H s) :
    I.cell (residualComplementEmbedOfDim I s hs v) = 0 := by
  have hv := LinearMap.mem_range_self (residualComplementEmbedOfDim I s hs) v
  rw [residualComplementEmbed_range I s hs] at hv
  change residualComplementEmbedOfDim I s hs v ∈ LinearMap.ker I.cell ⊓ residualSubspace I at hv
  exact hv.1

theorem cell_omegaAssembly (I : BinaryImpl n E ι) (r s : ℕ)
    (hr : excessEventDim I = r) (hs : excessComplementDim I = s) :
    I.cell ∘ₗ omegaAssembly I r s hr hs =
      omegaAssembly I r s hr hs ∘ₗ omegaSourceCell n r s := by
  apply LinearMap.ext
  intro z
  calc
    I.cell (omegaAssembly I r s hr hs z) =
        I.cell (omegaAssembly I r s hr hs
          (omegaMinimalSingle n r s (omegaMinimalCoord n r s z) +
            omegaEventSingle n r s (omegaEventCoord n r s z) +
            omegaComplementSingle n r s (omegaComplementCoord n r s z))) := by
              rw [omega_decomposition]
    _ = I.cell (omegaAssembly I r s hr hs
          (omegaMinimalSingle n r s (omegaMinimalCoord n r s z))) +
        I.cell (omegaAssembly I r s hr hs
          (omegaEventSingle n r s (omegaEventCoord n r s z))) +
        I.cell (omegaAssembly I r s hr hs
          (omegaComplementSingle n r s (omegaComplementCoord n r s z))) := by
              simp only [map_add, add_assoc]
    _ = combinedLeg I (singleL n 2 0 (coordL n 2 0
          (omegaMinimalCoord n r s z))) +
        residualEventEmbedOfDim I r hr (omegaEventCoord n r s z) := by
              rw [omegaAssembly_minimal_single, cell_combinedLeg,
                omegaAssembly_event_single, cell_residualEventEmbed,
                omegaAssembly_complement_single, cell_residualComplementEmbed]
              simp only [add_zero]
    _ = omegaAssembly I r s hr hs (omegaSourceCell n r s z) := by
              rw [omegaSourceCell_apply]
              rw [map_add, omegaAssembly_minimal_single, omegaAssembly_event_single]
              congr 1


private theorem inner_combinedLeg_residualEventEmbed (I : BinaryImpl n E ι) (r s : ℕ)
    (hr : excessEventDim I = r) (hs : excessComplementDim I = s)
    (w : DilSpace n 2) (u : H r) :
    ⟪combinedLeg I w, residualEventEmbedOfDim I r hr u⟫_ℂ = 0 := by
  have hm : combinedLeg I w ∈ minimalSubspace I := by
    rw [← range_combinedLeg I]
    exact LinearMap.mem_range_self (combinedLeg I) w
  have hu := LinearMap.mem_range_self (residualEventEmbedOfDim I r hr) u
  rw [residualEventEmbed_range I r hr] at hu
  have hle : minimalSubspace I ≤ (residualSubspace I)ᗮ :=
    Submodule.le_orthogonal_orthogonal (minimalSubspace I)
  have h := hle hm
  rw [Submodule.mem_orthogonal] at h
  rw [← inner_conj_symm]
  simpa using congrArg (starRingEnd ℂ) (h _ hu.2)

private theorem inner_combinedLeg_residualComplementEmbed (I : BinaryImpl n E ι) (r s : ℕ)
    (hr : excessEventDim I = r) (hs : excessComplementDim I = s)
    (w : DilSpace n 2) (v : H s) :
    ⟪combinedLeg I w, residualComplementEmbedOfDim I s hs v⟫_ℂ = 0 := by
  have hm : combinedLeg I w ∈ minimalSubspace I := by
    rw [← range_combinedLeg I]
    exact LinearMap.mem_range_self (combinedLeg I) w
  have hv := LinearMap.mem_range_self (residualComplementEmbedOfDim I s hs) v
  rw [residualComplementEmbed_range I s hs] at hv
  have hle : minimalSubspace I ≤ (residualSubspace I)ᗮ :=
    Submodule.le_orthogonal_orthogonal (minimalSubspace I)
  have h := hle hm
  rw [Submodule.mem_orthogonal] at h
  rw [← inner_conj_symm]
  simpa using congrArg (starRingEnd ℂ) (h _ hv.2)

private theorem inner_residualEventEmbed_combinedLeg (I : BinaryImpl n E ι) (r s : ℕ)
    (hr : excessEventDim I = r) (hs : excessComplementDim I = s)
    (u : H r) (w : DilSpace n 2) :
    ⟪residualEventEmbedOfDim I r hr u, combinedLeg I w⟫_ℂ = 0 := by
  rw [← inner_conj_symm]
  simpa using congrArg (starRingEnd ℂ)
    (inner_combinedLeg_residualEventEmbed I r s hr hs w u)

private theorem inner_residualComplementEmbed_combinedLeg (I : BinaryImpl n E ι) (r s : ℕ)
    (hr : excessEventDim I = r) (hs : excessComplementDim I = s)
    (v : H s) (w : DilSpace n 2) :
    ⟪residualComplementEmbedOfDim I s hs v, combinedLeg I w⟫_ℂ = 0 := by
  rw [← inner_conj_symm]
  simpa using congrArg (starRingEnd ℂ)
    (inner_combinedLeg_residualComplementEmbed I r s hr hs w v)

private theorem inner_residualEvent_residualComplement (I : BinaryImpl n E ι)
    (r s : ℕ) (hr : excessEventDim I = r) (hs : excessComplementDim I = s)
    (u : H r) (v : H s) :
    ⟪residualEventEmbedOfDim I r hr u,
      residualComplementEmbedOfDim I s hs v⟫_ℂ = 0 := by
  have hu := LinearMap.mem_range_self (residualEventEmbedOfDim I r hr) u
  have hv := LinearMap.mem_range_self (residualComplementEmbedOfDim I s hs) v
  rw [residualEventEmbed_range I r hr] at hu
  rw [residualComplementEmbed_range I s hs] at hv
  have h := residualEvent_orthogonal_residualComplement I hu
  rw [Submodule.mem_orthogonal] at h
  rw [← inner_conj_symm]
  simpa using congrArg (starRingEnd ℂ) (h _ hv)

private theorem inner_residualComplement_residualEvent (I : BinaryImpl n E ι)
    (r s : ℕ) (hr : excessEventDim I = r) (hs : excessComplementDim I = s)
    (v : H s) (u : H r) :
    ⟪residualComplementEmbedOfDim I s hs v,
      residualEventEmbedOfDim I r hr u⟫_ℂ = 0 := by
  rw [← inner_conj_symm]
  simpa using congrArg (starRingEnd ℂ)
    (inner_residualEvent_residualComplement I r s hr hs u v)

private theorem inner_residualEventEmbed (I : BinaryImpl n E ι) (r s : ℕ)
    (hr : excessEventDim I = r) (hs : excessComplementDim I = s)
    (u u' : H r) :
    ⟪residualEventEmbedOfDim I r hr u,
      residualEventEmbedOfDim I r hr u'⟫_ℂ = ⟪u, u'⟫_ℂ := by
  subst r
  exact (ofFinrank (residualEvent I)).embed_isometry u u'

private theorem inner_residualComplementEmbed (I : BinaryImpl n E ι) (r s : ℕ)
    (hr : excessEventDim I = r) (hs : excessComplementDim I = s)
    (v v' : H s) :
    ⟪residualComplementEmbedOfDim I s hs v,
      residualComplementEmbedOfDim I s hs v'⟫_ℂ = ⟪v, v'⟫_ℂ := by
  subst s
  exact (ofFinrank (residualComplement I)).embed_isometry v v'

theorem inner_omegaAssembly (I : BinaryImpl n E ι) (r s : ℕ)
    (hr : excessEventDim I = r) (hs : excessComplementDim I = s)
    (z z' : OmegaSpace n r s) :
    ⟪omegaAssembly I r s hr hs z, omegaAssembly I r s hr hs z'⟫_ℂ =
      ⟪combinedLeg I (omegaMinimalCoord n r s z),
        combinedLeg I (omegaMinimalCoord n r s z')⟫_ℂ +
      ⟪omegaEventCoord n r s z, omegaEventCoord n r s z'⟫_ℂ +
      ⟪omegaComplementCoord n r s z, omegaComplementCoord n r s z'⟫_ℂ := by
  rw [omegaAssembly_apply I r s hr hs, omegaAssembly_apply I r s hr hs]
  simp only [inner_add_left, inner_add_right]
  rw [inner_combinedLeg_residualEventEmbed I r s hr hs,
    inner_combinedLeg_residualComplementEmbed I r s hr hs,
    inner_residualEventEmbed_combinedLeg I r s hr hs,
    inner_residualComplementEmbed_combinedLeg I r s hr hs,
    inner_residualEvent_residualComplement I r s hr hs,
    inner_residualComplement_residualEvent I r s hr hs,
    inner_residualEventEmbed I r s hr hs,
    inner_residualComplementEmbed I r s hr hs]
  simp only [add_zero, zero_add]

theorem omegaAssembly_gram_eq (I : BinaryImpl n E ι) (J : BinaryImpl n E κ)
    (r s : ℕ) (hrI : excessEventDim I = r) (hsI : excessComplementDim I = s)
    (hrJ : excessEventDim J = r) (hsJ : excessComplementDim J = s) :
    LinearMap.adjoint (omegaAssembly I r s hrI hsI) ∘ₗ
        omegaAssembly I r s hrI hsI =
      LinearMap.adjoint (omegaAssembly J r s hrJ hsJ) ∘ₗ
        omegaAssembly J r s hrJ hsJ := by
  apply LinearMap.ext
  intro z
  apply ext_inner_left ℂ
  intro z'
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right,
    LinearMap.comp_apply, LinearMap.adjoint_inner_right,
    inner_omegaAssembly I r s hrI hsI z' z,
    inner_omegaAssembly J r s hrJ hsJ z' z]
  have h := LinearMap.congr_fun (combinedLeg_gram_eq I J)
    (omegaMinimalCoord n r s z')
  simp only [LinearMap.comp_apply] at h
  have hmin :
      ⟪combinedLeg I (omegaMinimalCoord n r s z'),
          combinedLeg I (omegaMinimalCoord n r s z)⟫_ℂ =
        ⟪combinedLeg J (omegaMinimalCoord n r s z'),
          combinedLeg J (omegaMinimalCoord n r s z)⟫_ℂ := by
    calc
      _ = ⟪LinearMap.adjoint (combinedLeg I)
            (combinedLeg I (omegaMinimalCoord n r s z')),
          omegaMinimalCoord n r s z⟫_ℂ :=
        (LinearMap.adjoint_inner_left (combinedLeg I)
          (omegaMinimalCoord n r s z)
          (combinedLeg I (omegaMinimalCoord n r s z'))).symm
      _ = ⟪LinearMap.adjoint (combinedLeg J)
            (combinedLeg J (omegaMinimalCoord n r s z')),
          omegaMinimalCoord n r s z⟫_ℂ := by rw [h]
      _ = _ :=
        LinearMap.adjoint_inner_left (combinedLeg J)
          (omegaMinimalCoord n r s z)
          (combinedLeg J (omegaMinimalCoord n r s z'))
  rw [hmin]

end
end QuantumFoundations.Naimark.BinaryImpl




















