import QuantumFoundations.Naimark.BinaryImpl.Nonvacuity
namespace QuantumFoundations.Naimark.BinaryImpl
open QuantumFoundations Gleason
open scoped InnerProductSpace
noncomputable section
theorem strictIso_not_total : ∃ (a b : ℕ) (a₀ : Fin a) (b₀ : Fin b), ¬ BinaryImpl.StrictIso
      (replicatedAncillaImpl (canonicalBinaryImpl (1 : H 1 →ₗ[ℂ] H 1) (one_isEffect 1)) a₀)
      (replicatedAncillaImpl (canonicalTernaryImpl (1 : H 1 →ₗ[ℂ] H 1) (one_isEffect 1)) b₀) :=
  ⟨1, 1, 0, 0, canonicalBinaryImpl_canonicalTernaryImpl_not_strictIso_replicatedAncilla
    (1 : H 1 →ₗ[ℂ] H 1) (one_isEffect 1) (by norm_num) 0 0⟩
theorem strictIsoInvariant_not_le_replicatedAncillaNeutral :
    ∃ (n : ℕ) (E : H n →ₗ[ℂ] H n) (v : ImplValuation n E), StrictIsoInvariant v ∧ ¬ ReplicatedAncillaNeutral v :=
  ⟨1, (1 : H 1 →ₗ[ℂ] H 1), ambientDimValuation, ambientDimValuation_strictIsoInvariant, ambientDimValuation_not_replicatedAncillaNeutral⟩
theorem rankRatio_eventResidualExtension_example :
    rankRatio (eventResidualExtension (canonicalBinaryImpl (1 : H 1 →ₗ[ℂ] H 1) (one_isEffect 1)) 1) = (2 : ℚ) / 3 := by
  have hrank : Module.finrank ℂ (LinearMap.range (LinearMap.id : EuclideanSpace ℂ (Fin 1) →ₗ[ℂ] EuclideanSpace ℂ (Fin 1))) = 1 := by
    rw [LinearMap.range_id, finrank_top]
    simpa using (finrank_euclideanSpace (𝕜 := ℂ) (ι := Fin 1))
  unfold rankRatio eventResidualExtension
  rw [projectorRank_residualExtension, ambientDim_residualExtension_fin, canonicalBinaryImpl_projectorRank, hrank]
  norm_num
theorem rankRatio_complementResidualExtension_example :
    rankRatio (complementResidualExtension (canonicalBinaryImpl (1 : H 1 →ₗ[ℂ] H 1) (one_isEffect 1)) 1) = (1 : ℚ) / 3 := by
  have hrank : Module.finrank ℂ (LinearMap.range (0 : EuclideanSpace ℂ (Fin 1) →ₗ[ℂ] EuclideanSpace ℂ (Fin 1))) = 0 := by
    rw [LinearMap.range_zero, finrank_bot]
  unfold rankRatio complementResidualExtension
  rw [projectorRank_residualExtension, ambientDim_residualExtension_fin, canonicalBinaryImpl_projectorRank, hrank]
  norm_num
theorem rankRatioValuation_not_eventResidualNeutral : ¬ EventResidualNeutral (rankRatioValuation (n := 1) (E := (1 : H 1 →ₗ[ℂ] H 1))) := by
  intro h
  have hh := h (canonicalBinaryImpl (1 : H 1 →ₗ[ℂ] H 1) (one_isEffect 1)) 1
  change rankRatio (eventResidualExtension (canonicalBinaryImpl (1 : H 1 →ₗ[ℂ] H 1) (one_isEffect 1)) 1) = rankRatio (canonicalBinaryImpl (1 : H 1 →ₗ[ℂ] H 1) (one_isEffect 1)) at hh
  rw [rankRatio_eventResidualExtension_example, canonicalBinaryImpl_rankRatio (1 : H 1 →ₗ[ℂ] H 1) (one_isEffect 1) (by norm_num)] at hh
  norm_num at hh
theorem rankRatioValuation_not_complementResidualNeutral : ¬ ComplementResidualNeutral (rankRatioValuation (n := 1) (E := (1 : H 1 →ₗ[ℂ] H 1))) := by
  intro h
  have hh := h (canonicalBinaryImpl (1 : H 1 →ₗ[ℂ] H 1) (one_isEffect 1)) 1
  change rankRatio (complementResidualExtension (canonicalBinaryImpl (1 : H 1 →ₗ[ℂ] H 1) (one_isEffect 1)) 1) = rankRatio (canonicalBinaryImpl (1 : H 1 →ₗ[ℂ] H 1) (one_isEffect 1)) at hh
  rw [rankRatio_complementResidualExtension_example, canonicalBinaryImpl_rankRatio (1 : H 1 →ₗ[ℂ] H 1) (one_isEffect 1) (by norm_num)] at hh
  norm_num at hh
theorem rankRatioValuation_not_residualNeutral : ¬ ResidualExtensionNeutral (rankRatioValuation (n := 1) (E := (1 : H 1 →ₗ[ℂ] H 1))) := by
  intro h
  exact rankRatioValuation_not_eventResidualNeutral h.1
theorem replicatedAncillaNeutral_not_implies_residualNeutral :
    ∃ (n : ℕ) (E : H n →ₗ[ℂ] H n) (v : ImplValuationR ℚ n E), StrictIsoInvariantR v ∧ ReplicatedAncillaNeutralR v ∧ ¬ ResidualExtensionNeutral v :=
  ⟨1, (1 : H 1 →ₗ[ℂ] H 1), rankRatioValuation, rankRatioValuation_strictIsoInvariant, rankRatioValuation_replicatedAncillaNeutral, rankRatioValuation_not_residualNeutral⟩
def totalResidualDim {n : ℕ} {E : H n →ₗ[ℂ] H n} {ι : Type} [Fintype ι] [DecidableEq ι] (I : BinaryImpl n E ι) : ℕ := excessEventDim I + excessComplementDim I
theorem totalResidualDim_not_complete_invariant :
    ∃ (I : BinaryImpl 1 (1 : H 1 →ₗ[ℂ] H 1) (Sum (Sum (Fin 2 × Fin 1) (Fin 1)) (Fin 0)))
      (J : BinaryImpl 1 (1 : H 1 →ₗ[ℂ] H 1) (Sum (Sum (Fin 2 × Fin 1) (Fin 0)) (Fin 1))),
      I.ambientDim = J.ambientDim ∧ totalResidualDim I = totalResidualDim J ∧ excessEventDim I ≠ excessEventDim J ∧ ¬ BinaryImpl.StrictIso I J := by
  let M := canonicalBinaryImpl (1 : H 1 →ₗ[ℂ] H 1) (one_isEffect 1)
  let I := twoSidedResidualExtension M 1 0
  let J := twoSidedResidualExtension M 0 1
  refine ⟨I, J, ?_⟩
  have hdim : I.ambientDim = J.ambientDim := by
    simp [I, J, M, twoSidedResidualExtension, complementResidualExtension, eventResidualExtension, ambientDim_residualExtension_fin]
  have htotal : totalResidualDim I = totalResidualDim J := by
    simp [totalResidualDim, I, J, twoSidedResidualExtension, excessEventDim_complementResidualExtension, excessComplementDim_complementResidualExtension, excessEventDim_eventResidualExtension, excessComplementDim_eventResidualExtension]
    omega
  have hevent : excessEventDim I ≠ excessEventDim J := by
    simp [I, J, twoSidedResidualExtension, excessEventDim_complementResidualExtension, excessEventDim_eventResidualExtension]
  refine ⟨hdim, htotal, hevent, ?_⟩
  intro hIso
  exact hevent (strictIso_iff_residualDims_eq.mp hIso).1
end
end QuantumFoundations.Naimark.BinaryImpl
