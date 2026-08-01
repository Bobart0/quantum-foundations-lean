import QuantumFoundations.Naimark.BinaryImpl.Main
import QuantumFoundations.Naimark.BinaryImpl.StrictClassification

/-!
**FR.** # Audit de régression pour la porte Ω (Module C, classification de Naimark)

Module non importé par la racine (à l'image de `Audit/FoP.lean`,
`Audit/DownstreamAPI.lean`, `Audit/SelectorStructure.lean`), exécuté
séparément en CI. Il `#check` chaque déclaration publique de
`Naimark/BinaryImpl/{Defs,Canonical,Minimal,GramRange,MinimalUniqueness,
Residual,StrictClassification,ReplicatedAncilla,TernaryFusion,Valuation,
Nonvacuity,Nontriviality,Main}.lean`, puis imprime les axiomes des
théorèmes phares. Objectif : un futur refactor qui casserait une
signature ou introduirait un axiome caché échoue ici.

**EN.** # Regression audit for the Omega Gate (Module C, Naimark classification)

A module not imported by the root (mirroring `Audit/FoP.lean`,
`Audit/DownstreamAPI.lean`, `Audit/SelectorStructure.lean`), run
separately in CI. It `#check`s every public declaration in
`Naimark/BinaryImpl/{Defs,Canonical,Minimal,GramRange,MinimalUniqueness,
Residual,StrictClassification,ReplicatedAncilla,TernaryFusion,Valuation,
Nonvacuity,Nontriviality,Main}.lean`, then prints the axioms of the
headline theorems. Goal: a future refactor that would break a signature
or introduce hidden axioms fails here.
-/

namespace QuantumFoundations.Audit.NaimarkOmega

open QuantumFoundations.Naimark.BinaryImpl
open Gleason

/-! ## `Defs.lean` -/

#check @BinaryImpl
#check @BinaryImpl.StrictIso
#check @BinaryImpl.ambientDim
#check @BinaryImpl.eventCell
#check @BinaryImpl.complementCell
#check @BinaryImpl.cell_idempotent
#check @BinaryImpl.cell_symmetric
#check @BinaryImpl.complementCell_isProjection
#check @BinaryImpl.cell_comp_complement_eq_zero
#check @BinaryImpl.complement_comp_cell_eq_zero
#check @BinaryImpl.cell_add_complement_eq_one
#check @BinaryImpl.StrictIso.refl
#check @BinaryImpl.StrictIso.symm
#check @BinaryImpl.StrictIso.trans
#check @BinaryImpl.StrictIso.ambientDim_eq
#check @BinaryImpl.StrictIso.projectorRange_finrank_eq
#check @BinaryImpl.StrictIso.projectorKernel_finrank_eq
#check @BinaryImpl.projectorRank
#check @BinaryImpl.projectorNullity
#check @BinaryImpl.projectorRank_add_nullity

/-! ## `Canonical.lean` -/

#check @povmOfEffect
#check @povmOfEffect_zero
#check @canonicalBinaryImpl
#check @canonicalBinaryImpl_ambientDim
#check @canonicalBinaryImpl_projectorRank
#check @canonicalBinaryImpl_projectorNullity
#check @canonicalSelectedOutcomeImpl
#check @canonicalSelectedOutcomeImpl_ambientDim
#check @canonicalSelectedOutcomeImpl_projectorRank
#check @canonicalSelectedOutcomeImpl_projectorNullity

/-! ## `Minimal.lean` -/

#check @eventLeg
#check @complementLeg
#check @eventGenerated
#check @complementGenerated
#check @minimalSubspace
#check @eventGenerated_le_cellRange
#check @complementGenerated_le_cellKernel
#check @eventGenerated_orthogonal_complementGenerated
#check @encoding_mem_minimalSubspace
#check @cell_maps_minimalSubspace
#check @complement_maps_minimalSubspace
#check @minimalSubspace_isReducing
#check @IsMinimal
#check @isMinimal_iff_span_legs_eq_top
#check @isMinimal_iff_orthogonal_eq_bot

/-! ## `GramRange.lean` -/

#check @eventLeg_adjoint_comp_self
#check @complementLeg_adjoint_comp_self
#check @event_complement_cross_gram_eq_zero
#check @exists_range_isometryEquiv_of_adjoint_comp_self_eq
#check @exists_isometryEquiv_of_adjoint_comp_self_eq_of_surjective
#check @eventGeneratedEquiv
#check @eventGeneratedEquiv_apply
#check @eventGeneratedEquiv_inner
#check @complementGeneratedEquiv
#check @complementGeneratedEquiv_apply
#check @complementGeneratedEquiv_inner

/-! ## `MinimalUniqueness.lean` -/

#check @combinedLeg
#check @combinedLeg_apply
#check @range_combinedLeg
#check @combinedLeg_gram_eq
#check @minimal_strictIso

/-! ## `Residual.lean` -/

#check @residualSubspace
#check @residualEvent
#check @residualComplement
#check @residualEvent_orthogonal_residualComplement
#check @residualEvent_sup_residualComplement_eq_residualSubspace
#check @minimalSubspace_sup_residualSubspace_eq_top
#check @excessEventDim
#check @excessComplementDim
#check @minimalSubspace_finrank_add_residualSubspace_finrank
#check @residualSubspace_finrank_eq_excess_sum
#check @ambientDim_decomposition
#check @range_cell_eq_eventGenerated_sup_residualEvent
#check @eventGenerated_orthogonal_residualEvent
#check @projectorRank_decomposition
#check @minimalSubspace_finrank_eq_sum
#check @projectorNullity_decomposition
#check @eventGenerated_finrank_eq_of_sameEffect
#check @complementGenerated_finrank_eq_of_sameEffect
#check @minimalSubspace_finrank_eq_of_sameEffect

/-! ## `StrictClassification.lean` -/

#check @StrictIso.excessEventDim_eq
#check @StrictIso.excessComplementDim_eq

/-! ## `ReplicatedAncilla.lean` -/

#check @blockSingle
#check @blockCoord
#check @adjoint_blockSingle
#check @adjoint_blockCoord
#check @blockCoord_blockSingle
#check @replicateOperator
#check @blockCoord_replicateOperator
#check @blockAssemble
#check @blockAssemble_injective
#check @range_replicateOperator_eq
#check @finrank_range_replicateOperator
#check @replicateOperator_idempotent
#check @adjoint_replicateOperator
#check @replicateOperator_symmetric
#check @replicatedAncillaImpl
#check @replicatedAncilla_ambientDim
#check @replicatedAncilla_projectorRank
#check @rankRatio
#check @rankRatio_replicatedAncilla
#check @StrictIso.rankRatio_eq

/-! ## `TernaryFusion.lean` -/

#check @ternaryPovmOfEffect
#check @ternaryPovmOfEffect_zero
#check @canonicalTernaryImpl
#check @canonicalTernaryImpl_ambientDim
#check @canonicalTernaryImpl_projectorRank
#check @canonicalBinaryImpl_rankRatio
#check @canonicalTernaryImpl_rankRatio
#check @not_strictIso_of_rankRatio_ne
#check @not_strictIso_replicatedAncilla_of_rankRatio_ne
#check @canonicalBinaryImpl_canonicalTernaryImpl_not_strictIso
#check @canonicalBinaryImpl_canonicalTernaryImpl_not_strictIso_replicatedAncilla

/-! ## `Valuation.lean` -/

#check @one_isEffect
#check @ImplValuation
#check @StrictIsoInvariant
#check @ReplicatedAncillaNeutral
#check @rankRatioValuation
#check @rankRatioValuation_strictIsoInvariant
#check @rankRatioValuation_replicatedAncillaNeutral
#check @ambientDimValuation
#check @ambientDimValuation_strictIsoInvariant
#check @ambientDimValuation_not_replicatedAncillaNeutral

/-! ## `Nonvacuity.lean` / `Nontriviality.lean` -/

#check @binaryImpl_nonempty
#check @strictIso_nonvacuous
#check @implValuation_nonvacuous
#check @strictIso_not_total
#check @strictIsoInvariant_not_le_replicatedAncillaNeutral

/-! ## `Main.lean` -/

#check @rankRatio_eq_of_isMinimal

/-! ## Axiom audit — headline theorems -/

#print axioms BinaryImpl.StrictIso.trans
#print axioms minimal_strictIso
#print axioms exists_range_isometryEquiv_of_adjoint_comp_self_eq
#print axioms exists_isometryEquiv_of_adjoint_comp_self_eq_of_surjective
#print axioms ambientDim_decomposition
#print axioms projectorRank_decomposition
#print axioms StrictIso.excessEventDim_eq
#print axioms StrictIso.excessComplementDim_eq
#print axioms finrank_range_replicateOperator
#print axioms replicatedAncillaImpl
#print axioms rankRatio_replicatedAncilla
#print axioms StrictIso.rankRatio_eq
#print axioms canonicalBinaryImpl_canonicalTernaryImpl_not_strictIso_replicatedAncilla
#print axioms ambientDimValuation_not_replicatedAncillaNeutral
#print axioms rankRatio_eq_of_isMinimal

end QuantumFoundations.Audit.NaimarkOmega
