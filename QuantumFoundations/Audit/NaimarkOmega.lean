import QuantumFoundations.Naimark.BinaryImpl.Main

namespace QuantumFoundations.Audit.NaimarkOmega

open QuantumFoundations.Naimark.BinaryImpl

#check @strictIso_iff_dim_rank_excess_eq
#check @blockDiagonal
#check @residualExtension
#check @eventResidualExtension
#check @complementResidualExtension
#check @twoSidedResidualExtension
#check @minimalCore
#check @minimalCore_isMinimal
#check @strictIso_normalForm
#check @minimalImpl_nonempty
#check @ImplValuationR
#check @StrictIsoInvariantR
#check @ReplicatedAncillaNeutralR
#check @EventResidualNeutral
#check @ComplementResidualNeutral
#check @ResidualExtensionNeutral
#check @MinimalImplValuation
#check @ResidualNeutralImplValuation
#check @valuation_eq_minimalCore_of_residualNeutral
#check @residualNeutralValuationsEquivMinimalValuations
#check @implementationIndependent_of_residualNeutral
#check @rankRatio_eventResidualExtension_example
#check @rankRatio_complementResidualExtension_example
#check @rankRatioValuation_not_residualNeutral
#check @totalResidualDim
#check @totalResidualDim_not_complete_invariant
#check @constantImplValuation
#check @constantResidualNeutralImplValuation
#check @residualNeutralImplValuation_nonempty
#check @minimalImplValuation_nonempty

#print axioms strictIso_iff_dim_rank_excess_eq
#print axioms strictIso_normalForm
#print axioms valuation_eq_minimalCore_of_residualNeutral
#print axioms residualNeutralValuationsEquivMinimalValuations
#print axioms rankRatioValuation_not_residualNeutral
#print axioms totalResidualDim_not_complete_invariant

end QuantumFoundations.Audit.NaimarkOmega
