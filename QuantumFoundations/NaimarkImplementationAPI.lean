import QuantumFoundations.Naimark.BinaryImpl.Main

/-! Public additive facade for the binary Naimark implementation results. -/
namespace QuantumFoundations.NaimarkImplementationAPI

export Gleason (H IsEffect)

export QuantumFoundations.Naimark.BinaryImpl.BinaryImpl (StrictIso)

export QuantumFoundations.Naimark.BinaryImpl
  (BinaryImpl IsMinimal minimalSubspace residualSubspace residualEvent
   residualComplement excessEventDim excessComplementDim
   strictIso_of_residualDims_eq strictIso_iff_residualDims_eq minimalCore
   minimalCore_isMinimal normalForm strictIso_normalForm residualExtension
   eventResidualExtension complementResidualExtension twoSidedResidualExtension
   ImplValuationR StrictIsoInvariantR ReplicatedAncillaNeutralR
   EventResidualNeutral ComplementResidualNeutral ResidualExtensionNeutral
   MinimalImplValuation ResidualNeutralImplValuation
   valuation_eq_minimalCore_of_residualNeutral
   residualNeutralValuationsEquivMinimalValuations
   implementationIndependent_of_residualNeutral rankRatio rankRatioValuation
   rankRatioValuation_not_residualNeutral
   replicatedAncillaNeutral_not_implies_residualNeutral
   totalResidualDim_not_complete_invariant)

end QuantumFoundations.NaimarkImplementationAPI
