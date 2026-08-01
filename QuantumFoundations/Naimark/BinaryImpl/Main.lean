import QuantumFoundations.Naimark.BinaryImpl.Nontriviality
import QuantumFoundations.Naimark.BinaryImpl.ResidualValuation
import QuantumFoundations.Naimark.BinaryImpl.StrictClassification

/-!
# Module C (Porte Ω) — synthèse complète

Le module formalise la classification stricte des implémentations binaires
d'un effet fixé. Toute implémentation est strictement isomorphe à une forme
normale obtenue en ajoutant séparément un résidu événementiel et un résidu
complémentaire à son cœur minimal.

Les extensions résiduelles, les formules de dimensions, la construction de
`minimalCore`, la normalisation stricte et la caractérisation
`residualNeutralValuationsEquivMinimalValuations` sont publics. La dernière
équivalence identifie exactement les valuations invariantes strictes et
neutres sous extensions résiduelles aux valuations définies sur les cœurs
minimaux.
-/

namespace QuantumFoundations.Naimark.BinaryImpl

open QuantumFoundations Gleason
open scoped InnerProductSpace

noncomputable section

variable {n : ℕ} {E : H n →ₗ[ℂ] H n}

theorem rankRatio_eq_of_isMinimal {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {I : BinaryImpl n E ι} {J : BinaryImpl n E κ}
    (hI : IsMinimal I) (hJ : IsMinimal J) : rankRatio I = rankRatio J :=
  StrictIso.rankRatio_eq (minimal_strictIso hI hJ)

end

end QuantumFoundations.Naimark.BinaryImpl
