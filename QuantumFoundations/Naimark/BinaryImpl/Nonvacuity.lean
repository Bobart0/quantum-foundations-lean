import QuantumFoundations.Naimark.BinaryImpl.ResidualValuation

namespace QuantumFoundations.Naimark.BinaryImpl

open QuantumFoundations Gleason
open scoped InnerProductSpace

noncomputable section

universe u
variable {R : Type u} {n : ℕ} {E : H n →ₗ[ℂ] H n}

theorem binaryImpl_nonempty (hE : Gleason.IsEffect E) :
    Nonempty (BinaryImpl n E (Fin 2 × Fin n)) :=
  ⟨canonicalBinaryImpl E hE⟩

theorem strictIso_nonvacuous {ι : Type} [Fintype ι] [DecidableEq ι]
    (I : BinaryImpl n E ι) :
    ∃ J : BinaryImpl n E ι, BinaryImpl.StrictIso I J :=
  ⟨I, BinaryImpl.StrictIso.refl I⟩

def constantImplValuation [Zero R] (c : R) : ImplValuationR R n E :=
  fun _ => c

theorem constantImplValuation_strictIsoInvariant [Zero R] (c : R) :
    StrictIsoInvariantR (constantImplValuation (n := n) (E := E) c) := by
  intro ι κ _ _ _ _ I J hIso
  rfl

theorem constantImplValuation_eventResidualNeutral [Zero R] (c : R) :
    EventResidualNeutral (constantImplValuation (n := n) (E := E) c) := by
  intro ι _ _ I r
  rfl

theorem constantImplValuation_complementResidualNeutral [Zero R] (c : R) :
    ComplementResidualNeutral (constantImplValuation (n := n) (E := E) c) := by
  intro ι _ _ I s
  rfl

theorem constantImplValuation_residualNeutral [Zero R] (c : R) :
    ResidualExtensionNeutral (constantImplValuation (n := n) (E := E) c) :=
  ⟨constantImplValuation_eventResidualNeutral c,
    constantImplValuation_complementResidualNeutral c⟩

def constantResidualNeutralImplValuation [Zero R] (c : R) :
    ResidualNeutralImplValuation R n E where
  valuation := constantImplValuation c
  strictIsoInvariant := constantImplValuation_strictIsoInvariant c
  residualNeutral := constantImplValuation_residualNeutral c

theorem residualNeutralImplValuation_nonempty [Zero R] :
    Nonempty (ResidualNeutralImplValuation R n E) :=
  ⟨constantResidualNeutralImplValuation (n := n) (E := E) 0⟩

def constantMinimalImplValuation [Zero R] (c : R) :
    MinimalImplValuation R n E where
  value := fun _ _ => c
  strictIsoInvariant := by
    intro ι κ _ _ _ _ I J hI hJ hIso
    rfl

theorem minimalImplValuation_nonempty [Zero R] :
    Nonempty (MinimalImplValuation R n E) :=
  ⟨constantMinimalImplValuation (n := n) (E := E) 0⟩

theorem implValuation_nonvacuous :
    ∃ v : ImplValuation n E, StrictIsoInvariant v ∧ ReplicatedAncillaNeutral v :=
  ⟨rankRatioValuation, rankRatioValuation_strictIsoInvariant,
    rankRatioValuation_replicatedAncillaNeutral⟩

end

end QuantumFoundations.Naimark.BinaryImpl
