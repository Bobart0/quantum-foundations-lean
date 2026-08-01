import QuantumFoundations.Naimark.BinaryImpl.MinimalCore
import QuantumFoundations.Naimark.BinaryImpl.Valuation
namespace QuantumFoundations.Naimark.BinaryImpl
open QuantumFoundations Gleason
noncomputable section
universe u
variable {R : Type u} {n : ℕ} {E : H n →ₗ[ℂ] H n}
def EventResidualNeutral (v : ImplValuationR R n E) : Prop := ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (I : BinaryImpl n E ι) (r : ℕ), v (eventResidualExtension I r) = v I
def ComplementResidualNeutral (v : ImplValuationR R n E) : Prop := ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (I : BinaryImpl n E ι) (s : ℕ), v (complementResidualExtension I s) = v I
def ResidualExtensionNeutral (v : ImplValuationR R n E) : Prop := EventResidualNeutral v ∧ ComplementResidualNeutral v
theorem ResidualExtensionNeutral.event (h : ResidualExtensionNeutral v) {ι : Type} [Fintype ι] [DecidableEq ι] (I : BinaryImpl n E ι) (r : ℕ) : v (eventResidualExtension I r) = v I := h.1 I r
theorem ResidualExtensionNeutral.complement (h : ResidualExtensionNeutral v) {ι : Type} [Fintype ι] [DecidableEq ι] (I : BinaryImpl n E ι) (s : ℕ) : v (complementResidualExtension I s) = v I := h.2 I s
theorem ResidualExtensionNeutral.twoSided (h : ResidualExtensionNeutral v) {ι : Type} [Fintype ι] [DecidableEq ι] (I : BinaryImpl n E ι) (r s : ℕ) : v (twoSidedResidualExtension I r s) = v I := by
  calc
    v (twoSidedResidualExtension I r s) = v (eventResidualExtension I r) := h.complement (eventResidualExtension I r) s
    _ = v I := h.event I r
structure MinimalImplValuation (R : Type u) (n : ℕ) (E : H n →ₗ[ℂ] H n) where
  value : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (I : BinaryImpl n E ι), IsMinimal I → R
  strictIsoInvariant : ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (I : BinaryImpl n E ι) (J : BinaryImpl n E κ) (hI : IsMinimal I) (hJ : IsMinimal J), BinaryImpl.StrictIso I J → value I hI = value J hJ
noncomputable def restrictToMinimal (v : ImplValuationR R n E) (hStrict : StrictIsoInvariantR v) : MinimalImplValuation R n E where
  value := fun I _ => v I
  strictIsoInvariant := by intro ι κ _ _ _ _ I J hI hJ hIso; exact hStrict I J hIso
noncomputable def extendFromMinimal (w : MinimalImplValuation R n E) : ImplValuationR R n E := fun I => w.value (minimalCore I) (minimalCore_isMinimal I)
theorem extendFromMinimal_strictIsoInvariant (w : MinimalImplValuation R n E) : StrictIsoInvariantR (extendFromMinimal w) := by
  intro ι κ _ _ _ _ I J hIso
  exact w.strictIsoInvariant (minimalCore I) (minimalCore J) (minimalCore_isMinimal I) (minimalCore_isMinimal J) (minimalCore_unique_up_to_strictIso I J)
theorem extendFromMinimal_eventResidualNeutral (w : MinimalImplValuation R n E) : EventResidualNeutral (extendFromMinimal w) := by
  intro ι _ _ I r
  exact w.strictIsoInvariant (minimalCore (eventResidualExtension I r)) (minimalCore I) (minimalCore_isMinimal _) (minimalCore_isMinimal I) (minimalCore_unique_up_to_strictIso _ I)
theorem extendFromMinimal_complementResidualNeutral (w : MinimalImplValuation R n E) : ComplementResidualNeutral (extendFromMinimal w) := by
  intro ι _ _ I s
  exact w.strictIsoInvariant (minimalCore (complementResidualExtension I s)) (minimalCore I) (minimalCore_isMinimal _) (minimalCore_isMinimal I) (minimalCore_unique_up_to_strictIso _ I)
theorem extendFromMinimal_residualNeutral (w : MinimalImplValuation R n E) : ResidualExtensionNeutral (extendFromMinimal w) := ⟨extendFromMinimal_eventResidualNeutral w, extendFromMinimal_complementResidualNeutral w⟩
structure ResidualNeutralImplValuation (R : Type u) (n : ℕ) (E : H n →ₗ[ℂ] H n) where
  valuation : ImplValuationR R n E
  strictIsoInvariant : StrictIsoInvariantR valuation
  residualNeutral : ResidualExtensionNeutral valuation
noncomputable def restrictResidualNeutralToMinimal (v : ResidualNeutralImplValuation R n E) : MinimalImplValuation R n E := restrictToMinimal v.valuation v.strictIsoInvariant
noncomputable def extendMinimalToResidualNeutral (w : MinimalImplValuation R n E) : ResidualNeutralImplValuation R n E where
  valuation := extendFromMinimal w
  strictIsoInvariant := extendFromMinimal_strictIsoInvariant w
  residualNeutral := extendFromMinimal_residualNeutral w
theorem valuation_eq_minimalCore_of_residualNeutral (v : ImplValuationR R n E) (hStrict : StrictIsoInvariantR v) (hNeutral : ResidualExtensionNeutral v) {ι : Type} [Fintype ι] [DecidableEq ι] (I : BinaryImpl n E ι) : v I = v (minimalCore I) := by
  have hIso := strictIso_normalForm I
  have h1 : v I = v (normalForm I) := hStrict I (normalForm I) hIso
  have h2 : v (normalForm I) = v (minimalCore I) := by
    unfold normalForm
    calc
      v (twoSidedResidualExtension (minimalCore I) (excessEventDim I) (excessComplementDim I)) = v (eventResidualExtension (minimalCore I) (excessEventDim I)) := hNeutral.complement _ _
      _ = v (minimalCore I) := hNeutral.event _ _
  exact h1.trans h2
theorem restrict_extend_minimal (w : MinimalImplValuation R n E) : restrictResidualNeutralToMinimal (extendMinimalToResidualNeutral w) = w := by
  cases w with
  | mk value invariant =>
    dsimp [restrictResidualNeutralToMinimal, extendMinimalToResidualNeutral, restrictToMinimal, extendFromMinimal]
    have hvalue : (fun {ι : Type} [Fintype ι] [DecidableEq ι] (I : BinaryImpl n E ι) (hI : IsMinimal I) => value (minimalCore I) (minimalCore_isMinimal I)) = @value := by
      funext ι instι instDec I hI
      exact (invariant I (minimalCore I) hI (minimalCore_isMinimal I) (minimal_strictIso hI (minimalCore_isMinimal I))).symm
    simpa only [hvalue]
theorem extend_restrict_residualNeutral (v : ResidualNeutralImplValuation R n E) : extendMinimalToResidualNeutral (restrictResidualNeutralToMinimal v) = v := by
  cases v with
  | mk valuation strict neutral =>
    dsimp [restrictResidualNeutralToMinimal, extendMinimalToResidualNeutral, restrictToMinimal]
    unfold extendFromMinimal
    have hvalue : (fun {ι : Type} [Fintype ι] [DecidableEq ι] (I : BinaryImpl n E ι) => valuation (minimalCore I)) = @valuation := by
      funext ι instι instDec I
      exact (valuation_eq_minimalCore_of_residualNeutral valuation strict neutral I).symm
    simpa only [hvalue]
noncomputable def residualNeutralValuationsEquivMinimalValuations : ResidualNeutralImplValuation R n E ≃ MinimalImplValuation R n E where
  toFun := restrictResidualNeutralToMinimal
  invFun := extendMinimalToResidualNeutral
  left_inv := extend_restrict_residualNeutral
  right_inv := restrict_extend_minimal
theorem implementationIndependent_of_residualNeutral (v : ImplValuationR R n E) (hStrict : StrictIsoInvariantR v) (hNeutral : ResidualExtensionNeutral v) {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (I : BinaryImpl n E ι) (J : BinaryImpl n E κ) : v I = v J := by
  rw [valuation_eq_minimalCore_of_residualNeutral v hStrict hNeutral I, valuation_eq_minimalCore_of_residualNeutral v hStrict hNeutral J]
  exact hStrict (minimalCore I) (minimalCore J) (minimalCore_unique_up_to_strictIso I J)
end
end QuantumFoundations.Naimark.BinaryImpl
