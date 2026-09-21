import Gleason.Main
import Gleason.Busch.Main
import QuantumFoundations.Wigner.Main
import QuantumFoundations.Uhlhorn.Assembly
import QuantumFoundations.Uhlhorn.WignerProjectionForm
import QuantumFoundations.BornRule.Perspective
import QuantumFoundations.BornRule.Assembly
import QuantumFoundations.BornRule.SplitGeneration
import QuantumFoundations.BornRule.RefinementClosure
import QuantumFoundations.BornRule.RCBornCalibration
import QuantumFoundations.BornRule.RCSharpness
import QuantumFoundations.BornRule.RCSharpnessResolution
import QuantumFoundations.BornRule.RCSharpnessPositivity
import QuantumFoundations.BornRule.EffectPerspectives.Main
import QuantumFoundations.BornRule.EffectPerspectives.Qubit
import QuantumFoundations.Naimark.Main
import QuantumFoundations.Naimark.BinaryImpl.StrictClassification

/-!
# Publication theorem audit

This file is the publication-facing QuantumFoundations audit surface for the
article on the Cooke--Keane--Moran route to Gleason's theorem and its
finite-dimensional applications. It does not prove new mathematics. It checks
the public signatures used by the article and asks Lean to report the axiom
dependencies of every principal Gleason/Busch or QuantumFoundations theorem
cited there as a substantive result.

The dimension-two countermodels and weight-level deletion witnesses that live
in the downstream `everettian-probability-lean` repository are audited there
by `EverettianProbability/Audit/JournalCore.lean`; importing that downstream
package here would create a dependency cycle.

Expected trust base for every `#print axioms` below:
`[propext, Classical.choice, Quot.sound]`.
-/

-- Representation layer (pinned Gleason dependency)
#check @Gleason.busch
#check @Gleason.busch_born_rule
#check @Gleason.gleason
#check @Gleason.no_dispersion_free

#print axioms Gleason.busch
#print axioms Gleason.busch_born_rule
#print axioms Gleason.gleason
#print axioms Gleason.no_dispersion_free

-- Wigner and one-directional Uhlhorn--Semrl
#check @QuantumFoundations.Wigner.wigner
#check @QuantumFoundations.Uhlhorn.wigner_projection_form
#check @QuantumFoundations.Uhlhorn.uhlhorn_finite_dim

#print axioms QuantumFoundations.Wigner.wigner
#print axioms QuantumFoundations.Uhlhorn.wigner_projection_form
#print axioms QuantumFoundations.Uhlhorn.uhlhorn_finite_dim

-- Projective perspective route
#check @QuantumFoundations.BornRule.lemma4_noncontextual_grain_only
#check @QuantumFoundations.BornRule.axGrain_not_imply_axNorm
#check @QuantumFoundations.BornRule.grainCoherenceTheorem_projector
#check @QuantumFoundations.BornRule.refinement_binaryGenerated
#check @QuantumFoundations.BornRule.axRC_norm_implies_axGrain
#check @QuantumFoundations.BornRule.splitRCBornCalibration_projector

#print axioms QuantumFoundations.BornRule.lemma4_noncontextual_grain_only
#print axioms QuantumFoundations.BornRule.axGrain_not_imply_axNorm
#print axioms QuantumFoundations.BornRule.grainCoherenceTheorem_projector
#print axioms QuantumFoundations.BornRule.refinement_binaryGenerated
#print axioms QuantumFoundations.BornRule.axRC_norm_implies_axGrain
#print axioms QuantumFoundations.BornRule.splitRCBornCalibration_projector

-- Relative sharpness of the elementary-split statement
#check @QuantumFoundations.BornRule.sharpness_remove_norm
#check @QuantumFoundations.BornRule.sharpness_remove_null
#check @QuantumFoundations.BornRule.sharpness_remove_rc
#check @QuantumFoundations.BornRule.sharpness_remove_pos

#print axioms QuantumFoundations.BornRule.sharpness_remove_norm
#print axioms QuantumFoundations.BornRule.sharpness_remove_null
#print axioms QuantumFoundations.BornRule.sharpness_remove_rc
#print axioms QuantumFoundations.BornRule.sharpness_remove_pos

-- Effect-perspective / Busch route
#check @QuantumFoundations.BornRule.EffectPerspectives.projectionEffect_weight_eq_born
#check @QuantumFoundations.BornRule.EffectPerspectives.qubit_contextual_projection_weight_eq_born

#print axioms QuantumFoundations.BornRule.EffectPerspectives.projectionEffect_weight_eq_born
#print axioms QuantumFoundations.BornRule.EffectPerspectives.qubit_contextual_projection_weight_eq_born

-- Naimark existence and strict classification
#check @QuantumFoundations.naimark
#check @QuantumFoundations.Naimark.BinaryImpl.strictIso_iff_residualDims_eq

#print axioms QuantumFoundations.naimark
#print axioms QuantumFoundations.Naimark.BinaryImpl.strictIso_iff_residualDims_eq
