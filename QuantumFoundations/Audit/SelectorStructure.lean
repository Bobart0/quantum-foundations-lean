import QuantumFoundations.Selectors.StructureMain

/-!
**FR.** # Audit de régression pour la structure supplémentaire de Module B

Module non importé par la racine (à l'image de `Audit/FoP.lean` et
`Audit/DownstreamAPI.lean`), exécuté séparément en CI. Il `#check` chaque
déclaration publique de `Selectors/{Dephasing,SubgroupCovariance,
BasisStabilizer,PerspectiveDephasing,PerspectiveStabilizer,
PerspectiveClassification,Monotonicity,StructureNonvacuity,
StructureNontriviality,StructureMain}.lean` (Module B, B1-B16), puis
imprime les axiomes des théorèmes phares. Objectif : un futur refactor qui
casserait une signature ou introduirait un axiome caché échoue ici.

**EN.** # Regression audit for Module B's additional structure

A module not imported by the root (mirroring `Audit/FoP.lean` and
`Audit/DownstreamAPI.lean`), run separately in CI. It `#check`s every
public declaration in `Selectors/{Dephasing,SubgroupCovariance,
BasisStabilizer,PerspectiveDephasing,PerspectiveStabilizer,
PerspectiveClassification,Monotonicity,StructureNonvacuity,
StructureNontriviality,StructureMain}.lean` (Module B, B1-B16), then prints
the axioms of the headline theorems. Goal: a future refactor that would
break a signature or introduce hidden axioms fails here.
-/

namespace QuantumFoundations.Audit.SelectorStructure

open QuantumFoundations.Selector
open QuantumFoundations.BornRule
open Gleason

/-! ## B1-B5 — `Dephasing.lean` -/

#check @dephasedDensity
#check @dephasedDensity_isDensity
#check @dephasingSelector
#check @dephasingSelector_not_covariant
#check @dephasingSelector_violates_nsnc1

/-! ## B6-B7 — `SubgroupCovariance.lean` -/

#check @IsCovariantUnder
#check @IsInvariantUnder
#check @isInvariantUnder_mono
#check @selector_value_invariant_under_stateStabilizer

/-! ## B8-B9 — `BasisStabilizer.lean` -/

#check @BasisPhaseStabilizer
#check @BasisMonomialStabilizer
#check @BasisPhaseStabilizer_le_BasisMonomialStabilizer
#check @phaseInvariant_density_iff_diagonal
#check @monomialInvariant_density_iff_maximallyMixed

/-! ## B10 — `PerspectiveDephasing.lean` -/

#check @Perspective.Cell
#check @cellProjection
#check @perspectiveDephasedDensity
#check @perspectiveDephasedDensity_isDensity
#check @perspectiveDephasingSelector
#check @perspectiveDephasedDensity_basisPerspective

/-! ## B11 — `PerspectiveStabilizer.lean` -/

#check @PerspectiveCellwiseStabilizer
#check @PerspectiveSetwiseStabilizer
#check @PerspectiveCellwiseStabilizer_le_PerspectiveSetwiseStabilizer
#check @mem_cellwiseStabilizer_iff_commutes_cellProjection
#check @perspectiveDephasingSelector_isCovariantUnder_cellwiseStabilizer
#check @perspectiveDephasingSelector_isCovariantUnder_setwiseStabilizer

/-! ## B12-B13 — `PerspectiveClassification.lean` -/

#check @sum_projL_cells_eq_id
#check @blockScalarOperator
#check @IsBlockDensityWeights
#check @blockScalarOperator_isDensity
#check @blockScalarOperator_isInvariantUnder_cellwiseStabilizer
#check @cellRestriction_eq_scalar
#check @cellwiseInvariant_density_iff_blockScalar
#check @blockScalarOperator_apply_of_mem
#check @blockScalarOperator_isInvariantUnder_setwiseStabilizer_of_orbitConstant
#check @setwiseInvariant_density_iff_blockScalar_orbitConstant

/-! ## B14 — `Monotonicity.lean` -/

#check @isInvariantUnder_bot
#check @PerspectiveCellwiseStabilizer_mono_of_refines
#check @PerspectiveCellwiseStabilizer_refinePerspective_le
#check @isInvariantUnder_cellwiseStabilizer_of_refines
#check @PerspectiveCellwiseStabilizer_eq_top_of_singleton_top

/-! ## B15 — `StructureNonvacuity.lean` / `StructureNontriviality.lean` -/

#check @maximallyMixed_isDensityOperator
#check @maximallyMixed_isInvariantUnder
#check @cellwiseInvariant_density_nonvacuous
#check @setwiseInvariant_density_nonvacuous
#check @PerspectiveCellwiseStabilizer_lt_PerspectiveSetwiseStabilizer_of_basisPerspective

/-! ## B16 — `StructureMain.lean` -/

#check @cellwiseInvariant_density_of_refines

/-! ## Axiom audit — headline theorems -/

#print axioms cellwiseInvariant_density_iff_blockScalar
#print axioms setwiseInvariant_density_iff_blockScalar_orbitConstant
#print axioms PerspectiveCellwiseStabilizer_mono_of_refines
#print axioms cellwiseInvariant_density_nonvacuous
#print axioms setwiseInvariant_density_nonvacuous
#print axioms PerspectiveCellwiseStabilizer_lt_PerspectiveSetwiseStabilizer_of_basisPerspective
#print axioms cellwiseInvariant_density_of_refines

end QuantumFoundations.Audit.SelectorStructure
