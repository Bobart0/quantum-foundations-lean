import QuantumFoundations.BornRule.RefinementAPI
import QuantumFoundations.BornRule.Nonvacuity
import QuantumFoundations.BornRule.EffectPerspectives.Qubit
import QuantumFoundations.BornRule.EffectPerspectives.Nonvacuity
import QuantumFoundations.BranchesRiedel.BornBridge.Synthesis
import QuantumFoundations.BranchesRiedel.BornBridge.Nonvacuity
import Gleason.Operator

/-!
**FR.** # API de probabilité pour les développements aval

Point d'entrée **unique et délibérément minimal** pour les développements
aval (théorie de la décision bornienne, `everettian-probability-lean`) : un
seul `import QuantumFoundations.ProbabilityAPI` donne accès à toute
déclaration atteignable depuis ce module. Toute déclaration qui n'est **pas**
réexportée ici est interne et peut changer sans préavis.

Ce module **n'a aucun rôle dans l'argument du manuscrit** *One State, Many
Perspectives*. Il n'`import`e et ne réexporte que des déclarations déjà
existantes ; il ne contient aucun nouvel énoncé mathématique.

**Collision de noms documentée.** `QuantumFoundations.BornRule.Refines`
(une `Prop` existentielle sur les perspectives projectives) et
`QuantumFoundations.BornRule.EffectPerspectives.Refines` (une structure
portant un champ `parent`, sur les perspectives d'effets) portent le même
nom court dans des espaces de noms distincts. Conformément à la règle de
non-renommage, aucun des deux n'est renommé : le premier est réexporté à la
racine de `QuantumFoundations.ProbabilityAPI` (accessible comme
`ProbabilityAPI.Refines`), le second dans le sous-espace de noms
`QuantumFoundations.ProbabilityAPI.EffectPerspectives` (accessible comme
`ProbabilityAPI.EffectPerspectives.Refines`). Les deux notions restent
distinctes et non interchangeables ; voir `BornRule/EffectPerspectives/
README.md` pour la justification de cette séparation.

**EN.** # Probability API for downstream developments

A **single, deliberately minimal** entry point for downstream developments
(Born-weight decision theory, `everettian-probability-lean`): one
`import QuantumFoundations.ProbabilityAPI` gives access to every
declaration reachable from this module. Any declaration **not** re-exported
here is internal and may change without notice.

This module has **no role in the manuscript's argument** *One State, Many
Perspectives*. It only imports and re-exports declarations that already
exist; it contains no new mathematical statement.

**Documented name collision.** `QuantumFoundations.BornRule.Refines` (an
existential `Prop` on projective perspectives) and
`QuantumFoundations.BornRule.EffectPerspectives.Refines` (a structure
carrying a `parent` field, on effect perspectives) share the same short
name in distinct namespaces. Per the no-renaming rule, neither is renamed:
the first is re-exported at the root of `QuantumFoundations.ProbabilityAPI`
(accessible as `ProbabilityAPI.Refines`), the second in the
`QuantumFoundations.ProbabilityAPI.EffectPerspectives` sub-namespace
(accessible as `ProbabilityAPI.EffectPerspectives.Refines`). The two
notions remain distinct and not interchangeable; see
`BornRule/EffectPerspectives/README.md` for why they are kept separate.

**Convention des témoins de non-vacuité.** Les témoins réexportés par cette
façade sont systématiquement placés dans des sous-espaces de noms reflétant
leur sous-système d'origine : `ProbabilityAPI.BornRule`,
`ProbabilityAPI.EffectPerspectives` et `ProbabilityAPI.BornBridge`. Cette
convention fait partie du contrat d'import aval. Les réexports projectifs
historiques à la racine de `ProbabilityAPI` restent inchangés afin de préserver
la compatibilité additive.

**Nonvacuity-witness convention.** Witnesses re-exported by this façade are
systematically placed in sub-namespaces reflecting their source subsystem:
`ProbabilityAPI.BornRule`, `ProbabilityAPI.EffectPerspectives`, and
`ProbabilityAPI.BornBridge`. This convention is part of the downstream import
contract. The historical projective re-exports at the root of
`ProbabilityAPI` remain unchanged to preserve additive compatibility.
-/

namespace QuantumFoundations.ProbabilityAPI

/-! ## From `Gleason` -/

export Gleason (H projL IsEffect IsPositiveOp)

/-! ## From `BornRule` (projective perspectives, including `RefinementAPI`) -/

export QuantumFoundations.BornRule
  (Perspective
   Perspective.unique_parent
   Perspective.binary
   AxGrain
   AxNorm
   AxPos
   AxNul
   lemma4_noncontextual
   refinePerspective
   refinePerspective_refines
   grainCoherenceTheorem
   grainCoherenceTheorem_projector
   Refines
   Refines.refl
   Refines.trans
   parentOf
   parentOf_mem
   parentOf_le
   parentOf_eq_of_le
   coarseCells
   mem_coarseCells_iff
   axGrain_iff_coarseCells
   coarseCells_eq_fiber_parentOf)

/-! ## Nonvacuity witnesses

**FR.** Ces déclarations sont des témoins de non-vacuité déjà existants,
réexportés afin que les développements aval construisent leurs propres témoins
sans reprouver les résultats ni importer directement des modules internes.
Elles n'ajoutent aucun contenu mathématique indépendant.

**EN.** These declarations are existing nonvacuity witnesses, re-exported so
that downstream developments can build their own witnesses without reproving
results or importing internal modules directly. They add no independent
mathematical content.
-/

namespace BornRule

export QuantumFoundations.BornRule
  (refine_filter_sup_eq
   E₀
   E₀_isPos
   E₀_isNul
   E₀_isNorm
   E₀_isGrain
   E₀_satisfies_axioms)

end BornRule

/-! ## From `BornRule.EffectPerspectives` (effect perspectives)

**FR.** Isolé dans son propre sous-espace de noms pour éviter la collision
avec `Refines` ci-dessus (voir le docstring de module).

**EN.** Isolated in its own sub-namespace to avoid the collision with
`Refines` above (see the module docstring).
-/

namespace EffectPerspectives

export QuantumFoundations.BornRule.EffectPerspectives
  (EffectPerspective
   Effect
   Refines
   EstimationRule
   EstimationRule.effectWeight
   qubit_projectionEffect_weight_eq_born
   qubit_contextual_projection_weight_eq_born)

export QuantumFoundations.BornRule.EffectPerspectives
  (pureStateEstimationRule
   pureStateEstimationRule_nullSupport
   pureStateEstimationRule_weight
   qubitZeroState
   qubitOneState
   qubitZeroState_norm
   qubitOneState_norm
   qubitZeroState_inner_qubitOneState
   nonempty_estimationRule_two)

end EffectPerspectives

/-! ## From `BranchesRiedel.BornBridge` (record-induced branches) -/

namespace BornBridge

export QuantumFoundations.BranchesRiedel.BornBridge
  (ActiveBranchIndex
   branchCell
   branchPerspectiveOfResidual
   BranchPerspectivePackage
   exists_branchPerspectivePackage
   recordBranch_weight_eq_norm_sq
   sum_activeBranch_weights_eq_one
   RecordInducedBornConclusion
   record_induced_Born_decomposition)

export QuantumFoundations.BranchesRiedel.BornBridge
  (concrete_activeBranchIndex_nonempty
   concrete_exists_branchPerspectivePackage
   concrete_branch0_weight_ne_zero
   concrete_branch1_weight_ne_zero
   concrete_recordChoice_distinct
   concrete_recordChoice_weight_invariant_nonvacuous)

end BornBridge

end QuantumFoundations.ProbabilityAPI
