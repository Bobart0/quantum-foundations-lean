import QuantumFoundations.BornRule.RefinementAPI
import QuantumFoundations.BornRule.EffectPerspectives.Qubit
import QuantumFoundations.BranchesRiedel.BornBridge.Synthesis
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

end BornBridge

end QuantumFoundations.ProbabilityAPI
