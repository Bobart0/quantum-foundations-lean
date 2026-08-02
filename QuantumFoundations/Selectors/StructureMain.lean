import QuantumFoundations.Selectors.Dephasing
import QuantumFoundations.Selectors.SubgroupCovariance
import QuantumFoundations.Selectors.BasisStabilizer
import QuantumFoundations.Selectors.PerspectiveDephasing
import QuantumFoundations.Selectors.PerspectiveStabilizer
import QuantumFoundations.Selectors.PerspectiveClassification
import QuantumFoundations.Selectors.Monotonicity
import QuantumFoundations.Selectors.StructureNonvacuity
import QuantumFoundations.Selectors.StructureNontriviality

/-!
**FR.** # Selectors — Module B, synthèse

Module B ajoute, au-dessus de la structure de sélecteur de Module A
(`Selectors/Defs.lean`), une deuxième couche : la **structure
supplémentaire** portée par une base ou une perspective (au sens
`QuantumFoundations.BornRule.Perspective`), et comment elle contraint les
opérateurs densité invariants sous les groupes de symétrie associés.

**Les quatre notions à ne pas confondre :**

1. **`Selector n`** (Module A, `Defs.lean`) : une règle `ψ ↦ ρ ψ` assignant
   à chaque état pur un opérateur densité. `IsCovariantUnder G σ` dit que
   `σ` commute avec l'action de `G` sur les états purs.
2. **`IsInvariantUnder G ρ`** (`SubgroupCovariance.lean`) : PAS une
   propriété d'un sélecteur, mais d'un opérateur densité FIXE `ρ` — `ρ`
   commute avec la conjugaison par tout élément de `G`. C'est cette notion,
   et non la covariance d'un sélecteur, que classifient les théorèmes de
   `PerspectiveClassification.lean`.
3. **`BasisPhaseStabilizer b` / `BasisMonomialStabilizer b`**
   (`BasisStabilizer.lean`) : sous-groupes attachés à UNE SEULE base
   orthonormée `b`, où chaque cellule est UNE DROITE. Cas particulier,
   pour `D = basisPerspective b`, du point suivant.
4. **`PerspectiveCellwiseStabilizer D` / `PerspectiveSetwiseStabilizer D`**
   (`PerspectiveStabilizer.lean`) : la généralisation à une perspective
   `D` quelconque (cellules de dimension arbitraire). Le premier fixe
   chaque cellule SETWISE ; le second permet des permutations de cellules.
   `PerspectiveCellwiseStabilizer D ≤ PerspectiveSetwiseStabilizer D`
   toujours (`PerspectiveCellwiseStabilizer_le_PerspectiveSetwiseStabilizer`),
   STRICTEMENT dès que `D` a au moins deux cellules de même "forme"
   (`PerspectiveCellwiseStabilizer_lt_PerspectiveSetwiseStabilizer_of_basisPerspective`,
   `StructureNontriviality.lean`).

**Fil conducteur du module :**
- `perspectiveDephasingSelector D` (`PerspectiveDephasing.lean`) est un
  sélecteur explicite (pinçage sur les cellules de `D`), covariant sous les
  DEUX stabilisateurs (`perspectiveDephasingSelector_isCovariantUnder_...`).
- Réciproquement, `cellwiseInvariant_density_iff_blockScalar` et
  `setwiseInvariant_density_iff_blockScalar_orbitConstant`
  (`PerspectiveClassification.lean`) CLASSIFIENT tous les opérateurs
  densité invariants sous chaque stabilisateur : ce sont exactement les
  opérateurs bloc-scalaires (`blockScalarOperator`), à poids constants sur
  chaque orbite pour le stabilisateur setwise. Ni l'un ni l'autre théorème
  n'utilise le lemme de Schur — la preuve passe par des témoins explicites
  (`reflIso`/`swapIso`, déjà présents dans `Unitaries.lean`) et une
  décomposition de Gram-Schmidt.
- Cette classification est NON VACUE pour toute perspective
  (`StructureNonvacuity.lean` : l'état maximalement mélangé qualifie
  toujours) et STRICTE au sens de la hiérarchie des sous-groupes
  (`StructureNontriviality.lean`).
- Elle est enfin MONOTONE sous raffinement (`Monotonicity.lean`) : un
  opérateur classifié pour une perspective grossière `D` l'est encore,
  automatiquement, pour toute perspective plus fine qu'elle raffine
  (`cellwiseInvariant_density_of_refines` ci-dessous, qui combine
  directement B12 et B14 sans preuve supplémentaire).

**EN.** # Selectors — Module B, synthesis

Module B adds, on top of Module A's selector structure
(`Selectors/Defs.lean`), a second layer: the **additional structure**
carried by a basis or a perspective (in the sense of
`QuantumFoundations.BornRule.Perspective`), and how it constrains the
density operators invariant under the associated symmetry groups.

**The four notions not to confuse:**

1. **`Selector n`** (Module A, `Defs.lean`): a rule `ψ ↦ ρ ψ` assigning a
   density operator to every pure state. `IsCovariantUnder G σ` says `σ`
   commutes with `G`'s action on pure states.
2. **`IsInvariantUnder G ρ`** (`SubgroupCovariance.lean`): NOT a property
   of a selector, but of a FIXED density operator `ρ` -- `ρ` commutes with
   conjugation by every element of `G`. This is the notion classified by
   the theorems in `PerspectiveClassification.lean`, not selector
   covariance.
3. **`BasisPhaseStabilizer b` / `BasisMonomialStabilizer b`**
   (`BasisStabilizer.lean`): subgroups attached to a SINGLE orthonormal
   basis `b`, where every cell is a LINE. A special case, for
   `D = basisPerspective b`, of the next point.
4. **`PerspectiveCellwiseStabilizer D` / `PerspectiveSetwiseStabilizer D`**
   (`PerspectiveStabilizer.lean`): the generalization to an arbitrary
   perspective `D` (cells of arbitrary dimension). The first fixes every
   cell SETWISE; the second allows cells to be permuted.
   `PerspectiveCellwiseStabilizer D ≤ PerspectiveSetwiseStabilizer D`
   always
   (`PerspectiveCellwiseStabilizer_le_PerspectiveSetwiseStabilizer`),
   STRICTLY as soon as `D` has at least two cells of the same "shape"
   (`PerspectiveCellwiseStabilizer_lt_PerspectiveSetwiseStabilizer_of_basisPerspective`,
   `StructureNontriviality.lean`).

**Module throughline:**
- `perspectiveDephasingSelector D` (`PerspectiveDephasing.lean`) is an
  explicit selector (pinching on `D`'s cells), covariant under BOTH
  stabilizers (`perspectiveDephasingSelector_isCovariantUnder_...`).
- Conversely, `cellwiseInvariant_density_iff_blockScalar` and
  `setwiseInvariant_density_iff_blockScalar_orbitConstant`
  (`PerspectiveClassification.lean`) CLASSIFY every density operator
  invariant under each stabilizer: they are exactly the block-scalar
  operators (`blockScalarOperator`), with weights constant on each orbit
  for the setwise stabilizer. Neither theorem uses Schur's lemma -- the
  proof goes through explicit witnesses (`reflIso`/`swapIso`, already
  present in `Unitaries.lean`) and a Gram-Schmidt decomposition.
- This classification is NONVACUOUS for every perspective
  (`StructureNonvacuity.lean`: the maximally mixed state always
  qualifies) and STRICT in the sense of the subgroup hierarchy
  (`StructureNontriviality.lean`).
- Finally, it is MONOTONE under refinement (`Monotonicity.lean`): an
  operator classified for a coarse perspective `D` remains classified,
  automatically, for any finer perspective it refines
  (`cellwiseInvariant_density_of_refines` below, which combines B12 and
  B14 directly with no further proof).
-/

namespace QuantumFoundations.Selector

open scoped InnerProductSpace
open Gleason
open QuantumFoundations.BornRule

noncomputable section

variable {n : ℕ}

/-- Capstone: combining the cellwise classification
(`cellwiseInvariant_density_iff_blockScalar`, B12) with refinement
monotonicity (`isInvariantUnder_cellwiseStabilizer_of_refines`, B14) --
any density operator classified as block-scalar for a COARSE perspective
`D` is automatically (re-)classified as block-scalar for any FINER
perspective `D'` it refines, with no additional invariance hypothesis
needed beyond the original one for `D`. -/
theorem cellwiseInvariant_density_of_refines {D' D : Perspective n} (h : Refines D' D)
    {ρ : H n →ₗ[ℂ] H n} (hdensity : IsDensityOperator ρ)
    (hinv : IsInvariantUnder (PerspectiveCellwiseStabilizer D) ρ) :
    ∃ t : Submodule ℂ (H n) → ℝ, IsBlockDensityWeights D' t ∧ ρ = blockScalarOperator D' t :=
  (cellwiseInvariant_density_iff_blockScalar D' ρ).mp
    ⟨hdensity, isInvariantUnder_cellwiseStabilizer_of_refines h hinv⟩

end

end QuantumFoundations.Selector
