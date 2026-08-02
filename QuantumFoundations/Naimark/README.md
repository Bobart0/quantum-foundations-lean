# Naimark — dilation theorem and the strict classification of its implementations

**FR.** `Naimark/{Defs,SqrtOp,DilSpace,Main,Unitary}.lean` établit le
théorème de dilatation de Naimark en dimension finie : toute POVM à `m`
issues sur `H n` se réalise comme la restriction d'une mesure projective
sur un espace ambiant `EuclideanSpace ℂ (Fin m × Fin n)`. `Naimark/
BinaryImpl/` (Module C, "Porte Ω") classe ENSUITE la structure exacte de
TOUTES les implémentations concrètes possibles d'un effet binaire fixé,
au-dessus de ce théorème, sans jamais le redémontrer.

**EN.** `Naimark/{Defs,SqrtOp,DilSpace,Main,Unitary}.lean` establishes the
finite-dimensional Naimark dilation theorem: every `m`-outcome POVM on
`H n` is realized as the restriction of a projective measurement on an
ambient space `EuclideanSpace ℂ (Fin m × Fin n)`. `Naimark/BinaryImpl/`
(Module C, "Omega Gate") THEN classifies the exact structure of ALL
possible concrete implementations of a fixed binary effect, on top of
that theorem, without ever re-proving it.

## `BinaryImpl/` file-by-file map

| File | Content |
|---|---|
| `Defs.lean` | `BinaryImpl n E ι` (isometric encoding + measurement cell realizing `E`); `StrictIso` (isometry transporting encoding AND intertwining cells — strictly stronger than mere effect equality); `ambientDim`/`projectorRank`/`projectorNullity` and their `StrictIso` invariance |
| `Canonical.lean` | `canonicalBinaryImpl`/`canonicalSelectedOutcomeImpl`, both from `naimark_dilation`, never re-proved |
| `Minimal.lean` | `eventLeg`/`complementLeg`, `minimalSubspace`, `IsMinimal` (no wasted residual dimension) |
| `GramRange.lean` | Gram identities; the general lemma `exists_range_isometryEquiv_of_adjoint_comp_self_eq` (same Gram ⟹ canonically isometric ranges) and its ambient-to-ambient surjective variant; `eventGeneratedEquiv`/`complementGeneratedEquiv` |
| `MinimalUniqueness.lean` | **`minimal_strictIso`** — two MINIMAL implementations of the same effect are ALWAYS strictly isomorphic (the module's central theorem) |
| `Residual.lean` | `excessEventDim`/`excessComplementDim` (the two residual multiplicities), additive decompositions of every global quantity into a minimal part (depends only on `E`) plus a residual part (depends on `I`) |
| `StrictClassification.lean` | Complete strict classification: `strictIso_of_residualDims_eq` and `strictIso_iff_residualDims_eq` for the two residual dimensions |
| `ReplicatedAncilla.lean` | `replicatedAncillaImpl` (identical replicas in `a` orthogonal blocks); `rankRatio := projectorRank / ambientDim` and its exact invariance under replication |
| `TernaryFusion.lean` | The canonical binary/ternary counterexample: ratios `1/2` vs `1/3`, non-isomorphism surviving arbitrary ancilla replication on both sides |
| `Valuation.lean` | `ImplValuation`, `StrictIsoInvariant`, `ReplicatedAncillaNeutral`; `rankRatio` satisfies both, `ambientDim` separates them |
| `Nonvacuity.lean` / `Nontriviality.lean` | Concrete witnesses that the structures above are satisfiable and genuinely distinguishing |
| `Main.lean` | Complete synthesis, capstone `rankRatio_eq_of_isMinimal`, and an explicit scope statement |

## The central theorem in one paragraph

**FR.** `minimal_strictIso` dit : si `I` et `J` sont deux implémentations
MINIMALES (`IsMinimal`, aucune dimension ambiante inutilisée) d'un même
effet `E`, alors elles sont strictement isomorphes — il existe une
isométrie de l'espace ambiant qui transporte l'encodage ET entrelace les
cellules, pas seulement qui préserve l'effet induit (ce qui serait
automatique). La construction évite le recollement général de deux
isométries séparées (`eventGeneratedEquiv`/`complementGeneratedEquiv`) en
routant par une application combinée UNIQUE `combinedLeg I : DilSpace n 2
→ₗ[ℂ] EuclideanSpace ℂ ι` dont l'image est exactement `minimalSubspace I`
et dont le Gram ne dépend que de `E`, ce qui contourne un diamant
d'instances Lean persistant entre le chemin `Module` propre à
`EuclideanSpace`/`WithLp` et celui, générique, attendu par
`LinearIsometryEquiv.inner_map_map` à un type `Submodule` explicite.

**EN.** `minimal_strictIso` says: if `I` and `J` are two MINIMAL
implementations (`IsMinimal`, no unused ambient dimension) of the same
effect `E`, then they are strictly isomorphic — there is an isometry of
the ambient space that transports the encoding AND intertwines the
cells, not merely one that preserves the induced effect (which would be
automatic). The construction avoids gluing two separately-built
isometries (`eventGeneratedEquiv`/`complementGeneratedEquiv`) by routing
through a SINGLE combined map `combinedLeg I : DilSpace n 2 →ₗ[ℂ]
EuclideanSpace ℂ ι` whose image is exactly `minimalSubspace I` and whose
Gram depends only on `E`, which sidesteps a persistent Lean instance
diamond between `EuclideanSpace`/`WithLp`'s own `Module` path and the
generic one expected by `LinearIsometryEquiv.inner_map_map` at an
explicit `Submodule` type.

## Status and scope

All finite-dimensional Module C constructions listed in this document are
implemented and audited. This includes the residual extensions and normal
form (`residualExtension`, `eventResidualExtension`,
`complementResidualExtension`, `twoSidedResidualExtension`, `minimalCore`,
`normalForm`, and `strictIso_normalForm`), the exact strict classification
`strictIso_iff_residualDims_eq`, and the residual-neutral valuation
classification through `implementationIndependent_of_residualNeutral`.

The public counter-models and nonvacuity results are included as well. The
complete surface is checked by `QuantumFoundations/Audit/NaimarkOmega.lean`,
whose declarations use only `[propext, Classical.choice, Quot.sound]` and no
`sorryAx`.

The scope remains finite-dimensional and interpretively neutral. Nothing here
reproves the Naimark dilation theorem, and no infinite-dimensional or physical
claim is made.