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
| `StrictClassification.lean` | The NECESSARY direction only: `StrictIso.excessEventDim_eq`/`StrictIso.excessComplementDim_eq`. The sufficient direction, and hence `strictIso_iff_residualDims_eq`, is deliberately not attempted — see "What is not claimed" below |
| `ReplicatedAncilla.lean` | `replicatedAncillaImpl` (identical replicas in `a` orthogonal blocks); `rankRatio := projectorRank / ambientDim` and its exact invariance under replication |
| `TernaryFusion.lean` | The canonical binary/ternary counterexample: ratios `1/2` vs `1/3`, non-isomorphism surviving arbitrary ancilla replication on both sides |
| `Valuation.lean` | `ImplValuation`, `StrictIsoInvariant`, `ReplicatedAncillaNeutral`; `rankRatio` satisfies both, `ambientDim` separates them |
| `Nonvacuity.lean` / `Nontriviality.lean` | Concrete witnesses that the structures above are satisfiable and genuinely distinguishing |
| `Main.lean` | Synthesis, capstone (`rankRatio_eq_of_isMinimal`), and an explicit accounting of what is and is not established |

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

## What is not claimed

- **The sufficient direction of strict classification.** `excessEventDim
  I = excessEventDim J ∧ excessComplementDim I = excessComplementDim J →
  StrictIso I J`, and hence the full equivalence
  `strictIso_iff_residualDims_eq`, are NOT proved. Their construction
  requires gluing THREE orthogonal isometries (the minimal part, plus two
  residual sectors of equal dimension but with no natural common domain)
  into a single ambient isometry — unlike the minimal case, which has
  `DilSpace n 2` as a ready-made common domain. No statement in this
  module uses the sufficient direction, replaces it with a single
  implication, or otherwise substitutes for it.
- **`ResidualExtension`/`minimalCore`.** The direct-sum construction
  extending a minimal core by residual sectors, and the theorem that
  every implementation decomposes this way, are not built: their
  intended use depends on the point above.
- **`ResidualExtensionNeutral`/`MinimalImplValuation`.** The strictly
  stronger third neutrality notion, the "residually neutral valuations ≃
  minimal valuations" equivalence, and
  `implementationIndependent_of_residualNeutral` are not formalized, for
  the same reason.
- **Nonvacuity of `IsMinimal`.** No concrete implementation is exhibited
  with `IsMinimal` proved; `canonicalBinaryImpl E hE` is minimal only
  when both `E` and `1-E` are injective, and this has not been formally
  verified for any concrete witness.
- Nothing here is stated or proved in infinite dimension. Nothing here
  re-proves `naimark`/`naimark_dilation`; every canonical implementation
  is built directly from them.
