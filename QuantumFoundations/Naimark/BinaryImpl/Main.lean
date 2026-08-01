import QuantumFoundations.Naimark.BinaryImpl.Nontriviality
import QuantumFoundations.Naimark.BinaryImpl.MinimalUniqueness

/-!
**FR.** # Module C (Porte Ω) — synthèse : classification stricte des implémentations de Naimark

Ce module formalise la structure EXACTE des implémentations binaires
concrètes d'un effet fixé `E : H n →ₗ[ℂ] H n`, au-dessus du théorème de
Naimark déjà établi (`Naimark/Main.lean`), sans jamais le redémontrer.

**Ce qui est ÉTABLI (tous les fichiers listés compilent, sans preuve
incomplète, sans axiome, sans décision native forcée) :**

1. `BinaryImpl n E ι`/`StrictIso` (`Defs.lean`) : une implémentation est un
   encodage isométrique plus une cellule de mesure dont le tiré-en-arrière
   redonne `E` ; `StrictIso` est STRICTEMENT plus fort que la seule
   égalité des effets induits.
2. `canonicalBinaryImpl`/`canonicalSelectedOutcomeImpl` (`Canonical.lean`) :
   les implémentations canoniques via `naimark_dilation`, jamais
   reprouvées.
3. `minimalSubspace`/`IsMinimal` (`Minimal.lean`) et les identités de Gram
   `eventGeneratedEquiv`/`complementGeneratedEquiv` (`GramRange.lean`) :
   les sous-espaces engendrés par N'IMPORTE QUELLE implémentation de `E`
   sont canoniquement isométriques entre eux.
4. **`minimal_strictIso`** (`MinimalUniqueness.lean`) : deux implémentations
   MINIMALES d'un même effet sont TOUJOURS strictement isomorphes —
   théorème central du module.
5. `excessEventDim`/`excessComplementDim` (`Residual.lean`) et la
   direction NÉCESSAIRE `StrictIso.excessEventDim_eq`/
   `StrictIso.excessComplementDim_eq` (`StrictClassification.lean`) : un
   isomorphisme strict force l'égalité des deux multiplicités résiduelles.
6. `replicatedAncillaImpl`/`rankRatio`/`rankRatio_replicatedAncilla`
   (`ReplicatedAncilla.lean`) : ajouter une ancilla répliquée ne change
   JAMAIS le ratio de rang.
7. Le contre-exemple canonique binaire/ternaire (`TernaryFusion.lean`,
   ratios `1/2` vs `1/3`) : sa non-isomorphie stricte SURVIT à toute
   réplication d'ancilla arbitraire des deux côtés.
8. `ImplValuation`/`StrictIsoInvariant`/`ReplicatedAncillaNeutral`
   (`Valuation.lean`) : `rankRatio` satisfait les deux ; `ambientDim`
   sépare les deux notions (satisfait la première, pas la seconde).
9. `Nonvacuity.lean`/`Nontriviality.lean` : les structures ci-dessus sont
   satisfiables ET non-triviales (témoins concrets).

**Ce qui N'EST PAS établi, et pourquoi (protocole de blocage de la
mission, §29) :**

- La direction SUFFISANTE de `strictIso_iff_residualDims_eq` (égalité des
  dimensions résiduelles ⟹ isomorphisme strict), et donc l'équivalence
  complète elle-même, ne sont PAS formalisées
  (`StrictClassification.lean`). Leur construction demande de recoller
  TROIS isométries orthogonales (partie minimale, plus deux secteurs
  résiduels de dimension égale mais sans domaine commun naturel) en une
  seule isométrie ambiante — l'obstacle "construction de l'unitaire
  global à partir des trois secteurs" anticipé par la mission. Aucun
  énoncé ne l'utilise ni ne prétend la substituer par une implication
  unique.
- `ResidualExtension.lean`/`minimalCore` (extension par somme directe
  d'un cœur minimal et de secteurs résiduels, et la décomposition de
  TOUTE implémentation sous cette forme) NE SONT PAS construits : leur
  usage prévu dépend directement du point précédent.
- `ResidualExtensionNeutral`/`MinimalImplValuation`/l'équivalence
  "valuations résiduellement neutres ≃ valuations minimales"/
  `implementationIndependent_of_residualNeutral` (`Valuation.lean`) NE
  SONT PAS formalisées, pour la même raison.
- La non-vacuité de `IsMinimal` (un témoin CONCRET d'implémentation
  minimale) n'est pas établie (`Nonvacuity.lean`) : elle demanderait une
  identité entre le noyau de `eventLeg`/`complementLeg` et celui de
  `E`/`1-E`, non encore formalisée.

Un blocage sur une phase tardive n'autorise pas à documenter le théorème
correspondant comme terminé : ces lacunes sont donc explicitement
signalées ici, dans le fichier de synthèse, plutôt que masquées.

**EN.** # Module C (Omega Gate) — synthesis: strict classification of Naimark implementations

This module formalizes the EXACT structure of concrete binary
implementations of a fixed effect `E : H n →ₗ[ℂ] H n`, on top of the
already-established Naimark theorem (`Naimark/Main.lean`), without ever
re-proving it.

**What IS established (every file listed compiles, with no incomplete
proof, no axiom, no forced native decision):**

1. `BinaryImpl n E ι`/`StrictIso` (`Defs.lean`): an implementation is an
   isometric encoding plus a measurement cell whose pullback recovers
   `E`; `StrictIso` is STRICTLY stronger than mere equality of the
   induced effects.
2. `canonicalBinaryImpl`/`canonicalSelectedOutcomeImpl` (`Canonical.lean`):
   the canonical implementations via `naimark_dilation`, never re-proved.
3. `minimalSubspace`/`IsMinimal` (`Minimal.lean`) and the Gram identities
   `eventGeneratedEquiv`/`complementGeneratedEquiv` (`GramRange.lean`):
   the subspaces generated by ANY implementation of `E` are canonically
   isometric to one another.
4. **`minimal_strictIso`** (`MinimalUniqueness.lean`): two MINIMAL
   implementations of the same effect are ALWAYS strictly isomorphic —
   the module's central theorem.
5. `excessEventDim`/`excessComplementDim` (`Residual.lean`) and the
   NECESSARY direction `StrictIso.excessEventDim_eq`/
   `StrictIso.excessComplementDim_eq` (`StrictClassification.lean`): a
   strict isomorphism forces equality of the two residual multiplicities.
6. `replicatedAncillaImpl`/`rankRatio`/`rankRatio_replicatedAncilla`
   (`ReplicatedAncilla.lean`): adding a replicated ancilla NEVER changes
   the rank ratio.
7. The canonical binary/ternary counterexample (`TernaryFusion.lean`,
   ratios `1/2` vs `1/3`): its strict non-isomorphism SURVIVES arbitrary
   ancilla replication on both sides.
8. `ImplValuation`/`StrictIsoInvariant`/`ReplicatedAncillaNeutral`
   (`Valuation.lean`): `rankRatio` satisfies both; `ambientDim` separates
   the two notions (satisfies the first, not the second).
9. `Nonvacuity.lean`/`Nontriviality.lean`: the structures above are
   satisfiable AND nontrivial (concrete witnesses).

**What is NOT established, and why (the mission's blocking protocol,
§29):**

- The SUFFICIENT direction of `strictIso_iff_residualDims_eq` (equal
  residual dimensions ⟹ strict isomorphism), and hence the full
  equivalence itself, are NOT formalized (`StrictClassification.lean`).
  Their construction requires gluing THREE orthogonal isometries (the
  minimal part, plus two residual sectors of equal dimension but with no
  natural common domain) into a single ambient isometry — the "gluing
  the global unitary from the three sectors" obstacle anticipated by the
  mission. No statement uses it or substitutes it with a single
  implication.
- `ResidualExtension.lean`/`minimalCore` (direct-sum extension of a
  minimal core by residual sectors, and the decomposition of ANY
  implementation into this form) are NOT built: their intended use
  depends directly on the point above.
- `ResidualExtensionNeutral`/`MinimalImplValuation`/the "residually
  neutral valuations ≃ minimal valuations" equivalence/
  `implementationIndependent_of_residualNeutral` (`Valuation.lean`) are
  NOT formalized, for the same reason.
- The nonvacuity of `IsMinimal` (a CONCRETE minimal-implementation
  witness) is not established (`Nonvacuity.lean`): it would require an
  identity between the kernel of `eventLeg`/`complementLeg` and that of
  `E`/`1-E`, not yet formalized.

A block on a late phase does not license documenting the corresponding
theorem as finished: these gaps are therefore explicitly flagged here, in
the synthesis file, rather than hidden.
-/

namespace QuantumFoundations.Naimark.BinaryImpl

open QuantumFoundations Gleason
open scoped InnerProductSpace

noncomputable section

variable {n : ℕ} {E : H n →ₗ[ℂ] H n}

/-- Capstone: combining `minimal_strictIso` (`MinimalUniqueness.lean`)
with `StrictIso.rankRatio_eq` (`ReplicatedAncilla.lean`) -- `rankRatio` is
already a COMPLETE invariant on minimal implementations: any two minimal
implementations of the same effect agree on it, with no need for the
blocked sufficiency direction of `strictIso_iff_residualDims_eq`. -/
theorem rankRatio_eq_of_isMinimal {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {I : BinaryImpl n E ι} {J : BinaryImpl n E κ} (hI : IsMinimal I)
    (hJ : IsMinimal J) : rankRatio I = rankRatio J :=
  StrictIso.rankRatio_eq (minimal_strictIso hI hJ)

end

end QuantumFoundations.Naimark.BinaryImpl
