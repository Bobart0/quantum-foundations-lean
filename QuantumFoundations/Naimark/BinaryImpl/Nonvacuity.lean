import QuantumFoundations.Naimark.BinaryImpl.Valuation

/-!
**FR.** # Non-vacuité : les structures du Module C sont satisfiables

Témoins concrets que les définitions centrales du module ne sont pas
vides : `BinaryImpl` a un habitant pour tout effet, `StrictIso` est une
relation satisfiable, et il existe une `ImplValuation` qui est à la fois
`StrictIsoInvariant` ET `ReplicatedAncillaNeutral` (`rankRatioValuation`,
`Valuation.lean`).

**Portée explicitement limitée.** La non-vacuité de `IsMinimal`
(`Minimal.lean`) -- exhiber une implémentation CONCRÈTE dont le
sous-espace engendré est tout l'espace ambiant, ce qui rendrait
`minimal_strictIso` non-vacuously applicable à un témoin explicite --
N'EST PAS établie ici. `canonicalBinaryImpl E hE` n'est minimale que
lorsque `E` ET `1-E` sont tous deux INJECTIFS (sans quoi il reste une
dimension résiduelle inutilisée, exactement le phénomène que
`Residual.lean` mesure) ; le construire demande une identité entre le
noyau de `eventLeg`/`complementLeg` et celui de `E`/`1-E` qui n'est pas
encore formalisée. Aucun énoncé ne prétend ici que `IsMinimal` est
habité.

**EN.** # Nonvacuity: Module C's structures are satisfiable

Concrete witnesses that the module's central definitions are not empty:
`BinaryImpl` has an inhabitant for every effect, `StrictIso` is a
satisfiable relation, and there exists an `ImplValuation` that is both
`StrictIsoInvariant` AND `ReplicatedAncillaNeutral` (`rankRatioValuation`,
`Valuation.lean`).

**Explicitly limited scope.** The nonvacuity of `IsMinimal`
(`Minimal.lean`) -- exhibiting a CONCRETE implementation whose generated
subspace is the whole ambient space, which would make `minimal_strictIso`
non-vacuously applicable to an explicit witness -- is NOT established
here. `canonicalBinaryImpl E hE` is minimal only when `E` AND `1-E` are
both INJECTIVE (otherwise a residual dimension goes unused, exactly the
phenomenon `Residual.lean` measures); building it requires an identity
between the kernel of `eventLeg`/`complementLeg` and that of `E`/`1-E`
which is not yet formalized. No statement here claims `IsMinimal` is
inhabited.
-/

namespace QuantumFoundations.Naimark.BinaryImpl

open QuantumFoundations Gleason
open scoped InnerProductSpace

noncomputable section

variable {n : ℕ} {E : H n →ₗ[ℂ] H n}

/-- `BinaryImpl` is inhabited for every effect: the canonical binary
implementation from the Naimark dilation. -/
theorem binaryImpl_nonempty (hE : Gleason.IsEffect E) :
    Nonempty (BinaryImpl n E (Fin 2 × Fin n)) :=
  ⟨canonicalBinaryImpl E hE⟩

/-- `StrictIso` is a satisfiable relation: every implementation is
strictly isomorphic to itself. -/
theorem strictIso_nonvacuous {ι : Type} [Fintype ι] [DecidableEq ι] (I : BinaryImpl n E ι) :
    ∃ J : BinaryImpl n E ι, BinaryImpl.StrictIso I J :=
  ⟨I, BinaryImpl.StrictIso.refl I⟩

/-- There exists an `ImplValuation` that is simultaneously
`StrictIsoInvariant` and `ReplicatedAncillaNeutral`: `rankRatio`. -/
theorem implValuation_nonvacuous :
    ∃ v : ImplValuation n E, StrictIsoInvariant v ∧ ReplicatedAncillaNeutral v :=
  ⟨rankRatioValuation, rankRatioValuation_strictIsoInvariant,
    rankRatioValuation_replicatedAncillaNeutral⟩

end

end QuantumFoundations.Naimark.BinaryImpl
