import QuantumFoundations.Naimark.BinaryImpl.Residual

/-!
**FR.** # Nécessité : un isomorphisme strict force l'égalité des dimensions
résiduelles

Ce fichier établit la direction NÉCESSAIRE de la classification stricte des
implémentations d'un même effet : si `I` et `J` sont strictement
isomorphes, leurs deux multiplicités résiduelles `excessEventDim`/
`excessComplementDim` (`Residual.lean`) coïncident.

**Portée explicitement limitée.** La direction RÉCIPROQUE (`excessEventDim
I = excessEventDim J ∧ excessComplementDim I = excessComplementDim J →
StrictIso I J`, et donc l'équivalence complète `strictIso_iff_residualDims_eq`
envisagée par la mission) N'EST PAS établie ici. Sa construction demande de
recoller TROIS isométries orthogonales (la partie minimale, via
`combinedLeg`/`GramRange.lean`, plus deux isométries de secteurs résiduels
de dimensions égales mais sans domaine commun naturel) en une seule
isométrie ambiante -- l'obstacle explicitement anticipé par la mission sous
le nom « construction de l'unitaire global à partir des trois secteurs ».
Contrairement à la direction nécessaire ci-dessous, elle n'a pas pu être
menée à bien dans le temps imparti sans risquer une preuve incomplète ou un
énoncé affaibli, ce qu'interdisent les règles absolues du module. Elle est
donc délibérément omise plutôt que bâclée : aucun énoncé la mentionnant
n'apparaît dans ce fichier.

**EN.** # Necessity: a strict isomorphism forces equal residual dimensions

This file establishes the NECESSARY direction of the strict classification
of implementations of a given effect: if `I` and `J` are strictly
isomorphic, their two residual multiplicities `excessEventDim`/
`excessComplementDim` (`Residual.lean`) coincide.

**Explicitly limited scope.** The CONVERSE direction (`excessEventDim I =
excessEventDim J ∧ excessComplementDim I = excessComplementDim J →
StrictIso I J`, and hence the full equivalence
`strictIso_iff_residualDims_eq` envisioned by the mission) is NOT
established here. Its construction requires gluing THREE orthogonal
isometries (the minimal part, via `combinedLeg`/`GramRange.lean`, plus two
residual-sector isometries of equal dimension but with no natural common
domain) into a single ambient isometry -- the obstacle explicitly
anticipated by the mission under the name "construction of the global
unitary from the three sectors." Unlike the necessary direction below, it
could not be completed within the available effort without risking an
incomplete proof or a weakened statement, both forbidden by the module's
absolute rules. It is therefore deliberately omitted rather than rushed:
no statement mentioning it appears in this file.
-/

namespace QuantumFoundations.Naimark.BinaryImpl

open QuantumFoundations Gleason
open scoped InnerProductSpace

noncomputable section

variable {n : ℕ} {E : H n →ₗ[ℂ] H n} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A strict isomorphism forces equal event-side residual dimensions. -/
theorem StrictIso.excessEventDim_eq {I : BinaryImpl n E ι} {J : BinaryImpl n E κ}
    (h : BinaryImpl.StrictIso I J) : excessEventDim I = excessEventDim J := by
  have h1 : I.projectorRank = J.projectorRank := h.projectorRange_finrank_eq
  have h2 := projectorRank_decomposition I
  have h3 := projectorRank_decomposition J
  have h4 := eventGenerated_finrank_eq_of_sameEffect I J
  omega

/-- A strict isomorphism forces equal complement-side residual dimensions. -/
theorem StrictIso.excessComplementDim_eq {I : BinaryImpl n E ι} {J : BinaryImpl n E κ}
    (h : BinaryImpl.StrictIso I J) : excessComplementDim I = excessComplementDim J := by
  have h1 : I.projectorNullity = J.projectorNullity := h.projectorKernel_finrank_eq
  have h2 := projectorNullity_decomposition I
  have h3 := projectorNullity_decomposition J
  have h4 := complementGenerated_finrank_eq_of_sameEffect I J
  omega

end

end QuantumFoundations.Naimark.BinaryImpl
