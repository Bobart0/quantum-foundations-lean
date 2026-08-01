import QuantumFoundations.Naimark.BinaryImpl.Canonical
import QuantumFoundations.Naimark.BinaryImpl.ReplicatedAncilla

/-!
**FR.** # Le contre-exemple canonique binaire/ternaire

Deux implémentations CANONIQUES du même effet `E` (obtenues, sans aucune
redémonstration, à partir de `naimark`/`naimark_dilation`) qui réalisent
`E` avec des multiplicités de dilatation DIFFÉRENTES et qui ne sont donc
JAMAIS strictement isomorphes -- même après adjonction d'une ancilla
répliquée arbitrairement grande de part et d'autre.

- `canonicalBinaryImpl E hE : BinaryImpl n E (Fin 2 × Fin n)` (`Canonical.lean`)
  encode `E` via la POVM à 2 issues `{E, 1-E}` ; ratio de rang `1/2`
  (`canonicalBinaryImpl_rankRatio`).
- `canonicalTernaryImpl E hE : BinaryImpl n E (Fin 3 × Fin n)` encode `E`
  via la POVM à 3 issues `{E, 1-E, 0}` (`ternaryPovmOfEffect`), en ne
  retenant que l'issue `0` (`canonicalSelectedOutcomeImpl`, `Canonical.lean`) ;
  ratio de rang `1/3` (`canonicalTernaryImpl_rankRatio`).

Le troisième effet `0` de `ternaryPovmOfEffect` est un artifice délibéré :
il complète la somme à `1` sans changer l'issue `0`, ce qui donne à
`canonicalTernaryImpl` un espace ambiant `3n` au lieu de `2n` -- une
« issue vide » qui gonfle la dilatation sans rien changer à l'effet
réalisé. C'est exactement le phénomène que `rankRatio` est censé détecter.

Puisque `1/2 ≠ 1/3` et que `StrictIso` force l'égalité de `rankRatio`
(`StrictIso.rankRatio_eq`, `ReplicatedAncilla.lean`) -- un invariant
LUI-MÊME invariant sous réplication d'ancilla
(`rankRatio_replicatedAncilla`) -- ces deux implémentations ne sont
JAMAIS strictement isomorphes, y compris après réplication d'ancilla
arbitraire des deux côtés
(`canonicalBinaryImpl_canonicalTernaryImpl_not_strictIso_replicatedAncilla`).
C'est le témoin explicite demandé par la mission : l'addition d'ancilla,
seule, ne suffit JAMAIS à identifier deux implémentations dont les
dimensions résiduelles diffèrent nativement.

**EN.** # The canonical binary/ternary counterexample

Two CANONICAL implementations of the same effect `E` (obtained, with no
re-proof, from `naimark`/`naimark_dilation`) that realize `E` with
DIFFERENT dilation multiplicities and are therefore NEVER strictly
isomorphic -- even after adjoining an arbitrarily large replicated
ancilla on either side.

- `canonicalBinaryImpl E hE : BinaryImpl n E (Fin 2 × Fin n)` (`Canonical.lean`)
  encodes `E` via the 2-outcome POVM `{E, 1-E}`; rank ratio `1/2`
  (`canonicalBinaryImpl_rankRatio`).
- `canonicalTernaryImpl E hE : BinaryImpl n E (Fin 3 × Fin n)` encodes `E`
  via the 3-outcome POVM `{E, 1-E, 0}` (`ternaryPovmOfEffect`), retaining
  only outcome `0` (`canonicalSelectedOutcomeImpl`, `Canonical.lean`);
  rank ratio `1/3` (`canonicalTernaryImpl_rankRatio`).

The third effect `0` of `ternaryPovmOfEffect` is a deliberate device: it
completes the sum to `1` without changing outcome `0`, giving
`canonicalTernaryImpl` an ambient space of size `3n` instead of `2n` -- an
"empty outcome" that inflates the dilation without changing the realized
effect at all. This is exactly the phenomenon `rankRatio` is meant to
detect.

Since `1/2 ≠ 1/3` and `StrictIso` forces equal `rankRatio`
(`StrictIso.rankRatio_eq`, `ReplicatedAncilla.lean`) -- an invariant that
is ITSELF invariant under ancilla replication
(`rankRatio_replicatedAncilla`) -- these two implementations are NEVER
strictly isomorphic, including after arbitrary ancilla replication on
both sides
(`canonicalBinaryImpl_canonicalTernaryImpl_not_strictIso_replicatedAncilla`).
This is the explicit witness the mission asks for: adding ancilla, by
itself, is NEVER enough to identify two implementations whose residual
dimensions natively differ.
-/

namespace QuantumFoundations.Naimark.BinaryImpl

open QuantumFoundations Gleason
open scoped InnerProductSpace

noncomputable section

variable {n : ℕ}

theorem zero_isPositiveOp : Gleason.IsPositiveOp (0 : H n →ₗ[ℂ] H n) := by
  constructor
  · intro x y; simp
  · intro x; simp

/-- The 3-outcome POVM `{E, 1-E, 0}`: completes the sum to `1` with an
"empty outcome" that never fires, so that outcome `0` still realizes `E`
exactly, but through a larger ambient dilation. -/
def ternaryPovmOfEffect (E : H n →ₗ[ℂ] H n) (hE : Gleason.IsEffect E) : POVM n 3 where
  E := ![E, 1 - E, 0]
  pos := by
    intro i
    fin_cases i
    · simpa using hE.1
    · simpa using hE.2
    · simpa using zero_isPositiveOp
  sum_eq_one := by
    rw [Fin.sum_univ_three]
    simp

theorem ternaryPovmOfEffect_zero (E : H n →ₗ[ℂ] H n) (hE : Gleason.IsEffect E) :
    (ternaryPovmOfEffect E hE).E 0 = E := rfl

/-- The canonical ternary implementation of `E`: the Naimark dilation of
`ternaryPovmOfEffect`, retaining only outcome `0`. Realizes the same
effect `E` as `canonicalBinaryImpl`, in an ambient space `1.5` times
larger. -/
def canonicalTernaryImpl (E : H n →ₗ[ℂ] H n) (hE : Gleason.IsEffect E) :
    BinaryImpl n E (Fin 3 × Fin n) :=
  canonicalSelectedOutcomeImpl (ternaryPovmOfEffect E hE) 0

theorem canonicalTernaryImpl_ambientDim (E : H n →ₗ[ℂ] H n) (hE : Gleason.IsEffect E) :
    (canonicalTernaryImpl E hE).ambientDim = 3 * n :=
  canonicalSelectedOutcomeImpl_ambientDim (ternaryPovmOfEffect E hE) 0

theorem canonicalTernaryImpl_projectorRank (E : H n →ₗ[ℂ] H n) (hE : Gleason.IsEffect E) :
    (canonicalTernaryImpl E hE).projectorRank = n :=
  canonicalSelectedOutcomeImpl_projectorRank (ternaryPovmOfEffect E hE) 0

theorem canonicalBinaryImpl_rankRatio (E : H n →ₗ[ℂ] H n) (hE : Gleason.IsEffect E) (hn : 0 < n) :
    rankRatio (canonicalBinaryImpl E hE) = 1 / 2 := by
  show ((canonicalBinaryImpl E hE).projectorRank : ℚ) / ((canonicalBinaryImpl E hE).ambientDim : ℚ)
    = 1 / 2
  rw [canonicalBinaryImpl_projectorRank, canonicalBinaryImpl_ambientDim]
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp

theorem canonicalTernaryImpl_rankRatio (E : H n →ₗ[ℂ] H n) (hE : Gleason.IsEffect E) (hn : 0 < n) :
    rankRatio (canonicalTernaryImpl E hE) = 1 / 3 := by
  show ((canonicalTernaryImpl E hE).projectorRank : ℚ) / ((canonicalTernaryImpl E hE).ambientDim : ℚ)
    = 1 / 3
  rw [canonicalTernaryImpl_projectorRank, canonicalTernaryImpl_ambientDim]
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp

/-- Unequal `rankRatio` forbids a strict isomorphism outright. -/
theorem not_strictIso_of_rankRatio_ne {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {E : H n →ₗ[ℂ] H n} {I : BinaryImpl n E ι} {J : BinaryImpl n E κ}
    (hne : rankRatio I ≠ rankRatio J) : ¬ BinaryImpl.StrictIso I J := by
  intro h
  exact hne (StrictIso.rankRatio_eq h)

/-- Unequal `rankRatio` forbids a strict isomorphism EVEN after replicating
an ancilla of any size on either side. -/
theorem not_strictIso_replicatedAncilla_of_rankRatio_ne {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {E : H n →ₗ[ℂ] H n} {I : BinaryImpl n E ι} {J : BinaryImpl n E κ}
    (hne : rankRatio I ≠ rankRatio J) {a b : ℕ} (a₀ : Fin a) (b₀ : Fin b) :
    ¬ BinaryImpl.StrictIso (replicatedAncillaImpl I a₀) (replicatedAncillaImpl J b₀) := by
  intro h
  apply hne
  have h1 := StrictIso.rankRatio_eq h
  rwa [rankRatio_replicatedAncilla, rankRatio_replicatedAncilla] at h1

/-- The canonical binary and ternary implementations of the same effect
are never strictly isomorphic: their rank ratios `1/2` and `1/3` differ. -/
theorem canonicalBinaryImpl_canonicalTernaryImpl_not_strictIso (E : H n →ₗ[ℂ] H n)
    (hE : Gleason.IsEffect E) (hn : 0 < n) :
    ¬ BinaryImpl.StrictIso (canonicalBinaryImpl E hE) (canonicalTernaryImpl E hE) := by
  apply not_strictIso_of_rankRatio_ne
  rw [canonicalBinaryImpl_rankRatio E hE hn, canonicalTernaryImpl_rankRatio E hE hn]
  norm_num

/-- The canonical binary/ternary non-isomorphism survives adjunction of
an arbitrarily large replicated ancilla on either side: no amount of
ancilla addition alone can reconcile implementations whose residual
dilation multiplicities natively differ. -/
theorem canonicalBinaryImpl_canonicalTernaryImpl_not_strictIso_replicatedAncilla
    (E : H n →ₗ[ℂ] H n) (hE : Gleason.IsEffect E) (hn : 0 < n) {a b : ℕ} (a₀ : Fin a) (b₀ : Fin b) :
    ¬ BinaryImpl.StrictIso (replicatedAncillaImpl (canonicalBinaryImpl E hE) a₀)
        (replicatedAncillaImpl (canonicalTernaryImpl E hE) b₀) := by
  apply not_strictIso_replicatedAncilla_of_rankRatio_ne
  rw [canonicalBinaryImpl_rankRatio E hE hn, canonicalTernaryImpl_rankRatio E hE hn]
  norm_num

end

end QuantumFoundations.Naimark.BinaryImpl
