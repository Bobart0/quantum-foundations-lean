import QuantumFoundations.Naimark.BinaryImpl.Defs

/-!
**FR.** # Implémentations binaires canoniques (dilatation de Naimark)

Deux constructions canoniques, toutes deux obtenues à partir de
`naimark`/`naimark_dilation` (`Naimark/Main.lean`), SANS aucune
redémonstration :

- `canonicalBinaryImpl E hE` : implémentation binaire de `E` via la POVM à
  2 issues `{E, 1-E}` (`povmOfEffect`).
- `canonicalSelectedOutcomeImpl P i` : implémentation binaire de l'issue
  `P.E i` d'une POVM générale à `m` issues, obtenue en regardant la
  dilatation projective complète de `P` mais en ne retenant que la
  cellule `i`.

Ces deux implémentations réalisent le MÊME effet quand `P := povmOfEffect
E hE` et `i := 0`, mais elles ne sont PAS la même construction : la
première est un cas particulier m=2 de la seconde. Le fil directeur du
Module C (§11, fusion ternaire) exploite précisément cette différence.

**EN.** # Canonical binary implementations (Naimark dilation)

Two canonical constructions, both obtained from `naimark`/
`naimark_dilation` (`Naimark/Main.lean`), with NO re-proof:

- `canonicalBinaryImpl E hE`: binary implementation of `E` via the
  2-outcome POVM `{E, 1-E}` (`povmOfEffect`).
- `canonicalSelectedOutcomeImpl P i`: binary implementation of outcome
  `P.E i` of a general `m`-outcome POVM, obtained by looking at the full
  projective dilation of `P` but retaining only cell `i`.

These two implementations realize the SAME effect when `P := povmOfEffect
E hE` and `i := 0`, but they are NOT the same construction: the first is
the special case m=2 of the second. Module C's throughline (§11, the
ternary fusion) exploits precisely this difference.
-/

namespace QuantumFoundations.Naimark.BinaryImpl

open QuantumFoundations Gleason
open scoped InnerProductSpace

noncomputable section

variable {n m : ℕ}

/-- The 2-outcome POVM `{E, 1-E}` associated to an effect `E`. -/
def povmOfEffect (E : H n →ₗ[ℂ] H n) (hE : Gleason.IsEffect E) : POVM n 2 where
  E := ![E, 1 - E]
  pos := by
    intro i
    fin_cases i
    · simpa using hE.1
    · simpa using hE.2
  sum_eq_one := by
    rw [Fin.sum_univ_two]
    simp

theorem povmOfEffect_zero (E : H n →ₗ[ℂ] H n) (hE : Gleason.IsEffect E) :
    (povmOfEffect E hE).E 0 = E := rfl

/-- The range of the block projection `dilProj n m i` equals the range of
the block injection `singleL n m i`: `dilProj i` collapses to
`singleL i` on the image side, since `coordL i` is surjective. -/
private theorem range_dilProj_eq_range_singleL (i : Fin m) :
    LinearMap.range (dilProj n m i) = LinearMap.range (singleL n m i) := by
  show LinearMap.range (singleL n m i ∘ₗ coordL n m i) = _
  rw [LinearMap.range_comp]
  have hsurj : Function.Surjective (coordL n m i) := by
    intro y
    refine ⟨singleL n m i y, ?_⟩
    have h := LinearMap.congr_fun (coordL_singleL i i) y
    simpa using h
  rw [LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]

private theorem singleL_injective (i : Fin m) : Function.Injective (singleL n m i) := by
  have hli : Function.LeftInverse (coordL n m i) (singleL n m i) := by
    intro x
    have h := LinearMap.congr_fun (coordL_singleL i i) x
    simpa using h
  exact hli.injective

private theorem finrank_range_dilProj (i : Fin m) :
    Module.finrank ℂ (LinearMap.range (dilProj n m i)) = n := by
  rw [range_dilProj_eq_range_singleL i, LinearMap.finrank_range_of_inj (singleL_injective i)]
  simp

/-- The canonical binary implementation of an effect `E`, via the Naimark
dilation of the associated 2-outcome POVM `{E, 1-E}`. -/
noncomputable def canonicalBinaryImpl (E : H n →ₗ[ℂ] H n) (hE : Gleason.IsEffect E) :
    BinaryImpl n E (Fin 2 × Fin n) where
  encoding := dilV (povmOfEffect E hE)
  cell := dilProj n 2 0
  encoding_isometry := dilV_isometry (povmOfEffect E hE)
  cell_isProjection := ⟨dilProj_idempotent 0, dilProj_isSymmetric 0⟩
  realizes := by
    have h := naimark_dilation (povmOfEffect E hE) 0
    rwa [povmOfEffect_zero] at h

theorem canonicalBinaryImpl_ambientDim (E : H n →ₗ[ℂ] H n) (hE : Gleason.IsEffect E) :
    (canonicalBinaryImpl E hE).ambientDim = 2 * n := by
  show Fintype.card (Fin 2 × Fin n) = 2 * n
  simp

theorem canonicalBinaryImpl_projectorRank (E : H n →ₗ[ℂ] H n) (hE : Gleason.IsEffect E) :
    (canonicalBinaryImpl E hE).projectorRank = n :=
  finrank_range_dilProj 0

theorem canonicalBinaryImpl_projectorNullity (E : H n →ₗ[ℂ] H n) (hE : Gleason.IsEffect E) :
    (canonicalBinaryImpl E hE).projectorNullity = n := by
  have h := (canonicalBinaryImpl E hE).projectorRank_add_nullity
  rw [canonicalBinaryImpl_projectorRank, canonicalBinaryImpl_ambientDim] at h
  omega

/-- The canonical binary implementation of an arbitrary outcome `i` of a
general finite POVM `P`, via `dilV P`/`dilProj n m i`. -/
noncomputable def canonicalSelectedOutcomeImpl (P : POVM n m) (i : Fin m) :
    BinaryImpl n (P.E i) (Fin m × Fin n) where
  encoding := dilV P
  cell := dilProj n m i
  encoding_isometry := dilV_isometry P
  cell_isProjection := ⟨dilProj_idempotent i, dilProj_isSymmetric i⟩
  realizes := naimark_dilation P i

theorem canonicalSelectedOutcomeImpl_ambientDim (P : POVM n m) (i : Fin m) :
    (canonicalSelectedOutcomeImpl P i).ambientDim = m * n := by
  show Fintype.card (Fin m × Fin n) = m * n
  simp

theorem canonicalSelectedOutcomeImpl_projectorRank (P : POVM n m) (i : Fin m) :
    (canonicalSelectedOutcomeImpl P i).projectorRank = n :=
  finrank_range_dilProj i

theorem canonicalSelectedOutcomeImpl_projectorNullity (P : POVM n m) (i : Fin m) :
    (canonicalSelectedOutcomeImpl P i).projectorNullity = (m - 1) * n := by
  have hm : 0 < m := i.pos
  have h := (canonicalSelectedOutcomeImpl P i).projectorRank_add_nullity
  rw [canonicalSelectedOutcomeImpl_projectorRank, canonicalSelectedOutcomeImpl_ambientDim] at h
  have hmn : m * n = n + (m - 1) * n := by
    conv_lhs => rw [← Nat.succ_pred_eq_of_pos hm]
    rw [Nat.succ_mul, Nat.pred_eq_sub_one]
    ring
  omega

end

end QuantumFoundations.Naimark.BinaryImpl
