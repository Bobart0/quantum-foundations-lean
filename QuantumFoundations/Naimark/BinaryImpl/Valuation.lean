import QuantumFoundations.Naimark.BinaryImpl.TernaryFusion

/-!
**FR.** # Valuations d'implémentation : deux notions de neutralité, séparées

Une "valuation" `v : ImplValuation n E` assigne un rationnel à toute
implémentation de `E`, pour tout espace ambiant `ι`. Ce fichier formalise
deux notions de neutralité qu'une telle valuation peut satisfaire :

- `StrictIsoInvariant v` : `v` ne distingue pas deux implémentations
  strictement isomorphes.
- `ReplicatedAncillaNeutral v` : `v` est inchangée par adjonction d'une
  ancilla répliquée (`ReplicatedAncilla.lean`).

`rankRatio` (`ReplicatedAncilla.lean`) satisfait LES DEUX
(`rankRatioValuation_strictIsoInvariant`,
`rankRatioValuation_replicatedAncillaNeutral`) : c'est l'exemple central,
et la raison pour laquelle il sert d'invariant dans
`TernaryFusion.lean`.

**Modèle séparateur.** `ambientDimValuation := fun I => (I.ambientDim : ℚ)`
est `StrictIsoInvariant` (`StrictIso.ambientDim_eq`) mais PAS
`ReplicatedAncillaNeutral` (`ambientDimValuation_not_replicatedAncillaNeutral`,
témoin explicite : `canonicalBinaryImpl` sur `E := 1 : H 1 →ₗ H 1`,
répliqué `2` fois, double `ambientDim` de `2` à `4`). Ce modèle établit
que les deux notions de neutralité sont RÉELLEMENT distinctes : être
invariant par isomorphisme strict n'entraîne PAS d'être neutre à
l'ancilla, contrairement à ce qu'on pourrait espérer d'un invariant
"purement structurel".

**Portée explicitement limitée.** La troisième notion envisagée par la
mission, `ResidualExtensionNeutral` (neutralité par extension résiduelle,
strictement plus forte que `ReplicatedAncillaNeutral`), ainsi que
`MinimalImplValuation`, l'équivalence "valuations résiduellement
neutres ≃ valuations minimales", et
`implementationIndependent_of_residualNeutral`, NE SONT PAS formalisées
ici : leur définition précise nécessite la construction `residualExtension`
(extension par somme directe d'une implémentation minimale et de secteurs
résiduels), elle-même omise (`ReplicatedAncilla.lean`) parce que son usage
prévu -- décomposer TOUTE implémentation en cœur minimal plus extension
résiduelle -- dépend de la direction de suffisance de
`strictIso_iff_residualDims_eq`, déjà documentée comme bloquée dans
`StrictClassification.lean`. Aucun énoncé les mentionnant n'apparaît ici.

**EN.** # Implementation valuations: two notions of neutrality, separated

A "valuation" `v : ImplValuation n E` assigns a rational number to every
implementation of `E`, for every ambient space `ι`. This file formalizes
two neutrality notions such a valuation may satisfy:

- `StrictIsoInvariant v`: `v` does not distinguish two strictly isomorphic
  implementations.
- `ReplicatedAncillaNeutral v`: `v` is unchanged by adjoining a replicated
  ancilla (`ReplicatedAncilla.lean`).

`rankRatio` (`ReplicatedAncilla.lean`) satisfies BOTH
(`rankRatioValuation_strictIsoInvariant`,
`rankRatioValuation_replicatedAncillaNeutral`): this is the central
example, and the reason it serves as the invariant in
`TernaryFusion.lean`.

**Separating model.** `ambientDimValuation := fun I => (I.ambientDim : ℚ)`
is `StrictIsoInvariant` (`StrictIso.ambientDim_eq`) but NOT
`ReplicatedAncillaNeutral` (`ambientDimValuation_not_replicatedAncillaNeutral`,
explicit witness: `canonicalBinaryImpl` on `E := 1 : H 1 →ₗ H 1`,
replicated `2`-fold, doubles `ambientDim` from `2` to `4`). This model
establishes that the two neutrality notions are GENUINELY distinct: being
invariant under strict isomorphism does NOT entail ancilla neutrality,
contrary to what one might hope from a "purely structural" invariant.

**Explicitly limited scope.** The third notion the mission envisions,
`ResidualExtensionNeutral` (neutrality under residual extension, strictly
stronger than `ReplicatedAncillaNeutral`), together with
`MinimalImplValuation`, the "residually neutral valuations ≃ minimal
valuations" equivalence, and
`implementationIndependent_of_residualNeutral`, are NOT formalized here:
their precise definition requires the `residualExtension` construction
(direct-sum extension of a minimal implementation by residual sectors),
itself omitted (`ReplicatedAncilla.lean`) because its intended use --
decomposing ANY implementation into a minimal core plus a residual
extension -- depends on the sufficiency direction of
`strictIso_iff_residualDims_eq`, already documented as blocked in
`StrictClassification.lean`. No statement mentioning them appears here.
-/

namespace QuantumFoundations.Naimark.BinaryImpl

open QuantumFoundations Gleason
open scoped InnerProductSpace

noncomputable section

/-- The identity is always an effect: a minimal, dimension-free witness
used to instantiate concrete implementations below. -/
theorem one_isEffect (n : ℕ) : Gleason.IsEffect (1 : H n →ₗ[ℂ] H n) := by
  constructor
  · constructor
    · intro x y; simp
    · intro x
      show 0 ≤ (⟪x, x⟫_ℂ).re
      exact inner_self_nonneg (𝕜 := ℂ) (x := x)
  · rw [sub_self]
    exact zero_isPositiveOp

/-- A valuation of implementations of `E`: assigns a rational number to
every implementation, in every ambient space. -/
def ImplValuation (n : ℕ) (E : H n →ₗ[ℂ] H n) : Type 1 :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι], BinaryImpl n E ι → ℚ

variable {n : ℕ} {E : H n →ₗ[ℂ] H n}

/-- `v` does not distinguish strictly isomorphic implementations. -/
def StrictIsoInvariant (v : ImplValuation n E) : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {I : BinaryImpl n E ι} {J : BinaryImpl n E κ}, BinaryImpl.StrictIso I J → v I = v J

/-- `v` is unchanged by adjoining a replicated ancilla. -/
def ReplicatedAncillaNeutral (v : ImplValuation n E) : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (I : BinaryImpl n E ι) {a : ℕ} (a₀ : Fin a),
    v (replicatedAncillaImpl I a₀) = v I

/-- `rankRatio`, packaged as an `ImplValuation`. -/
def rankRatioValuation : ImplValuation n E := fun {_} _ _ I => rankRatio I

theorem rankRatioValuation_strictIsoInvariant :
    StrictIsoInvariant (rankRatioValuation (n := n) (E := E)) := by
  intro _ι _κ _ _ _ _ I J h
  exact StrictIso.rankRatio_eq h

theorem rankRatioValuation_replicatedAncillaNeutral :
    ReplicatedAncillaNeutral (rankRatioValuation (n := n) (E := E)) := by
  intro _ι _ _ I a a₀
  exact rankRatio_replicatedAncilla I a₀

/-- `ambientDim`, packaged as an `ImplValuation`: the separating model
showing `StrictIsoInvariant` does not entail `ReplicatedAncillaNeutral`. -/
def ambientDimValuation : ImplValuation n E := fun {_} _ _ I => (I.ambientDim : ℚ)

theorem ambientDimValuation_strictIsoInvariant :
    StrictIsoInvariant (ambientDimValuation (n := n) (E := E)) := by
  intro _ι _κ _ _ _ _ I J h
  show (I.ambientDim : ℚ) = (J.ambientDim : ℚ)
  rw [h.ambientDim_eq]

/-- `ambientDimValuation` is `StrictIsoInvariant` but NOT
`ReplicatedAncillaNeutral`: replicating the canonical binary
implementation of the identity effect on `H 1` twofold doubles its
`ambientDim` from `2` to `4`. This separates the two neutrality notions. -/
theorem ambientDimValuation_not_replicatedAncillaNeutral :
    ¬ ReplicatedAncillaNeutral (ambientDimValuation (n := 1) (E := (1 : H 1 →ₗ[ℂ] H 1))) := by
  intro hneutral
  have h := hneutral (canonicalBinaryImpl (1 : H 1 →ₗ[ℂ] H 1) (one_isEffect 1)) (a := 2) 0
  have h' : ((replicatedAncillaImpl (canonicalBinaryImpl (1 : H 1 →ₗ[ℂ] H 1) (one_isEffect 1))
      (0 : Fin 2)).ambientDim : ℚ)
      = ((canonicalBinaryImpl (1 : H 1 →ₗ[ℂ] H 1) (one_isEffect 1)).ambientDim : ℚ) := h
  rw [replicatedAncilla_ambientDim, canonicalBinaryImpl_ambientDim] at h'
  norm_num at h'

end

end QuantumFoundations.Naimark.BinaryImpl
