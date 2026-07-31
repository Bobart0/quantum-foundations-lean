import QuantumFoundations.Selectors.Covariance

/-!
**FR.** # Selectors — Module B, covariance relative à un sous-groupe

Généralise `IsCovariant` (covariance sous **tout** le groupe unitaire) à la
covariance sous un sous-groupe quelconque `G ≤ (H n ≃ₗᵢ[ℂ] H n)`
(`IsCovariantUnder`). Trois faits structurels :

- **monotonie** (`isCovariantUnder_mono`) : covariant sous un groupe plus
  gros implique covariant sous tout sous-groupe plus petit — moins de
  symétrie exigée est une condition plus faible, donc plus facile à
  satisfaire (voir `StructureNontriviality.lean` pour les témoins stricts) ;
- **cas extrêmes** : `⊤` retrouve exactement `IsCovariant`
  (`isCovariant_iff_covariantUnder_top`), `⊥` est vide de contenu — tout
  sélecteur y est covariant (`covariantUnder_bot`) ;
- **stabilisateur d'un vecteur** (`stateStabilizer`) : le sous-groupe qui
  fixe un `ψ` donné ; tout sélecteur covariant a sa valeur en `ψ`
  invariante sous ce stabilisateur (`selector_value_invariant_under_stateStabilizer`),
  fait qui prépare la spécialisation aux stabilisateurs de base/perspective
  dans `BasisStabilizer.lean`/`PerspectiveStabilizer.lean`.

**EN.** # Selectors — Module B, subgroup-relative covariance

Generalizes `IsCovariant` (covariance under the **whole** unitary group) to
covariance under an arbitrary subgroup `G ≤ (H n ≃ₗᵢ[ℂ] H n)`
(`IsCovariantUnder`). Three structural facts:

- **monotonicity** (`isCovariantUnder_mono`): covariant under a larger
  group implies covariant under any smaller subgroup — requiring less
  symmetry is a weaker condition, hence easier to satisfy (see
  `StructureNontriviality.lean` for strict witnesses);
- **extreme cases**: `⊤` recovers exactly `IsCovariant`
  (`isCovariant_iff_covariantUnder_top`), `⊥` is content-free — every
  selector is covariant under it (`covariantUnder_bot`);
- **stabilizer of a vector** (`stateStabilizer`): the subgroup fixing a
  given `ψ`; every covariant selector has its value at `ψ` invariant
  under this stabilizer
  (`selector_value_invariant_under_stateStabilizer`), a fact that sets up
  the specialization to basis/perspective stabilizers in
  `BasisStabilizer.lean`/`PerspectiveStabilizer.lean`.
-/

namespace QuantumFoundations.Selector

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ}

/--
**FR.** Covariance relative à un sous-groupe `G` du groupe unitaire :
l'équation de covariance de `IsCovariant`, mais seulement exigée pour
`U ∈ G`.

**EN.** Covariance relative to a subgroup `G` of the unitary group: the
covariance equation of `IsCovariant`, but only required for `U ∈ G`.
-/
def IsCovariantUnder (G : Subgroup (H n ≃ₗᵢ[ℂ] H n)) (σ : Selector n) : Prop :=
  ∀ U : H n ≃ₗᵢ[ℂ] H n, U ∈ G → ∀ ψ : H n, ‖ψ‖ = 1 →
    σ.ρ (U ψ) = U.toLinearMap ∘ₗ σ.ρ ψ ∘ₗ U.symm.toLinearMap

/--
**FR.** Monotonie : covariance sous un sous-groupe `K` implique covariance
sous tout sous-groupe plus petit `G ≤ K`.

**EN.** Monotonicity: covariance under a subgroup `K` implies covariance
under any smaller subgroup `G ≤ K`.
-/
theorem isCovariantUnder_mono {G K : Subgroup (H n ≃ₗᵢ[ℂ] H n)} (hGK : G ≤ K) {σ : Selector n}
    (hσ : IsCovariantUnder K σ) : IsCovariantUnder G σ := by
  intro U hU ψ hψ
  exact hσ U (hGK hU) ψ hψ

/--
**FR.** Le cas `G = ⊤` retrouve exactement `IsCovariant`.

**EN.** The case `G = ⊤` recovers exactly `IsCovariant`.
-/
theorem isCovariant_iff_covariantUnder_top (σ : Selector n) :
    IsCovariant σ ↔ IsCovariantUnder (⊤ : Subgroup (H n ≃ₗᵢ[ℂ] H n)) σ := by
  constructor
  · intro hσ U _ ψ hψ; exact hσ U ψ hψ
  · intro hσ U ψ hψ; exact hσ U (Subgroup.mem_top U) ψ hψ

/--
**FR.** Le cas `G = ⊥` (le sous-groupe trivial) est vide de contenu : tout
sélecteur y est covariant, puisque seule l'identité doit être testée.

**EN.** The case `G = ⊥` (the trivial subgroup) is content-free: every
selector is covariant under it, since only the identity needs checking.
-/
theorem covariantUnder_bot (σ : Selector n) :
    IsCovariantUnder (⊥ : Subgroup (H n ≃ₗᵢ[ℂ] H n)) σ := by
  intro U hU ψ _hψ
  have hU1 : U = 1 := hU
  subst hU1
  show σ.ρ ψ = (1 : H n ≃ₗᵢ[ℂ] H n).toLinearMap ∘ₗ σ.ρ ψ ∘ₗ (1 : H n ≃ₗᵢ[ℂ] H n).symm.toLinearMap
  rw [show (1 : H n ≃ₗᵢ[ℂ] H n).symm = 1 from rfl]
  apply LinearMap.ext
  intro x
  simp

/--
**FR.** Covariance sous une intersection binaire de sous-groupes, dès que
covariance sous l'un des deux facteurs.

**EN.** Covariance under a binary intersection of subgroups, as soon as
covariance under one of the two factors holds.
-/
theorem covariantUnder_inf {G K : Subgroup (H n ≃ₗᵢ[ℂ] H n)} {σ : Selector n}
    (hσ : IsCovariantUnder G σ) : IsCovariantUnder (G ⊓ K) σ :=
  isCovariantUnder_mono inf_le_left hσ

/--
**FR.** Covariance sous une intersection indexée, dès que covariance sous
l'un des facteurs.

**EN.** Covariance under an indexed intersection, as soon as covariance
under one of the factors holds.
-/
theorem covariantUnder_iInf {ι : Type*} {G : ι → Subgroup (H n ≃ₗᵢ[ℂ] H n)} {σ : Selector n}
    (i : ι) (hσ : IsCovariantUnder (G i) σ) : IsCovariantUnder (⨅ j, G j) σ :=
  isCovariantUnder_mono (iInf_le G i) hσ

/--
**FR.** Le sélecteur de Born est covariant sous tout sous-groupe (via
`bornSelector_isCovariant` + monotonie).

**EN.** The Born selector is covariant under every subgroup (via
`bornSelector_isCovariant` + monotonicity).
-/
theorem bornSelector_isCovariantUnder (G : Subgroup (H n ≃ₗᵢ[ℂ] H n)) :
    IsCovariantUnder G (bornSelector n) :=
  isCovariantUnder_mono le_top
    ((isCovariant_iff_covariantUnder_top (bornSelector n)).mp bornSelector_isCovariant)

/--
**FR.** Toute la famille candidate `tSelector` est covariante sous tout
sous-groupe.

**EN.** The entire candidate family `tSelector` is covariant under every
subgroup.
-/
theorem tSelector_isCovariantUnder (G : Subgroup (H n ≃ₗᵢ[ℂ] H n)) (hn : 2 ≤ n) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : IsCovariantUnder G (tSelector n hn t ht0 ht1) :=
  isCovariantUnder_mono le_top
    ((isCovariant_iff_covariantUnder_top (tSelector n hn t ht0 ht1)).mp
      (tSelector_isCovariant hn ht0 ht1))

/--
**FR.** Le stabilisateur unitaire d'un vecteur `ψ` : le sous-groupe des
isométries qui le fixent.

**EN.** The unitary stabilizer of a vector `ψ`: the subgroup of isometries
that fix it.
-/
def stateStabilizer (ψ : H n) : Subgroup (H n ≃ₗᵢ[ℂ] H n) where
  carrier := {U | U ψ = ψ}
  one_mem' := by show (1 : H n ≃ₗᵢ[ℂ] H n) ψ = ψ; simp
  mul_mem' := by
    intro U V hU hV
    show (U * V) ψ = ψ
    show U (V ψ) = ψ
    rw [hV, hU]
  inv_mem' := by
    intro U hU
    show U⁻¹ ψ = ψ
    have h1 : U⁻¹ (U ψ) = U⁻¹ ψ := by rw [hU]
    have h2 : U⁻¹ (U ψ) = ψ := by
      show U.symm (U ψ) = ψ
      exact U.symm_apply_apply ψ
    rw [h2] at h1
    exact h1.symm

/--
**FR.** Invariance d'un opérateur sous un sous-groupe : commute avec la
conjugaison par tout élément de `G`.

**EN.** Invariance of an operator under a subgroup: commutes with
conjugation by every element of `G`.
-/
def IsInvariantUnder (G : Subgroup (H n ≃ₗᵢ[ℂ] H n)) (ρ : H n →ₗ[ℂ] H n) : Prop :=
  ∀ U : H n ≃ₗᵢ[ℂ] H n, U ∈ G → U.toLinearMap ∘ₗ ρ ∘ₗ U.symm.toLinearMap = ρ

/--
**FR.** Monotonie de `IsInvariantUnder` : invariance sous un groupe plus
gros `K` implique invariance sous tout sous-groupe plus petit `G ≤ K`.

**EN.** Monotonicity of `IsInvariantUnder`: invariance under a larger
group `K` implies invariance under any smaller subgroup `G ≤ K`.
-/
theorem isInvariantUnder_mono {G K : Subgroup (H n ≃ₗᵢ[ℂ] H n)} (hGK : G ≤ K)
    {ρ : H n →ₗ[ℂ] H n} (hρ : IsInvariantUnder K ρ) : IsInvariantUnder G ρ := by
  intro U hU
  exact hρ U (hGK hU)

/--
**FR.** Pour un sélecteur covariant, la densité en un point `ψ` est
invariante sous le stabilisateur de `ψ` : `σ(Uψ) = σ(ψ)` puisque `Uψ = ψ`,
et la covariance donne alors `σ(ψ) = U σ(ψ) U†`.

**EN.** For a covariant selector, the density at a point `ψ` is invariant
under the stabilizer of `ψ`: `σ(Uψ) = σ(ψ)` since `Uψ = ψ`, and covariance
then gives `σ(ψ) = U σ(ψ) U†`.
-/
theorem selector_value_invariant_under_stateStabilizer (σ : Selector n) (hσ : IsCovariant σ)
    {ψ : H n} (hψ : ‖ψ‖ = 1) : IsInvariantUnder (stateStabilizer ψ) (σ.ρ ψ) := by
  intro U hU
  have hUψ : U ψ = ψ := hU
  have hcov := hσ U ψ hψ
  rw [hUψ] at hcov
  exact hcov.symm

end
end QuantumFoundations.Selector
