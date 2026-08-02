import QuantumFoundations.Selectors.PerspectiveClassification

/-!
**FR.** # Selectors — Module B, monotonie sous raffinement

Comment le stabilisateur cellwise se comporte quand la perspective se
raffine (`QuantumFoundations.BornRule.Refines`) :

- **`PerspectiveCellwiseStabilizer_mono_of_refines`** : si `D'` raffine `D`
  (chaque cellule fine de `D'` est contenue dans une cellule grossière de
  `D`), alors `PerspectiveCellwiseStabilizer D' ≤ PerspectiveCellwiseStabilizer D`
  — fixer chaque petit morceau setwise force à fixer chaque gros morceau
  bâti à partir de ces petits morceaux. La preuve décompose tout vecteur
  d'une cellule grossière `c` via la résolution de l'identité sur `D'`
  (`sum_projL_cells_eq_id`) : les termes issus de cellules fines NON
  contenues dans `c` s'annulent (elles lui sont orthogonales), et les
  autres restent dans `c` par hypothèse.
- **`PerspectiveCellwiseStabilizer_refinePerspective_le`** : instance
  concrète via le raffinement canonique `refinePerspective` déjà présent
  dans `BornRule/Perspective.lean`.
- **`isInvariantUnder_cellwiseStabilizer_of_refines`** : corollaire pour les
  densités — l'invariance sous le stabilisateur de la perspective
  GROSSIÈRE descend à celle de toute perspective plus FINE qu'elle raffine.
- **`PerspectiveCellwiseStabilizer_eq_top_of_singleton_top`** : cas extrême
  le plus grossier (une seule cellule, `⊤`) — le stabilisateur cellwise est
  alors le groupe TOUT ENTIER, aucune isométrie n'est exclue.
- **`isInvariantUnder_bot`** : cas extrême opposé — TOUT opérateur est
  trivialement invariant sous le sous-groupe trivial `⊥`. Ensemble, ces
  deux faits illustrent le thème "moins de symétrie imposée, plus de
  sélecteurs admissibles" : `⊥` (symétrie minimale) admet tous les
  opérateurs, `⊤` version cellwise à une cellule aussi.

Le stabilisateur SETWISE n'a délibérément PAS d'énoncé de monotonie
analogue ici : une isométrie qui permute les cellules fines de `D'` entre
elles n'a aucune raison de respecter le découpage grossier de `D` (rien
n'empêche qu'elle envoie deux cellules fines d'une même cellule grossière
vers des cellules grossières différentes). Affirmer une telle monotonie
serait une généralisation fausse.

**EN.** # Selectors — Module B, monotonicity under refinement

How the cellwise stabilizer behaves as the perspective is refined
(`QuantumFoundations.BornRule.Refines`):

- **`PerspectiveCellwiseStabilizer_mono_of_refines`**: if `D'` refines `D`
  (every fine cell of `D'` is contained in some coarse cell of `D`), then
  `PerspectiveCellwiseStabilizer D' ≤ PerspectiveCellwiseStabilizer D` —
  fixing every small piece setwise forces fixing every big piece built
  from those pieces setwise too. The proof decomposes any vector of a
  coarse cell `c` via the resolution of the identity on `D'`
  (`sum_projL_cells_eq_id`): the terms coming from fine cells NOT
  contained in `c` vanish (they are orthogonal to it), and the rest stay
  in `c` by hypothesis.
- **`PerspectiveCellwiseStabilizer_refinePerspective_le`**: concrete
  instance via the canonical refinement `refinePerspective` already
  present in `BornRule/Perspective.lean`.
- **`isInvariantUnder_cellwiseStabilizer_of_refines`**: corollary for
  densities — invariance under the COARSE perspective's stabilizer
  descends to invariance under any FINER perspective it refines.
- **`PerspectiveCellwiseStabilizer_eq_top_of_singleton_top`**: the
  coarsest extreme case (a single cell, `⊤`) — the cellwise stabilizer is
  then the WHOLE group, no isometry is excluded.
- **`isInvariantUnder_bot`**: the opposite extreme — ANY operator is
  trivially invariant under the trivial subgroup `⊥`. Together, these two
  facts illustrate the "less imposed symmetry, more admissible selectors"
  theme: `⊥` (minimal symmetry) admits every operator, and so does the
  single-cell `⊤` case of the cellwise stabilizer.

The SETWISE stabilizer deliberately has NO analogous monotonicity
statement here: an isometry that permutes `D'`'s fine cells among
themselves has no reason to respect `D`'s coarse grouping (nothing stops
it from sending two fine cells of the same coarse cell to two DIFFERENT
coarse cells). Asserting such a monotonicity would be a false
generalization.
-/

namespace QuantumFoundations.Selector

open scoped InnerProductSpace
open Gleason
open QuantumFoundations.BornRule
open scoped Classical

noncomputable section

variable {n : ℕ}

theorem isInvariantUnder_bot (ρ : H n →ₗ[ℂ] H n) :
    IsInvariantUnder (⊥ : Subgroup (H n ≃ₗᵢ[ℂ] H n)) ρ := by
  intro U hU
  rw [Subgroup.mem_bot] at hU
  subst hU
  apply LinearMap.ext
  intro x
  show (1 : H n ≃ₗᵢ[ℂ] H n) (ρ ((1 : H n ≃ₗᵢ[ℂ] H n).symm x)) = ρ x
  rfl

private theorem cellwiseStabilizer_refines_le {D' D : Perspective n} (h : Refines D' D)
    {U : H n ≃ₗᵢ[ℂ] H n} (hU : U ∈ PerspectiveCellwiseStabilizer D') {c : Submodule ℂ (H n)}
    (hc : c ∈ D.cells) : c.map U.toLinearMap ≤ c := by
  rintro y ⟨x, hx, rfl⟩
  have hxsum : x = ∑ c' ∈ D'.cells, projL c' x := by
    have hid := LinearMap.congr_fun (sum_projL_cells_eq_id D') x
    rw [LinearMap.sum_apply] at hid
    exact hid.symm
  have hterm : ∀ c' ∈ D'.cells, U (projL c' x) ∈ c := by
    intro c' hc'
    by_cases hle : c' ≤ c
    · have hproj_mem : projL c' x ∈ c' := Submodule.starProjection_apply_mem c' x
      have hmapped : U.toLinearMap (projL c' x) ∈ c'.map U.toLinearMap :=
        Submodule.mem_map_of_mem hproj_mem
      rw [hU c' hc'] at hmapped
      exact hle hmapped
    · obtain ⟨d, hd, hc'd⟩ := h c' hc'
      have hdc : d ≠ c := fun heq => hle (heq ▸ hc'd)
      have hortho : d ≤ c ᗮ := D.ortho d hd c hc hdc
      have hc'_le_cperp : c' ≤ c ᗮ := hc'd.trans hortho
      have hc_le_c'perp : c ≤ c' ᗮ := Submodule.IsOrtho.ge hc'_le_cperp
      have hxperp : x ∈ c' ᗮ := hc_le_c'perp hx
      have hzero : projL c' x = 0 := (Submodule.starProjection_apply_eq_zero_iff c').mpr hxperp
      rw [hzero, map_zero]
      exact Submodule.zero_mem c
  rw [hxsum, map_sum]
  exact Submodule.sum_mem _ (fun c' hc' => hterm c' hc')

/-- Refinement monotonicity: an isometry that cellwise-stabilizes a FINER
perspective `D'` automatically cellwise-stabilizes any COARSER `D` it
refines -- fixing every small piece setwise forces fixing every big piece
built from those pieces setwise too. -/
theorem PerspectiveCellwiseStabilizer_mono_of_refines {D' D : Perspective n} (h : Refines D' D) :
    PerspectiveCellwiseStabilizer D' ≤ PerspectiveCellwiseStabilizer D := by
  intro U hU c hc
  have hUsymm : U.symm ∈ PerspectiveCellwiseStabilizer D' := by
    have hinv : U⁻¹ ∈ PerspectiveCellwiseStabilizer D' := (PerspectiveCellwiseStabilizer D').inv_mem hU
    have hinv_eq : U⁻¹ = U.symm := rfl
    rwa [hinv_eq] at hinv
  have hle1 : c.map U.toLinearMap ≤ c := cellwiseStabilizer_refines_le h hU hc
  have hle2 : c.map U.symm.toLinearMap ≤ c := cellwiseStabilizer_refines_le h hUsymm hc
  have hle3 : (c.map U.symm.toLinearMap).map U.toLinearMap ≤ c.map U.toLinearMap :=
    Submodule.map_mono hle2
  rw [← Submodule.map_comp,
    show U.toLinearMap.comp U.symm.toLinearMap = LinearMap.id from by ext x; simp,
    Submodule.map_id] at hle3
  exact le_antisymm hle1 hle3

/-- Concrete instance: the canonical `refinePerspective D` is always finer
than `D`, so its cellwise stabilizer sits inside `D`'s. -/
theorem PerspectiveCellwiseStabilizer_refinePerspective_le (D : Perspective n) :
    PerspectiveCellwiseStabilizer (refinePerspective D) ≤ PerspectiveCellwiseStabilizer D :=
  PerspectiveCellwiseStabilizer_mono_of_refines (refinePerspective_refines D)

/-- Corollary for densities: invariance under the COARSER perspective's
cellwise stabilizer descends to invariance under any FINER perspective's
cellwise stabilizer it refines. -/
theorem isInvariantUnder_cellwiseStabilizer_of_refines {D' D : Perspective n} (h : Refines D' D)
    {ρ : H n →ₗ[ℂ] H n} (hρ : IsInvariantUnder (PerspectiveCellwiseStabilizer D) ρ) :
    IsInvariantUnder (PerspectiveCellwiseStabilizer D') ρ :=
  isInvariantUnder_mono (PerspectiveCellwiseStabilizer_mono_of_refines h) hρ

/-- Extreme case: the coarsest possible perspective (a single cell, the
whole space) has full cellwise stabilizer -- every isometry preserves the
one cell `⊤` setwise, so there is no constraint on `U` at all. -/
theorem PerspectiveCellwiseStabilizer_eq_top_of_singleton_top {D : Perspective n}
    (hD : D.cells = {⊤}) : PerspectiveCellwiseStabilizer D = ⊤ := by
  apply (PerspectiveCellwiseStabilizer D).eq_top_iff'.mpr
  intro U c hc
  rw [hD, Finset.mem_singleton] at hc
  subst hc
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.mpr U.surjective

end

end QuantumFoundations.Selector
