import QuantumFoundations.BornRule.Perspective
import Gleason.Operator

/-!
**FR.** # Nonvacuity — la règle de Born satisfait (Grain), (Norm), (Pos), (Null)

`Perspective` seule est trivialement habitée (`basisPerspective`, déjà utilisé
dans `Perspective.lean`). Le point non trivial est de montrer que les quatre
axiomes `AxGrain`/`AxNorm`/`AxPos`/`AxNul` admettent SIMULTANÉMENT un témoin :
`E₀ v D c := ‖projL c v‖²`, la règle de Born pour un vecteur unitaire `v`
fixé.

**Lemme-clé (`refine_filter_sup_eq`)** : pour `D'` raffinant `D` et `c ∈
D.cells`, les cellules de `D'` contenues dans `c` (`D'.cells.filter (· ≤ c)`)
ont pour somme `c` exactement — pas seulement `≤ c`. La direction non
triviale (`c ≤ sup`) utilise la résolution de l'identité restreinte à `D'`
(`Gleason.projL_sup_of_pairwise_isOrtho`, déjà disponible dans
`gleason-theorem-lean`, donc PAS re-dérivée ici) : tout `x ∈ c` s'écrit comme
somme de ses projections sur les cellules de `D'`, et les cellules HORS de
`c` (celles dont le parent dans `D` diffère de `c`, via `unique_parent`)
contribuent 0 puisqu'elles sont orthogonales à `c`.

(Grain) et (Norm) découlent alors du même mécanisme : résolution de
l'identité + théorème de Pythagore fini (`sum_sq_projL_of_pairwise_isOrtho`,
dérivé ici par récurrence sur le Finset — absent tel quel de
`gleason-theorem-lean`, qui n'a besoin de l'additivité que sur `bornValue`,
pas sur `‖·‖²`). (Pos) et (Null) sont immédiats.

**EN.** # Nonvacuity — the Born rule satisfies (Grain), (Norm), (Pos), and (Null)

Perspective alone is trivially inhabited (basisPerspective, already used
in Perspective.lean). The nontrivial point is to show that the four axioms
AxGrain/AxNorm/AxPos/AxNul SIMULTANEOUSLY admit a witness:
E₀ v D c := ‖projL c v‖², the Born rule for a fixed unit vector v.

Key lemma (refine_filter_sup_eq): if D' refines D and c ∈
D.cells, then the cells of D' contained in c
(D'.cells.filter (· ≤ c)) have supremum exactly c—not merely ≤ c. The
nontrivial direction (c ≤ sup) uses the resolution of the identity
restricted to D' (Gleason.projL_sup_of_pairwise_isOrtho, already available
in gleason-theorem-lean and therefore NOT rederived here): every x ∈ c is
the sum of its projections onto the cells of D', while the cells OUTSIDE
c (those whose parent in D differs from c, via unique_parent)
contribute 0 because they are orthogonal to c.

(Grain) and (Norm) then follow from the same mechanism: resolution of the
identity + the finite Pythagorean theorem
(sum_sq_projL_of_pairwise_isOrtho, derived here by induction on the Finset—
not available in this form in gleason-theorem-lean, which needs additivity
only for bornValue, not for ‖·‖²). (Pos) and (Null) are immediate.
-/

namespace QuantumFoundations.BornRule

open scoped InnerProductSpace
open scoped Classical
open Gleason

noncomputable section

variable {n : ℕ}

/--
**FR.** **Lemme 3** (généralisation de `refine_filter_eq_cellLines`, B1, à un
raffinement `D'` ARBITRAIRE plutôt qu'au seul `refinePerspective D`
canonique) : les cellules de `D'` sous `c` couvrent exactement `c`.

**EN.** Lemma 3 (generalization of refine_filter_eq_cellLines, B1, to an
ARBITRARY refinement D' rather than only the canonical
refinePerspective D): the cells of D' below c cover exactly c.
-/
theorem refine_filter_sup_eq (D' D : Perspective n) (hD' : Refines D' D)
    (c : Submodule ℂ (H n)) (hc : c ∈ D.cells) :
    (D'.cells.filter (· ≤ c)).sup id = c := by
  apply le_antisymm
  · exact Finset.sup_le (fun c' hc' => (Finset.mem_filter.mp hc').2)
  · have htop : D'.cells.sup id = (⊤ : Submodule ℂ (H n)) := by
      rw [Finset.sup_id_eq_sSup]; exact D'.span
    have hresI : projL (D'.cells.sup id) = ∑ c'' ∈ D'.cells, projL c'' :=
      Gleason.projL_sup_of_pairwise_isOrtho D'.cells id
        (fun c'' hc'' c''' hc''' hne => D'.ortho c'' hc'' c''' hc''' hne)
    rw [htop] at hresI
    have hid : projL (⊤ : Submodule ℂ (H n)) = LinearMap.id := by
      unfold projL
      rw [Submodule.starProjection_top]
      rfl
    rw [hid] at hresI
    intro x hx
    have hxeq : x = ∑ c'' ∈ D'.cells, projL c'' x := by
      have := congrArg (fun T => T x) hresI
      simpa using this
    rw [← Finset.sum_filter_add_sum_filter_not D'.cells (· ≤ c) (fun c'' => projL c'' x)] at hxeq
    have hzero : ∑ c'' ∈ D'.cells.filter (fun c'' => ¬ c'' ≤ c), projL c'' x = 0 := by
      apply Finset.sum_eq_zero
      intro c'' hc''
      obtain ⟨hc''mem, hc''nle⟩ := Finset.mem_filter.mp hc''
      obtain ⟨p, hp, hc''p⟩ := hD' c'' hc''mem
      have hpc : p ≠ c := fun heq => hc''nle (heq ▸ hc''p)
      have hpc' : p ≤ cᗮ := D.ortho p hp c hc hpc
      have hc''ortho : c'' ⟂ c := (hc''p.trans hpc' : c'' ≤ cᗮ)
      have hxperp : x ∈ c''ᗮ := hc''ortho.symm hx
      show projL c'' x = 0
      unfold projL
      rw [ContinuousLinearMap.coe_coe, (Submodule.starProjection_apply_eq_zero_iff c'').mpr hxperp]
    rw [hzero, add_zero] at hxeq
    rw [hxeq]
    apply Submodule.sum_mem
    intro c'' hc''
    have hc''le : c'' ≤ (D'.cells.filter (· ≤ c)).sup id := Finset.le_sup (f := id) hc''
    exact hc''le (Submodule.starProjection_apply_mem c'' x)

/--
**FR.** **Témoin** : la règle de Born pour un vecteur unitaire `v` fixé,
`E₀ v D c := ‖projL c v‖²` (ignore `D`, comme `g` en B2 : ne dépend que de
la cellule).

**EN.** Witness: the Born rule for a fixed unit vector v,
E₀ v D c := ‖projL c v‖² (it ignores D, as does g in B2: it depends
only on the cell).
-/
noncomputable def E₀ (v : H n) : Perspective n → Submodule ℂ (H n) → ℝ :=
  fun _ c => ‖projL c v‖ ^ 2

theorem E₀_isPos (v : H n) : AxPos (E₀ v) := fun _ _ _ => sq_nonneg _

theorem E₀_isNul (v : H n) : AxNul (E₀ v) v := by
  intro D c _ hv
  show ‖projL c v‖ ^ 2 = 0
  have hzero : projL c v = 0 := by
    unfold projL
    rw [ContinuousLinearMap.coe_coe, (Submodule.starProjection_apply_eq_zero_iff c).mpr hv]
  rw [hzero]; simp

theorem E₀_isNorm (v : H n) (hv : ‖v‖ = 1) : AxNorm (E₀ v) := by
  intro D
  have htop : D.cells.sup id = (⊤ : Submodule ℂ (H n)) := by
    rw [Finset.sup_id_eq_sSup]; exact D.span
  have hpyth := sum_sq_projL_of_pairwise_isOrtho D.cells D.ortho v
  rw [htop] at hpyth
  have hid : projL (⊤ : Submodule ℂ (H n)) = LinearMap.id := by
    unfold projL
    rw [Submodule.starProjection_top]
    rfl
  rw [hid] at hpyth
  show ∑ c ∈ D.cells, E₀ v D c = 1
  simp only [E₀]
  rw [← hpyth]
  simp [hv]

theorem E₀_isGrain (v : H n) : AxGrain (E₀ v) := by
  intro D' D hD' c hc
  show E₀ v D c = ∑ c' ∈ D'.cells.filter (· ≤ c), E₀ v D' c'
  simp only [E₀]
  have hsup := refine_filter_sup_eq D' D hD' c hc
  have hpyth := sum_sq_projL_of_pairwise_isOrtho (D'.cells.filter (· ≤ c))
    (fun c' hc' c'' hc'' hne => D'.ortho c' (Finset.mem_filter.mp hc').1
      c'' (Finset.mem_filter.mp hc'').1 hne) v
  rw [hsup] at hpyth
  exact hpyth

/--
**FR.** La règle de Born pour n'importe quel vecteur unitaire `v` satisfait
SIMULTANÉMENT les quatre axiomes — `grainCoherenceTheorem` n'est donc pas
vacuement vrai.

**EN.** The Born rule for any unit vector v SIMULTANEOUSLY satisfies all four
axioms—hence grainCoherenceTheorem is not vacuously true.
-/
theorem E₀_satisfies_axioms (v : H n) (hv : ‖v‖ = 1) :
    AxGrain (E₀ v) ∧ AxNorm (E₀ v) ∧ AxPos (E₀ v) ∧ AxNul (E₀ v) v :=
  ⟨E₀_isGrain v, E₀_isNorm v hv, E₀_isPos v, E₀_isNul v⟩

example : ∃ (v : H 3) (_ : ‖v‖ = 1), AxGrain (E₀ v) ∧ AxNorm (E₀ v) ∧ AxPos (E₀ v) ∧ AxNul (E₀ v) v :=
  ⟨EuclideanSpace.single (0 : Fin 3) 1, by simp, E₀_satisfies_axioms _ (by simp)⟩

end
end QuantumFoundations.BornRule
