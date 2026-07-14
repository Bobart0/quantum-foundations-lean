import QuantumFoundations.BornRule.Perspective
import Gleason.Operator

/-!
# Nonvacuity — la règle de Born satisfait (Grain), (Norm), (Pos), (Null)

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
-/

namespace QuantumFoundations.BornRule

open scoped InnerProductSpace
open scoped Classical
open Gleason

noncomputable section

variable {n : ℕ}

/-- **Lemme 3** (généralisation de `refine_filter_eq_cellLines`, B1, à un
raffinement `D'` ARBITRAIRE plutôt qu'au seul `refinePerspective D`
canonique) : les cellules de `D'` sous `c` couvrent exactement `c`. -/
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

/-- Théorème de Pythagore fini : la norme au carré d'une somme de vecteurs
deux à deux orthogonaux est la somme des normes au carré. Absent tel quel de
`gleason-theorem-lean` (qui n'a besoin que de l'additivité de `bornValue`,
pas de `‖·‖²`), dérivé ici directement via l'expansion bilinéaire du produit
scalaire. -/
private theorem norm_sq_sum_of_pairwise_orthogonal {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (x : ι → H n) (hortho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪x i, x j⟫_ℂ = 0) :
    ‖∑ i ∈ s, x i‖ ^ 2 = ∑ i ∈ s, ‖x i‖ ^ 2 := by
  have hinner : (⟪∑ i ∈ s, x i, ∑ j ∈ s, x j⟫_ℂ) = ∑ i ∈ s, ⟪x i, x i⟫_ℂ := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_sum, Finset.sum_eq_single i]
    · intro j hj hji
      exact hortho i hi j hj (fun h => hji h.symm)
    · intro hi'
      exact absurd hi hi'
  rw [inner_self_eq_norm_sq_to_K] at hinner
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ s) => inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x i))] at hinner
  exact_mod_cast hinner

/-- Combine la résolution de l'identité (`Gleason.projL_sup_of_pairwise_isOrtho`)
et Pythagore fini : la valeur de Born sur le sup d'une famille orthogonale de
cellules est la somme des valeurs de Born sur chaque cellule. -/
private theorem sum_sq_projL_of_pairwise_isOrtho (s : Finset (Submodule ℂ (H n)))
    (hortho : ∀ c' ∈ s, ∀ c'' ∈ s, c' ≠ c'' → c' ⟂ c'') (v : H n) :
    ‖projL (s.sup id) v‖ ^ 2 = ∑ c' ∈ s, ‖projL c' v‖ ^ 2 := by
  rw [Gleason.projL_sup_of_pairwise_isOrtho s id hortho]
  simp only [id_eq]
  have happly : (∑ c' ∈ s, projL c') v = ∑ c' ∈ s, projL c' v := by
    simp [LinearMap.sum_apply]
  rw [happly]
  apply norm_sq_sum_of_pairwise_orthogonal
  intro c' hc' c'' hc'' hne
  have hcc : c' ⟂ c'' := hortho c' hc' c'' hc'' hne
  have hmem : projL c' v ∈ c' := Submodule.starProjection_apply_mem c' v
  have hmem2 : projL c'' v ∈ c'' := Submodule.starProjection_apply_mem c'' v
  have h1 : projL c' v ∈ c''ᗮ := hcc hmem
  have h2 : ⟪projL c'' v, projL c' v⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal c'' (projL c' v)).mp h1 (projL c'' v) hmem2
  rw [← inner_conj_symm (projL c' v) (projL c'' v), h2]
  simp

/-- **Témoin** : la règle de Born pour un vecteur unitaire `v` fixé,
`E₀ v D c := ‖projL c v‖²` (ignore `D`, comme `g` en B2 : ne dépend que de
la cellule). -/
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

/-- La règle de Born pour n'importe quel vecteur unitaire `v` satisfait
SIMULTANÉMENT les quatre axiomes — `grainCoherenceTheorem` n'est donc pas
vacuement vrai. -/
theorem E₀_satisfies_axioms (v : H n) (hv : ‖v‖ = 1) :
    AxGrain (E₀ v) ∧ AxNorm (E₀ v) ∧ AxPos (E₀ v) ∧ AxNul (E₀ v) v :=
  ⟨E₀_isGrain v, E₀_isNorm v hv, E₀_isPos v, E₀_isNul v⟩

example : ∃ (v : H 3) (_ : ‖v‖ = 1), AxGrain (E₀ v) ∧ AxNorm (E₀ v) ∧ AxPos (E₀ v) ∧ AxNul (E₀ v) v :=
  ⟨EuclideanSpace.single (0 : Fin 3) 1, by simp, E₀_satisfies_axioms _ (by simp)⟩

end
end QuantumFoundations.BornRule
