import QuantumFoundations.Uhlhorn.Defs
import Gleason.Complex.RealSections

/-!
**FR.** # U2 — Lemme spectral élémentaire

Pure algèbre linéaire, aucune dépendance sur Gleason ou Wigner. Brique centrale
réutilisable : `Gleason.positive_inner_self_eq_zero` (déjà prouvé dans la
dépendance épinglée) fournit l'argument quadratique-en-`t` nécessaire.

**Écart par rapport à la stratégie de reconnaissance** : l'assemblage final
n'utilise ni `LinearMap.restrict` ni un « Sous-lemme 3 » générique
(« opérateur positif de trace nulle est nul », qui n'existe pas côté
`gleason-theorem-lean`). À la place, `x` est complété en une base orthonormée
COMPLÈTE de `H n` (`exists_orthonormalBasis_extension_complex`, déjà utilisé
côté Naimark/Gleason) et la trace est décomposée directement autour de cette
base via `LinearMap.trace_eq_sum_inner` — ceci donne `E (b i) = 0` pour chaque
`i` autre que la position de `x`, DIRECTEMENT sur `E` complet, sans jamais
restreindre `E` à `x⊥`. Le « Sous-lemme 2 » (stabilité de `x⊥`) s'avère alors
inutile : il n'est jamais invoqué.

**EN.** # U2 — Elementary spectral lemma

Pure linear algebra, with no dependence on Gleason or Wigner. The reusable
central component Gleason.positive_inner_self_eq_zero, already proved in
the pinned dependency, provides the required quadratic-in-t argument.

Deviation from the reconnaissance strategy: the final assembly uses
neither LinearMap.restrict nor a generic “Sublemma 3” stating that a
positive operator of trace zero is zero, which does not exist in
gleason-theorem-lean. Instead, x is completed to a COMPLETE orthonormal
basis of H n (exists_orthonormalBasis_extension_complex, already used in
Naimark/Gleason), and the trace is decomposed directly around this basis via
LinearMap.trace_eq_sum_inner. This gives E (b i) = 0 for every i other
than the position of x, DIRECTLY for the full operator E, without ever
restricting E to x⊥. The proposed “Sublemma 2” (stability of x⊥) is
therefore unnecessary and is never invoked.
-/

namespace QuantumFoundations.Uhlhorn

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ}

/-- **Sous-lemme 1** : `E` fixe `x`. -/
private theorem E_fixes_x {E : H n →ₗ[ℂ] H n} (hE : IsEffect E) {x : H n} (hx : ‖x‖ = 1)
    (hEx : ⟪E x, x⟫_ℂ = 1) : E x = x := by
  have hsymm : LinearMap.IsSymmetric (1 - E) := hE.2.1
  have hnn : ∀ z, 0 ≤ (⟪(1 - E) z, z⟫_ℂ).re := hE.2.2
  have hzero : ⟪(1 - E) x, x⟫_ℂ = 0 := by
    have hxx : ⟪x, x⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hx]; norm_num
    simp only [LinearMap.sub_apply, Module.End.one_apply, inner_sub_left, hEx, hxx]
    norm_num
  have h0 := Gleason.positive_inner_self_eq_zero hsymm hnn hzero
  have hxE : x - E x = 0 := by simpa using h0
  exact (sub_eq_zero.mp hxE).symm

/--
**FR.** **U2** : un opérateur positif, borné par l'identité (`IsEffect`, i.e.
`0 ≤ E ≤ 1`), de trace `1`, dont la forme quadratique vaut `1` en un vecteur
unitaire `x`, est EXACTEMENT la projection sur `x`.

**EN.** U2: a positive operator bounded above by the identity (IsEffect,
i.e. 0 ≤ E ≤ 1), with trace 1 and quadratic form equal to 1 at a unit
vector x, is EXACTLY the projection onto x.
-/
theorem eq_projL_of_positive_le_one_trace_one_inner_one {E : H n →ₗ[ℂ] H n}
    (hE : IsEffect E) (hE1 : LinearMap.trace ℂ (H n) E = 1) {x : H n} (hx : ‖x‖ = 1)
    (hEx : ⟪E x, x⟫_ℂ = 1) : E = projL (ℂ ∙ x) := by
  have hn1 : 1 ≤ n := one_le_of_norm_eq_one hx
  have hEfix : E x = x := E_fixes_x hE hx hEx
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_extension_complex hn1 (fun _ : Fin 1 => x)
    (by rw [orthonormal_iff_ite]; intro i j; fin_cases i; fin_cases j; simp [hx])
  set i0 : Fin n := Fin.castLE hn1 (0 : Fin 1) with hi0
  have hbi0 : b i0 = x := hb 0
  have hEsymm : LinearMap.IsSymmetric E := hE.1.1
  have hEnn : ∀ z, 0 ≤ (⟪E z, z⟫_ℂ).re := hE.1.2
  -- Décomposition de la trace autour de `i0` (base adaptée, PAS `LinearMap.restrict`).
  have htrace_sum : LinearMap.trace ℂ (H n) E = ∑ i, ⟪b i, E (b i)⟫_ℂ :=
    LinearMap.trace_eq_sum_inner E b
  have hsplit : ⟪b i0, E (b i0)⟫_ℂ + ∑ i ∈ Finset.univ.erase i0, ⟪b i, E (b i)⟫_ℂ
      = ∑ i, ⟪b i, E (b i)⟫_ℂ :=
    Finset.add_sum_erase Finset.univ (fun i => ⟪b i, E (b i)⟫_ℂ) (Finset.mem_univ i0)
  have hxx : ⟪x, x⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hx]; norm_num
  have hterm0 : ⟪b i0, E (b i0)⟫_ℂ = 1 := by rw [hbi0, hEfix, hxx]
  have hrest0 : ∑ i ∈ Finset.univ.erase i0, ⟪b i, E (b i)⟫_ℂ = 0 := by
    have := hsplit
    rw [hterm0, ← htrace_sum, hE1] at this
    linear_combination this
  -- Chaque terme de la somme restante est nul (positivité + somme nulle).
  have hnn_term : ∀ i ∈ Finset.univ.erase i0, 0 ≤ (⟪b i, E (b i)⟫_ℂ).re := by
    intro i _
    rw [← hEsymm (b i) (b i)]
    exact hEnn (b i)
  have hre_sum : (∑ i ∈ Finset.univ.erase i0, ⟪b i, E (b i)⟫_ℂ).re = 0 := by
    rw [hrest0]; simp
  rw [Complex.re_sum] at hre_sum
  have hre_zero : ∀ i ∈ Finset.univ.erase i0, (⟪b i, E (b i)⟫_ℂ).re = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn_term).mp hre_sum
  have hE_vanish : ∀ i ∈ Finset.univ.erase i0, E (b i) = 0 := by
    intro i hi
    have hre : (⟪b i, E (b i)⟫_ℂ).re = 0 := hre_zero i hi
    have him : (⟪b i, E (b i)⟫_ℂ).im = 0 := by
      have hconj : (starRingEnd ℂ) ⟪b i, E (b i)⟫_ℂ = ⟪E (b i), b i⟫_ℂ := inner_conj_symm _ _
      rw [hEsymm (b i) (b i)] at hconj
      exact Complex.conj_eq_iff_im.mp hconj
    have hzero : ⟪b i, E (b i)⟫_ℂ = 0 := Complex.ext hre (by rw [him]; simp)
    have hzero' : ⟪E (b i), b i⟫_ℂ = 0 := by rw [← hEsymm (b i) (b i)] at hzero; exact hzero
    exact Gleason.positive_inner_self_eq_zero hEsymm hEnn hzero'
  -- Assemblage final : `E z = ⟪x,z⟫•x = projL (ℂ∙x) z` pour tout `z`.
  apply LinearMap.ext
  intro z
  rw [projL_singleton_unit x z hx]
  have hrepr : (∑ i, ⟪b i, z⟫_ℂ • b i) = z := b.sum_repr' z
  conv_lhs => rw [← hrepr, map_sum]
  rw [← Finset.add_sum_erase Finset.univ (fun i => E (⟪b i, z⟫_ℂ • b i)) (Finset.mem_univ i0)]
  have hi0term : E (⟪b i0, z⟫_ℂ • b i0) = ⟪x, z⟫_ℂ • x := by
    rw [map_smul, hbi0, hEfix]
  have hresttermszero : ∑ i ∈ Finset.univ.erase i0, E (⟪b i, z⟫_ℂ • b i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [map_smul, hE_vanish i hi, smul_zero]
  rw [hi0term, hresttermszero, add_zero]

end
end QuantumFoundations.Uhlhorn
