import QuantumFoundations.BornRule.GleasonBridge
import QuantumFoundations.Uhlhorn.Spectral

/-!
# B3 — Pinning : identification de `ρ`

Lemme de repérage abstrait (« pinning lemma », Section 4 du papier) : si `ρ`
est un opérateur densité qui s'annule sur l'orthogonal d'un vecteur unitaire
`v`, alors `ρ` est EXACTEMENT la projection de rang 1 sur `v`.

**Écart favorable trouvé en reconnaissance** : le prototype
(`tstar-born-rule-lean`, `theorem1_general_en.lean`, ~100 lignes) reconstruit
`lam = 1` via une identité de Parseval/Bessel sur une base orthonormée
QUELCONQUE. Ici, en repartant directement de l'hypothèse « `ρ` s'annule sur
`v⊥` » (plutôt que « la partie réelle de `⟪w,ρw⟫` s'annule », comme le fait le
prototype via `symmetric_pos_zero_of_diag_zero`) et en complétant `v` en une
base orthonormée ADAPTÉE (`exists_orthonormalBasis_extension_complex`, déjà
utilisé 3 fois dans Uhlhorn), la décomposition de trace donne directement
`⟪ρv,v⟫ = 1`, puis U2 (`eq_projL_of_positive_le_one_trace_one_inner_one`)
conclut l'égalité opératorielle COMPLÈTE en une seule application — sans
reformuler l'argument de Parseval. Le pas « diagonale nulle ⟹ `ρw = 0` »
(`Gleason.positive_inner_self_eq_zero`) est repoussé à B4, qui en a de toute
façon besoin pour dériver l'hypothèse `hker` à partir de (Null).
-/

namespace QuantumFoundations.BornRule

open scoped InnerProductSpace
open Gleason
open QuantumFoundations.Uhlhorn (one_le_of_norm_eq_one isEffect_of_isDensityOperator
  eq_projL_of_positive_le_one_trace_one_inner_one)

noncomputable section

variable {n : ℕ}

/-- **Pinning** : un opérateur densité qui s'annule sur l'orthogonal d'un
vecteur unitaire `v` est exactement la projection de rang 1 sur `v`. -/
theorem eq_projL_of_vanishes_on_orthogonal {ρ : H n →ₗ[ℂ] H n} (hρ : IsDensityOperator ρ)
    {v : H n} (hv : ‖v‖ = 1) (hker : ∀ w : H n, ⟪v, w⟫_ℂ = 0 → ρ w = 0) :
    ρ = projL (ℂ ∙ v) := by
  have hn1 : 1 ≤ n := one_le_of_norm_eq_one hv
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_extension_complex hn1 (fun _ : Fin 1 => v)
    (by rw [orthonormal_iff_ite]; intro i j; fin_cases i; fin_cases j; simp [hv])
  set i0 : Fin n := Fin.castLE hn1 (0 : Fin 1) with hi0
  have hbi0 : b i0 = v := hb 0
  have hvanish : ∀ i ∈ Finset.univ.erase i0, ρ (b i) = 0 := by
    intro i hi
    have hine : i0 ≠ i := Ne.symm (Finset.mem_erase.mp hi).1
    apply hker
    rw [← hbi0]
    exact b.orthonormal.2 hine
  have htrace_sum : LinearMap.trace ℂ (H n) ρ = ∑ i, ⟪b i, ρ (b i)⟫_ℂ :=
    LinearMap.trace_eq_sum_inner ρ b
  have hsplit : ⟪b i0, ρ (b i0)⟫_ℂ + ∑ i ∈ Finset.univ.erase i0, ⟪b i, ρ (b i)⟫_ℂ
      = ∑ i, ⟪b i, ρ (b i)⟫_ℂ :=
    Finset.add_sum_erase Finset.univ (fun i => ⟪b i, ρ (b i)⟫_ℂ) (Finset.mem_univ i0)
  have hrest0 : ∑ i ∈ Finset.univ.erase i0, ⟪b i, ρ (b i)⟫_ℂ = 0 :=
    Finset.sum_eq_zero (fun i hi => by rw [hvanish i hi, inner_zero_right])
  have heq : ⟪b i0, ρ (b i0)⟫_ℂ = 1 := by
    have h := hsplit
    rw [hrest0, add_zero, ← htrace_sum, hρ.trace_one] at h
    exact h
  rw [hbi0] at heq
  have hvv : ⟪ρ v, v⟫_ℂ = 1 := by rw [hρ.symmetric v v]; exact heq
  have hEff : IsEffect ρ := isEffect_of_isDensityOperator hρ
  exact eq_projL_of_positive_le_one_trace_one_inner_one hEff hρ.trace_one hv hvv

end
end QuantumFoundations.BornRule
