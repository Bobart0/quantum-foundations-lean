import Mathlib.Analysis.Complex.Basic

/-!
# W1 — Kit scalaire ℂ

Trois lemmes purement scalaires (aucune dépendance à `H n` ni à `T`), à prouver en
premier : ils calibrent le niveau de difficulté réel (`nlinarith`/`Complex.ext`
territoriaux) et `W4` (`Core.lean`) s'appuie entièrement sur `scalar_dichotomy`.
Blueprint : Bargmann 1964, §4.6 (la dichotomie tient en trois lignes une fois
l'identité de partie réelle établie).
-/

namespace QuantumFoundations.Wigner

open scoped ComplexConjugate

noncomputable section

/-- Si `u` et `v` ont même norme et `1+u`, `1+v` ont même norme, alors `u` et `v`
ont même partie réelle. Via `‖1+r‖² = 1+‖r‖²+2Re r`. -/
theorem re_eq_of_norm_eq {u v : ℂ} (h1 : ‖u‖ = ‖v‖) (h2 : ‖(1 : ℂ) + u‖ = ‖(1 : ℂ) + v‖) :
    u.re = v.re := by
  have key : ∀ r : ℂ, ‖(1 : ℂ) + r‖ ^ 2 = 1 + ‖r‖ ^ 2 + 2 * r.re := by
    intro r
    rw [Complex.sq_norm, Complex.normSq_add, Complex.normSq_one, ← Complex.sq_norm]
    simp [Complex.conj_re]
  have hu := key u
  have hv := key v
  have h1' : ‖u‖ ^ 2 = ‖v‖ ^ 2 := by rw [h1]
  have h2' : ‖(1 : ℂ) + u‖ ^ 2 = ‖(1 : ℂ) + v‖ ^ 2 := by rw [h2]
  rw [hu, h1'] at h2'
  rw [hv] at h2'
  linarith

/-- Rigidité : un scalaire de norme 1 et de partie réelle 1 vaut 1. -/
theorem eq_one_of_norm_one_re_one {u : ℂ} (h1 : ‖u‖ = 1) (h2 : u.re = 1) : u = 1 := by
  sorry

/-- **Dichotomie scalaire** (Bargmann §4.6, abstrait en pur lemme ℂ) : toute fonction
`f : ℂ → ℂ` qui préserve la norme, fixe `1`, et préserve la partie réelle du produit
`conj(f α) * f β` (i.e. la partie réelle de `⟪α,β⟫` vu dans ℂ) est l'identité ou la
conjugaison. -/
theorem scalar_dichotomy {f : ℂ → ℂ} (hnorm : ∀ α, ‖f α‖ = ‖α‖) (hone : f 1 = 1)
    (hre : ∀ α β, (starRingEnd ℂ (f α) * f β).re = (starRingEnd ℂ α * β).re) :
    f = id ∨ f = starRingEnd ℂ := by
  sorry

end
end QuantumFoundations.Wigner
