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
  have hns : Complex.normSq u = 1 := by rw [← Complex.sq_norm, h1]; norm_num
  rw [Complex.normSq_apply, h2] at hns
  have him : u.im = 0 := by nlinarith [sq_nonneg u.im]
  exact Complex.ext h2 him

/-- **Dichotomie scalaire** (Bargmann §4.6, abstrait en pur lemme ℂ) : toute fonction
`f : ℂ → ℂ` qui préserve la norme, fixe `1`, et préserve la partie réelle du produit
`conj(f α) * f β` (i.e. la partie réelle de `⟪α,β⟫` vu dans ℂ) est l'identité ou la
conjugaison. -/
theorem scalar_dichotomy {f : ℂ → ℂ} (_hnorm : ∀ α, ‖f α‖ = ‖α‖) (hone : f 1 = 1)
    (hre : ∀ α β, (starRingEnd ℂ (f α) * f β).re = (starRingEnd ℂ α * β).re) :
    f = id ∨ f = starRingEnd ℂ := by
  have reI : ∀ w : ℂ, (starRingEnd ℂ w * Complex.I).re = w.im := by
    intro w; simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  have conjMulSelf : ∀ z : ℂ, (starRingEnd ℂ z * z).re = Complex.normSq z := by
    intro z; simp [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  -- (Eq A) Re (f β) = Re β, en substituant α := 1 dans `hre` (et `f 1 = 1`).
  have eqA : ∀ β, (f β).re = β.re := by
    intro β
    have h := hre 1 β
    rw [hone] at h
    simpa using h
  -- (Étape B) f I = I ou f I = -I : partie réelle nulle (Eq A en `I`) et norme 1
  -- (`hre I I` donne `normSq (f I) = 1`).
  have hreI0 : (f Complex.I).re = 0 := by rw [eqA]; exact Complex.I_re
  have hnormSqI : Complex.normSq (f Complex.I) = 1 := by
    have h := hre Complex.I Complex.I
    rw [conjMulSelf, reI, Complex.I_im] at h
    exact h
  have himI : (f Complex.I).im = 1 ∨ (f Complex.I).im = -1 := by
    rw [Complex.normSq_apply, hreI0] at hnormSqI
    have h2 : (f Complex.I).im ^ 2 = 1 := by nlinarith
    exact sq_eq_one_iff.mp h2
  rcases himI with hI | hI
  · -- (Étape C, cas f I = I) `hre α I` donne Im(f α) = Im α ⟹ f = id.
    left
    have hfI : f Complex.I = Complex.I := Complex.ext hreI0 (by rw [hI, Complex.I_im])
    funext α
    have hImα : (f α).im = α.im := by
      have h := hre α Complex.I
      rw [hfI] at h
      simpa [reI] using h
    exact Complex.ext (eqA α) hImα
  · -- (Étape C, cas f I = -I) `hre α I` donne Im(f α) = -Im α ⟹ f = conj.
    right
    have hfI : f Complex.I = -Complex.I := Complex.ext (by rw [hreI0]; simp) (by rw [hI]; simp)
    funext α
    have hImα : (f α).im = -α.im := by
      have h := hre α Complex.I
      rw [hfI] at h
      simp only [mul_neg, Complex.neg_re, reI] at h
      linarith
    exact Complex.ext (eqA α) (by rw [Complex.conj_im]; exact hImα)

end
end QuantumFoundations.Wigner
