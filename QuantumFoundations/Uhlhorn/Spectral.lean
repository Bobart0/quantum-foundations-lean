import QuantumFoundations.Uhlhorn.Defs

/-!
# U2 — Lemme spectral élémentaire

Pure algèbre linéaire, aucune dépendance sur Gleason ou Wigner. Brique centrale
réutilisable : `Gleason.positive_inner_self_eq_zero` (déjà prouvé dans la
dépendance épinglée) fournit l'argument quadratique-en-`t` nécessaire.
-/

namespace QuantumFoundations.Uhlhorn

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ}

/-- **U2** : un opérateur positif, borné par l'identité (`IsEffect`, i.e.
`0 ≤ E ≤ 1`), de trace `1`, dont la forme quadratique vaut `1` en un vecteur
unitaire `x`, est EXACTEMENT la projection sur `x`. -/
theorem eq_projL_of_positive_le_one_trace_one_inner_one {E : H n →ₗ[ℂ] H n}
    (hE : IsEffect E) (hE1 : LinearMap.trace ℂ (H n) E = 1) {x : H n} (hx : ‖x‖ = 1)
    (hEx : ⟪E x, x⟫_ℂ = 1) : E = projL (ℂ ∙ x) := by
  sorry

end
end QuantumFoundations.Uhlhorn
