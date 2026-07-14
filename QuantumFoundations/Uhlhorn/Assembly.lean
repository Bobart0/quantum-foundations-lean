import QuantumFoundations.Uhlhorn.WignerProjectionForm
import QuantumFoundations.Uhlhorn.GleasonTwice

/-!
# U4/U5 — Assemblage final et Corollaire 1.2 de Šemrl

U4 combine U1 et U3b. U5 réduit `PreservesOrthogonality` (orthogonalité préservée
dans un seul sens, ni injectivité ni surjectivité supposées) à `SendsONBToONB` par
un argument de comptage de cardinalité valable en dimension finie, puis conclut via
U4 — c'est le théorème final.
-/

namespace QuantumFoundations.Uhlhorn

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ}

/-- **U4** (assemblage) : U1 + U3b — si `φ` envoie tout COSP sur un COSP, `φ` est
une symétrie de Wigner. -/
theorem wignerSymmetryProj_of_sendsONBToONB (hn : 3 ≤ n) (φ : Proj1 n → Proj1 n)
    (hφ : SendsONBToONB φ) : IsWignerSymmetryProj φ :=
  wigner_projection_form n φ (traceProd_preserved_of_sendsONBToONB hn φ hφ)

/-- **U5 — Corollaire 1.2 de Šemrl** (Šemrl 2021, arXiv:2106.06182) : en dimension
finie `n ≥ 3`, toute application sur les projections de rang 1 qui préserve
l'orthogonalité DANS UN SEUL SENS est automatiquement une symétrie de Wigner. -/
theorem uhlhorn_finite_dim (hn : 3 ≤ n) (φ : Proj1 n → Proj1 n)
    (hφ : PreservesOrthogonality φ) : IsWignerSymmetryProj φ := by
  sorry

end
end QuantumFoundations.Uhlhorn
