import QuantumFoundations.Uhlhorn.Defs

/-!
# U1 — Corollaire (B) de Wigner en langage de projections

Jamais construit jusqu'ici (mis de côté au tout début du projet Wigner, W0). Se
déduit de `QuantumFoundations.Wigner.wigner` en choisissant un représentant
unitaire par projection.
-/

namespace QuantumFoundations.Uhlhorn

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ}

/-- **U1** : une application `φ : Proj1 n → Proj1 n` (PAS supposée bijective)
préservant `tr(φ(P)φ(Q)) = tr(PQ)` pour TOUTE paire `P, Q` est une symétrie de
Wigner. -/
theorem wigner_projection_form (n : ℕ) (φ : Proj1 n → Proj1 n)
    (hφ : ∀ P Q : Proj1 n, TraceProd (φ P) (φ Q) = TraceProd P Q) :
    IsWignerSymmetryProj φ := by
  sorry

end
end QuantumFoundations.Uhlhorn
