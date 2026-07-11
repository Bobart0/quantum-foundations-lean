import QuantumFoundations.Naimark.SqrtOp
import QuantumFoundations.Naimark.DilSpace

/-!
# Dilatation de Naimark (Watrous, *TQI*, Theorem 2.42)

`dilV P := Σᵢ singleL i ∘ √(E i)` réalise la POVM `P` comme mesure projective sur
`DilSpace n m` : `dilV` est une isométrie, et `adjoint (dilV P) ∘ dilProj i ∘ dilV P = E i`.
-/

namespace QuantumFoundations

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n m : ℕ}

/-- L'isométrie de dilatation de Naimark : `V := Σᵢ singleL i ∘ √(E i)`. -/
noncomputable def dilV (P : POVM n m) : H n →ₗ[ℂ] DilSpace n m :=
  ∑ i, singleL n m i ∘ₗ sqrtOp (P.E i)

/-- `dilV P` est une isométrie : `adjoint (dilV P) ∘ dilV P = id`. -/
theorem dilV_isometry (P : POVM n m) :
    LinearMap.adjoint (dilV P) ∘ₗ dilV P = LinearMap.id := by
  sorry

/-- La mesure projective `dilProj` réalise `P` via `dilV` : `adjoint V ∘ dilProj i ∘ V = E i`. -/
theorem naimark_dilation (P : POVM n m) (i : Fin m) :
    LinearMap.adjoint (dilV P) ∘ₗ dilProj n m i ∘ₗ dilV P = P.E i := by
  sorry

/-- **Théorème de dilation de Naimark** (dimension finie, somme directe). -/
theorem naimark (P : POVM n m) :
    ∃ V : H n →ₗ[ℂ] DilSpace n m, LinearMap.adjoint V ∘ₗ V = LinearMap.id ∧
      ∀ i, LinearMap.adjoint V ∘ₗ dilProj n m i ∘ₗ V = P.E i := by
  sorry

/-- Corollaire statistique : les probabilités de Born coïncident sous la dilatation. -/
theorem naimark_born (P : POVM n m) (i : Fin m) (x : H n) :
    ⟪x, P.E i x⟫_ℂ = ⟪dilV P x, dilProj n m i (dilV P x)⟫_ℂ := by
  sorry

end
end QuantumFoundations
