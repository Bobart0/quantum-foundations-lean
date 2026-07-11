import Gleason.Busch.Effects

/-!
# POVM finie à `m` issues sur `H n`

Réutilise `Gleason.IsPositiveOp` (ne pas redéfinir la positivité : cf. CLAUDE.md).
-/

namespace QuantumFoundations

open scoped InnerProductSpace
open Gleason

noncomputable section

/-- **POVM** (positive operator-valued measure) à `m` issues sur `H n`. -/
structure POVM (n m : ℕ) where
  /-- Les opérateurs d'effet, un par issue. -/
  E : Fin m → (H n →ₗ[ℂ] H n)
  /-- Chaque effet est positif (réutilise `Gleason.IsPositiveOp`). -/
  pos : ∀ i, IsPositiveOp (E i)
  /-- Complétude : les effets somment à l'identité. -/
  sum_eq_one : ∑ i, E i = 1

end
end QuantumFoundations
