import Gleason.Busch.Effects

/-!
**FR.** # POVM finie à `m` issues sur `H n`

Réutilise `Gleason.IsPositiveOp` (ne pas redéfinir la positivité : cf. CLAUDE.md).

**EN.** # Finite POVM with m outcomes on H n

Reuses Gleason.IsPositiveOp (do not redefine positivity; see CLAUDE.md).
-/

namespace QuantumFoundations

open scoped InnerProductSpace
open Gleason

noncomputable section

/--
**FR.** **POVM** (positive operator-valued measure) à `m` issues sur `H n`.

**EN.** POVM (positive operator-valued measure) with m outcomes on H n.
-/
structure POVM (n m : ℕ) where
  /--
**FR.** Les opérateurs d'effet, un par issue.

**EN.** The effect operators, one for each outcome.
-/
  E : Fin m → (H n →ₗ[ℂ] H n)
  /--
**FR.** Chaque effet est positif (réutilise `Gleason.IsPositiveOp`).

**EN.** Each effect is positive (reusing Gleason.IsPositiveOp).
-/
  pos : ∀ i, IsPositiveOp (E i)
  /--
**FR.** Complétude : les effets somment à l'identité.

**EN.** Completeness: the effects sum to the identity.
-/
  sum_eq_one : ∑ i, E i = 1

end
end QuantumFoundations
