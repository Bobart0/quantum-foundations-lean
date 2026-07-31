import QuantumFoundations.Selectors.Unitaries

/-!
**FR.** # Selectors — S2 : le témoin et la non-vacuité qui compte

Deux témoins de covariance : le sélecteur de Born, et toute la famille
candidate `tSelector`. Le second énoncé est le point mathématique du jalon :
il prouve que **la covariance ne suffit pas** à isoler le sélecteur de Born,
puisque toute la famille à un paramètre la satisfait.

Route (`Submodule.starProjection_map_apply`, `Submodule.map_orthogonal_equiv`) :
pour une isométrie `U`, `U P_A U† = P_{A.map U}`, et `(ℂ ∙ ψ).map U = ℂ ∙ (U ψ)`,
`(Aᗮ).map U = (A.map U)ᗮ`.

**EN.** # Selectors — S2: the witness and the nonvacuity that matters

Two covariance witnesses: the Born selector, and the whole candidate family
`tSelector`. The second statement is the mathematical point of the milestone:
it proves that **covariance alone is not enough** to isolate the Born
selector, since the entire one-parameter family satisfies it.

Route (`Submodule.starProjection_map_apply`, `Submodule.map_orthogonal_equiv`):
for an isometry `U`, `U P_A U† = P_{A.map U}`, and `(ℂ ∙ ψ).map U = ℂ ∙ (U ψ)`,
`(Aᗮ).map U = (A.map U)ᗮ`.
-/

namespace QuantumFoundations.Selector

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ}

/--
**FR.** Le sélecteur de Born est unitairement covariant.

**EN.** The Born selector is unitarily covariant.
-/
theorem bornSelector_isCovariant : IsCovariant (bornSelector n) := by
  sorry

/--
**FR.** Toute la famille candidate `tSelector` est unitairement covariante :
la covariance seule ne fixe donc pas le paramètre `t`.

**EN.** The entire candidate family `tSelector` is unitarily covariant:
covariance alone therefore does not fix the parameter `t`.
-/
theorem tSelector_isCovariant (hn : 2 ≤ n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsCovariant (tSelector n hn t ht0 ht1) := by
  sorry

end
end QuantumFoundations.Selector
