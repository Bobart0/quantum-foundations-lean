import QuantumFoundations.Wigner.Core

/-!
# W5 — Assemblage (Bargmann §5) et théorème de Wigner

`U` étend `chi`/`V` à tout l'espace par la décomposition `a = ⟪e,a⟫•e + (a −
⟪e,a⟫•e)` (le second terme est dans `𝒫`). La compatibilité `∀x, ∃c, T x = c•U x`
se scinde en deux cas : `⟪e,x⟫ ≠ 0` (calcul direct) et `⟪e,x⟫ = 0` (GRATUIT, via la
colinéarité définitionnelle de `V_colinear` — aucun Cauchy-Schwarz nécessaire,
contrairement à l'inquiétude initiale). La bijectivité de `U` (isométrie ⟹
injective ⟹ surjective en dimension finie) se fait en restreignant à la structure
ℝ-linéaire sous-jacente pour la branche antiunitaire (`LinearMap.injective_iff_surjective`
n'existe que pour des endomorphismes `K`-linéaires ; une application
conj-semilinéaire sur ℂ est ℝ-linéaire par restriction des scalaires) — aucune
coordonnée nécessaire.

**Énoncé final : formulation (A), sans hypothèse de bijectivité** (Bargmann §1.2-
§1.3) — l'injectivité au niveau des rayons découle de `hT` via Cauchy-Schwarz, et
en dimension finie `U` construit est automatiquement bijectif. Énoncé strictement
plus fort que Simon et al. (qui supposent la bijectivité, eq. 2.8).
-/

namespace QuantumFoundations.Wigner

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ} {T : H n → H n}

theorem U_additive (hT : IsWignerMap T) (hn : 2 ≤ n) (a b : H n) :
    U T (a + b) = U T a + U T b := by
  sorry

theorem U_chi_semilinear (hT : IsWignerMap T) (hn : 2 ≤ n) (c : ℂ) (a : H n) :
    U T (c • a) = chi T c • U T a := by
  sorry

theorem inner_U_eq_chi_inner (hT : IsWignerMap T) (hn : 2 ≤ n) (a b : H n) :
    ⟪U T a, U T b⟫_ℂ = chi T ⟪a, b⟫_ℂ := by
  sorry

/-- Compatibilité de `U` avec `T` à une phase près, sur la sphère unité. Cœur de
la preuve de `wigner`. -/
theorem exists_phase_U (hT : IsWignerMap T) (hn : 2 ≤ n) (x : H n) (hx : ‖x‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U T x := by
  sorry

theorem U_bijective (hT : IsWignerMap T) (hn : 2 ≤ n) : Function.Bijective (U T) := by
  sorry

/-- **Théorème de Wigner** (dimension finie, sans hypothèse de bijectivité sur
`T`). Toute transformation sur les états purs qui préserve les probabilités de
transition `|⟨φ|ψ⟩|²` est induite par un unitaire ou un antiunitaire. -/
theorem wigner (n : ℕ) (T : H n → H n) (hT : IsWignerMap T) :
    (∃ U' : H n ≃ₗᵢ[ℂ] H n, ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U' x)
  ∨ (∃ U' : H n ≃ₛₗᵢ[starRingEnd ℂ] H n, ∀ x, ‖x‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ T x = c • U' x) := by
  rcases n with _ | _ | n
  · -- n = 0 : aucun vecteur unitaire dans H 0, vacuité.
    refine Or.inl ⟨LinearIsometryEquiv.refl ℂ (H 0), fun x hx => ?_⟩
    rw [Subsingleton.elim x 0] at hx
    simp at hx
  · -- n = 1 : les deux branches marchent (Bargmann §1.4) ; une seule "phase"
    -- possible dès que dim = 1. À prouver : reste un lemme court et autonome
    -- (aucune dépendance sur W1-W5), pas encore attaqué à ce stade du squelette.
    sorry
  · -- n ≥ 2 : cœur, via exists_phase_U + U_bijective + bundling dans les deux
    -- branches (LinearIsometryEquiv.mk / LinearEquiv.ofBijective).
    sorry

end
end QuantumFoundations.Wigner
