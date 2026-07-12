import QuantumFoundations.Wigner.VConstruction
import QuantumFoundations.Wigner.Scalar

/-!
# W4 — LE cœur : analyse de `V` (Bargmann §4, l'analogue de `sqrtOp` pour N1)

Seul contenu mathématique réellement neuf du dépôt Wigner (le reste est de la
plomberie disciplinée, comme N2-N3-N5 l'étaient pour Naimark).

Le case split de la construction du repère adapté (`V_additive` etc.) porte sur la
**dépendance linéaire** de la paire de vecteurs, PAS sur `n` : `n = 2` est absorbé
automatiquement (la dépendance y est forcée), aucune disjonction `n = 2` vs `n ≥ 3`
n'apparaît dans le cœur — contrairement à Gleason.
-/

namespace QuantumFoundations.Wigner

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ} {T : H n → H n}

/-- (14)(15)(15a)(15b) : `chidir T f` est une fonction scalaire qui vérifie les
hypothèses de `scalar_dichotomy` pour tout `f` unitaire de `𝒫`. -/
theorem chidir_dichotomy (hT : IsWignerMap T) (hn : 2 ≤ n) (f : H n) (hf : InPerp f)
    (hfu : ‖f‖ = 1) :
    (fun α => chidir T f α) = id ∨ (fun α => chidir T f α) = starRingEnd ℂ := by
  sorry

/-- `chi` (calculé le long de `refVec`) coïncide avec `chidir` le long de
n'importe quel autre vecteur unitaire de `𝒫` : globalisation de la dichotomie
directionnelle (Bargmann §4, `w = f₁ + f₂`). -/
theorem chi_eq_chidir (hT : IsWignerMap T) (hn : 2 ≤ n) (f : H n) (hf : InPerp f)
    (hfu : ‖f‖ = 1) (α : ℂ) : chi T α = chidir T f α := by
  sorry

/-- `chi` est globalement l'identité ou la conjugaison (conséquence directe de
`chidir_dichotomy` + `chi_eq_chidir`). -/
theorem chi_dichotomy (hT : IsWignerMap T) (hn : 2 ≤ n) :
    (fun α => chi T α) = id ∨ (fun α => chi T α) = starRingEnd ℂ := by
  sorry

/-- (18a) `V` est additive sur `𝒫`. -/
theorem V_additive (hT : IsWignerMap T) (hn : 2 ≤ n) (y z : H n) (hy : InPerp y)
    (hz : InPerp z) : V T (y + z) = V T y + V T z := by
  sorry

/-- (18b) `V` est `χ`-homogène sur `𝒫`. -/
theorem V_chi_homogeneous (hT : IsWignerMap T) (hn : 2 ≤ n) (c : ℂ) (z : H n)
    (hz : InPerp z) : V T (c • z) = chi T c • V T z := by
  sorry

/-- (18c) `V` transporte le produit scalaire via `χ` sur `𝒫`. -/
theorem inner_V_eq_chi_inner (hT : IsWignerMap T) (hn : 2 ≤ n) (y z : H n)
    (hy : InPerp y) (hz : InPerp z) : ⟪V T y, V T z⟫_ℂ = chi T ⟪y, z⟫_ℂ := by
  sorry

end
end QuantumFoundations.Wigner
