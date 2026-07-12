import QuantumFoundations.Wigner.Defs

/-!
# W2 — Plomberie produit-scalaire (Bargmann §3.1)

Le lemme (9) de Bargmann élimine deux blocages anticipés d'un coup : sa preuve
n'utilise qu'une identité de Bessel AVEC ÉGALITÉ (`‖u − Σ⟪gₚ,u⟫•gₚ‖² = ‖u‖² −
Σ‖⟪gₚ,u⟫‖²`, vraie sans hypothèse). Aucune extension de famille orthonormée en
base, aucun comptage de cardinal, aucune surjectivité. Le blueprint Mathlib pour
cette identité est la preuve (non exportée) de `Orthonormal.sum_inner_products_le`
(`Mathlib.Analysis.InnerProductSpace.Orthonormal`) : `norm_sub_sq`,
`InnerProductSpace.norm_sq_eq_re_inner`, `inner_sum`/`sum_inner`,
`inner_smul_left`/`right`, `inner_conj_symm`, `Orthonormal.inner_left_right_finset`.
-/

namespace QuantumFoundations.Wigner

open scoped InnerProductSpace
open Gleason

noncomputable section

variable {n : ℕ} {T : H n → H n}

/-- **Lemme (9) de Bargmann.** Si `‖u‖² = Σₚ ‖⟪gₚ,u⟫‖²` pour une famille orthonormée
finie `g`, alors `u = Σₚ ⟪gₚ,u⟫ • gₚ` — `u` est entièrement déterminé par ses
coefficients contre `g`, sans supposer que `g` engendre l'espace. -/
theorem bessel_eq_of_norm_sq_eq {ι : Type*} [Fintype ι] {g : ι → H n} (hg : Orthonormal ℂ g)
    (u : H n) (h : ‖u‖ ^ 2 = ∑ p, ‖⟪g p, u⟫_ℂ‖ ^ 2) :
    u = ∑ p, ⟪g p, u⟫_ℂ • g p := by
  sorry

/-- Si `T` préserve les probabilités de transition, l'image par `T` d'une famille
orthonormée (finie) reste orthonormée. -/
theorem orthonormal_image (hT : IsWignerMap T) {ι : Type*} [Fintype ι] {g : ι → H n}
    (hg : Orthonormal ℂ g) : Orthonormal ℂ (fun p => T (g p)) := by
  sorry

end
end QuantumFoundations.Wigner
