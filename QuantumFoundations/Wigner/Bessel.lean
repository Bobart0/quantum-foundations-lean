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
  classical
  set y := ∑ p, ⟪g p, u⟫_ℂ • g p with hy_def
  -- `y` "répond comme `u`" contre chaque `g p` (effondrement simple, orthonormalité).
  have key : ∀ p, ⟪g p, y⟫_ℂ = ⟪g p, u⟫_ℂ := by
    intro p
    rw [hy_def, inner_sum]
    simp only [inner_smul_right]
    have hite := orthonormal_iff_ite.mp hg
    simp only [hite]
    rw [Finset.sum_eq_single p]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hp; exact absurd (Finset.mem_univ p) hp
  have hyy : ⟪y, y⟫_ℂ = (∑ p, ‖⟪g p, u⟫_ℂ‖ ^ 2 : ℝ) := by
    nth_rewrite 1 [hy_def]
    rw [sum_inner]
    push_cast
    apply Finset.sum_congr rfl
    intro p _
    rw [inner_smul_left, key p, mul_comm, Complex.mul_conj]
    norm_cast
    exact (Complex.sq_norm _).symm
  have hyu : ⟪u, y⟫_ℂ = (∑ p, ‖⟪g p, u⟫_ℂ‖ ^ 2 : ℝ) := by
    nth_rewrite 1 [hy_def]
    rw [inner_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro p _
    rw [inner_smul_right, ← inner_conj_symm u (g p), Complex.mul_conj]
    norm_cast
    exact (Complex.sq_norm _).symm
  have hy2 : ‖y‖ ^ 2 = (∑ p, ‖⟪g p, u⟫_ℂ‖ ^ 2 : ℝ) := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hyy]
    exact RCLike.ofReal_re _
  have hnorm_sub : ‖u - y‖ ^ 2 = 0 := by
    rw [norm_sub_sq (𝕜 := ℂ), hyu, hy2,
      show RCLike.re ((∑ p, ‖⟪g p, u⟫_ℂ‖ ^ 2 : ℝ) : ℂ) = ∑ p, ‖⟪g p, u⟫_ℂ‖ ^ 2 from
        RCLike.ofReal_re _]
    linarith [h]
  have huy : u - y = 0 := by
    have h0 : ‖u - y‖ = 0 := by nlinarith [sq_nonneg ‖u - y‖, hnorm_sub, norm_nonneg (u - y)]
    exact norm_eq_zero.mp h0
  exact sub_eq_zero.mp huy

/-- Si `T` préserve les probabilités de transition, l'image par `T` d'une famille
orthonormée (finie) reste orthonormée. -/
theorem orthonormal_image (hT : IsWignerMap T) {ι : Type*} [Fintype ι] {g : ι → H n}
    (hg : Orthonormal ℂ g) : Orthonormal ℂ (fun p => T (g p)) := by
  sorry

end
end QuantumFoundations.Wigner
