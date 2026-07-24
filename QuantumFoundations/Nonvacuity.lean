import QuantumFoundations.Naimark.Defs

/-!
**FR.** # Nonvacuity — `POVM` est habitée

Habitant concret : la POVM uniforme à 2 issues sur `H 2`, `E i := 2⁻¹ • 1`.
Convention constante du projet : toute nouvelle structure d'hypothèses reçoit
un habitant concret dans le même commit.

**EN.** # Nonvacuity — POVM is inhabited

Concrete inhabitant: the uniform two-outcome POVM on H 2,
E i := 2⁻¹ • 1. A standing project convention is that every new hypothesis
structure receives a concrete inhabitant in the same commit.
-/

namespace QuantumFoundations

open scoped InnerProductSpace
open Gleason

noncomputable section

private def uniformE : H 2 →ₗ[ℂ] H 2 := ((2 : ℂ)⁻¹ : ℂ) • (1 : H 2 →ₗ[ℂ] H 2)

private theorem uniformE_isPositiveOp : IsPositiveOp uniformE := by
  constructor
  · intro x y
    simp only [uniformE, LinearMap.smul_apply, Module.End.one_apply, inner_smul_left,
      inner_smul_right]
    rw [map_inv₀, map_ofNat]
  · intro x
    simp only [uniformE, LinearMap.smul_apply, Module.End.one_apply, inner_smul_left]
    rw [Complex.mul_re]
    have h1 : ((starRingEnd ℂ) ((2 : ℂ)⁻¹)).re = (2 : ℝ)⁻¹ := by
      rw [map_inv₀, map_ofNat, Complex.inv_re]; norm_num [Complex.normSq]
    have h2 : ((starRingEnd ℂ) ((2 : ℂ)⁻¹)).im = 0 := by
      rw [map_inv₀, map_ofNat, Complex.inv_im]; norm_num
    have h3 : (0 : ℝ) ≤ (⟪x, x⟫_ℂ).re := by
      have := inner_self_nonneg (𝕜 := ℂ) (x := x)
      exact this
    rw [h1, h2]
    nlinarith [h3]

private theorem uniformE_sum_eq_one : (∑ _i : Fin 2, uniformE) = 1 := by
  simp only [uniformE, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [show (2 : ℕ) • (((2 : ℂ)⁻¹ : ℂ) • (1 : H 2 →ₗ[ℂ] H 2))
      = (((2 : ℕ) : ℂ) * (2 : ℂ)⁻¹) • (1 : H 2 →ₗ[ℂ] H 2) from by
    rw [← smul_smul, ← Nat.cast_smul_eq_nsmul ℂ]]
  norm_num

/--
**FR.** La POVM uniforme à 2 issues sur `H 2` : `E i := 2⁻¹ • 1`.

**EN.** The uniform two-outcome POVM on H 2: E i := 2⁻¹ • 1.
-/
def uniformPOVM : POVM 2 2 where
  E _ := uniformE
  pos _ := uniformE_isPositiveOp
  sum_eq_one := uniformE_sum_eq_one

example : Nonempty (POVM 2 2) := ⟨uniformPOVM⟩

end
end QuantumFoundations
