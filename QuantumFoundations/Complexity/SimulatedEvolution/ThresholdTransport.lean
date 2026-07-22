import QuantumFoundations.Complexity.SimulatedEvolution.MatrixElementStability
import QuantumFoundations.Complexity.ProxyDefs

/-!
# C13c — Threshold transport under operator-norm evolution error

If a target norm-preserving evolution `U` is within operator-norm error `ε`
of a norm-preserving operator `Eop` (e.g. an exact circuit's transported
evaluation), then on unit states `a`, `b` the diagonal and cross-amplitude
proxy expressions used by `DistinguishesAt`/`InterferesAt` move by at most
`4 * ε` (`diagonal_difference_stability`/`cross_sum_stability`, C13b). Since
both definitions compare against `2 * (threshold)`, a distinguishability
certificate at `δ + μ` on the `Eop`-side transports to one at `δ` on the
`U`-side whenever `2 * ε ≤ μ` (`2 * (δ + μ) - 4 * ε ≥ 2 * δ`), and dually a
non-interference certificate at `δ - μ` on the `Eop`-side transports from
one at `δ` on the `U`-side.
-/

namespace QuantumFoundations.Complexity.SimulatedEvolution

open scoped InnerProductSpace

open Gleason
open QuantumFoundations.BranchesRiedel
open QuantumFoundations.Complexity
open QuantumFoundations.Complexity.OperatorNorm

noncomputable section

variable {N d : ℕ}

/-! ## C13c.0 — Pointwise image displacement -/

theorem norm_sub_evolved_left {U Eop : H (d ^ N) →L[ℂ] H (d ^ N)} {ε : ℝ}
    {a : H (d ^ N)} (hApprox : ApproximatesOperator U Eop ε) (ha : ‖a‖ = 1) :
    ‖U a - Eop a‖ ≤ ε :=
  norm_image_sub_image_le hApprox ha

theorem norm_sub_evolved_right {U Eop : H (d ^ N) →L[ℂ] H (d ^ N)} {ε : ℝ}
    {b : H (d ^ N)} (hApprox : ApproximatesOperator U Eop ε) (hb : ‖b‖ = 1) :
    ‖U b - Eop b‖ ≤ ε :=
  norm_image_sub_image_le hApprox hb

/-! ## C13c.1 — Distinguishability transport -/

/-- A distinguishability certificate at the widened threshold `δ + μ` on the
`Eop`-evolved states transports to a certificate at the central threshold
`δ` on the `U`-evolved states, whenever `2 * ε ≤ μ`. -/
theorem distinguishesAt_transport_of_operator_approx
    {U Eop : H (d ^ N) →L[ℂ] H (d ^ N)} {ε : ℝ}
    (hApprox : ApproximatesOperator U Eop ε)
    (hU : IsNormPreserving U) (hE : IsNormPreserving Eop)
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (D : Circuit N d)
    {a b : H (d ^ N)} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {δ μ : ℝ}
    (hDist : DistinguishesAt e (Eop a) (Eop b) (δ + μ) D)
    (hmargin : 2 * ε ≤ μ) :
    DistinguishesAt e (U a) (U b) δ D := by
  have hTnp : IsNormPreserving (circuitCLMOnH D e) := circuitCLMOnH_isNormPreserving D e
  have hUa : ‖U a‖ = 1 := by rw [hU a, ha]
  have hUb : ‖U b‖ = 1 := by rw [hU b, hb]
  have hEa : ‖Eop a‖ = 1 := by rw [hE a, ha]
  have hEb : ‖Eop b‖ = 1 := by rw [hE b, hb]
  have hεa : ‖Eop a - U a‖ ≤ ε := by
    rw [norm_sub_rev]; exact norm_sub_evolved_left hApprox ha
  have hεb : ‖Eop b - U b‖ ≤ ε := by
    rw [norm_sub_rev]; exact norm_sub_evolved_right hApprox hb
  have hstab := diagonal_difference_stability hTnp hEa hUa hEb hUb hεa hεb
  simp only [circuitCLMOnH_apply] at hstab
  unfold DistinguishesAt at hDist ⊢
  have hrev := norm_sub_norm_le
    (⟪Eop a, Circuit.evalOnH D e (Eop a)⟫_ℂ - ⟪Eop b, Circuit.evalOnH D e (Eop b)⟫_ℂ)
    (⟪U a, Circuit.evalOnH D e (U a)⟫_ℂ - ⟪U b, Circuit.evalOnH D e (U b)⟫_ℂ)
  linarith

/-! ## C13c.2 — Interference transport -/

/-- If the `U`-evolved states interfere at threshold `δ`, the `Eop`-evolved
states interfere at the narrowed threshold `δ - μ`, whenever `2 * ε ≤ μ`.
Used for contradiction against a supplied non-interference certificate on
the `Eop` side. -/
theorem interferesAt_target_implies_interferesAt_approximation
    {U Eop : H (d ^ N) →L[ℂ] H (d ^ N)} {ε : ℝ}
    (hApprox : ApproximatesOperator U Eop ε)
    (hU : IsNormPreserving U) (hE : IsNormPreserving Eop)
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (C : Circuit N d)
    {a b : H (d ^ N)} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {δ μ : ℝ}
    (hInt : InterferesAt e (U a) (U b) δ C)
    (hmargin : 2 * ε ≤ μ) :
    InterferesAt e (Eop a) (Eop b) (δ - μ) C := by
  have hTnp : IsNormPreserving (circuitCLMOnH C e) := circuitCLMOnH_isNormPreserving C e
  have hUa : ‖U a‖ = 1 := by rw [hU a, ha]
  have hUb : ‖U b‖ = 1 := by rw [hU b, hb]
  have hEa : ‖Eop a‖ = 1 := by rw [hE a, ha]
  have hEb : ‖Eop b‖ = 1 := by rw [hE b, hb]
  have hεa : ‖U a - Eop a‖ ≤ ε := norm_sub_evolved_left hApprox ha
  have hεb : ‖U b - Eop b‖ ≤ ε := norm_sub_evolved_right hApprox hb
  have hstab := cross_sum_stability hTnp hUa hEa hUb hEb hεa hεb
  simp only [circuitCLMOnH_apply] at hstab
  unfold InterferesAt at hInt ⊢
  have habs := abs_le.mp hstab
  linarith [habs.1, habs.2]

/-- Transport of *non*-interference: the contrapositive of
`interferesAt_target_implies_interferesAt_approximation`. -/
theorem not_interferesAt_transport_of_operator_approx
    {U Eop : H (d ^ N) →L[ℂ] H (d ^ N)} {ε : ℝ}
    (hApprox : ApproximatesOperator U Eop ε)
    (hU : IsNormPreserving U) (hE : IsNormPreserving Eop)
    (e : H (d ^ N) ≃ₗᵢ[ℂ] Sites N d) (C : Circuit N d)
    {a b : H (d ^ N)} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    {δ μ : ℝ}
    (hNoInt : ¬ InterferesAt e (Eop a) (Eop b) (δ - μ) C)
    (hmargin : 2 * ε ≤ μ) :
    ¬ InterferesAt e (U a) (U b) δ C :=
  fun hInt => hNoInt
    (interferesAt_target_implies_interferesAt_approximation
      hApprox hU hE e C ha hb hInt hmargin)

#print axioms distinguishesAt_transport_of_operator_approx
#print axioms interferesAt_target_implies_interferesAt_approximation
#print axioms not_interferesAt_transport_of_operator_approx

end

end QuantumFoundations.Complexity.SimulatedEvolution
