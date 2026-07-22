import QuantumFoundations.Complexity.OperatorNorm.FiniteDimensional

/-!
# C12b — Generic operator-norm approximation

`ApproximatesOperator A B ε` is a pure operator-norm statement about two
continuous linear maps: `ε` is an *operator-norm error budget*, i.e. a bound
on the worst-case pointwise discrepancy `‖A x - B x‖` relative to `‖x‖`
(`ContinuousLinearMap`'s norm is exactly the operator norm
`sInf {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖}`, so `‖A - B‖ ≤ ε` already *is* the
uniform bound `‖A x - B x‖ ≤ ε * ‖x‖`).  This file mentions no quantum
records, circuits, or physical readout: it is a generic, reusable normed-space
fact.
-/

namespace QuantumFoundations.Complexity.OperatorNorm

noncomputable section

variable {E F : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]

/-! ## C12b.1 — The generic predicate -/

/-- `A` approximates `B` with operator-norm error at most `ε`: an
`ε`-bound on the operator norm of their difference. -/
def ApproximatesOperator (A B : E →L[ℂ] F) (ε : ℝ) : Prop :=
  ‖A - B‖ ≤ ε

namespace ApproximatesOperator

/-- Increasing the error budget preserves operator-norm approximation. -/
theorem mono {A B : E →L[ℂ] F} {ε ε' : ℝ}
    (h : ApproximatesOperator A B ε) (hε : ε ≤ ε') :
    ApproximatesOperator A B ε' :=
  h.trans hε

/-- Every operator trivially approximates itself with a nonnegative error
budget. -/
theorem refl (A : E →L[ℂ] F) {ε : ℝ} (hε : 0 ≤ ε) :
    ApproximatesOperator A A ε := by
  unfold ApproximatesOperator
  simpa using hε

/-- The exact case: an operator approximates itself with error budget
exactly zero. -/
theorem zero (A : E →L[ℂ] F) : ApproximatesOperator A A 0 := by
  unfold ApproximatesOperator
  simp

/-- Operator-norm approximation is symmetric in its two operators. -/
theorem symm {A B : E →L[ℂ] F} {ε : ℝ}
    (h : ApproximatesOperator A B ε) : ApproximatesOperator B A ε := by
  unfold ApproximatesOperator at *
  rwa [norm_sub_rev]

/-- Operator-norm approximation errors add along a chain of three
operators. -/
theorem trans {A B C : E →L[ℂ] F} {ε η : ℝ}
    (hAB : ApproximatesOperator A B ε) (hBC : ApproximatesOperator B C η) :
    ApproximatesOperator A C (ε + η) := by
  unfold ApproximatesOperator at *
  calc
    ‖A - C‖ = ‖(A - B) + (B - C)‖ := by congr 1; abel
    _ ≤ ‖A - B‖ + ‖B - C‖ := norm_add_le _ _
    _ ≤ ε + η := add_le_add hAB hBC

end ApproximatesOperator

/-! ## C12b.2 — Application bounds -/

/-- The central estimate: an operator-norm error budget bounds the pointwise
discrepancy scaled by the input's norm. -/
theorem norm_apply_sub_le_of_approximatesOperator {A B : E →L[ℂ] F} {ε : ℝ}
    (h : ApproximatesOperator A B ε) (x : E) :
    ‖A x - B x‖ ≤ ε * ‖x‖ := by
  calc
    ‖A x - B x‖ = ‖(A - B) x‖ := by rw [sub_apply]
    _ ≤ ‖A - B‖ * ‖x‖ := ContinuousLinearMap.le_opNorm (A - B) x
    _ ≤ ε * ‖x‖ := mul_le_mul_of_nonneg_right h (norm_nonneg x)

/-- On a unit vector, the operator-norm error budget bounds the pointwise
discrepancy directly. -/
theorem norm_apply_sub_le_of_unit {A B : E →L[ℂ] F} {ε : ℝ}
    (h : ApproximatesOperator A B ε) {x : E} (hx : ‖x‖ = 1) :
    ‖A x - B x‖ ≤ ε := by
  have := norm_apply_sub_le_of_approximatesOperator h x
  rwa [hx, mul_one] at this

/-- On two unit vectors, the pointwise discrepancies accumulate to at most
twice the operator-norm error budget. -/
theorem sum_two_apply_errors_le {A B : E →L[ℂ] F} {ε : ℝ} {a b : E}
    (h : ApproximatesOperator A B ε) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖A a - B a‖ + ‖A b - B b‖ ≤ 2 * ε := by
  have hab := norm_apply_sub_le_of_unit h ha
  have hbb := norm_apply_sub_le_of_unit h hb
  linarith

#print axioms norm_apply_sub_le_of_approximatesOperator
#print axioms norm_apply_sub_le_of_unit
#print axioms sum_two_apply_errors_le

end

end QuantumFoundations.Complexity.OperatorNorm
