import QuantumFoundations.Complexity.SimulatedEvolution.NormPreserving

/-!
# C13b — Matrix-element perturbation bounds

If `x`, `y` are each perturbed by at most `εx`, `εy` (in norm, on the unit
sphere) and `T` is norm preserving, the matrix element `⟪x, T y⟫_ℂ` moves by
at most `εx + εy`: add and subtract `⟪x, T y'⟫_ℂ`, bound the two resulting
differences by Cauchy–Schwarz (`norm_inner_le_norm`) and norm preservation,
and add. No finite-dimensional compactness is used. The repository's inner
product `⟪·,·⟫_ℂ` is conjugate-linear in the first slot and linear in the
second (`inner_smul_left`/`inner_smul_right`), matching the direction used
throughout C1–C12; only additivity (`inner_sub_left`/`inner_sub_right`,
valid regardless of (conjugate-)linearity) is used below. All four
unit-norm hypotheses are kept (matching the intended use: both a state and
its norm-preserving-evolved perturbation are unit vectors), even though this
particular decomposition only consumes two of them; the unused primed
hypothesis is kept for signature symmetry with the downstream call sites,
where all four are genuinely available.
-/

namespace QuantumFoundations.Complexity.SimulatedEvolution

open scoped InnerProductSpace

open Gleason
open QuantumFoundations.BranchesRiedel

noncomputable section

variable {n : ℕ} {T : H n →L[ℂ] H n}

/-! ## C13b.1 — The general two-sided perturbation bound -/

/-- Perturbing both arguments of a matrix element of a norm-preserving
operator moves it by at most the sum of the two perturbation budgets. -/
theorem norm_inner_map_sub_inner_map_le
    (hT : IsNormPreserving T)
    {x x' y y' : H n} {εx εy : ℝ}
    (hx : ‖x‖ = 1) (_hx' : ‖x'‖ = 1) (_hy : ‖y‖ = 1) (hy' : ‖y'‖ = 1)
    (hxx' : ‖x - x'‖ ≤ εx) (hyy' : ‖y - y'‖ ≤ εy) :
    ‖⟪x, T y⟫_ℂ - ⟪x', T y'⟫_ℂ‖ ≤ εx + εy := by
  have hsplit : ⟪x, T y⟫_ℂ - ⟪x', T y'⟫_ℂ =
      ⟪x, T y - T y'⟫_ℂ + ⟪x - x', T y'⟫_ℂ := by
    rw [inner_sub_right, inner_sub_left]
    ring
  rw [hsplit]
  have h1 : ‖⟪x, T y - T y'⟫_ℂ‖ ≤ εy := by
    calc ‖⟪x, T y - T y'⟫_ℂ‖ ≤ ‖x‖ * ‖T y - T y'‖ := norm_inner_le_norm _ _
      _ = ‖T (y - y')‖ := by rw [hx, one_mul, map_sub]
      _ = ‖y - y'‖ := hT (y - y')
      _ ≤ εy := hyy'
  have h2 : ‖⟪x - x', T y'⟫_ℂ‖ ≤ εx := by
    calc ‖⟪x - x', T y'⟫_ℂ‖ ≤ ‖x - x'‖ * ‖T y'‖ := norm_inner_le_norm _ _
      _ = ‖x - x'‖ * ‖y'‖ := by rw [hT y']
      _ = ‖x - x'‖ := by rw [hy', mul_one]
      _ ≤ εx := hxx'
  calc ‖⟪x, T y - T y'⟫_ℂ + ⟪x - x', T y'⟫_ℂ‖
      ≤ ‖⟪x, T y - T y'⟫_ℂ‖ + ‖⟪x - x', T y'⟫_ℂ‖ := norm_add_le _ _
    _ ≤ εy + εx := add_le_add h1 h2
    _ = εx + εy := by ring

/-- Equal-error specialization: `2 * ε` when both perturbations share the
same budget. -/
theorem norm_inner_map_sub_inner_map_le_two_mul
    (hT : IsNormPreserving T)
    {x x' y y' : H n} {ε : ℝ}
    (hx : ‖x‖ = 1) (hx' : ‖x'‖ = 1) (hy : ‖y‖ = 1) (hy' : ‖y'‖ = 1)
    (hxx' : ‖x - x'‖ ≤ ε) (hyy' : ‖y - y'‖ ≤ ε) :
    ‖⟪x, T y⟫_ℂ - ⟪x', T y'⟫_ℂ‖ ≤ 2 * ε := by
  have h := norm_inner_map_sub_inner_map_le hT hx hx' hy hy' hxx' hyy'
  linarith

/-- Absolute-value stability of the matrix element's norm. -/
theorem abs_norm_inner_map_sub_le
    (hT : IsNormPreserving T)
    {x x' y y' : H n} {ε : ℝ}
    (hx : ‖x‖ = 1) (hx' : ‖x'‖ = 1) (hy : ‖y‖ = 1) (hy' : ‖y'‖ = 1)
    (hxx' : ‖x - x'‖ ≤ ε) (hyy' : ‖y - y'‖ ≤ ε) :
    |‖⟪x, T y⟫_ℂ‖ - ‖⟪x', T y'⟫_ℂ‖| ≤ 2 * ε := by
  calc |‖⟪x, T y⟫_ℂ‖ - ‖⟪x', T y'⟫_ℂ‖|
      ≤ ‖⟪x, T y⟫_ℂ - ⟪x', T y'⟫_ℂ‖ := abs_norm_sub_norm_le _ _
    _ ≤ 2 * ε := norm_inner_map_sub_inner_map_le_two_mul hT hx hx' hy hy' hxx' hyy'

/-! ## C13b.2 — Diagonal and cross-sum stability -/

/-- The diagonal-difference proxy expression moves by at most `4 * ε` under
independent `ε`-perturbations of each of the two unit states (each
perturbation itself landing on a unit vector). -/
theorem diagonal_difference_stability
    (hT : IsNormPreserving T)
    {a a' b b' : H n} {ε : ℝ}
    (ha0 : ‖a‖ = 1) (ha0' : ‖a'‖ = 1) (hb0 : ‖b‖ = 1) (hb0' : ‖b'‖ = 1)
    (ha : ‖a - a'‖ ≤ ε) (hb : ‖b - b'‖ ≤ ε) :
    ‖(⟪a, T a⟫_ℂ - ⟪b, T b⟫_ℂ) - (⟪a', T a'⟫_ℂ - ⟪b', T b'⟫_ℂ)‖ ≤ 4 * ε := by
  have hsplit :
      (⟪a, T a⟫_ℂ - ⟪b, T b⟫_ℂ) - (⟪a', T a'⟫_ℂ - ⟪b', T b'⟫_ℂ) =
        (⟪a, T a⟫_ℂ - ⟪a', T a'⟫_ℂ) - (⟪b, T b⟫_ℂ - ⟪b', T b'⟫_ℂ) := by ring
  rw [hsplit]
  have h1 := norm_inner_map_sub_inner_map_le_two_mul hT ha0 ha0' ha0 ha0' ha ha
  have h2 := norm_inner_map_sub_inner_map_le_two_mul hT hb0 hb0' hb0 hb0' hb hb
  calc ‖(⟪a, T a⟫_ℂ - ⟪a', T a'⟫_ℂ) - (⟪b, T b⟫_ℂ - ⟪b', T b'⟫_ℂ)‖
      ≤ ‖⟪a, T a⟫_ℂ - ⟪a', T a'⟫_ℂ‖ + ‖⟪b, T b⟫_ℂ - ⟪b', T b'⟫_ℂ‖ := norm_sub_le _ _
    _ ≤ 2 * ε + 2 * ε := add_le_add h1 h2
    _ = 4 * ε := by ring

/-- The cross-sum proxy expression moves by at most `4 * ε` under
independent `ε`-perturbations of each of the two unit states. -/
theorem cross_sum_stability
    (hT : IsNormPreserving T)
    {a a' b b' : H n} {ε : ℝ}
    (ha0 : ‖a‖ = 1) (ha0' : ‖a'‖ = 1) (hb0 : ‖b‖ = 1) (hb0' : ‖b'‖ = 1)
    (ha : ‖a - a'‖ ≤ ε) (hb : ‖b - b'‖ ≤ ε) :
    |(‖⟪a, T b⟫_ℂ‖ + ‖⟪b, T a⟫_ℂ‖) - (‖⟪a', T b'⟫_ℂ‖ + ‖⟪b', T a'⟫_ℂ‖)| ≤ 4 * ε := by
  have h1 := abs_norm_inner_map_sub_le hT ha0 ha0' hb0 hb0' ha hb
  have h2 := abs_norm_inner_map_sub_le hT hb0 hb0' ha0 ha0' hb ha
  have hrw :
      (‖⟪a, T b⟫_ℂ‖ + ‖⟪b, T a⟫_ℂ‖) - (‖⟪a', T b'⟫_ℂ‖ + ‖⟪b', T a'⟫_ℂ‖) =
        (‖⟪a, T b⟫_ℂ‖ - ‖⟪a', T b'⟫_ℂ‖) + (‖⟪b, T a⟫_ℂ‖ - ‖⟪b', T a'⟫_ℂ‖) := by ring
  rw [hrw]
  calc |(‖⟪a, T b⟫_ℂ‖ - ‖⟪a', T b'⟫_ℂ‖) + (‖⟪b, T a⟫_ℂ‖ - ‖⟪b', T a'⟫_ℂ‖)|
      ≤ |‖⟪a, T b⟫_ℂ‖ - ‖⟪a', T b'⟫_ℂ‖| + |‖⟪b, T a⟫_ℂ‖ - ‖⟪b', T a'⟫_ℂ‖| := abs_add_le _ _
    _ ≤ 2 * ε + 2 * ε := add_le_add h1 h2
    _ = 4 * ε := by ring

#print axioms norm_inner_map_sub_inner_map_le
#print axioms diagonal_difference_stability
#print axioms cross_sum_stability

end

end QuantumFoundations.Complexity.SimulatedEvolution
