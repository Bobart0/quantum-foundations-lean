import Mathlib

/-!
# C15a — Additive maps on non-negative reals

The only analytic ingredient in C15 is that an additive non-negative-real
function is multiplication by its value at one.  Non-negativity makes the
function monotone; rational homogeneity and density then determine every
value.  No continuity assumption is needed.
-/

namespace QuantumFoundations.BornRule.RestrictedRecordSectors

open scoped NNReal

/-- An additive function on `ℝ≥0` is multiplication by a fixed coefficient. -/
theorem nnreal_additive_eq_mul
    (f : ℝ≥0 → ℝ≥0)
    (hadd : ∀ x y, f (x + y) = f x + f y) :
    ∃ c : ℝ≥0, ∀ x : ℝ≥0, f x = c * x := by
  have hzero : f 0 = 0 := by
    exact add_left_cancel (by simpa only [add_zero] using (hadd 0 0).symm)
  let F : ℝ≥0 →+ ℝ≥0 :=
    { toFun := f
      map_zero' := hzero
      map_add' := hadd }
  have hmono : Monotone f := by
    intro x y hxy
    obtain ⟨z, rfl⟩ := exists_add_of_le hxy
    rw [hadd]
    exact le_add_right (le_refl _)
  let c : ℝ≥0 := f 1
  have hrat (q : ℚ) (hq : 0 ≤ q) :
      f (Real.toNNReal (q : ℝ)) = c * Real.toNNReal (q : ℝ) := by
    have harg : Real.toNNReal (q : ℝ) = (q.toNNRat : ℝ≥0) := by
      apply NNReal.eq
      have hqreal : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      rw [Real.coe_toNNReal _ hqreal]
      change (q : ℝ) = ((q.toNNRat : ℚ) : ℝ)
      exact congrArg (fun r : ℚ => (r : ℝ)) (Rat.coe_toNNRat q hq).symm
    rw [harg]
    have hm := map_nnrat_smul F q.toNNRat (1 : ℝ≥0)
    change f (q.toNNRat • (1 : ℝ≥0)) = q.toNNRat • f 1 at hm
    change f ((q.toNNRat : ℝ≥0) * 1) = (q.toNNRat : ℝ≥0) * f 1 at hm
    calc
      f (q.toNNRat : ℝ≥0) = (q.toNNRat : ℝ≥0) * f 1 := by
        simpa only [mul_one] using hm
      _ = c * (q.toNNRat : ℝ≥0) := by
        change (q.toNNRat : ℝ≥0) * f 1 = f 1 * (q.toNNRat : ℝ≥0)
        exact mul_comm _ _
  refine ⟨c, fun x => ?_⟩
  by_cases hc : c = 0
  · have hcx : c * x = 0 := by rw [hc, zero_mul]
    rw [hcx]
    apply le_antisymm
    · obtain ⟨n, hn⟩ := exists_nat_ge x
      have hfn : f (n : ℝ≥0) = 0 := by
        have hnrat := hrat (n : ℚ) (by positivity)
        simpa only [Rat.cast_natCast, Real.toNNReal_natCast, hc, zero_mul] using hnrat
      rw [← hfn]
      exact hmono hn
    · exact zero_le
  · have hcpos : 0 < c := lt_of_le_of_ne zero_le (Ne.symm hc)
    apply le_antisymm
    · by_contra hnot
      have hlt : c * x < f x := lt_of_not_ge hnot
      have hxdiv : x < f x / c :=
        (lt_div_iff₀ hcpos).2 (by simpa only [mul_comm] using hlt)
      obtain ⟨q, hq0, hxq, hqdiv⟩ :=
        (NNReal.lt_iff_exists_rat_btwn x (f x / c)).mp hxdiv
      have hqmul : c * Real.toNNReal (q : ℝ) < f x :=
        by simpa only [mul_comm] using (lt_div_iff₀ hcpos).1 hqdiv
      have hxfq : f x ≤ f (Real.toNNReal (q : ℝ)) := hmono hxq.le
      rw [hrat q hq0] at hxfq
      exact (not_lt_of_ge hxfq) hqmul
    · by_contra hnot
      have hlt : f x < c * x := lt_of_not_ge hnot
      have hdivx : f x / c < x :=
        (div_lt_iff₀ hcpos).2 (by simpa only [mul_comm] using hlt)
      obtain ⟨q, hq0, hdivq, hqx⟩ :=
        (NNReal.lt_iff_exists_rat_btwn (f x / c) x).mp hdivx
      have hfmul : f x < c * Real.toNNReal (q : ℝ) :=
        by simpa only [mul_comm] using (div_lt_iff₀ hcpos).1 hdivq
      have hfqfx : f (Real.toNNReal (q : ℝ)) ≤ f x := hmono hqx.le
      rw [hrat q hq0] at hfqfx
      exact (not_lt_of_ge hfqfx) hfmul

end QuantumFoundations.BornRule.RestrictedRecordSectors
