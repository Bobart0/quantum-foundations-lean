import QuantumFoundations.Selectors.BridgeDefs

namespace QuantumFoundations.Selector

theorem ancilla_self_value_eq_forces_t_eq_one {n a : ℕ}
    (hn : 2 ≤ n) (ha : 2 ≤ a) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : t + (a - 1 : ℝ) * ((1 - t) / ((n * a : ℝ) - 1)) = t) : t = 1 := by
  have hprod_nat : 4 ≤ n * a := by
    have hmul := Nat.mul_le_mul hn ha
    norm_num at hmul ⊢
    exact hmul
  have hprod : (4 : ℝ) ≤ (n * a : ℝ) := by exact_mod_cast hprod_nat
  have hna_pos : (0 : ℝ) < (n * a : ℝ) - 1 := by
    norm_num [Nat.cast_mul] at hprod ⊢
    nlinarith
  have ha1 : (0 : ℝ) < (a : ℝ) - 1 := by
    have ha' : (2 : ℝ) ≤ a := by exact_mod_cast ha
    linarith
  have hzero : ((a : ℝ) - 1) * ((1 - t) / ((n * a : ℝ) - 1)) = 0 := by
    linarith [h]
  have hquot : (1 - t) / ((n * a : ℝ) - 1) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (ne_of_gt ha1)
  have hnum : 1 - t = 0 :=
    (div_eq_zero_iff.mp hquot).resolve_right (ne_of_gt hna_pos)
  linarith

end QuantumFoundations.Selector
