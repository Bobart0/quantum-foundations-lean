import QuantumFoundations.FiniteTensor.Transport
import QuantumFoundations.Selectors.Pinning
namespace QuantumFoundations.Selector
open QuantumFoundations
open QuantumFoundations.FiniteTensor
open Gleason
open scoped InnerProductSpace
noncomputable section
def AncillaNeutralUnder {n a : ℕ} (D : TensorDecomposition n a) (σSA : Selector (n * a)) (σS : Selector n) : Prop := ∀ (ψ : H n) (η : H a), ‖ψ‖ = 1 → ‖η‖ = 1 → partialTraceAncilla (D.toCoordinatesOperator (σSA.ρ (D.productState ψ η))) = σS.ρ ψ
def TensorMultiplicativeUnder {n a : ℕ} (D : TensorDecomposition n a) (σS : Selector n) (σA : Selector a) (σSA : Selector (n * a)) : Prop := ∀ (ψ : H n) (η : H a), ‖ψ‖ = 1 → ‖η‖ = 1 → D.toCoordinatesOperator (σSA.ρ (D.productState ψ η)) = tensorOperator (σS.ρ ψ) (σA.ρ η)
theorem mul_dimension_ge_two {n a : ℕ} (hn : 2 ≤ n) (ha : 2 ≤ a) : 2 ≤ n * a := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ha' : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hna : (n : ℝ) * a ≥ 4 := by nlinarith
  exact_mod_cast (show (2 : ℝ) ≤ n * a by linarith)
theorem dimension_cast_pos {d : ℕ} (hd : 2 ≤ d) : 0 < (d : ℝ) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  linarith
theorem dimension_sub_one_pos {d : ℕ} (hd : 2 ≤ d) : 0 < (d : ℝ) - 1 := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  linarith
theorem one_sub_inv_dim_div_sub_one {d : ℕ} (hd : 2 ≤ d) :
    (1 - 1 / (d : ℝ)) / ((d : ℝ) - 1) = 1 / (d : ℝ) := by
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt (dimension_cast_pos hd)
  have hd1 : (d : ℝ) - 1 ≠ 0 := ne_of_gt (dimension_sub_one_pos hd)
  field_simp [hd0, hd1]
theorem inv_dim_nonneg {d : ℕ} (hd : 2 ≤ d) : 0 ≤ 1 / (d : ℝ) := by
  exact le_of_lt (one_div_pos.mpr (dimension_cast_pos hd))
theorem inv_dim_le_one {d : ℕ} (hd : 2 ≤ d) : 1 / (d : ℝ) ≤ 1 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  exact (div_le_iff₀ (dimension_cast_pos hd)).2 (by linarith)
theorem mul_unit_interval_le_one {t u : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : t * u ≤ 1 := by nlinarith
theorem tDensity_at_one {d : ℕ} (v : H d) : tDensity d 1 v = projL (ℂ ∙ v) := by
  unfold tDensity
  norm_num
theorem tDensity_at_inv_dim {d : ℕ} (hd : 2 ≤ d) {v : H d} (hv : ‖v‖ = 1) : tDensity d (1 / (d : ℝ)) v = ((1 / (d : ℝ) : ℝ) : ℂ) • (LinearMap.id : H d →ₗ[ℂ] H d) := by
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
    linarith
  have hc : (1 - (1 / (d : ℝ))) / ((d : ℝ) - 1) = 1 / (d : ℝ) := by field_simp
  unfold tDensity
  rw [hc, ← smul_add, projL_add_projL_compl]
end
end QuantumFoundations.Selector
