import QuantumFoundations.Selectors.BridgeDefs
import QuantumFoundations.FiniteTensor.Transport
namespace QuantumFoundations.Selector
open QuantumFoundations
open QuantumFoundations.FiniteTensor
open Gleason
open scoped InnerProductSpace
noncomputable section
theorem reduced_tDensity_apply_self {n a : ℕ} (hn : 2 ≤ n) (ha : 2 ≤ a) (D : TensorDecomposition n a) {ψ : H n} {η : H a} (hψ : ‖ψ‖ = 1) (hη : ‖η‖ = 1) (t : ℝ) : partialTraceAncilla (D.toCoordinatesOperator (tDensity (n * a) t (D.productState ψ η))) ψ = (((t + ((a : ℝ) - 1) * ((1 - t) / ((n * a : ℝ) - 1)) : ℝ) : ℂ) • ψ) := by
  rw [partialTrace_tDensity_product hn ha D hψ hη t]
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.sub_apply]
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [QuantumFoundations.Uhlhorn.projL_singleton_unit ψ ψ hψ, inner_self_eq_norm_sq_to_K, hψ]
  norm_num
  ring_nf
  module
theorem reduced_tDensity_selfValue {n a : ℕ} (hn : 2 ≤ n) (ha : 2 ≤ a) (D : TensorDecomposition n a) {ψ : H n} {η : H a} (hψ : ‖ψ‖ = 1) (hη : ‖η‖ = 1) (t : ℝ) : (⟪ψ, partialTraceAncilla (D.toCoordinatesOperator (tDensity (n * a) t (D.productState ψ η))) ψ⟫_ℂ).re = t + ((a : ℝ) - 1) * ((1 - t) / ((n * a : ℝ) - 1)) := by
  rw [reduced_tDensity_apply_self hn ha D hψ hη t]
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, hψ]
  norm_num
  have hden : (0 : ℝ) < (n : ℝ) * a - 1 := by
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have ha' : (2 : ℝ) ≤ a := by exact_mod_cast ha
    nlinarith
  have hden0 : (n : ℝ) * a - 1 ≠ 0 := ne_of_gt hden
  left
  norm_num [Complex.div_re, Complex.normSq]
  field_simp [hden0]
end
end QuantumFoundations.Selector
