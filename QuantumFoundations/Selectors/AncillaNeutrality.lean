import QuantumFoundations.Selectors.ReducedIsotropic

namespace QuantumFoundations.Selector

open QuantumFoundations
open QuantumFoundations.FiniteTensor
open Gleason
open scoped InnerProductSpace

noncomputable section

theorem ancilla_scalar_eq_forces_t_eq_one {n a : ℕ}
    (hn : 2 ≤ n) (ha : 2 ≤ a) {t : ℝ}
    (h : t + (a - 1 : ℝ) * ((1 - t) / ((n * a : ℝ) - 1)) = t) : t = 1 := by
  have hna_pos : (0 : ℝ) < (n : ℝ) * a - 1 := by
    have h := dimension_sub_one_pos (mul_dimension_ge_two hn ha)
    simpa [Nat.cast_mul] using h
  have ha_pos : (0 : ℝ) < (a : ℝ) - 1 :=
    dimension_sub_one_pos ha
  have hzero : ((a : ℝ) - 1) * ((1 - t) / ((n : ℝ) * a - 1)) = 0 := by
    linarith [h]
  have hquot : (1 - t) / ((n : ℝ) * a - 1) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (ne_of_gt ha_pos)
  have hnum : 1 - t = 0 :=
    (div_eq_zero_iff.mp hquot).resolve_right (ne_of_gt hna_pos)
  linarith

theorem tSelector_one_ancillaNeutral
    (hn : 2 ≤ n)
    (ha : 2 ≤ a)
    (D : TensorDecomposition n a) :
    AncillaNeutralUnder D
      (tSelector (n * a) (mul_dimension_ge_two hn ha) 1 (by norm_num) (by norm_num))
      (tSelector n hn 1 (by norm_num) (by norm_num)) := by
  intro ψ η hψ hη
  change partialTraceAncilla
      (D.toCoordinatesOperator (tDensity (n * a) 1 (D.productState ψ η))) =
    tDensity n 1 ψ
  rw [partialTrace_tDensity_product hn ha D hψ hη 1]
  rw [tDensity_at_one]
  norm_num

private theorem tSelector_ancillaNeutral_implies_t_eq_one
    (hn : 2 ≤ n)
    (ha : 2 ≤ a)
    (D : TensorDecomposition n a)
    {t : ℝ}
    (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1)
    (hNeutral :
      AncillaNeutralUnder D
        (tSelector (n * a) (mul_dimension_ge_two hn ha) t ht0 ht1)
        (tSelector n hn t ht0 ht1)) :
    t = 1 := by
  let ψ : H n := stdKet ⟨0, by omega⟩
  let η : H a := stdKet ⟨0, by omega⟩
  have hψ : ‖ψ‖ = 1 := by
    dsimp [ψ]
    exact stdKet_norm _
  have hη : ‖η‖ = 1 := by
    dsimp [η]
    exact stdKet_norm _
  have hop := hNeutral ψ η hψ hη
  change partialTraceAncilla
      (D.toCoordinatesOperator (tDensity (n * a) t (D.productState ψ η))) =
    tDensity n t ψ at hop
  have hquad := congrArg
    (fun A : H n →ₗ[ℂ] H n => (⟪ψ, A ψ⟫_ℂ).re) hop
  have hright : (⟪ψ, tDensity n t ψ ψ⟫_ℂ).re = t := by
    rw [tDensity_apply_self hψ t, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  have hscalar :
      t + ((a : ℝ) - 1) * ((1 - t) / ((n * a : ℝ) - 1)) = t := by
    calc
      t + ((a : ℝ) - 1) * ((1 - t) / ((n * a : ℝ) - 1)) =
          (⟪ψ, partialTraceAncilla
            (D.toCoordinatesOperator
              (tDensity (n * a) t (D.productState ψ η))) ψ⟫_ℂ).re := by
            symm
            exact reduced_tDensity_selfValue hn ha D hψ hη t
      _ = (⟪ψ, tDensity n t ψ ψ⟫_ℂ).re := hquad
      _ = t := hright
  exact ancilla_scalar_eq_forces_t_eq_one hn ha hscalar

theorem tSelector_ancillaNeutral_iff_t_eq_one
    (hn : 2 ≤ n)
    (ha : 2 ≤ a)
    (D : TensorDecomposition n a)
    {t : ℝ}
    (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    AncillaNeutralUnder D
      (tSelector (n * a) (mul_dimension_ge_two hn ha) t ht0 ht1)
      (tSelector n hn t ht0 ht1) ↔
      t = 1 := by
  constructor
  · exact tSelector_ancillaNeutral_implies_t_eq_one hn ha D ht0 ht1
  · intro ht
    subst t
    exact tSelector_one_ancillaNeutral hn ha D

theorem bornSelector_ancillaNeutral
    (hn : 2 ≤ n)
    (ha : 2 ≤ a)
    (D : TensorDecomposition n a) :
    AncillaNeutralUnder D (bornSelector (n * a)) (bornSelector n) := by
  intro ψ η hψ hη
  change partialTraceAncilla
      (D.toCoordinatesOperator (projL (ℂ ∙ D.productState ψ η))) =
    projL (ℂ ∙ ψ)
  rw [D.toCoordinatesOperator_projL_span, D.toBipartite_productState]
  exact partialTraceAncilla_productProjection hψ hη

theorem tSelector_ancillaNeutral_implies_nsnc1
    (hn : 2 ≤ n)
    (ha : 2 ≤ a)
    (D : TensorDecomposition n a)
    {t : ℝ}
    (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1)
    (hNeutral :
      AncillaNeutralUnder D
        (tSelector (n * a) (mul_dimension_ge_two hn ha) t ht0 ht1)
        (tSelector n hn t ht0 ht1)) :
    NSNC1 (tSelector n hn t ht0 ht1) := by
  have ht : t = 1 :=
    (tSelector_ancillaNeutral_iff_t_eq_one hn ha D ht0 ht1).mp hNeutral
  exact (tSelector_nsnc1_iff_t_eq_one hn ht0 ht1).mpr ht

end
end QuantumFoundations.Selector
