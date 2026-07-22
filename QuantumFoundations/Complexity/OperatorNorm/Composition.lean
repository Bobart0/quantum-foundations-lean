import QuantumFoundations.Complexity.OperatorNorm.Approximation

/-!
# C12h — Composition laws for operator-norm approximation

Generic, reusable composition estimates for `ApproximatesOperator`, intended
to support future (C13) accumulated simulation error along a composed chain
of circuit stages. Purely a normed-space fact: no quantum records or
circuits are mentioned. Unitary/isometric specializations (operator norm
exactly `1`) were not added: nothing downstream in C12 needs them, and
adding them would be scope creep beyond the mandatory record-readout bridge.
-/

namespace QuantumFoundations.Complexity.OperatorNorm

noncomputable section

variable {E F G : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
    [NormedSpace ℂ E] [NormedSpace ℂ F] [NormedSpace ℂ G]

/-- Left composition with a bounded operator scales the approximation error
by the bound. -/
theorem approximation_comp_left
    {A B : E →L[ℂ] F} {ε : ℝ} (h : ApproximatesOperator A B ε)
    (L : F →L[ℂ] G) {M : ℝ} (hM : ‖L‖ ≤ M) :
    ApproximatesOperator (L.comp A) (L.comp B) (M * ε) := by
  have hε0 : 0 ≤ ε := (norm_nonneg (A - B)).trans h
  have hsub : L.comp A - L.comp B = L.comp (A - B) := by
    ext x
    simp
  have hbase : ApproximatesOperator (L.comp A) (L.comp B) (‖L‖ * ε) := by
    unfold ApproximatesOperator
    rw [hsub]
    calc ‖L.comp (A - B)‖ ≤ ‖L‖ * ‖A - B‖ := ContinuousLinearMap.opNorm_comp_le L (A - B)
      _ ≤ ‖L‖ * ε := mul_le_mul_of_nonneg_left h (norm_nonneg L)
  exact hbase.mono (mul_le_mul_of_nonneg_right hM hε0)

/-- Right composition with a bounded operator scales the approximation error
by the bound. -/
theorem approximation_comp_right
    {A B : F →L[ℂ] G} {ε : ℝ} (h : ApproximatesOperator A B ε)
    (R : E →L[ℂ] F) {M : ℝ} (hM : ‖R‖ ≤ M) :
    ApproximatesOperator (A.comp R) (B.comp R) (ε * M) := by
  have hε0 : 0 ≤ ε := (norm_nonneg (A - B)).trans h
  have hsub : A.comp R - B.comp R = (A - B).comp R := by
    ext x
    simp
  have hbase : ApproximatesOperator (A.comp R) (B.comp R) (ε * ‖R‖) := by
    unfold ApproximatesOperator
    rw [hsub]
    calc ‖(A - B).comp R‖ ≤ ‖A - B‖ * ‖R‖ := ContinuousLinearMap.opNorm_comp_le (A - B) R
      _ ≤ ε * ‖R‖ := mul_le_mul_of_nonneg_right h (norm_nonneg R)
  exact hbase.mono (mul_le_mul_of_nonneg_left hM hε0)

/-- Two-sided composition: approximation errors on both factors combine
asymmetrically, weighted by the other factor's operator norm. Standard
triangle-inequality splitting:
`A ∘ C - B ∘ D = A ∘ (C - D) + (A - B) ∘ D`. -/
theorem approximation_comp_two_sided
    {A B : F →L[ℂ] G} {ε : ℝ} (hAB : ApproximatesOperator A B ε)
    {C D : E →L[ℂ] F} {η : ℝ} (hCD : ApproximatesOperator C D η) :
    ApproximatesOperator (A.comp C) (B.comp D) (‖A‖ * η + ε * ‖D‖) := by
  have hsplit : A.comp C - B.comp D = A.comp (C - D) + (A - B).comp D := by
    ext x
    simp
  unfold ApproximatesOperator at *
  rw [hsplit]
  calc ‖A.comp (C - D) + (A - B).comp D‖
      ≤ ‖A.comp (C - D)‖ + ‖(A - B).comp D‖ := norm_add_le _ _
    _ ≤ ‖A‖ * ‖C - D‖ + ‖A - B‖ * ‖D‖ :=
        add_le_add (ContinuousLinearMap.opNorm_comp_le A (C - D))
          (ContinuousLinearMap.opNorm_comp_le (A - B) D)
    _ ≤ ‖A‖ * η + ε * ‖D‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hCD (norm_nonneg A))
          (mul_le_mul_of_nonneg_right hAB (norm_nonneg D))

#print axioms approximation_comp_left
#print axioms approximation_comp_right
#print axioms approximation_comp_two_sided

end

end QuantumFoundations.Complexity.OperatorNorm
